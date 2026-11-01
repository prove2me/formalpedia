-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.theorem_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T12:24:28.705512+00:00
-- url     : https://prove2.me/submissions/91730c53-4ffd-416c-aea3-04360070ebfd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Policy
import Definitions.Def_ForkJoinCtrl_Tracking_SRBM
import Definitions.Def_PuhaWardFluid_Limit_Paths
import Theorems.Thm_ForkJoinCtrl_Tracking_proposition_2
import Theorems.Thm_ForkJoinCtrl_Tracking_proposition_3
import Theorems.Thm_ForkJoinCtrl_Tracking_lemma_1_part_2
import Theorems.Thm_ForkJoinCtrl_Tracking_srbm_cost_no_atom


open Filter Topology
open scoped NNReal

namespace FJT2

theorem j1_pointwise {S : Type*} [PseudoMetricSpace S] (xs : ℕ → ℝ≥0 → S) (x : ℝ≥0 → S)
    (h : PuhaWardFluid.Limit.J1Tendsto dist xs x) (t0 : ℝ≥0) (hc : ContinuousAt x t0) :
    Tendsto (fun n => xs n t0) atTop (𝓝 (x t0)) := by
  obtain ⟨_, _, l, hl, hxl, hlid⟩ := h
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.1 hc (ε / 2) (by positivity)
  set T' : ℝ≥0 := t0 + 1
  have h1 := hlid T' (min δ 1) (lt_min hδ one_pos)
  have h2 := hxl T' (ε / 2) (by positivity)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (h1.and h2)
  refine ⟨N0, fun n hn => ?_⟩
  obtain ⟨hA, hB⟩ := hN0 n hn
  obtain ⟨sn, hsn⟩ := (hl n).2.2 t0
  have hsT : sn ≤ T' := by
    by_contra hgt
    push Not at hgt
    have hlt : l n T' < l n sn := (hl n).2.1 hgt
    rw [hsn] at hlt
    have := hA T' le_rfl
    simp only [id, Real.dist_eq] at this
    have hm : min δ 1 ≤ 1 := min_le_right _ _
    have hlt' : ((l n T' : ℝ≥0) : ℝ) < (t0 : ℝ) := by exact_mod_cast hlt
    have hT : ((T' : ℝ≥0) : ℝ) = (t0 : ℝ) + 1 := by simp [T']
    rw [hT] at this
    have := (abs_lt.1 this).1
    linarith
  have hd1 : dist (x sn) (x t0) < ε / 2 := by
    apply hδc
    have := hA sn hsT
    rw [hsn] at this
    simp only [id, Real.dist_eq] at this
    rw [NNReal.dist_eq, abs_sub_comm]
    exact lt_of_lt_of_le this (min_le_left _ _)
  have hd2 : dist (xs n (l n sn)) (x sn) < ε / 2 := by simpa using hB sn hsT
  rw [hsn] at hd2
  calc dist (xs n t0) (x t0) ≤ dist (xs n t0) (x sn) + dist (x sn) (x t0) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hd2 hd1
    _ = ε := by ring

end FJT2


open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
open ForkJoinCtrl.Tracking

namespace FJT2

variable {N : Network}

/-- projection onto the nonnegative orthant -/
def clampP (b : LPParam N) : LPParam N := (fun k => max (b.1 k) 0, fun i => max (b.2 i) 0)

theorem clampP_nonneg (b : LPParam N) : (clampP b).Nonneg :=
  ⟨fun k => le_max_right _ _, fun i => le_max_right _ _⟩

theorem clampP_of_nonneg {b : LPParam N} (hb : b.Nonneg) : clampP b = b := by
  ext k
  · simp [clampP, max_eq_left (hb.1 k)]
  · simp [clampP, max_eq_left (hb.2 k)]

theorem norm_clampP_sub (b b' : LPParam N) : ‖clampP b - clampP b'‖ ≤ ‖b - b'‖ := by
  rw [Prod.norm_def, Prod.norm_def]
  apply max_le_max
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun k => ?_)
    refine le_trans ?_ (norm_le_pi_norm _ k)
    simp only [clampP, Prod.fst_sub, Pi.sub_apply, Real.norm_eq_abs]
    exact abs_max_sub_max_le_abs _ _ _
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 (fun k => ?_)
    refine le_trans ?_ (norm_le_pi_norm _ k)
    simp only [clampP, Prod.snd_sub, Pi.sub_apply, Real.norm_eq_abs]
    exact abs_max_sub_max_le_abs _ _ _

/-- `z` composed with the projection on the orthant: a globally Lipschitz extension of `z`. -/
noncomputable def zc (N : Network) (b : LPParam N) : ℝ := z N (clampP b)

theorem zc_lip (C1 : ℝ) (hC1 : 0 < C1)
    (hz : ∀ b1 b2 : LPParam N, b1.Nonneg → b2.Nonneg → |z N b1 - z N b2| ≤ C1 * ‖b1 - b2‖) :
    Continuous (zc N) := by
  have : LipschitzWith (Real.toNNReal C1) (zc N) := by
    apply LipschitzWith.of_dist_le_mul
    intro b b'
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hC1.le]
    exact (hz _ _ (clampP_nonneg b) (clampP_nonneg b')).trans
      (mul_le_mul_of_nonneg_left (norm_clampP_sub b b') hC1.le)
  exact this.continuous

theorem zc_eq {b : LPParam N} (hb : b.Nonneg) : zc N b = z N b := by
  simp [zc, clampP_of_nonneg hb]


section Facts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Model N Ω P}

theorem bhat_nonneg {r : ℕ} (X : Run M r) {ω : Ω} (hω : X.toPaths.IsAdmissibleAt M r ω)
    {s : ℝ} (hs : 0 ≤ s) : (X.bhat ω s).Nonneg := by
  have hu : 0 ≤ (r : ℝ) ^ 2 * s := by positivity
  have hc : 0 ≤ (r : ℝ) * ((r : ℝ) ^ 2)⁻¹ := by positivity
  refine ⟨fun k => ?_, fun i => ?_⟩
  · show 0 ≤ (r : ℝ) * (((r : ℝ) ^ 2)⁻¹ * X.Qk k ω ((r : ℝ) ^ 2 * s))
    rw [← mul_assoc]
    exact mul_nonneg hc (hω.2.2.1 k _ hu).1
  · show 0 ≤ (r : ℝ) * (((r : ℝ) ^ 2)⁻¹ * X.W i ω ((r : ℝ) ^ 2 * s))
    rw [← mul_assoc]
    apply mul_nonneg hc
    apply Finset.sum_nonneg
    intro j hj
    have hij : N.P i j = true := by simpa [Network.Ji] using hj
    exact div_nonneg (hω.2.2.2.1 i j _ hij hu).1 (N.mu_pos i j hij).le

variable {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {Z : Ω' → ℝ → Fin M.a1 → ℝ}

theorem limitVec_nonneg (hZ : IsSRBM P' M.Theta M.Sigma Z) (ω' : Ω') {s : ℝ} (hs : 0 ≤ s) :
    (M.limitVec Z ω' s).Nonneg := by
  obtain ⟨X, Y, -, hR⟩ := hZ
  have h := (hR ω').2.2.2.2.1 s hs
  refine ⟨fun k => ?_, fun i => ?_⟩
  · dsimp only [Model.limitVec]
    split_ifs with hk
    · exact h _
    · exact le_rfl
  · exact h _

theorem limitVec_cont (hZ : IsSRBM P' M.Theta M.Sigma Z) (ω' : Ω') :
    Continuous (fun s : ℝ≥0 => M.limitVec Z ω' (s : ℝ)) := by
  obtain ⟨X, Y, -, hR⟩ := hZ
  have hc : ContinuousOn (Z ω') (Set.Ici 0) := (hR ω').2.2.1
  have hc' : Continuous (fun s : ℝ≥0 => Z ω' (s : ℝ)) :=
    hc.comp_continuous NNReal.continuous_coe (fun s => Set.mem_Ici.2 s.2)
  apply Continuous.prodMk
  · apply continuous_pi
    intro k
    show Continuous (fun s : ℝ≥0 =>
      (if hk : M.heavy k = true then Z ω' (s : ℝ) (M.coordEquiv (.inl ⟨k, hk⟩)) else 0))
    split_ifs with hk
    · exact (continuous_apply _).comp hc'
    · exact continuous_const
  · apply continuous_pi
    intro i
    exact (continuous_apply _).comp hc'

end Facts

/-- continuity at `t0` of a càdlàg path whose values along `t0 - 1/(m+1)` converge to the value
at `t0` -/
theorem contAt_of_cadlag {S : Type*} [MetricSpace S] (x : ℝ≥0 → S)
    (hx : PuhaWardFluid.Limit.IsCadlag x) (t0 : ℝ≥0)
    (hseq : Tendsto (fun m : ℕ => x (t0 - 1 / ((m : ℝ≥0) + 1))) atTop (𝓝 (x t0))) :
    ContinuousAt x t0 := by
  rcases eq_or_ne t0 0 with h0 | h0
  · have := hx.1 t0
    rw [h0] at this ⊢
    have hI : Set.Ici (0 : ℝ≥0) = Set.univ := by ext s; simp
    rw [hI, continuousWithinAt_univ] at this
    exact this
  · have ht0 : 0 < t0 := pos_iff_ne_zero.2 h0
    obtain ⟨a, ha⟩ := hx.2 t0 ht0
    have hu : Tendsto (fun m : ℕ => t0 - 1 / ((m : ℝ≥0) + 1)) atTop (𝓝[<] t0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ≥0) + 1)) atTop (𝓝 0) := by
          have hr : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          rw [← NNReal.tendsto_coe]; simpa using hr
        have := (tendsto_const_nhds (x := t0)).sub h1
        simpa using this
      · have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ≥0) + 1)) atTop (𝓝 0) := by
          have hr : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          rw [← NNReal.tendsto_coe]; simpa using hr
        filter_upwards [h1.eventually (gt_mem_nhds ht0)] with m hm
        simp only [Set.mem_Iio]
        apply tsub_lt_self ht0
        positivity
    have hlim := ha.comp hu
    have hax : a = x t0 := tendsto_nhds_unique hlim hseq
    rw [hax] at ha
    rw [continuousAt_iff_continuous_left_right]
    refine ⟨continuousWithinAt_Iio_iff_Iic.1 ha, hx.1 t0⟩


/-- one-dimensional marginal convergence from the coupling form of convergence in distribution,
at a time where the limit has continuous paths, for a level `c` that is not an atom -/
theorem kc {S : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ≥0 → S)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y' : Ω' → ℝ≥0 → S)
    {Ω'' : Type*} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (W : ℕ → Ω'' → ℝ≥0 → S) (W' : Ω'' → ℝ≥0 → S)
    (hW : ∀ n, IdentDistrib (W n) (Y n) P'' P) (hW' : IdentDistrib W' Y' P'' P')
    (hJ : ∀ᵐ ω ∂P'', PuhaWardFluid.Limit.J1Tendsto dist (fun n => W n ω) (W' ω))
    (hY'c : ∀ ω', Continuous (Y' ω')) (f : S → ℝ) (hf : Continuous f) (t0 : ℝ≥0) (c : ℝ)
    (hatom : P' {ω' | f (Y' ω' t0) = c} = 0) :
    Tendsto (fun n => P {ω | c < f (Y n ω t0)}) atTop (𝓝 (P' {ω' | c < f (Y' ω' t0)})) := by
  have hev : Measurable (fun x : ℝ≥0 → S => x t0) := measurable_pi_apply t0
  have hF : Measurable (fun x : ℝ≥0 → S => f (x t0)) := hf.measurable.comp hev
  set u : ℕ → ℝ≥0 := fun m => t0 - 1 / ((m : ℝ≥0) + 1)
  set Acp := {x : ℝ≥0 → S | Tendsto (fun m => x (u m)) atTop (𝓝 (x t0))}
  have hAcp : MeasurableSet Acp := by
    have : Acp = {x : ℝ≥0 → S | Tendsto (fun m => dist (x (u m)) (x t0)) atTop (𝓝 0)} := by
      ext x; simp only [Acp, Set.mem_ofPred_eq]; exact tendsto_iff_dist_tendsto_zero
    rw [this]
    apply measurableSet_tendsto
    intro m
    exact (measurable_pi_apply (u m)).dist hev
  have hu : Tendsto u atTop (𝓝 t0) := by
    have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ≥0) + 1)) atTop (𝓝 0) := by
      have hr : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      rw [← NNReal.tendsto_coe]; simpa using hr
    have := (tendsto_const_nhds (x := t0)).sub h1
    simpa [u, one_div] using this
  have hY'A : ∀ᵐ ω' ∂P', Y' ω' ∈ Acp :=
    Eventually.of_forall (fun ω' => ((hY'c ω').tendsto t0).comp hu)
  have hW'A : ∀ᵐ ω ∂P'', W' ω ∈ Acp := hW'.symm.ae_mem_snd hAcp hY'A
  -- measurable modifications
  set Wm : ℕ → Ω'' → ℝ≥0 → S := fun n => (hW n).aemeasurable_fst.mk (W n)
  have hWm_meas : ∀ n, Measurable (Wm n) := fun n => (hW n).aemeasurable_fst.measurable_mk
  have hWm_eq : ∀ n, W n =ᵐ[P''] Wm n := fun n => (hW n).aemeasurable_fst.ae_eq_mk
  have hWm_id : ∀ n, IdentDistrib (Wm n) (Y n) P'' P :=
    fun n => ((hW n).aemeasurable_fst.identDistrib_mk).symm.trans (hW n)
  set W'm : Ω'' → ℝ≥0 → S := hW'.aemeasurable_fst.mk W'
  have hW'm_meas : Measurable W'm := hW'.aemeasurable_fst.measurable_mk
  have hW'm_eq : W' =ᵐ[P''] W'm := hW'.aemeasurable_fst.ae_eq_mk
  have hW'm_id : IdentDistrib W'm Y' P'' P' := (hW'.aemeasurable_fst.identDistrib_mk).symm.trans hW'
  have hset : MeasurableSet {x : ℝ≥0 → S | c < f (x t0)} := hF measurableSet_Ioi
  have hset' : MeasurableSet {x : ℝ≥0 → S | f (x t0) = c} :=
    hF (measurableSet_singleton c)
  have e1 : ∀ n, P {ω | c < f (Y n ω t0)} = P'' {ω | c < f (Wm n ω t0)} :=
    fun n => ((hWm_id n).measure_mem_eq hset).symm
  have e2 : P' {ω' | c < f (Y' ω' t0)} = P'' {ω | c < f (W'm ω t0)} :=
    (hW'm_id.measure_mem_eq hset).symm
  have hatom'' : P'' {ω | f (W'm ω t0) = c} = 0 := by
    show P'' (W'm ⁻¹' {x | f (x t0) = c}) = 0
    rw [hW'm_id.measure_mem_eq hset']; exact hatom
  simp_rw [e1, e2]
  apply tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    (hF.comp hW'm_meas measurableSet_Ioi) (fun n => hF.comp (hWm_meas n) measurableSet_Ioi)
  have hall : ∀ᵐ ω ∂P'', ∀ n, W n ω = Wm n ω := ae_all_iff.2 hWm_eq
  have hna : ∀ᵐ ω ∂P'', f (W'm ω t0) ≠ c := by
    rw [ae_iff]; simpa using hatom''
  filter_upwards [hJ, hall, hW'm_eq, hW'A, hna] with ω hJω hallω heqω hAω hnaω
  have hcont : ContinuousAt (W' ω) t0 := contAt_of_cadlag (W' ω) hJω.2.1 t0 hAω
  have hconv := j1_pointwise (fun n => W n ω) (W' ω) hJω t0 hcont
  have hconvf : Tendsto (fun n => f (Wm n ω t0)) atTop (𝓝 (f (W'm ω t0))) := by
    have := (hf.tendsto _).comp hconv
    simp only [Function.comp_def] at this
    rw [← heqω]
    refine this.congr (fun n => ?_)
    rw [hallω n]
  simp only [Set.mem_preimage, Set.mem_Ioi, Function.comp_apply]
  rcases lt_or_gt_of_ne hnaω with hlt | hgt
  · filter_upwards [hconvf.eventually (gt_mem_nhds hlt)] with n hn
    constructor
    · intro h; linarith
    · intro h; linarith
  · filter_upwards [hconvf.eventually (lt_mem_nhds hgt)] with n hn
    exact ⟨fun _ => hgt, fun _ => hn⟩


end FJT2

theorem solution {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hSigma : M.Sigma.PosDef)
    (run : ∀ r : ℕ, PolicyRun M r)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (Z : Ω' → ℝ → Fin M.a1 → ℝ)
    (hZ : IsSRBM P' M.Theta M.Sigma Z) (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun r : ℕ => P {ω | ε < ∑ j, N.h j * (run r).Nhat j ω t}) atTop
      (𝓝 (P' {ω' | ε < z N (M.limitVec Z ω' t)})) := by
  obtain ⟨hPp, hP'p, Ω'', mΩ'', P'', W, W', hP''p, hW, hW', hJ⟩ :=
    ForkJoinCtrl.Tracking.proposition_2 M hA1 hA2 hSigma (fun r => (run r).toRun) P' Z hZ
  obtain ⟨_, C1, hC1, hzl⟩ := ForkJoinCtrl.Tracking.lemma_1_part_2 N
  have hzc := FJT2.zc_lip C1 hC1 hzl
  set t0 : ℝ≥0 := ⟨t, ht⟩ with ht0
  set fZ : Ω' → ℝ := fun ω' => z N (M.limitVec Z ω' t) with hfZ
  have hfZc : ∀ ω', FJT2.zc N (M.limitVec Z ω' t) = fZ ω' :=
    fun ω' => FJT2.zc_eq (FJT2.limitVec_nonneg hZ ω' ht)
  -- marginal convergence at every positive level
  have hKC : ∀ c : ℝ, 0 < c → Tendsto (fun r => P {ω | c < z N ((run r).bhat ω t)}) atTop
      (𝓝 (P' {ω' | c < fZ ω'})) := by
    intro c hc
    have hatom : P' {ω' | FJT2.zc N (M.limitVec Z ω' (t0 : ℝ)) = c} = 0 := by
      have := ForkJoinCtrl.Tracking.srbm_cost_no_atom M hSigma P' Z hZ c hc t ht
      convert this using 2
      ext ω'; simp only [Set.mem_ofPred_eq]; rw [show ((t0 : ℝ)) = t from rfl, hfZc]
    have h := FJT2.kc P (fun r ω (s : ℝ≥0) => (run r).bhat ω (s : ℝ)) P'
      (fun ω' (s : ℝ≥0) => M.limitVec Z ω' (s : ℝ)) P'' W W' hW hW' hJ
      (fun ω' => FJT2.limitVec_cont hZ ω') (FJT2.zc N) hzc t0 c hatom
    have e1 : ∀ r : ℕ, P {ω | c < FJT2.zc N ((run r).bhat ω (t0 : ℝ))} =
        P {ω | c < z N ((run r).bhat ω t)} := by
      intro r
      apply measure_congr
      rw [Filter.eventuallyEq_set]
      filter_upwards [(run r).adm] with ω hω
      rw [show ((t0 : ℝ)) = t from rfl, FJT2.zc_eq (FJT2.bhat_nonneg (run r).toRun hω ht)]
    have e2 : P' {ω' | c < FJT2.zc N (M.limitVec Z ω' (t0 : ℝ))} = P' {ω' | c < fZ ω'} := by
      congr 1; ext ω'; simp only [Set.mem_ofPred_eq]; rw [show ((t0 : ℝ)) = t from rfl, hfZc]
    rw [e2] at h
    exact h.congr e1
  -- measurability of the limit marginal
  have hY'ae : AEMeasurable (fun ω' => (fun s : ℝ≥0 => M.limitVec Z ω' (s : ℝ))) P' :=
    hW'.aemeasurable_snd
  have hFm : Measurable (fun x : ℝ≥0 → LPParam N => FJT2.zc N (x t0)) :=
    hzc.measurable.comp (measurable_pi_apply t0)
  have hfZae : AEMeasurable fZ P' := by
    have := hFm.comp_aemeasurable hY'ae
    refine this.congr (Eventually.of_forall (fun ω' => ?_))
    simp only [Function.comp_apply]
    exact hfZc ω'
  have hnull : ∀ c : ℝ, NullMeasurableSet {ω' | c < fZ ω'} P' :=
    fun c => hfZae.nullMeasurable measurableSet_Ioi
  have hatomε : P' {ω' | fZ ω' = ε} = 0 := ForkJoinCtrl.Tracking.srbm_cost_no_atom M hSigma P' Z hZ ε hε t ht
  -- continuity of `c ↦ P'(c < fZ)` at `ε`
  set δs : ℕ → ℝ := fun m => ε / ((m : ℝ) + 2) with hδs
  have hδpos : ∀ m, 0 < δs m := fun m => by positivity
  have hδlt : ∀ m, δs m < ε := by
    intro m
    simp only [hδs]
    rw [div_lt_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hδ0 : Tendsto δs atTop (𝓝 0) := by
    have h : Tendsto (fun m : ℕ => (m : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa [hδs] using h.const_div_atTop ε
  have hδanti : Antitone δs := by
    intro m n hmn
    simp only [hδs]
    apply div_le_div_of_nonneg_left hε.le (by positivity)
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hdown : Tendsto (fun m => P' {ω' | ε - δs m < fZ ω'}) atTop (𝓝 (P' {ω' | ε < fZ ω'})) := by
    have hanti : Antitone (fun m => {ω' | ε - δs m < fZ ω'}) := by
      intro m n hmn ω' hω'
      simp only [Set.mem_ofPred_eq] at hω' ⊢
      linarith [hδanti hmn]
    have h := tendsto_measure_iInter_atTop (μ := P') (fun m => hnull (ε - δs m)) hanti
      ⟨0, measure_ne_top _ _⟩
    have hI : (⋂ m, {ω' | ε - δs m < fZ ω'}) = {ω' | ε ≤ fZ ω'} := by
      ext ω'
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      constructor
      · intro hω'
        by_contra hlt
        push Not at hlt
        obtain ⟨m, hm⟩ := (hδ0.eventually (gt_mem_nhds (sub_pos.2 hlt))).exists
        have := hω' m
        linarith
      · intro hω' m; linarith [hδpos m]
    have hE : P' {ω' | ε ≤ fZ ω'} = P' {ω' | ε < fZ ω'} := by
      apply le_antisymm
      · have hsub : {ω' | ε ≤ fZ ω'} ⊆ {ω' | ε < fZ ω'} ∪ {ω' | fZ ω' = ε} := by
          intro ω' hω'
          simp only [Set.mem_ofPred_eq] at hω'
          rcases hω'.lt_or_eq with h | h
          · exact Or.inl h
          · exact Or.inr h.symm
        calc P' {ω' | ε ≤ fZ ω'} ≤ P' ({ω' | ε < fZ ω'} ∪ {ω' | fZ ω' = ε}) := measure_mono hsub
          _ ≤ P' {ω' | ε < fZ ω'} + P' {ω' | fZ ω' = ε} := measure_union_le _ _
          _ = P' {ω' | ε < fZ ω'} := by rw [hatomε, add_zero]
      · exact measure_mono (fun ω' (hω' : ε < fZ ω') => (le_of_lt hω' : ε ≤ fZ ω'))
    rw [hI, hE] at h
    exact h
  have hup : Tendsto (fun m => P' {ω' | ε + δs m < fZ ω'}) atTop (𝓝 (P' {ω' | ε < fZ ω'})) := by
    have hmono : Monotone (fun m => {ω' | ε + δs m < fZ ω'}) := by
      intro m n hmn ω' hω'
      simp only [Set.mem_ofPred_eq] at hω' ⊢
      linarith [hδanti hmn]
    have h := tendsto_measure_iUnion_atTop (μ := P') hmono
    have hU : (⋃ m, {ω' | ε + δs m < fZ ω'}) = {ω' | ε < fZ ω'} := by
      ext ω'
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨m, hm⟩; linarith [hδpos m]
      · intro hω'
        obtain ⟨m, hm⟩ := (hδ0.eventually (gt_mem_nhds (sub_pos.2 hω'))).exists
        exact ⟨m, by linarith⟩
    rw [hU] at h
    exact h
  -- pass to real numbers
  have hfin : ∀ (μ : Measure Ω') [IsFiniteMeasure μ] (s : Set Ω'), μ s ≠ ⊤ := fun μ _ s =>
    measure_ne_top μ s
  rw [← ENNReal.tendsto_toReal_iff (fun r => measure_ne_top P _) (measure_ne_top P' _)]
  set L := (P' {ω' | ε < fZ ω'}).toReal with hL
  have hdownR : Tendsto (fun m => (P' {ω' | ε - δs m < fZ ω'}).toReal) atTop (𝓝 L) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hdown
  have hupR : Tendsto (fun m => (P' {ω' | ε + δs m < fZ ω'}).toReal) atTop (𝓝 L) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hup
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨m1, hm1⟩ := Metric.tendsto_atTop.1 hdownR (η / 4) (by positivity)
  obtain ⟨m2, hm2⟩ := Metric.tendsto_atTop.1 hupR (η / 4) (by positivity)
  set m := max m1 m2
  have hA := hm1 m (le_max_left _ _)
  have hB := hm2 m (le_max_right _ _)
  rw [Real.dist_eq] at hA hB
  set δ := δs m
  have hδ := hδpos m
  have hδε := hδlt m
  -- convergences along `r`
  have hK1 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hKC (ε - δ) (by linarith))
  have hK2 := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (hKC (ε + δ) (by linarith))
  have hD := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (ForkJoinCtrl.Tracking.proposition_3 M hA1 hA2 run δ (t + 1) hδ (by linarith))
  simp only [ENNReal.toReal_zero] at hD
  obtain ⟨R1, hR1⟩ := Metric.tendsto_atTop.1 hK1 (η / 4) (by positivity)
  obtain ⟨R2, hR2⟩ := Metric.tendsto_atTop.1 hK2 (η / 4) (by positivity)
  obtain ⟨R3, hR3⟩ := Metric.tendsto_atTop.1 hD (η / 4) (by positivity)
  refine ⟨max R1 (max R2 R3), fun r hr => ?_⟩
  have h1 := hR1 r (le_trans (le_max_left _ _) hr)
  have h2 := hR2 r (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hr))
  have h3 := hR3 r (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hr))
  simp only [Function.comp_apply, Real.dist_eq, sub_zero] at h1 h2 h3
  set D := {ω | ∃ s ∈ Set.Icc 0 (t + 1),
    δ < |∑ j, N.h j * (run r).Nhat j ω s - z N ((run r).bhat ω s)|}
  have hDnn : 0 ≤ (P D).toReal := ENNReal.toReal_nonneg
  rw [abs_of_nonneg hDnn] at h3
  have htI : t ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨ht, by linarith⟩
  have hsub1 : {ω | ε < ∑ j, N.h j * (run r).Nhat j ω t} ⊆
      {ω | ε - δ < z N ((run r).bhat ω t)} ∪ D := by
    intro ω hω
    by_cases hωD : ω ∈ D
    · exact Or.inr hωD
    · left
      simp only [D, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hωD
      have := hωD t htI
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have := (abs_le.1 this).2
      linarith
  have hsub2 : {ω | ε + δ < z N ((run r).bhat ω t)} ⊆
      {ω | ε < ∑ j, N.h j * (run r).Nhat j ω t} ∪ D := by
    intro ω hω
    by_cases hωD : ω ∈ D
    · exact Or.inr hωD
    · left
      simp only [D, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hωD
      have := hωD t htI
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have := (abs_le.1 this).1
      linarith
  have hu1 : (P {ω | ε < ∑ j, N.h j * (run r).Nhat j ω t}).toReal ≤
      (P {ω | ε - δ < z N ((run r).bhat ω t)}).toReal + (P D).toReal := by
    have := measureReal_mono (μ := P) hsub1 (measure_ne_top _ _)
    exact this.trans (measureReal_union_le _ _)
  have hu2 : (P {ω | ε + δ < z N ((run r).bhat ω t)}).toReal ≤
      (P {ω | ε < ∑ j, N.h j * (run r).Nhat j ω t}).toReal + (P D).toReal := by
    have := measureReal_mono (μ := P) hsub2 (measure_ne_top _ _)
    exact this.trans (measureReal_union_le _ _)
  rw [Real.dist_eq, abs_lt]
  constructor
  · have := (abs_lt.1 h2).1
    have := (abs_lt.1 hB).1
    linarith
  · have := (abs_lt.1 h1).2
    have := (abs_lt.1 hA).2
    linarith
