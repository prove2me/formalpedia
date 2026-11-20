-- Prove2me | solution 1 for DurrettProbability.brownian_holder
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T10:07:12.736196+00:00
-- url     : https://prove2.me/submissions/8902646d-e907-447f-b546-de64e5e30bce

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
import Definitions.Def_LevyStochCalc_Brownian_ContinuityKolmogorovBounds_F001
import Definitions.Def_LevyStochCalc_Probability_GaussianMoments_F000

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace DurrettProbability
open LevyStochCalc.Brownian.Continuity


theorem AuxBH_trunc_ge (n : ℕ) (j : ℤ) {s : ℝ} (hs : (j : ℝ) ≤ s) : (j : ℝ) ≤ dyadicTrunc n s := by
  rw [dyadicTrunc, le_div_iff₀ (by positivity)]
  have : ((j * 2 ^ n : ℤ) : ℝ) ≤ ⌊s * 2 ^ n⌋ := by
    exact_mod_cast Int.le_floor.mpr (by push_cast; nlinarith [pow_pos (two_pos : (0:ℝ) < 2) n])
  push_cast at this
  exact this

theorem AuxBH_trunc_gt (n : ℕ) (s : ℝ) : s - (1 / 2 : ℝ) ^ n < dyadicTrunc n s := by
  rw [dyadicTrunc, lt_div_iff₀ (by positivity)]
  have h := Int.lt_floor_add_one (s * 2 ^ n)
  have : (s - (1 / 2 : ℝ) ^ n) * 2 ^ n = s * 2 ^ n - 1 := by
    rw [sub_mul, ← mul_pow]; norm_num
  rw [this]; linarith

theorem AuxBH_trunc_tendsto (s : ℝ) : Tendsto (fun n => dyadicTrunc n s) atTop (𝓝 s) := by
  have h0 : Tendsto (fun n : ℕ => s - (1 / 2 : ℝ) ^ n) atTop (𝓝 s) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
    simpa using (tendsto_const_nhds (x := s)).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds
    (fun n => (AuxBH_trunc_gt n s).le) (fun n => dyadicTrunc_le n s)

theorem AuxBH_ext {g : ℝ → ℝ} (hg : Continuous g) {γ : ℝ} (hγ : 0 < γ) {K : ℝ} {N : ℕ} {j : ℤ}
    (hb : ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals, (j : ℝ) ≤ s → s ≤ j + 1 → (j : ℝ) ≤ t →
      t ≤ j + 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N → |g s - g t| ≤ K * |s - t| ^ γ)
    {s t : ℝ} (hs1 : (j : ℝ) ≤ s) (hs2 : s ≤ j + 1) (ht1 : (j : ℝ) ≤ t) (ht2 : t ≤ j + 1)
    (hst : |s - t| < (1 / 2 : ℝ) ^ N) : |g s - g t| ≤ K * |s - t| ^ γ := by
  have ha := AuxBH_trunc_tendsto s
  have hb' := AuxBH_trunc_tendsto t
  have hL : Tendsto (fun n => |g (dyadicTrunc n s) - g (dyadicTrunc n t)|) atTop
      (𝓝 (|g s - g t|)) :=
    (((hg.tendsto s).comp ha).sub ((hg.tendsto t).comp hb')).abs
  have hR : Tendsto (fun n => K * |dyadicTrunc n s - dyadicTrunc n t| ^ γ) atTop
      (𝓝 (K * |s - t| ^ γ)) := by
    refine tendsto_const_nhds.mul ?_
    exact ((ha.sub hb').abs).rpow_const (Or.inr hγ.le)
  refine le_of_tendsto_of_tendsto hL hR ?_
  have hd : Tendsto (fun n => |dyadicTrunc n s - dyadicTrunc n t|) atTop (𝓝 |s - t|) :=
    (ha.sub hb').abs
  filter_upwards [hd.eventually (gt_mem_nhds hst)] with n hn
  refine hb _ (dyadicTrunc_mem_dyadicRationals n s) _ (dyadicTrunc_mem_dyadicRationals n t)
    (AuxBH_trunc_ge n j hs1) ((dyadicTrunc_le n s).trans hs2)
    (AuxBH_trunc_ge n j ht1) ((dyadicTrunc_le n t).trans ht2) hn.le

theorem AuxBH_det {g : ℝ → ℝ} (hg : Continuous g) {γ : ℝ} (hγ : 0 < γ) (J : ℕ)
    (K : ℤ → ℝ) (N : ℤ → ℕ) (hK : ∀ j, 0 ≤ K j)
    (hb : ∀ j : ℤ, ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals, (j : ℝ) ≤ s → s ≤ j + 1 →
      (j : ℝ) ≤ t → t ≤ j + 1 → |s - t| ≤ (1 / 2 : ℝ) ^ (N j) → |g s - g t| ≤ K j * |s - t| ^ γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : ℝ, 0 ≤ s → s ≤ J → 0 ≤ t → t ≤ J → |g s - g t| ≤ C * |s - t| ^ γ := by
  set S : Finset ℤ := Finset.Icc 0 (J : ℤ) with hS
  set Ks : ℝ := ∑ j ∈ S, K j
  set Nm : ℕ := S.sup N
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => hK i
  have hKle : ∀ j ∈ S, K j ≤ Ks := fun j hj => Finset.single_le_sum (fun i _ => hK i) hj
  set δ : ℝ := (1 / 2 : ℝ) ^ (Nm + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδN : ∀ j ∈ S, δ < (1 / 2 : ℝ) ^ (N j) := fun j hj =>
    lt_of_lt_of_le (pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (Nat.lt_succ_self _))
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Finset.le_sup (f := N) hj))
  have hδ1 : δ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := J)).exists_bound_of_continuousOn
    hg.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, by positivity⟩)
  set C : ℝ := 2 * Ks + 2 * M * δ ^ (-γ)
  have hC0 : 0 ≤ C := by positivity
  have hloc : ∀ j ∈ S, ∀ s t : ℝ, (j : ℝ) ≤ s → s ≤ j + 1 → (j : ℝ) ≤ t → t ≤ j + 1 → |s - t| < δ →
      |g s - g t| ≤ Ks * |s - t| ^ γ := fun j hj s t h1 h2 h3 h4 h5 =>
    (AuxBH_ext hg hγ (hb j) h1 h2 h3 h4 (h5.trans (hδN j hj))).trans
      (mul_le_mul_of_nonneg_right (hKle j hj) (by positivity))
  have main : ∀ s t : ℝ, 0 ≤ s → s ≤ J → 0 ≤ t → t ≤ J → s < t → |g s - g t| ≤ C * |s - t| ^ γ := by
    intro s t hs0 hsJ ht0 htJ hst
    have hpos : 0 ≤ |s - t| ^ γ := by positivity
    by_cases hfar : δ ≤ |s - t|
    · have h1 : |g s - g t| ≤ 2 * M := by
        have := hM s ⟨hs0, hsJ⟩; have := hM t ⟨ht0, htJ⟩
        rw [Real.norm_eq_abs] at *
        calc |g s - g t| ≤ |g s| + |g t| := abs_sub _ _
          _ ≤ 2 * M := by linarith
      have h2 : 1 ≤ δ ^ (-γ) * |s - t| ^ γ := by
        rw [Real.rpow_neg hδ0.le, ← div_eq_inv_mul, le_div_iff₀ (by positivity), one_mul]
        exact Real.rpow_le_rpow hδ0.le hfar hγ.le
      calc |g s - g t| ≤ 2 * M := h1
        _ ≤ 2 * M * (δ ^ (-γ) * |s - t| ^ γ) := le_mul_of_one_le_right (by positivity) h2
        _ ≤ C * |s - t| ^ γ := by
          have : 0 ≤ 2 * Ks * |s - t| ^ γ := by positivity
          simp only [C]; nlinarith
    · push_neg at hfar
      have hts : t - s < δ := by rw [abs_sub_comm, abs_of_pos (by linarith)] at hfar; exact hfar
      set a : ℤ := ⌊s⌋ with ha
      have ha1 : (a : ℝ) ≤ s := Int.floor_le s
      have ha2 : s < (a : ℝ) + 1 := Int.lt_floor_add_one s
      have ha0 : 0 ≤ a := Int.floor_nonneg.mpr hs0
      have haJ : a < J := by
        have : (a : ℝ) < J := by linarith
        exact_mod_cast this
      have haS : a ∈ S := by rw [hS, Finset.mem_Icc]; omega
      have hCK : Ks * |s - t| ^ γ ≤ C * |s - t| ^ γ := by
        apply mul_le_mul_of_nonneg_right _ hpos
        have : 0 ≤ 2 * M * δ ^ (-γ) := by positivity
        simp only [C]; linarith
      by_cases hc : t ≤ (a : ℝ) + 1
      · exact (hloc a haS s t ha1 ha2.le (by linarith) hc hfar).trans hCK
      · push_neg at hc
        have ha1S : a + 1 ∈ S := by
          rw [hS, Finset.mem_Icc]
          have : ((a + 1 : ℤ) : ℝ) ≤ J := by push_cast; linarith
          constructor
          · omega
          · exact_mod_cast this
        have d1 : |s - ((a : ℝ) + 1)| ≤ |s - t| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
        have d2 : |((a : ℝ) + 1) - t| ≤ |s - t| := by
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
        have e1 := hloc a haS s ((a : ℝ) + 1) ha1 ha2.le (by linarith) le_rfl (d1.trans_lt hfar)
        have e2 := hloc (a + 1) ha1S ((a : ℝ) + 1) t (by push_cast; linarith) (by push_cast; linarith)
          (by push_cast; linarith) (by push_cast; linarith) (d2.trans_lt hfar)
        have p1 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) d1 hγ.le) hKs0
        have p2 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) d2 hγ.le) hKs0
        have tri : |g s - g t| ≤ |g s - g ((a : ℝ) + 1)| + |g ((a : ℝ) + 1) - g t| := abs_sub_le _ _ _
        have : 2 * Ks * |s - t| ^ γ ≤ C * |s - t| ^ γ := by
          apply mul_le_mul_of_nonneg_right _ hpos
          have : 0 ≤ 2 * M * δ ^ (-γ) := by positivity
          simp only [C]; linarith
        linarith
  refine ⟨C, hC0, fun s t hs0 hsJ ht0 htJ => ?_⟩
  rcases lt_trichotomy s t with h | h | h
  · exact main s t hs0 hsJ ht0 htJ h
  · subst h; simp [Real.zero_rpow hγ.ne']
  · rw [abs_sub_comm, abs_sub_comm s]; exact main t s ht0 htJ hs0 hsJ h


theorem AuxBH_mom {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (m : ℕ) (s t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal ((B s ω - B t ω) ^ (2 * m)) ∂P
      = ENNReal.ofReal ((nndist (s : ℝ) (t : ℝ) : ℝ) ^ m * (2 * m - 1).doubleFactorial) := by
  have h := hB.hasLaw_sub s t
  have h2 := h.lintegral_comp (f := fun x : ℝ => ENNReal.ofReal (x ^ (2 * m))) (by fun_prop)
  simp only [Pi.sub_apply] at h2
  rw [h2, ← ofReal_integral_eq_lintegral_ofReal]
  · rw [LevyStochCalc.Probability.integral_pow_even_gaussianReal]
    norm_cast
  · have hm := (memLp_id_gaussianReal' (μ := 0) (v := nndist (s : ℝ) (t : ℝ)) ((2 * m : ℕ) : ENNReal)
      (ENNReal.natCast_ne_top _)).integrable_norm_pow'
    refine hm.congr (ae_of_all _ fun x => ?_)
    simp only [id, Real.norm_eq_abs]
    exact (Even.pow_abs ⟨m, by ring⟩ x)
  · exact ae_of_all _ fun x => by
      simp only [Pi.zero_apply]; exact Even.pow_nonneg ⟨m, by ring⟩ x

theorem AuxBH_pt (a b : ℝ) (m : ℕ) :
    edist a b ^ (2 * (m : ℝ)) = ENNReal.ofReal ((a - b) ^ (2 * m)) := by
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by positivity)]
  congr 1
  rw [show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  exact Even.pow_abs ⟨m, by ring⟩ _

theorem AuxBH_nnd (r r' : ℝ) : (nndist (r.toNNReal : ℝ) (r'.toNNReal : ℝ) : ℝ) ≤ |r - r'| := by
  rw [coe_nndist, Real.dist_eq, Real.coe_toNNReal', Real.coe_toNNReal']
  exact abs_max_sub_max_le_abs r r' 0

theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {γ : ℝ≥0} (hγ : 0 < γ) (hγ2 : γ < 1 / 2) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∃ C : ℝ≥0,
      HolderOnWith C γ (fun t : ℝ≥0 => B t ω) (Set.Iic T) := by
  have hγ' : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hγ2' : (γ : ℝ) < 1 / 2 := by exact_mod_cast hγ2
  have h12 : 0 < 1 - 2 * (γ : ℝ) := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (1 - 2 * (γ : ℝ)))
  have hm0 : (0 : ℝ) < m := lt_trans (by positivity) hm
  have hm1 : 1 < (m : ℝ) * (1 - 2 * γ) := by rwa [div_lt_iff₀ h12] at hm
  have hαpq : (γ : ℝ) * (2 * (m : ℝ)) < (m : ℝ) - 1 := by nlinarith
  set B' : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t) with hB'
  set X : ℝ → Ω → ℝ := fun r => B' r.toNNReal with hXdef
  set M : ℝ≥0 := ((2 * m - 1).doubleFactorial : ℝ≥0)
  have hX : IsKolmogorovProcess X P (2 * (m : ℝ)) (m : ℝ) M := by
    refine IsKolmogorovProcess.mk_of_secondCountableTopology
      (fun r => (hB.aemeasurable _).measurable_mk) (fun r r' => ?_) (by positivity) hm0
    have e1 : ∫⁻ ω, edist (X r ω) (X r' ω) ^ (2 * (m : ℝ)) ∂P
        = ∫⁻ ω, ENNReal.ofReal ((B r.toNNReal ω - B r'.toNNReal ω) ^ (2 * m)) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [(hB.aemeasurable r.toNNReal).ae_eq_mk,
        (hB.aemeasurable r'.toNNReal).ae_eq_mk] with ω h1 h2
      simp only [hXdef, hB', AuxBH_pt, ← h1, ← h2]
    rw [e1, AuxBH_mom hB, edist_dist, Real.dist_eq,
      ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hm0.le, Real.rpow_natCast]
    have : (M : ENNReal) = ENNReal.ofReal ((2 * m - 1).doubleFactorial : ℝ) := by
      simp [M]
    rw [this, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm]
    gcongr
    exact AuxBH_nnd r r'
  have hdy : ∀ᵐ ω ∂P, ∀ k : ℤ, ∀ n : ℕ,
      B' ((k : ℝ) * (2 : ℝ) ^ (-n : ℤ)).toNNReal ω = B ((k : ℝ) * (2 : ℝ) ^ (-n : ℤ)).toNNReal ω := by
    rw [ae_all_iff]; intro k; rw [ae_all_iff]; intro n
    filter_upwards [(hB.aemeasurable ((k : ℝ) * (2 : ℝ) ^ (-n : ℤ)).toNNReal).ae_eq_mk] with ω h
    exact h.symm
  filter_upwards [kc_ae_interval_holder P X hX hγ' hαpq, hB.cont, hdy] with ω h1 h2 h3
  choose K N hK hb using h1
  set g : ℝ → ℝ := fun r => B r.toNNReal ω with hg
  have hcont : Continuous g := h2.comp continuous_real_toNNReal
  have hXe : ∀ s ∈ dyadicRationals, g s = X s ω := by
    rintro s ⟨k, n, rfl⟩; exact (h3 k n).symm
  have hb' : ∀ j : ℤ, ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals, (j : ℝ) ≤ s → s ≤ j + 1 →
      (j : ℝ) ≤ t → t ≤ j + 1 → |s - t| ≤ (1 / 2 : ℝ) ^ (N j) → |g s - g t| ≤ K j * |s - t| ^ (γ : ℝ) := by
    intro j s hs t ht a1 a2 a3 a4 a5
    rw [hXe s hs, hXe t ht]; exact hb j s hs t ht a1 a2 a3 a4 a5
  intro T
  obtain ⟨C, hC0, hC⟩ := AuxBH_det hcont hγ' ⌈(T : ℝ)⌉₊ K N hK hb'
  refine ⟨C.toNNReal, fun x hx y hy => ?_⟩
  have hxT : (x : ℝ) ≤ ⌈(T : ℝ)⌉₊ := (NNReal.coe_le_coe.mpr hx).trans (Nat.le_ceil _)
  have hyT : (y : ℝ) ≤ ⌈(T : ℝ)⌉₊ := (NNReal.coe_le_coe.mpr hy).trans (Nat.le_ceil _)
  have key := hC x y x.2 hxT y.2 hyT
  simp only [hg, Real.toNNReal_coe] at key
  simp only
  rw [edist_dist, Real.dist_eq, edist_dist, NNReal.dist_eq,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hγ'.le]
  rw [show ((C.toNNReal : ℝ≥0) : ENNReal) = ENNReal.ofReal C from rfl, ← ENNReal.ofReal_mul hC0]
  exact ENNReal.ofReal_le_ofReal key

end DurrettProbability
