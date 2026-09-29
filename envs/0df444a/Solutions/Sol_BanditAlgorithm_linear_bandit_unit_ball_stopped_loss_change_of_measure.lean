-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_unit_ball_stopped_loss_change_of_measure
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T16:41:04.98364+00:00
-- url     : https://prove2.me/submissions/7ce4d082-5009-4d60-a821-649c5251ee9e

import Mathlib
import Definitions.Def_LinearBanditProtocol

/-! Disproof of 74901317 `BanditAlgorithm.linear_bandit_unit_ball_stopped_loss_change_of_measure`.

The claimed change-of-measure slack `(Δ/2)(4n/d + 2)√(n/d + 1)` is too small by a constant factor
(it is half of what Pinsker gives). Counterexample: `d = 1`, `n = 10001`, `σ = true`, `i = 0`, so
`θ = Δ`, `θ' = -Δ` with `Δ = √(1/(48n))`, and every round is active. The policy plays `+1` or `-1`
(unit ball) according to the sign of the running statistic `Sₜ = ∑_{s<t} Aₛ Xₛ`: it plays `-1`
iff `Sₜ < 0`. Since `Aₛ Xₛ = θ + Aₛ ηₛ` and `Aₛ ηₛ ~ 𝒩(0,1)` whatever `Aₛ = ±1` is, the law of `Sₜ`
is `𝒩(tθ, t)` under both parameters, and `U = 4 · #{t : Sₜ < 0}`. Hence
`E_θ'[U] - E_θ[U] = 4 ∑_{t<n} P(|𝒩(0,t)| < tΔ) ≥ 8Δ e^{-1/96}/√(2π) · ∑_{t<n} √t`,
which is about `2.1 Δ n^{3/2}`, while the slack is about `2 Δ n^{3/2}`
(numerically, for `n = 10001`: difference ≥ `2.10·10⁶ Δ`, slack ≤ `2.0005·10⁶ Δ`). -/

set_option autoImplicit false

open Matrix MeasureTheory ProbabilityTheory BanditAlgorithm

/-- Running sufficient statistic `∑ₛ Aₛ Xₛ` of a one-dimensional history. -/
noncomputable def lbdpS {m : ℕ} (h : LinearBanditHistory 1 m) : ℝ :=
  ∑ s, (h s).1 0 * (h s).2

theorem lbdp_coord_meas (m : ℕ) (s : Fin m) :
    Measurable (fun h : LinearBanditHistory 1 m => (h s).1 0) :=
  (measurable_pi_apply 0).comp (measurable_fst.comp (measurable_pi_apply s))

theorem lbdpS_meas (m : ℕ) : Measurable (lbdpS (m := m)) := by
  unfold lbdpS
  apply Finset.measurable_sum
  intro s _
  exact (lbdp_coord_meas m s).mul (measurable_snd.comp (measurable_pi_apply s))

/-- The sign played next: `-1` if the evidence favours a negative parameter. -/
noncomputable def lbdpSgn {m : ℕ} (h : LinearBanditHistory 1 m) : ℝ :=
  if lbdpS h < 0 then -1 else 1

theorem lbdpSgn_meas (m : ℕ) : Measurable (lbdpSgn (m := m)) :=
  Measurable.ite (measurableSet_lt (lbdpS_meas m) measurable_const) measurable_const
    measurable_const

theorem lbdpSgn_sq {m : ℕ} (h : LinearBanditHistory 1 m) : lbdpSgn h ^ 2 = 1 := by
  unfold lbdpSgn
  split_ifs <;> norm_num

noncomputable def lbdpAct {m : ℕ} (h : LinearBanditHistory 1 m) : Fin 1 → ℝ :=
  fun _ => lbdpSgn h

theorem lbdpAct_meas (m : ℕ) : Measurable (lbdpAct (m := m)) :=
  measurable_pi_lambda _ (fun _ => lbdpSgn_meas m)

noncomputable def lbdpPol : LinearBanditPolicy 1 where
  select m := Kernel.deterministic (lbdpAct (m := m)) (lbdpAct_meas m)
  markov _ := Kernel.isMarkovKernel_deterministic _

theorem lbdpPol_supp : IsSupportedLinearPolicy {a : Fin 1 → ℝ | a ⬝ᵥ a ≤ 1} lbdpPol := by
  intro m h
  show Kernel.deterministic (lbdpAct (m := m)) (lbdpAct_meas m) h _ = 0
  rw [Kernel.deterministic_apply, Measure.dirac_apply]
  have hmem : lbdpAct h ∈ {a : Fin 1 → ℝ | a ⬝ᵥ a ≤ 1} := by
    show lbdpAct h ⬝ᵥ lbdpAct h ≤ 1
    have := lbdpSgn_sq h
    simp only [dotProduct, lbdpAct, Finset.univ_unique, Finset.sum_singleton]
    nlinarith
  simp [Set.indicator, hmem]

/-- One round of the interaction, written as a map out of `history × noise`. -/
noncomputable def lbdpF (θ : Fin 1 → ℝ) (m : ℕ) (p : LinearBanditHistory 1 m × ℝ) :
    LinearBanditHistory 1 (m + 1) :=
  Fin.snoc (α := fun _ ↦ (Fin 1 → ℝ) × ℝ) p.1 (lbdpAct p.1, lbdpAct p.1 ⬝ᵥ θ + p.2)

theorem lbdpF_meas (θ : Fin 1 → ℝ) (m : ℕ) : Measurable (lbdpF θ m) := by
  have h1 : Measurable (fun q : LinearBanditHistory 1 m × ℝ => ((q.1, lbdpAct q.1), q.2)) :=
    (measurable_fst.prodMk ((lbdpAct_meas m).comp measurable_fst)).prodMk measurable_snd
  exact (measurable_linearBanditHistorySnoc (n := m) θ).comp h1

theorem lbdp_step (θ : Fin 1 → ℝ) (m : ℕ) :
    linearBanditMeasure θ lbdpPol (m + 1) =
      ((linearBanditMeasure θ lbdpPol m).prod (gaussianReal 0 1)).map (lbdpF θ m) := by
  rw [linearBanditMeasure]
  have hsel : lbdpPol.select m = Kernel.deterministic (lbdpAct (m := m)) (lbdpAct_meas m) := rfl
  rw [hsel, Measure.compProd_deterministic, Measure.compProd_const]
  have hf : Measurable (fun a : LinearBanditHistory 1 m => (a, lbdpAct a)) :=
    measurable_id.prodMk (lbdpAct_meas m)
  have key : ((linearBanditMeasure θ lbdpPol m).map (fun a => (a, lbdpAct a))).prod
      (gaussianReal 0 1) =
      ((linearBanditMeasure θ lbdpPol m).prod (gaussianReal 0 1)).map
        (Prod.map (fun a => (a, lbdpAct a)) id) := by
    rw [← Measure.map_prod_map _ _ hf measurable_id, Measure.map_id]
  rw [key, Measure.map_map (measurable_linearBanditHistorySnoc θ) (hf.prodMap measurable_id)]
  rfl

theorem lbdp_gmap (c s : ℝ) (hs : s ^ 2 = 1) :
    (gaussianReal 0 1).map (fun η => c + s * η) = gaussianReal c 1 := by
  have : (fun η : ℝ => c + s * η) = (fun x => c + x) ∘ (fun η => s * η) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  congr 1
  · simp
  · ext
    simp [hs]

theorem lbdp_law (θ : Fin 1 → ℝ) (m : ℕ) :
    (linearBanditMeasure θ lbdpPol m).map lbdpS = gaussianReal (m * θ 0) (m : NNReal) := by
  induction m with
  | zero =>
    rw [linearBanditMeasure, Measure.map_dirac' (lbdpS_meas 0)]
    simp [lbdpS]
  | succ m ih =>
    rw [lbdp_step, Measure.map_map (lbdpS_meas _) (lbdpF_meas θ m)]
    have hcomp : lbdpS ∘ lbdpF θ m =
        fun p => lbdpS p.1 + θ 0 + lbdpSgn p.1 * p.2 := by
      funext p
      have hs2 := lbdpSgn_sq p.1
      simp only [Function.comp, lbdpS, lbdpF, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
        Fin.snoc_last, lbdpAct, dotProduct, Finset.univ_unique, Finset.sum_singleton,
        Fin.default_eq_zero]
      linear_combination θ 0 * hs2
    rw [hcomp]
    have hconv : gaussianReal (((m + 1 : ℕ) : ℝ) * θ 0) ((m + 1 : ℕ) : NNReal) =
        (gaussianReal (m * θ 0) (m : NNReal)) ∗ (gaussianReal (θ 0) 1) := by
      rw [gaussianReal_conv_gaussianReal]
      congr 1
      · push_cast; ring
      · push_cast; ring
    rw [hconv, ← ih, Measure.conv]
    have hS := lbdpS_meas m
    have key : ((linearBanditMeasure θ lbdpPol m).map lbdpS).prod (gaussianReal (θ 0) 1) =
        ((linearBanditMeasure θ lbdpPol m).prod (gaussianReal (θ 0) 1)).map
          (Prod.map lbdpS id) := by
      rw [← Measure.map_prod_map _ _ hS measurable_id, Measure.map_id]
    rw [key, Measure.map_map (by fun_prop) (hS.prodMap measurable_id)]
    have hG1 : Measurable (fun p : LinearBanditHistory 1 m × ℝ =>
        lbdpS p.1 + θ 0 + lbdpSgn p.1 * p.2) :=
      ((hS.comp measurable_fst).add_const _).add
        (((lbdpSgn_meas m).comp measurable_fst).mul measurable_snd)
    have hG2 : Measurable ((fun x : ℝ × ℝ => x.1 + x.2) ∘ Prod.map lbdpS id) :=
      (by fun_prop : Measurable (fun x : ℝ × ℝ => x.1 + x.2)).comp (hS.prodMap measurable_id)
    ext B hB
    rw [Measure.map_apply hG1 hB, Measure.map_apply hG2 hB, Measure.prod_apply (hG1 hB),
      Measure.prod_apply (hG2 hB)]
    apply lintegral_congr
    intro h
    have e1 : (gaussianReal 0 1) (Prod.mk h ⁻¹'
        ((fun p : LinearBanditHistory 1 m × ℝ => lbdpS p.1 + θ 0 + lbdpSgn p.1 * p.2) ⁻¹' B)) =
        gaussianReal (lbdpS h + θ 0) 1 B := by
      rw [← lbdp_gmap (lbdpS h + θ 0) (lbdpSgn h) (lbdpSgn_sq h),
        Measure.map_apply (by fun_prop) hB]
      rfl
    have e2 : (gaussianReal (θ 0) 1) (Prod.mk h ⁻¹'
        (((fun x : ℝ × ℝ => x.1 + x.2) ∘ Prod.map lbdpS id) ⁻¹' B)) =
        gaussianReal (θ 0 + lbdpS h) 1 B := by
      rw [← gaussianReal_map_const_add (lbdpS h), Measure.map_apply (by fun_prop) hB]
      rfl
    rw [e1, e2, add_comm]

theorem lbdp_ae (θ : Fin 1 → ℝ) (m : ℕ) :
    ∀ᵐ h ∂(linearBanditMeasure θ lbdpPol m), ∀ s, (h s).1 0 ^ 2 = 1 := by
  induction m with
  | zero => exact ae_of_all _ (fun h s => s.elim0)
  | succ m ih =>
    have hmeas : MeasurableSet {h : LinearBanditHistory 1 (m + 1) | ∀ s, (h s).1 0 ^ 2 = 1} := by
      have : {h : LinearBanditHistory 1 (m + 1) | ∀ s, (h s).1 0 ^ 2 = 1} =
          ⋂ s, {h | (h s).1 0 ^ 2 = 1} := by
        ext; simp
      rw [this]
      exact MeasurableSet.iInter (fun s => measurableSet_eq_fun
        ((lbdp_coord_meas (m + 1) s).pow_const 2) measurable_const)
    rw [lbdp_step, ae_map_iff (lbdpF_meas θ m).aemeasurable hmeas]
    have h2 := (Measure.quasiMeasurePreserving_fst
      (μ := linearBanditMeasure θ lbdpPol m) (ν := gaussianReal 0 1)).ae ih
    filter_upwards [h2] with p hp
    intro s
    refine Fin.lastCases ?_ (fun s => ?_) s
    · simp only [lbdpF, Fin.snoc_last, lbdpAct]
      exact lbdpSgn_sq p.1
    · simp only [lbdpF, Fin.snoc_castSucc]
      exact hp s

/-- The stopped loss with a fixed horizon threshold `L` and constants specialised later. -/
noncomputable def lbdpV (L : ℝ) {m : ℕ} (h : LinearBanditHistory 1 m) : ℝ :=
  ∑ t, if (∑ s ∈ Finset.univ.filter (fun s : Fin m => s < t), ((h s).1 0) ^ 2) < L then
    (1 - (h t).1 0) ^ 2 else 0

theorem lbdpV_meas (L : ℝ) (m : ℕ) : Measurable (lbdpV L (m := m)) := by
  unfold lbdpV
  apply Finset.measurable_sum
  intro t _
  apply Measurable.ite
  · exact measurableSet_lt (Finset.measurable_sum _
      (fun s _ => (lbdp_coord_meas m s).pow_const 2)) measurable_const
  · exact (measurable_const.sub (lbdp_coord_meas m t)).pow_const 2
  · exact measurable_const

theorem lbdpV_snoc (L : ℝ) {m : ℕ} (h : LinearBanditHistory 1 m) (x : (Fin 1 → ℝ) × ℝ) :
    lbdpV L (Fin.snoc (α := fun _ ↦ (Fin 1 → ℝ) × ℝ) h x) =
      lbdpV L h + if (∑ s, ((h s).1 0) ^ 2) < L then (1 - x.1 0) ^ 2 else 0 := by
  unfold lbdpV
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    have hlast : ¬ (Fin.last m < t.castSucc) := not_lt.2 (Fin.le_last _)
    have hsum : (∑ s ∈ Finset.univ.filter (fun s : Fin (m + 1) => s < t.castSucc),
        ((Fin.snoc (α := fun _ ↦ (Fin 1 → ℝ) × ℝ) h x s).1 0) ^ 2) =
        ∑ s ∈ Finset.univ.filter (fun s : Fin m => s < t), ((h s).1 0) ^ 2 := by
      rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.castSucc_lt_castSucc_iff, hlast]
    rw [hsum, Fin.snoc_castSucc]
  · have hsum : (∑ s ∈ Finset.univ.filter (fun s : Fin (m + 1) => s < Fin.last m),
        ((Fin.snoc (α := fun _ ↦ (Fin 1 → ℝ) × ℝ) h x s).1 0) ^ 2) =
        ∑ s, ((h s).1 0) ^ 2 := by
      rw [Finset.sum_filter, Fin.sum_univ_castSucc]
      simp [Fin.snoc_castSucc, Fin.castSucc_lt_last]
    rw [hsum, Fin.snoc_last]

noncomputable def lbdpT (L : ℝ) {m : ℕ} (h : LinearBanditHistory 1 m) : ℝ :=
  if (∑ s, ((h s).1 0) ^ 2) < L then (1 - lbdpSgn h) ^ 2 else 0

theorem lbdpT_meas (L : ℝ) (m : ℕ) : Measurable (lbdpT L (m := m)) := by
  unfold lbdpT
  apply Measurable.ite
  · exact measurableSet_lt (Finset.measurable_sum _
      (fun s _ => (lbdp_coord_meas m s).pow_const 2)) measurable_const
  · exact (measurable_const.sub (lbdpSgn_meas m)).pow_const 2
  · exact measurable_const

theorem lbdp_sq_le (a : ℝ) (ha : a ^ 2 = 1) : (1 - a) ^ 2 ≤ 4 := by
  have h' : (a - 1) * (a + 1) = 0 := by ring_nf; linarith
  rcases mul_eq_zero.1 h' with h | h
  · have : a = 1 := by linarith
    subst this; norm_num
  · have : a = -1 := by linarith
    subst this; norm_num

theorem lbdpV_int (θ : Fin 1 → ℝ) (L : ℝ) (m : ℕ) (hm : (m : ℝ) ≤ L) :
    ∫ h, lbdpV L h ∂(linearBanditMeasure θ lbdpPol m) =
      4 * ∑ t ∈ Finset.range m, (gaussianReal (t * θ 0) (t : NNReal)).real (Set.Iio 0) := by
  induction m with
  | zero =>
    rw [linearBanditMeasure, integral_dirac]
    simp [lbdpV]
  | succ m ih =>
    have hmL : (m : ℝ) < L := by push_cast at hm; linarith
    rw [lbdp_step, integral_map (lbdpF_meas θ m).aemeasurable
      (lbdpV_meas L _).aestronglyMeasurable]
    have hsplit : (fun p : LinearBanditHistory 1 m × ℝ => lbdpV L (lbdpF θ m p)) =
        fun p => (fun h => lbdpV L h + lbdpT L h) p.1 := by
      funext p
      exact lbdpV_snoc L p.1 _
    rw [hsplit, integral_fun_fst (fun h : LinearBanditHistory 1 m => lbdpV L h + lbdpT L h),
      probReal_univ, one_smul]
    have hae := lbdp_ae θ m
    have hIV : Integrable (lbdpV L) (linearBanditMeasure θ lbdpPol m) := by
      refine Integrable.of_bound (lbdpV_meas L m).aestronglyMeasurable (4 * m) ?_
      filter_upwards [hae] with h hh
      unfold lbdpV
      rw [Real.norm_eq_abs]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have hb : ∀ t : Fin m, |(if (∑ s ∈ Finset.univ.filter (fun s : Fin m => s < t),
          ((h s).1 0) ^ 2) < L then (1 - (h t).1 0) ^ 2 else (0 : ℝ))| ≤ 4 := by
        intro t
        split_ifs
        · rw [abs_of_nonneg (sq_nonneg _)]
          exact lbdp_sq_le _ (hh t)
        · simp
      refine (Finset.sum_le_sum (fun t _ => hb t)).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hIT : Integrable (lbdpT L) (linearBanditMeasure θ lbdpPol m) := by
      refine Integrable.of_bound (lbdpT_meas L m).aestronglyMeasurable 4
        (ae_of_all _ (fun h => ?_))
      unfold lbdpT
      rw [Real.norm_eq_abs]
      split_ifs
      · rw [abs_of_nonneg (sq_nonneg _)]
        exact lbdp_sq_le _ (lbdpSgn_sq h)
      · norm_num
    rw [integral_add hIV hIT, ih (by linarith), Finset.sum_range_succ, mul_add]
    congr 1
    have hTeq : (lbdpT L) =ᵐ[linearBanditMeasure θ lbdpPol m]
        (lbdpS ⁻¹' Set.Iio 0).indicator (fun _ => (4 : ℝ)) := by
      filter_upwards [hae] with h hh
      have hsum : (∑ s, ((h s).1 0) ^ 2) = (m : ℝ) := by
        rw [Finset.sum_congr rfl (fun s _ => hh s)]
        simp
      unfold lbdpT lbdpSgn
      rw [if_pos (by rw [hsum]; exact hmL)]
      by_cases hS : lbdpS h < 0
      · simp [hS, Set.indicator]
        norm_num
      · simp [hS, Set.indicator]
    rw [integral_congr_ae hTeq, integral_indicator_const _ ((lbdpS_meas m) measurableSet_Iio),
      smul_eq_mul, ← map_measureReal_apply (lbdpS_meas m) measurableSet_Iio, lbdp_law, mul_comm]

noncomputable def lbdpU (L c x : ℝ) {m : ℕ} (h : LinearBanditHistory 1 m) : ℝ :=
  ∑ t, if (∑ s ∈ Finset.univ.filter (fun s : Fin m ↦ s < t), ((h s).1 0) ^ 2) < L then
    (c - (h t).1 0 * x) ^ 2 else 0

theorem lbdpU_int (θ : Fin 1 → ℝ) (N : ℕ) (L c x a : ℝ) (hL : (N : ℝ) ≤ L) (hc : c = 1)
    (hx : x = 1) (ha : θ 0 = a) :
    ∫ h, lbdpU L c x h ∂(linearBanditMeasure θ lbdpPol N) =
      4 * ∑ t ∈ Finset.range N, (gaussianReal (t * a) (t : NNReal)).real (Set.Iio 0) := by
  subst hc hx ha
  have hfun : ∀ h : LinearBanditHistory 1 N, lbdpU L 1 1 h = lbdpV L h := by
    intro h
    simp [lbdpU, lbdpV]
  rw [integral_congr_ae (ae_of_all _ hfun)]
  exact lbdpV_int θ L N hL

theorem lbdp_shift (μ : ℝ) (v : NNReal) :
    (gaussianReal μ v).real (Set.Iio 0) = (gaussianReal 0 v).real (Set.Iio (-μ)) := by
  have h := gaussianReal_map_add_const (μ := 0) (v := v) μ
  rw [zero_add] at h
  rw [← h, map_measureReal_apply (by fun_prop) measurableSet_Iio]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iio]
  constructor <;> intro hx <;> linarith

theorem lbdp_gauss (v : NNReal) (hv : v ≠ 0) (a : ℝ) (ha : 0 ≤ a) :
    2 * a * ((Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(a ^ 2) / (2 * v))) ≤
      (gaussianReal 0 v).real (Set.Iio a) - (gaussianReal 0 v).real (Set.Iio (-a)) := by
  have hU : Set.Iio a = Set.Iio (-a) ∪ Set.Ico (-a) a :=
    (Set.Iio_union_Ico_eq_Iio (by linarith)).symm
  have hD : Disjoint (Set.Iio (-a)) (Set.Ico (-a) a) :=
    Set.disjoint_left.2 (fun x h1 h2 => absurd h2.1 (not_le.2 h1))
  rw [hU, measureReal_union hD measurableSet_Ico, add_sub_cancel_left]
  have hvpos : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hc0 : 0 ≤ (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(a ^ 2) / (2 * v)) := by
    positivity
  have hle : ENNReal.ofReal (2 * a * ((Real.sqrt (2 * Real.pi * v))⁻¹ *
      Real.exp (-(a ^ 2) / (2 * v)))) ≤ gaussianReal 0 v (Set.Ico (-a) a) := by
    rw [gaussianReal_apply 0 hv]
    calc ENNReal.ofReal (2 * a * ((Real.sqrt (2 * Real.pi * v))⁻¹ *
          Real.exp (-(a ^ 2) / (2 * v))))
        = ∫⁻ _ in Set.Ico (-a) a, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹ *
            Real.exp (-(a ^ 2) / (2 * v))) := by
          rw [setLIntegral_const, Real.volume_Ico, ← ENNReal.ofReal_mul hc0]
          congr 1
          ring
      _ ≤ ∫⁻ x in Set.Ico (-a) a, gaussianPDF 0 v x := by
          apply setLIntegral_mono (measurable_gaussianPDF 0 v)
          intro x hx
          rw [gaussianPDF]
          apply ENNReal.ofReal_le_ofReal
          rw [gaussianPDFReal]
          have hx2 : (x - 0) ^ 2 ≤ a ^ 2 := by nlinarith [hx.1, hx.2]
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 (Real.sqrt_nonneg _))
          apply Real.exp_le_exp.2
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  have := (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hle
  simpa [measureReal_def] using this

theorem lbdp_sqrt_sum (K : ℕ) :
    (2 / 3 : ℝ) * K * Real.sqrt K ≤ ∑ t ∈ Finset.range (K + 1), Real.sqrt t := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sqrt_nonneg (K : ℝ)
    have hb := Real.sqrt_nonneg ((K : ℝ) + 1)
    have ha2 : Real.sqrt (K : ℝ) ^ 2 = K := Real.sq_sqrt (Nat.cast_nonneg K)
    have hb2 : Real.sqrt ((K : ℝ) + 1) ^ 2 = (K : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have key : (2 * (K : ℝ) - 1) * Real.sqrt ((K : ℝ) + 1) ≤ 2 * K * Real.sqrt K := by
      rcases Nat.eq_zero_or_pos K with hK | hK
      · subst hK
        simp
      · have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
        by_contra hcon
        push Not at hcon
        have h0 : 0 ≤ 2 * (K : ℝ) * Real.sqrt K := by positivity
        have hsq := mul_self_lt_mul_self h0 hcon
        have e1 : 2 * (K : ℝ) * Real.sqrt K * (2 * K * Real.sqrt K) = 4 * K ^ 2 * K := by
          rw [show 2 * (K : ℝ) * Real.sqrt K * (2 * K * Real.sqrt K) =
            4 * K ^ 2 * Real.sqrt K ^ 2 by ring, ha2]
        have e2 : (2 * (K : ℝ) - 1) * Real.sqrt ((K : ℝ) + 1) *
            ((2 * (K : ℝ) - 1) * Real.sqrt ((K : ℝ) + 1)) = (2 * K - 1) ^ 2 * (K + 1) := by
          rw [show (2 * (K : ℝ) - 1) * Real.sqrt ((K : ℝ) + 1) *
            ((2 * (K : ℝ) - 1) * Real.sqrt ((K : ℝ) + 1)) =
            (2 * K - 1) ^ 2 * Real.sqrt ((K : ℝ) + 1) ^ 2 by ring, hb2]
        rw [e1, e2] at hsq
        nlinarith
    push_cast
    linarith [key, ih]

theorem lbdp_final (Δ : ℝ) (hΔ : 0 < Δ) (hΔ2 : Δ ^ 2 = 1 / (48 * 10001)) :
    Δ / 2 * (4 * 10001 + 2) * Real.sqrt (10001 + 1) <
      4 * ∑ t ∈ Finset.range 10001, (gaussianReal (t * -Δ) (t : NNReal)).real (Set.Iio 0) -
      4 * ∑ t ∈ Finset.range 10001, (gaussianReal (t * Δ) (t : NNReal)).real (Set.Iio 0) := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hterm : ∀ t ∈ Finset.range 10001, (2 * Δ * (95 / 96) / (251 / 100)) * Real.sqrt t ≤
      (gaussianReal (t * -Δ) (t : NNReal)).real (Set.Iio 0) -
        (gaussianReal (t * Δ) (t : NNReal)).real (Set.Iio 0) := by
    intro t ht
    have ht' : t ≤ 10000 := by
      rw [Finset.mem_range] at ht
      omega
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      simp
    · rw [lbdp_shift, lbdp_shift]
      have e : -((t : ℝ) * -Δ) = t * Δ := by ring
      rw [e]
      have hv : (t : NNReal) ≠ 0 := by exact_mod_cast hpos.ne'
      have htr : (0 : ℝ) < t := by exact_mod_cast hpos
      refine le_trans ?_ (lbdp_gauss (t : NNReal) hv (t * Δ) (mul_nonneg htr.le hΔ.le))
      push_cast
      have htle : (t : ℝ) ≤ 10000 := by exact_mod_cast ht'
      have hexp : (95 / 96 : ℝ) ≤ Real.exp (-(((t : ℝ) * Δ) ^ 2) / (2 * t)) := by
        have e2 : -(((t : ℝ) * Δ) ^ 2) / (2 * t) = -((t : ℝ) * Δ ^ 2) / 2 := by
          field_simp
        rw [e2, hΔ2]
        have h1 := Real.add_one_le_exp (-((t : ℝ) * (1 / (48 * 10001))) / 2)
        have h3 : (t : ℝ) * (1 / (48 * 10001)) ≤ 1 / 48 := by linarith
        linarith
      have hpi : Real.sqrt (2 * Real.pi) ≤ 251 / 100 := by
        rw [show (251 / 100 : ℝ) = Real.sqrt ((251 / 100) ^ 2) from
          (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
      have hsq : Real.sqrt (2 * Real.pi * t) ≤ 251 / 100 * Real.sqrt t := by
        rw [Real.sqrt_mul (by positivity)]
        exact mul_le_mul_of_nonneg_right hpi (Real.sqrt_nonneg _)
      have hst : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 htr
      have hinv : (251 / 100 * Real.sqrt t)⁻¹ ≤ (Real.sqrt (2 * Real.pi * t))⁻¹ :=
        inv_anti₀ (Real.sqrt_pos.2 (by positivity)) hsq
      set s := Real.sqrt (t : ℝ) with hs
      have ht_eq : (t : ℝ) = s ^ 2 := (Real.sq_sqrt htr.le).symm
      have hs0 : s ≠ 0 := hst.ne'
      calc 2 * Δ * (95 / 96) / (251 / 100) * s
          = 2 * (s ^ 2 * Δ) * ((251 / 100 * s)⁻¹ * (95 / 96)) := by
            field_simp
        _ = 2 * ((t : ℝ) * Δ) * ((251 / 100 * s)⁻¹ * (95 / 96)) := by rw [← ht_eq]
        _ ≤ 2 * ((t : ℝ) * Δ) * ((Real.sqrt (2 * Real.pi * t))⁻¹ *
              Real.exp (-(((t : ℝ) * Δ) ^ 2) / (2 * t))) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) (mul_nonneg htr.le hΔ.le))
            exact mul_le_mul hinv hexp (by norm_num) (inv_nonneg.2 (Real.sqrt_nonneg _))
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hsum
  have hA := lbdp_sqrt_sum 10000
  have h100 : Real.sqrt 10000 = 100 := by
    rw [show (10000 : ℝ) = 100 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  push_cast at hA
  rw [h100] at hA
  have hC0 : 0 ≤ 2 * Δ * (95 / 96) / (251 / 100) :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hΔ.le) (by norm_num)) (by norm_num)
  have hCA := mul_le_mul_of_nonneg_left hA hC0
  have h10002 : Real.sqrt (10001 + 1) ≤ 10001 / 100 := by
    rw [show (10001 / 100 : ℝ) = Real.sqrt ((10001 / 100) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsl : Δ / 2 * (4 * 10001 + 2) * Real.sqrt (10001 + 1) ≤
      Δ / 2 * (4 * 10001 + 2) * (10001 / 100) :=
    mul_le_mul_of_nonneg_left h10002 (by positivity)
  nlinarith [hsum, hCA, hsl, hΔ]

open BanditAlgorithm in
theorem solution : ¬ (∀ {d n : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d),
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    let sign : Fin d → ℝ := fun j ↦ if σ j then 1 else -1
    let θ : Fin d → ℝ := fun j ↦ Δ * sign j
    let σ' : Fin d → Bool := Function.update σ i (!(σ i))
    let sign' : Fin d → ℝ := fun j ↦ if σ' j then 1 else -1
    let θ' : Fin d → ℝ := fun j ↦ Δ * sign' j
    let active : LinearBanditHistory d n → Fin n → Prop := fun h t ↦
      (∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s < t),
          ((h s).1 i) ^ 2) < (n : ℝ) / d
    let U : LinearBanditHistory d n → ℝ → ℝ := fun h x ↦
      ∑ t, if active h t then
        (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0
    (∫ h, U h (sign i) ∂linearBanditMeasure θ' π n) -
        (Δ / 2) * (4 * (n : ℝ) / d + 2) *
          Real.sqrt ((n : ℝ) / d + 1) ≤
      ∫ h, U h (sign i) ∂linearBanditMeasure θ π n) := by
  intro H
  have key := H (d := 1) (n := 10001) (by norm_num) (by norm_num) lbdpPol lbdpPol_supp
    (fun _ => true) 0
  change (∫ h, lbdpU _ _ _ h ∂linearBanditMeasure _ lbdpPol 10001) - _ ≤
    ∫ h, lbdpU _ _ _ h ∂linearBanditMeasure _ lbdpPol 10001 at key
  rw [lbdpU_int _ _ _ _ _ (-Real.sqrt (((1 : ℕ) : ℝ) / (48 * ((10001 : ℕ) : ℝ))))
      (by norm_num) (by simp) (by simp) (by simp),
    lbdpU_int _ _ _ _ _ (Real.sqrt (((1 : ℕ) : ℝ) / (48 * ((10001 : ℕ) : ℝ))))
      (by norm_num) (by simp) (by simp) (by simp)] at key
  simp only [Nat.cast_one, Nat.cast_ofNat, div_one] at key
  have hΔ : 0 < Real.sqrt (1 / (48 * 10001) : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hΔ2 : Real.sqrt (1 / (48 * 10001) : ℝ) ^ 2 = 1 / (48 * 10001) :=
    Real.sq_sqrt (by norm_num)
  have hfin := lbdp_final _ hΔ hΔ2
  linarith
