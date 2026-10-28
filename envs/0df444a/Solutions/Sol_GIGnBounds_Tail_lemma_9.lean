-- Prove2me | solution 1 for GIGnBounds.Tail.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:40:15.355875+00:00
-- url     : https://prove2.me/submissions/70fc090e-e7fe-48ec-9f4a-f037ab4d5231

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

namespace GIGnL9Aux

open Classical

variable {Ω : Type}

/-- The exponential process `M_k = ∏_{i<k} exp(θ (c - Z_i)) = exp(θ (c k - S_k))`. -/
noncomputable def M (θ c : ℝ) (Z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ Finset.range k, Real.exp (θ * (c - Z i ω))

/-- `M_j < L` for every `j < k` (the level `L` has not yet been reached). -/
def G (θ c L : ℝ) (Z : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : Prop := ∀ j < k, M θ c Z j ω < L

/-- The process `M` stopped at the first time it reaches level `L`. -/
noncomputable def X (θ c L : ℝ) (Z : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | N + 1 => fun ω => if G θ c L Z (N + 1) ω then M θ c Z (N + 1) ω else X θ c L Z N ω

/-- The increment weight `1_{G_{N+1}} M_N`. -/
noncomputable def H (θ c L : ℝ) (Z : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  if G θ c L Z (N + 1) ω then M θ c Z N ω else 0

variable (θ c L : ℝ) (Z : ℕ → Ω → ℝ)

lemma M_pos (k : ℕ) (ω : Ω) : 0 < M θ c Z k ω :=
  Finset.prod_pos (fun _ _ => Real.exp_pos _)

lemma M_zero (ω : Ω) : M θ c Z 0 ω = 1 := by simp [M]

lemma M_succ (k : ℕ) (ω : Ω) :
    M θ c Z (k + 1) ω = M θ c Z k ω * Real.exp (θ * (c - Z k ω)) := by
  simp [M, Finset.prod_range_succ]

lemma M_eq_exp (k : ℕ) (ω : Ω) :
    M θ c Z k ω = Real.exp (θ * (c * k - ∑ i ∈ Finset.range k, Z i ω)) := by
  rw [M, ← Real.exp_sum]
  congr 1
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [mul_comm]

lemma X_eq_M (N : ℕ) (ω : Ω) (h : G θ c L Z N ω) : X θ c L Z N ω = M θ c Z N ω := by
  cases N with
  | zero => simp [X, M_zero]
  | succ N => simp [X, h]

lemma X_nonneg (N : ℕ) (ω : Ω) : 0 ≤ X θ c L Z N ω := by
  induction N with
  | zero => simp [X]
  | succ N ih =>
    simp only [X]
    split_ifs
    · exact (M_pos θ c Z _ ω).le
    · exact ih

lemma X_ge (N : ℕ) (ω : Ω) (h : ∃ k ≤ N, L ≤ M θ c Z k ω) : L ≤ X θ c L Z N ω := by
  induction N with
  | zero =>
    obtain ⟨k, hk, hL⟩ := h
    have : k = 0 := by omega
    subst this
    simpa [X, M_zero] using hL
  | succ N ih =>
    simp only [X]
    split_ifs with hg
    · obtain ⟨k, hk, hL⟩ := h
      rcases Nat.lt_or_ge k (N + 1) with hk' | hk'
      · exact absurd (hg k hk') (not_lt.mpr hL)
      · have : k = N + 1 := by omega
        subst this; exact hL
    · simp only [G, not_forall, not_lt] at hg
      obtain ⟨j, hj, hL⟩ := hg
      exact ih ⟨j, by omega, hL⟩

lemma X_succ_sub (N : ℕ) (ω : Ω) :
    X θ c L Z (N + 1) ω - X θ c L Z N ω =
      H θ c L Z N ω * (Real.exp (θ * (c - Z N ω)) - 1) := by
  by_cases hg : G θ c L Z (N + 1) ω
  · have hgN : G θ c L Z N ω := fun j hj => hg j (by omega)
    simp only [X, H, hg, if_true]
    rw [X_eq_M θ c L Z N ω hgN, M_succ]
    ring
  · simp [X, H, hg]

lemma M_le (k : ℕ) (ω : Ω) (_hc : 0 ≤ c) (hθ : 0 ≤ θ) (hZ : ∀ i, 0 ≤ Z i ω) :
    M θ c Z k ω ≤ Real.exp (θ * c * k) := by
  rw [M_eq_exp]
  apply Real.exp_le_exp.mpr
  have : 0 ≤ ∑ i ∈ Finset.range k, Z i ω := Finset.sum_nonneg (fun i _ => hZ i)
  nlinarith

lemma X_le (N : ℕ) (ω : Ω) (hc : 0 ≤ c) (hθ : 0 ≤ θ) (hZ : ∀ i, 0 ≤ Z i ω) :
    X θ c L Z N ω ≤ Real.exp (θ * c * N) := by
  induction N with
  | zero => simp [X]
  | succ N ih =>
    simp only [X]
    split_ifs
    · exact M_le θ c Z _ ω hc hθ hZ
    · refine ih.trans (Real.exp_le_exp.mpr ?_)
      have : 0 ≤ θ * c := mul_nonneg hθ hc
      push_cast; nlinarith

section meas

variable {m : MeasurableSpace Ω}

lemma M_meas (K : ℕ) (hZ : ∀ i < K, Measurable[m] (Z i)) (j : ℕ) (hj : j ≤ K) :
    Measurable[m] (M θ c Z j) := by
  unfold M
  apply Finset.measurable_prod
  intro i hi
  have hi' : i < K := by simp at hi; omega
  exact (measurable_const.mul (measurable_const.sub (hZ i hi'))).exp

lemma G_meas (K : ℕ) (hZ : ∀ i < K, Measurable[m] (Z i)) :
    MeasurableSet[m] {ω | G θ c L Z (K + 1) ω} := by
  have : {ω | G θ c L Z (K + 1) ω} = ⋂ j : Fin (K + 1), {ω | M θ c Z j ω < L} := by
    ext ω; simp only [G, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h j; exact h j j.isLt
    · intro h j hj; exact h ⟨j, hj⟩
  rw [this]
  exact MeasurableSet.iInter (fun j => measurableSet_lt
    (M_meas θ c Z K hZ j (by omega)) measurable_const)

lemma H_meas (K : ℕ) (hZ : ∀ i < K, Measurable[m] (Z i)) : Measurable[m] (H θ c L Z K) := by
  unfold H
  exact Measurable.ite (G_meas θ c L Z K hZ) (M_meas θ c Z K hZ K le_rfl) measurable_const

lemma X_meas (hZ : ∀ i, Measurable[m] (Z i)) (N : ℕ) : Measurable[m] (X θ c L Z N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    exact Measurable.ite (G_meas θ c L Z N (fun i _ => hZ i))
      (M_meas θ c Z (N + 1) (fun i _ => hZ i) _ le_rfl) ih

end meas

end GIGnL9Aux

open GIGnL9Aux in
theorem solution (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0)
    (hν1 : ∫ z, z ∂ν = 1) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (θ : ℝ) (hθ : 0 < θ)
    (hmgf : ∫ z, Real.exp (θ * (c - z)) ∂ν ≤ 1)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (hZ : IsIIDSeq P Z ν) (x : ℝ) (hx : 0 < x) :
    P.real {ω | (x : EReal) ≤ ⨆ k : ℕ, ((c * k - ∑ i ∈ Finset.range k, Z i ω : ℝ) : EReal)} ≤
      Real.exp (-θ * x) := by
  have hZm : ∀ i, Measurable (Z i) := hZ.measurable
  -- nonnegativity of every `Z i`, almost surely
  have hZnn : ∀ᵐ ω ∂P, ∀ i, 0 ≤ Z i ω := by
    rw [ae_all_iff]
    intro i
    have h1 : P (Z i ⁻¹' Set.Iio 0) = 0 := by
      rw [← Measure.map_apply (hZm i) measurableSet_Iio, hZ.law i, hν0]
    rw [ae_iff]
    simpa [Set.preimage, not_le] using h1
  -- the law of `exp(θ(c - Z N))`
  have hY : ∀ N, ∫ ω, Real.exp (θ * (c - Z N ω)) ∂P ≤ 1 := by
    intro N
    have : ∫ ω, Real.exp (θ * (c - Z N ω)) ∂P = ∫ z, Real.exp (θ * (c - z)) ∂(P.map (Z N)) := by
      rw [integral_map (hZm N).aemeasurable]
      exact (Real.continuous_exp.comp (continuous_const.mul
        (continuous_const.sub continuous_id))).aestronglyMeasurable
    rw [this, hZ.law N]; exact hmgf
  have hYint : ∀ N, Integrable (fun ω => Real.exp (θ * (c - Z N ω))) P := by
    intro N
    refine Integrable.mono' (integrable_const (Real.exp (θ * c))) ?_ ?_
    · exact ((measurable_const.mul (measurable_const.sub (hZm N))).exp).aestronglyMeasurable
    · filter_upwards [hZnn] with ω hω
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      nlinarith [hω N]
  -- independence structure
  have hind : iIndep (fun i => MeasurableSpace.comap (Z i) inferInstance) P :=
    (iIndepFun_iff_iIndep _ Z P).mp hZ.indep
  have hle : ∀ i, MeasurableSpace.comap (Z i) (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace Ω) := fun i => (hZm i).comap_le
  -- main maximal inequality: for every level `L > 0` and every `N`
  have key : ∀ L : ℝ, 0 < L → ∀ N : ℕ,
      L * P.real {ω | ∃ k ≤ N, L ≤ M θ c Z k ω} ≤ 1 := by
    intro L hL N
    have hXint : ∀ N, Integrable (X θ c L Z N) P := by
      intro N
      refine Integrable.mono' (integrable_const (Real.exp (θ * c * N))) ?_ ?_
      · exact (X_meas θ c L Z hZm N).aestronglyMeasurable
      · filter_upwards [hZnn] with ω hω
        rw [Real.norm_eq_abs, abs_of_nonneg (X_nonneg θ c L Z N ω)]
        exact X_le θ c L Z N ω hc0.le hθ.le hω
    have hHint : ∀ N, Integrable (H θ c L Z N) P := by
      intro N
      refine Integrable.mono' (integrable_const (Real.exp (θ * c * N))) ?_ ?_
      · exact (H_meas θ c L Z N (fun i _ => hZm i)).aestronglyMeasurable
      · filter_upwards [hZnn] with ω hω
        unfold H
        split_ifs
        · rw [Real.norm_eq_abs, abs_of_pos (M_pos θ c Z N ω)]
          exact M_le θ c Z N ω hc0.le hθ.le hω
        · rw [norm_zero]; exact (Real.exp_pos _).le
    have hint_le : ∀ N, ∫ ω, X θ c L Z N ω ∂P ≤ 1 := by
      intro N
      induction N with
      | zero => simp [X]
      | succ N ih =>
        -- independence of `H N` and `exp(θ(c - Z N)) - 1`
        have hindep : IndepFun (H θ c L Z N) (fun ω => Real.exp (θ * (c - Z N ω)) - 1) P := by
          rw [IndepFun_iff_Indep]
          have hI := indep_iSup_of_disjoint hle hind
            (S := Set.Iio N) (T := {N}) (by simp)
          have hT : (⨆ i ∈ ({N} : Set ℕ), MeasurableSpace.comap (Z i)
              (inferInstance : MeasurableSpace ℝ)) = MeasurableSpace.comap (Z N) inferInstance := by
            simp
          rw [hT] at hI
          refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hI ?_) ?_
          · apply Measurable.comap_le
            apply H_meas θ c L Z N
            intro i hi
            apply Measurable.of_comap_le
            exact le_iSup₂ (f := fun j (_ : j ∈ Set.Iio N) =>
              MeasurableSpace.comap (Z j) (inferInstance : MeasurableSpace ℝ)) i hi
          · apply Measurable.comap_le
            have : Measurable[MeasurableSpace.comap (Z N) inferInstance] (Z N) :=
              comap_measurable (Z N)
            exact ((measurable_const.mul (measurable_const.sub this)).exp).sub measurable_const
        have hprod : ∫ ω, H θ c L Z N ω * (Real.exp (θ * (c - Z N ω)) - 1) ∂P =
            (∫ ω, H θ c L Z N ω ∂P) * ∫ ω, (Real.exp (θ * (c - Z N ω)) - 1) ∂P :=
          hindep.integral_mul_eq_mul_integral (hHint N).aestronglyMeasurable
            ((hYint N).sub (integrable_const 1)).aestronglyMeasurable
        have hdiff : ∫ ω, X θ c L Z (N + 1) ω ∂P - ∫ ω, X θ c L Z N ω ∂P =
            ∫ ω, H θ c L Z N ω * (Real.exp (θ * (c - Z N ω)) - 1) ∂P := by
          rw [← integral_sub (hXint (N + 1)) (hXint N)]
          exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => X_succ_sub θ c L Z N ω))
        have hHnn : 0 ≤ ∫ ω, H θ c L Z N ω ∂P := by
          apply integral_nonneg
          intro ω; unfold H; split_ifs
          · exact (M_pos θ c Z N ω).le
          · exact le_rfl
        have hY1 : ∫ ω, (Real.exp (θ * (c - Z N ω)) - 1) ∂P ≤ 0 := by
          rw [integral_sub (hYint N) (integrable_const 1)]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          linarith [hY N]
        have : (∫ ω, H θ c L Z N ω ∂P) * ∫ ω, (Real.exp (θ * (c - Z N ω)) - 1) ∂P ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hHnn hY1
        linarith
    calc L * P.real {ω | ∃ k ≤ N, L ≤ M θ c Z k ω}
        ≤ L * P.real {ω | L ≤ X θ c L Z N ω} := by
          apply mul_le_mul_of_nonneg_left _ hL.le
          apply measureReal_mono _ (measure_ne_top _ _)
          intro ω hω
          exact X_ge θ c L Z N ω hω
      _ ≤ ∫ ω, X θ c L Z N ω ∂P :=
          mul_meas_ge_le_integral_of_nonneg
            (Filter.Eventually.of_forall (fun ω => X_nonneg θ c L Z N ω)) (hXint N) L
      _ ≤ 1 := hint_le N
  -- bound for every level `y`
  have hy : ∀ y : ℝ, y < x → P.real {ω | (x : EReal) ≤
      ⨆ k : ℕ, ((c * k - ∑ i ∈ Finset.range k, Z i ω : ℝ) : EReal)} ≤ Real.exp (-θ * y) := by
    intro y hyx
    set L := Real.exp (θ * y) with hLdef
    have hL : 0 < L := Real.exp_pos _
    have hsub : {ω | (x : EReal) ≤
        ⨆ k : ℕ, ((c * k - ∑ i ∈ Finset.range k, Z i ω : ℝ) : EReal)} ⊆
        ⋃ N : ℕ, {ω | ∃ k ≤ N, L ≤ M θ c Z k ω} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      have hlt : ((y : ℝ) : EReal) < ⨆ k : ℕ, ((c * k - ∑ i ∈ Finset.range k, Z i ω : ℝ) : EReal) :=
        lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hyx) hω
      obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
      have hk' : y < c * k - ∑ i ∈ Finset.range k, Z i ω := EReal.coe_lt_coe_iff.mp hk
      refine Set.mem_iUnion.mpr ⟨k, k, le_rfl, ?_⟩
      rw [M_eq_exp, hLdef]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hmono : Monotone (fun N : ℕ => {ω | ∃ k ≤ N, L ≤ M θ c Z k ω}) := by
      intro a b hab ω hω
      obtain ⟨k, hk, h⟩ := hω
      exact ⟨k, hk.trans hab, h⟩
    have hU : P (⋃ N : ℕ, {ω | ∃ k ≤ N, L ≤ M θ c Z k ω}) ≤ ENNReal.ofReal (1 / L) := by
      rw [hmono.measure_iUnion]
      apply iSup_le
      intro N
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      apply ENNReal.ofReal_le_ofReal
      rw [le_div_iff₀ hL]
      linarith [key L hL N]
    have hU' : P.real (⋃ N : ℕ, {ω | ∃ k ≤ N, L ≤ M θ c Z k ω}) ≤ 1 / L := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) hU
    calc _ ≤ P.real (⋃ N : ℕ, {ω | ∃ k ≤ N, L ≤ M θ c Z k ω}) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ 1 / L := hU'
      _ = Real.exp (-θ * y) := by
          rw [hLdef, one_div, ← Real.exp_neg]; ring_nf
  -- let `y ↑ x`
  have hcont : Filter.Tendsto (fun y => Real.exp (-θ * y)) (nhdsWithin x (Set.Iio x))
      (nhds (Real.exp (-θ * x))) :=
    tendsto_nhdsWithin_of_tendsto_nhds
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).tendsto x)
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall (fun y hy' => hy y hy'))
