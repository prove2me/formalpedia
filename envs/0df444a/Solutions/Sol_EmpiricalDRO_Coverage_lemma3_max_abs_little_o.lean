-- Prove2me | solution 1 for EmpiricalDRO.Coverage.lemma3_max_abs_little_o
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:05:21.116179+00:00
-- url     : https://prove2.me/submissions/61e67a97-6318-489d-a450-10e4516632bc

import Mathlib

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology

lemma edc_det (y : ℕ → ℝ) (hy : ∀ i, 0 ≤ y i)
    (h : ∀ k : ℕ, ∀ᶠ i : ℕ in atTop, y i ≤ (1 / ((k : ℝ) + 1)) * Real.sqrt i) :
    Tendsto (fun n : ℕ => (⨆ i : Fin n, y i) / Real.sqrt n) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall (fun n => lt_of_lt_of_le ha ?_), fun δ hδ => ?_⟩
  · exact div_nonneg (Real.iSup_nonneg (fun i => hy _)) (Real.sqrt_nonneg _)
  · obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < δ / 2 by positivity)
    set ε : ℝ := 1 / ((k : ℝ) + 1) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h k)
    set C : ℝ := ∑ i ∈ Finset.range N, y i with hC
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => hy i)
    have hT : Tendsto (fun n : ℕ => C / Real.sqrt n) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
    have hev := (tendsto_order.1 hT).2 (δ / 2) (by positivity)
    filter_upwards [hev, eventually_ge_atTop N, eventually_ge_atTop 1] with n hn hnN hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hmax : (⨆ i : Fin n, y i) ≤ C + ε * Real.sqrt n := by
      refine Real.iSup_le (fun i => ?_) (by positivity)
      by_cases hi : (i : ℕ) < N
      · have : y i ≤ C := Finset.single_le_sum (f := y) (fun j _ => hy j) (Finset.mem_range.2 hi)
        have : 0 ≤ ε * Real.sqrt n := by positivity
        linarith
      · have h1 := hN i (not_lt.mp hi)
        have h2 : Real.sqrt (i : ℕ) ≤ Real.sqrt n :=
          Real.sqrt_le_sqrt (by exact_mod_cast i.2.le)
        have : ε * Real.sqrt (i : ℕ) ≤ ε * Real.sqrt n := mul_le_mul_of_nonneg_left h2 hεpos.le
        linarith
    rw [div_lt_iff₀ hsq]
    have h3 : C / Real.sqrt n * Real.sqrt n = C := div_mul_cancel₀ _ hsq.ne'
    have h4 : C < δ / 2 * Real.sqrt n := by
      have := mul_lt_mul_of_pos_right hn hsq
      linarith
    have h5 : ε * Real.sqrt n < δ / 2 * Real.sqrt n := mul_lt_mul_of_pos_right hk hsq
    linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (hY : ∀ i, Measurable (Y i))
    (hindep : iIndepFun Y P) (hident : ∀ i, IdentDistrib (Y i) (Y 0) P P)
    (h2 : Integrable (fun ω => Y 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (⨆ i : Fin n, |Y i ω|) / Real.sqrt n) atTop (𝓝 0) := by
  letI : MeasureSpace Ω := { volume := P }
  have hbc : ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂P, ∀ᶠ i : ℕ in atTop, |Y i ω| ≤ ε * Real.sqrt i := by
    intro ε hε
    set X : Ω → ℝ := fun ω => Y 0 ω ^ 2 / ε ^ 2 with hX
    have hXint : Integrable X := h2.div_const _
    have hXnn : 0 ≤ X := fun ω => by positivity
    have hsum := tsum_prob_mem_Ioi_lt_top hXint hXnn
    have hmeasX : ∀ i, Measurable (fun ω => Y i ω ^ 2 / ε ^ 2) := fun i =>
      ((hY i).pow_const 2).div_const _
    set A : ℕ → Set Ω := fun i => {ω | (i : ℝ) < Y i ω ^ 2 / ε ^ 2} with hA
    have hAeq : ∀ i, P (A i) = ℙ {ω | X ω ∈ Set.Ioi (i : ℝ)} := by
      intro i
      have := ((hident i).comp ((measurable_id.pow_const 2).div_const (ε ^ 2))).measure_mem_eq
        (measurableSet_Ioi (a := (i : ℝ)))
      exact this
    have hsum' : ∑' i, P (A i) ≠ ⊤ := by
      simp only [hAeq]
      exact hsum.ne
    filter_upwards [ae_eventually_notMem hsum'] with ω hω
    filter_upwards [hω] with i hi
    simp only [hA, Set.mem_setOf_eq, not_lt] at hi
    have h1 : Y i ω ^ 2 ≤ ε ^ 2 * i := by
      rw [div_le_iff₀ (by positivity)] at hi
      linarith
    have h3 : |Y i ω| ≤ ε * Real.sqrt i := by
      have := Real.abs_le_sqrt h1
      rwa [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le] at this
    exact h3
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ i : ℕ in atTop,
      |Y i ω| ≤ (1 / ((k : ℝ) + 1)) * Real.sqrt i := by
    rw [ae_all_iff]
    intro k
    exact hbc _ (by positivity)
  filter_upwards [hall] with ω hω
  exact edc_det (fun i => |Y i ω|) (fun i => abs_nonneg _) hω
