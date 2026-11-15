-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a345_finite_masked_gaussian_small_discount_Young_bound_almost_sure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T11:26:14.485483+00:00
-- url     : https://prove2.me/submissions/eaae736f-d725-4189-9eaf-6df162fd0d66

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
import Theorems.Thm_AvramDividend_Classical_avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ ε L M η : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ)
    (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hM : 0 ≤ M) (hη : 0 < η)
    (hTime : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ᵐ ω ∂P, ∀ i ∈ S, A i ω → |h i ω| ≤ M) :
    ∀ᵐ ω ∂P,
      max (∑ i ∈ S, if A i ω then
        Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
          Real.exp (-(q*s i ω))*
            (d i ω*r i ω+h i ω/2*(z i ω)^2)
        else 0) 0 ≤
      ∑ i ∈ S, if A i ω then
        (ε+η)*(r i ω)^2+(q*Δ*L)^2/(4*η)+
          M/2*|(r i ω)^2-(z i ω)^2|
        else 0 := by
  classical
  filter_upwards [hTime, hTaylor, hLip, hHess] with ω ht htay hlip hhess
  let f : ℕ → ℝ := fun i =>
    if A i ω then
      Real.exp (-(q * (s i ω + Δ))) * (v i ω - u i ω) -
        Real.exp (-(q * s i ω)) *
          (d i ω * r i ω + h i ω / 2 * (z i ω) ^ 2)
    else 0
  let g : ℕ → ℝ := fun i =>
    if A i ω then
      (ε + η) * (r i ω) ^ 2 + (q * Δ * L) ^ 2 / (4 * η) +
        M / 2 * |(r i ω) ^ 2 - (z i ω) ^ 2|
    else 0
  have hg : ∀ i ∈ S, 0 ≤ g i := by
    intro i hi
    by_cases ha : A i ω
    · dsimp [g]
      rw [if_pos ha]
      positivity
    · simp [g, ha]
  have hc : ∀ i ∈ S, max (f i) 0 ≤ g i := by
    intro i hi
    by_cases ha : A i ω
    · have hs := ht i hi ha
      have hta := htay i hi ha
      have hl := hlip i hi ha
      have hh := hhess i hi ha
      have hb :=
        AvramDividend.Classical.avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
          q (s i ω) Δ (u i ω) (v i ω) (d i ω) (h i ω)
          (r i ω) (z i ω) ε L M hq hs hΔ hε hL hM hta hl hh
      have hy :=
        AvramDividend.Classical.avram_ga_a281_discount_raw_first_increment_Young_square_budget
          η (q * Δ) L (r i ω) hη (mul_nonneg hq hΔ) hL
      dsimp [f, g]
      rw [if_pos ha, if_pos ha]
      nlinarith
    · simp [f, g, ha]
  have hresult :=
    AvramDividend.Classical.avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
      S (fun i => A i ω) f g hg hc
  have hsumF :
      (∑ i ∈ S, if A i ω then f i else 0) =
      (∑ i ∈ S, if A i ω then
        Real.exp (-(q * (s i ω + Δ))) * (v i ω - u i ω) -
          Real.exp (-(q * s i ω)) *
            (d i ω * r i ω + h i ω / 2 * (z i ω) ^ 2)
        else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i ω <;> simp [f, ha]
  have hsumG :
      (∑ i ∈ S, if A i ω then g i else 0) =
      (∑ i ∈ S, if A i ω then
        (ε + η) * (r i ω) ^ 2 + (q * Δ * L) ^ 2 / (4 * η) +
          M / 2 * |(r i ω) ^ 2 - (z i ω) ^ 2|
        else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : A i ω <;> simp [g, ha]
  rw [hsumF, hsumG] at hresult
  convert hresult using 1
