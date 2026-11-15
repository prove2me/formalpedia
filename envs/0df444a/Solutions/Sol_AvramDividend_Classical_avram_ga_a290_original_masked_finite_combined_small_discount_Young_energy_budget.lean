-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a290_original_masked_finite_combined_small_discount_Young_energy_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:24:08.110407+00:00
-- url     : https://prove2.me/submissions/6e282bbc-206e-4dad-878e-ddcf72937b43

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
import Theorems.Thm_AvramDividend_Classical_avram_ga_a281_discount_raw_first_increment_Young_square_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} (S : Finset ℕ) (A : ℕ → Ω → Prop)
    [∀ i, DecidablePred (A i)]
    (s u v d h r z : ℕ → Ω → ℝ)
    (q Δ ε L M η : ℝ)
    (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε)
    (hL : 0 ≤ L) (hM : 0 ≤ M) (hη : 0 < η)
    (hTime : ∀ i ω, A i ω → 0 ≤ s i ω)
    (hTaylor : ∀ i ω, A i ω →
      max (Real.exp (-(q*s i ω)) *
        (v i ω-u i ω-d i ω*r i ω-h i ω/2*(r i ω)^2)) 0 ≤
        ε*(r i ω)^2)
    (hLip : ∀ i ω, A i ω →
      |v i ω-u i ω| ≤ L*|r i ω|)
    (hHess : ∀ i ω, A i ω → |h i ω| ≤ M)
    (ω : Ω) :
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
  let F : ℕ → ℝ := fun i =>
    Real.exp (-(q*(s i ω+Δ)))*(v i ω-u i ω) -
      Real.exp (-(q*s i ω))*(d i ω*r i ω+h i ω/2*(z i ω)^2)
  let G : ℕ → ℝ := fun i =>
    (ε+η)*(r i ω)^2+(q*Δ*L)^2/(4*η)+
      M/2*|(r i ω)^2-(z i ω)^2|
  have hGPos (i : ℕ) : 0 ≤ G i := by
    dsimp [G]
    have he : 0 ≤ ε+η := by linarith
    positivity
  have hEach (i : ℕ) (ha : A i ω) :
      max (F i) 0 ≤ G i := by
    have hBase := avram_ga_a236_original_gaussian_discounted_one_sided_small_cell_source_bound
      q (s i ω) Δ (u i ω) (v i ω)
      (d i ω) (h i ω) (r i ω) (z i ω) ε L M
      hq (hTime i ω ha) hΔ hε hL hM
      (hTaylor i ω ha) (hLip i ω ha) (hHess i ω ha)
    have hY := avram_ga_a281_discount_raw_first_increment_Young_square_budget
      η (q*Δ) L (r i ω) hη (mul_nonneg hq hΔ) hL
    dsimp [F,G]
    linarith
  have hGP (i : ℕ) (_ : i ∈ S) :
      0 ≤ (if A i ω then G i else 0) := by
    by_cases ha : A i ω <;> simp [ha,hGPos]
  have hEP (i : ℕ) (_ : i ∈ S) :
      max (if A i ω then F i else 0) 0 ≤
        (if A i ω then G i else 0) := by
    by_cases ha : A i ω
    · simpa only [if_pos ha] using hEach i ha
    · simp only [if_neg ha, max_self, le_refl]
  have hS := avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
    S (fun _ : ℕ => True)
    (fun i => if A i ω then F i else 0)
    (fun i => if A i ω then G i else 0) hGP hEP
  simpa only [if_true, F, G] using hS
