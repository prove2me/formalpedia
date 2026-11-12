-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger108_nonnegative_shifted_domination_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:07:28.822627+00:00
-- url     : https://prove2.me/submissions/66722739-7073-4ee3-a3cd-c5fc264fa2f5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
noncomputable section

/-- Measurable nonnegative errors dominated by a shifted vanishing L1 envelope vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (E B : ℕ → Ω → ℝ)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (B m) P ∧ (∫ ω, B m ω ∂P) ≤ ε)
    (hEmeas : ∀ m : ℕ, Measurable (E (m + 1)))
    (hEnonneg : ∀ m : ℕ, ∀ ω : Ω, 0 ≤ E (m + 1) ω)
    (hBnonneg : ∀ m : ℕ, ∀ ω : Ω, 0 ≤ B m ω)
    (hpoint : ∀ m : ℕ, ∀ ω : Ω, E (m + 1) ω ≤ B m ω) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨k, hk⟩ := hB ε hε
  refine ⟨k + 1, ?_⟩
  intro m hm
  have hshift : (m - 1) + 1 = m := by omega
  obtain ⟨hBI, hBε⟩ := hk (m - 1) (by omega)
  have hEI : Integrable (E ((m - 1) + 1)) P := by
    apply hBI.mono' (hEmeas (m - 1)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (hEnonneg (m - 1) ω),
        abs_of_nonneg (hBnonneg (m - 1) ω)] using hpoint (m - 1) ω)
  have hIntLe : (∫ ω, E ((m - 1) + 1) ω ∂P) ≤
      (∫ ω, B (m - 1) ω ∂P) :=
    integral_mono_ae hEI hBI (Filter.Eventually.of_forall (hpoint (m - 1)))
  rw [hshift] at hEI hIntLe
  exact ⟨hEI, le_trans hIntLe hBε⟩
