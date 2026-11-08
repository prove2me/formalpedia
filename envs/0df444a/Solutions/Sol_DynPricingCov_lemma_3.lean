-- Prove2me | solution 1 for DynPricingCov.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:48:52.057292+00:00
-- url     : https://prove2.me/submissions/d02c1126-f445-4d8d-a0fc-537eb7507707

import Mathlib
import Definitions.Def_DynPricingCov_Model

open MeasureTheory ProbabilityTheory

open DynPricingCov in
theorem solution {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d T : ℕ} (g : ℝ → ℝ) (θstar : Fin (d + d) → ℝ)
    (x : ℕ → Fin d → ℝ) {ℱ : Filtration ℕ mΩ} {σbar : ℝ} {ε : ℕ → Ω → ℝ}
    (h3 : Assumption3 P ℱ σbar ε) (p : ℕ → Ω → ℝ) {t : ℕ} (ht : t ∈ Finset.Icc 1 T) :
    P[xi g θstar x ε p θstar t | ℱ (t - 1)] =ᵐ[P] 0 ∧
      HasCondSubgaussianMGF (ℱ (t - 1)) (ℱ.le (t - 1)) (xi g θstar x ε p θstar t)
        (σbar ^ 2).toNNReal P := by
  have hxi : xi g θstar x ε p θstar t = ε t := by
    funext ω
    unfold xi demand
    ring
  rw [hxi]
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by have := (Finset.mem_Icc.mp ht).1; omega⟩
  simp only [Nat.add_sub_cancel]
  exact ⟨h3.condExp_eq_zero s, h3.subgaussian s⟩
