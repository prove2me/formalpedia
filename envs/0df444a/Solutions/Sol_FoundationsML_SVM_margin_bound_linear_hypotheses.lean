-- Prove2me | solution 1 for FoundationsML.SVM.margin_bound_linear_hypotheses
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T14:32:05.960816+00:00
-- url     : https://prove2.me/submissions/1c03cbe4-bbc1-41d1-a324-caf5018d4af2

import Mathlib
import Definitions.Def_FoundationsML_SVM_MarginGeneralizationError
import Definitions.Def_FoundationsML_SVM_EmpiricalMarginLoss

/-! Disproof of 4da9f8c1 `FoundationsML.SVM.margin_bound_linear_hypotheses`.

The statement puts no lower bound on the sample size `m`. At `m = 0`, every sample-dependent
quantity on the right-hand side is zero in Lean. `EmpiricalMarginLoss` is `(1/0) * (empty sum)`,
and both square-root terms are `√(c / 0) = √0 = 0`.

Take `X = ℝ`, `D = δ_{(0, 1)}`, `r = Λ = 0`, `ρ = 1`, `δ = 1/2`. The hypothesis `‖p.1‖ ≤ 0` holds
at the single atom. For `w = 0` the hypothesis `x ↦ ⟪0, x⟫` is identically `0`, so its
generalization error is `D {p | p.2 * 0 ≤ 0} = D univ = 1`, which is not `≤ 0`. So the event
is empty, its probability is `0`, and `1 - δ = 1/2 ≤ 0` fails. -/

set_option autoImplicit false

open MeasureTheory

namespace SVMDis511

open FoundationsML.SVM

/-- At sample size `0` the empirical margin loss vanishes. -/
theorem eml_zero {X : Type} (ρ : ℝ) (S : Fin 0 → X) (y : Fin 0 → ℝ) (h : X → ℝ) :
    EmpiricalMarginLoss ρ S y h = 0 := by
  unfold EmpiricalMarginLoss
  simp

/-- The zero linear hypothesis has generalization error `1` under any probability measure. -/
theorem mge_inner_zero (D : Measure (ℝ × ℝ)) [IsProbabilityMeasure D] :
    MarginGeneralizationError D (fun x => inner ℝ (0 : ℝ) x) = 1 := by
  unfold MarginGeneralizationError
  simp

/-- The point mass at `(0, 1)` is supported where `‖p.1‖ ≤ 0`. -/
theorem ae_bound : ∀ᵐ p ∂(Measure.dirac (((0 : ℝ), (1 : ℝ)))), ‖p.1‖ ≤ (0 : ℝ) := by
  rw [ae_dirac_eq]
  simp

end SVMDis511

open FoundationsML.SVM in
theorem solution : ¬ (∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (r Λ : ℝ) (hr : 0 ≤ r) (hΛ : 0 ≤ Λ) (hX : ∀ᵐ p ∂D, ‖p.1‖ ≤ r)
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (m : ℕ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ w : X, ‖w‖ ≤ Λ →
        MarginGeneralizationError D (fun x => inner ℝ w x) ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun x => inner ℝ w x) +
            2 * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro hT
  have key := @hT ℝ _ _ _ _ (Measure.dirac (((0 : ℝ), (1 : ℝ)))) _ 0 0 le_rfl le_rfl
    SVMDis511.ae_bound 1 one_pos (1 / 2) (by norm_num) 0
  have hempty : {S : Fin 0 → ℝ × ℝ | ∀ w : ℝ, ‖w‖ ≤ 0 →
        MarginGeneralizationError (Measure.dirac (((0 : ℝ), (1 : ℝ)))) (fun x => inner ℝ w x) ≤
          EmpiricalMarginLoss 1 (fun i => (S i).1) (fun i => (S i).2) (fun x => inner ℝ w x) +
            2 * Real.sqrt ((0 : ℝ) ^ 2 * (0 : ℝ) ^ 2 / (1 : ℝ) ^ 2 / ((0 : ℕ) : ℝ)) +
            Real.sqrt (Real.log (1 / (1 / 2)) / (2 * ((0 : ℕ) : ℝ)))} = ∅ := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have h1 := hS 0 (by simp)
    rw [SVMDis511.mge_inner_zero, SVMDis511.eml_zero] at h1
    norm_num at h1
  rw [hempty, measure_empty, ENNReal.toReal_zero] at key
  norm_num at key
