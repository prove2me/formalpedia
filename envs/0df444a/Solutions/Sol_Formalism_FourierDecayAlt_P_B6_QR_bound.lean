-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.QR_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:25:53.514295+00:00
-- url     : https://prove2.me/submissions/62f0f78f-8b55-4165-8f24-34cd54f9cb5b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_right_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weight_lower_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_left_derivative
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissibleWeight_of_succ_left_order
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phdil_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (m l : ℕ) (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
    AdmW α cA l m A → AdmW α cB l m B → ∀ p, D.inSS p → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2, ‖QR D p m l A B x y‖ ≤ 2 ^ (m + l) * (K * cA * cB * XX Ξ p) := by
  obtain ⟨K, hK, hb⟩ := phdil_bound H
  refine ⟨K, hK, ?_⟩
  have hQL : ∀ (m : ℕ) (A B : Mat k r → (Wq →L[ℂ] Wp)) (cA cB : ℝ),
      AdmW α cA 0 m A → AdmW α cB 0 m B → ∀ p, D.inSS p → ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2,
      ∀ y ∈ Set.Icc (1 / 2 : ℝ) 2, ‖QL D p m A B x y‖ ≤ 2 ^ m * (K * cA * cB * XX Ξ p) := by
    intro m
    induction m with
    | zero =>
      intro A B cA cB hA hB p hp x hx y hy
      simpa [QL] using hb A B cA cB (admissible_of_weighted hA) (admissible_of_weighted hB) p hp x hx y hy
    | succ m ih =>
      intro A B cA cB hA hB p hp x hx y hy
      have h1 := ih (Ll A) B cA cB (admissibleWeight_left_derivative hA) (admissibleWeight_of_succ_left_order hB) p hp x hx y hy
      have h2 := ih A (Ll B) cA cB (admissibleWeight_of_succ_left_order hA) (admissibleWeight_left_derivative hB) p hp x hx y hy
      calc ‖QL D p (m + 1) A B x y‖ ≤ ‖QL D p m (Ll A) B x y‖ + ‖QL D p m A (Ll B) x y‖ := norm_add_le _ _
        _ ≤ 2 ^ m * (K * cA * cB * XX Ξ p) + 2 ^ m * (K * cA * cB * XX Ξ p) := add_le_add h1 h2
        _ = _ := by ring
  intro m l
  induction l with
  | zero =>
    intro A B cA cB hA hB p hp x hx y hy
    exact hQL m A B cA cB hA hB p hp x hx y hy
  | succ l ih =>
    intro A B cA cB hA hB p hp x hx y hy
    have h1 := ih (Rr A) B cA cB (admissibleWeight_right_derivative hA) (admissible_weight_lower_order hB) p hp x hx y hy
    have h2 := ih A (Rr B) cA cB (admissible_weight_lower_order hA) (admissibleWeight_right_derivative hB) p hp x hx y hy
    calc ‖QR D p m (l + 1) A B x y‖ ≤ ‖QR D p m l (Rr A) B x y‖ + ‖QR D p m l A (Rr B) x y‖ := norm_add_le _ _
      _ ≤ 2 ^ (m + l) * (K * cA * cB * XX Ξ p) + 2 ^ (m + l) * (K * cA * cB * XX Ξ p) := add_le_add h1 h2
      _ = _ := by rw [← add_assoc m l 1]; ring
end Formalism.FourierDecayAlt.P.B6
