-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.coker_sep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:24.356376+00:00
-- url     : https://prove2.me/submissions/79225e4e-17f9-4b70-a1c1-01e5b4ea5f7c

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_rowFun_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_rowFun_kills

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (Z : Matrix (Fin n) (Fin n) K) (hZ : IsUnit Z.det) (c : coker R Z)
    (hc : ∀ α : coker R Z →ₗ[R] KR R, α c = 0) : c = 0 := by
  induction c using Submodule.Quotient.induction_on with
  | H v =>
    rw [Submodule.Quotient.mk_eq_zero, Formalism.DoubleCosetMeasures.P.mem_latZ]
    have h1 : ∀ a, (Z⁻¹ *ᵥ coeLin R v) a ∈ R := by
      intro a
      have := hc ((latZ R Z).liftQ (rowFun R Z a) (rowFun_kills R Z hZ a))
      rw [Submodule.liftQ_apply, rowFun_apply, mk_eq_zero] at this
      exact this
    refine ⟨fun a => ⟨_, h1 a⟩, ?_⟩
    have h2 : coeLin R (fun a => (⟨_, h1 a⟩ : R)) = Z⁻¹ *ᵥ coeLin R v := by
      funext a
      rw [Formalism.DoubleCosetMeasures.P.coeLin_apply]
    rw [h2, mulVec_mulVec, Matrix.mul_nonsing_inv Z hZ, one_mulVec]
end Formalism.FourierDecayAlt.P.A5x3
