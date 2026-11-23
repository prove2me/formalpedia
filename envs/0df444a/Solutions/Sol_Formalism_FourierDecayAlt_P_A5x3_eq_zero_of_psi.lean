-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.eq_zero_of_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:22.292739+00:00
-- url     : https://prove2.me/submissions/6b45a732-2b4d-4759-8629-9ccfc13c153d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_smul_mk

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
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) (y : KR R)
    (hy : ∀ r : R, psiKR R ψ (r • y) = 1) : y = 0 := by
  induction y using Submodule.Quotient.induction_on with
  | H a =>
    rw [mk_eq_zero, ← h a]
    intro r hr
    have := hy ⟨r, hr⟩
    rw [smul_mk, psiKR_mk h] at this
    rw [mul_comm]; exact this
end Formalism.FourierDecayAlt.P.A5x3
