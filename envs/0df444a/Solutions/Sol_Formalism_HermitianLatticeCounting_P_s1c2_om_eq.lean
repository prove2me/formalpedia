-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_om_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:14.164627+00:00
-- url     : https://prove2.me/submissions/644248e9-f9cc-46b1-a6c8-213017364c89

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z')
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    N3om k r z z' g = reflectFlagCoordinates k r (formalDeterminantVectorOnGroup k r z z' g) +
      (herm (Hpk k r) (formalDeterminantVectorOnGroup k r z z' g) z' / (Tz k r z' : ℂ)) • z' := by
  funext i
  simp only [N3om, reflectFlagCoordinates, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · rfl
  · rw [hz' i (by omega), mul_zero, add_zero]
end Formalism.HermitianLatticeCounting.P
