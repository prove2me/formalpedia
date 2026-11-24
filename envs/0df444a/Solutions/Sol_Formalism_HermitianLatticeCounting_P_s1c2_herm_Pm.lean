-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_herm_Pm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:33.00744+00:00
-- url     : https://prove2.me/submissions/615a0dfe-befa-4490-86dd-3effdd874532

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_sub_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_mid

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
theorem _root_.solution (k r : ℕ) (z' x : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') :
    herm (Hpk k r) (reflectFlagCoordinates k r x) z' = herm (Hpk k r) x z' := by
  have := s1c2_herm_mid k r z' (reflectFlagCoordinates k r x - x) hz' (by
    intro i h1 h2; simp [reflectFlagCoordinates, h1, h2])
  rw [s1c2_herm_sub_left, sub_eq_zero] at this
  exact this
end Formalism.HermitianLatticeCounting.P
