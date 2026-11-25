-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minimal_degree_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:14.046269+00:00
-- url     : https://prove2.me/submissions/1506f842-5e66-4e69-a08c-465017f2a0b2

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_P2M_Formalism_HermitianLatticeCounting_P_leading_minor_codings_agree__61f7b61d77c5

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
theorem _root_.solution : DminBridge := by
  intro k r z z' g l
  rw [leading_minor_codings_agree' _ _ _ _ (Nat.le_of_lt_succ l.isLt)]
  rfl
end Formalism.HermitianLatticeCounting.P
