-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s1c2_Hh
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:12.794525+00:00
-- url     : https://prove2.me/submissions/a6d84a03-9eb3-4b30-ba21-cbf63afc17ee

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm


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
open Formalism.QuantumDeterminants.WeylGroupFacts
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := Formalism.QuantumDeterminants.GBasic.Hpk_herm k r
end Formalism.HermitianLatticeCounting.P
