-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gaussian_lattice_cutoff_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:26.262902+00:00
-- url     : https://prove2.me/submissions/20f8cfc4-79a2-42ee-870b-712764e51782

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gaussian_lattice_cutoff_sum_of_separated_cutoff_sum
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_separated_sum_estimate_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.ExpansionTerms.GaussianLatticeCutoffSum := gaussian_lattice_cutoff_sum_of_separated_cutoff_sum separated_sum_estimate_holds
end Formalism.HermitianLatticeCounting.P
