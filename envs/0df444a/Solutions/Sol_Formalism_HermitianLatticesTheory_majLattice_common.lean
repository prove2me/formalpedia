-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majLattice_common
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:56.156066+00:00
-- url     : https://prove2.me/submissions/40cb9ff9-aed6-4b6f-ad16-794c9ce5b5d7

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_CommonMajorizingLattice_majLattice_common__06b6d465f20d
import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice
import Definitions.Def_Lemmata_GeneralBFactSecondRest_Imports
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module
open scoped Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (t : Finset K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ a ∈ t, IsIntegral ℤ ((d : K) * a) := by
  first | exact UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common .. | (apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> assumption) | (apply @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› t | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K ‹_› | exact @UpperTheory.Reformulated.B.CommonMajorizingLattice.majLattice_common K
end Formalism.HermitianLatticesTheory
