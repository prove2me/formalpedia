-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.pi_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:57:42.793193+00:00
-- url     : https://prove2.me/submissions/c55c528f-e454-4ce1-a654-e8b2c2f730b8

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_RowCol
import Definitions.Def_Formalism_WachLatticeTwists_TorsionLengthCounts_SubmoduleLengthBoundStatement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_QuotLen
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_LOC_KO_torsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism.NG (KO annih)
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.LOC
open Module
variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution {d : ℕ} (w : Fin d → KO O) : ∃ c : O, c ≠ 0 ∧ c • w = 0 := by
  choose c hc hc' using fun z : KO O => KO_torsion z
  refine ⟨∏ i, c (w i), Finset.prod_ne_zero_iff.2 fun i _ => hc _, ?_⟩
  funext i
  obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun i => c (w i)) (Finset.mem_univ i)
  rw [Pi.smul_apply, Pi.zero_apply, hr, mul_comm, mul_smul, hc', smul_zero]
end Formalism.RepresentationBoundsCohomology.LOC
