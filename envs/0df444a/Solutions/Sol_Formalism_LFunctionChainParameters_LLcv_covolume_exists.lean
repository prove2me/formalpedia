-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.covolume_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:28.83284+00:00
-- url     : https://prove2.me/submissions/b2996e50-db22-4fa5-89a3-fe75413ff773

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution : LcvExists := by
  intro K V _ _ _ _ _ _ _ M
  obtain ⟨s, hsN, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
  have hfin : s.Finite := hli.setFinite
  let _ : Fintype s := hfin.fintype
  let e : Fin (Fintype.card s) → V := fun i => ((Fintype.equivFin s).symm i : V)
  have he : LinearIndependent K e := hli.comp _ (Fintype.equivFin s).symm.injective
  have hrange : Set.range e = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact ((Fintype.equivFin s).symm i).2
    · intro hx; exact ⟨Fintype.equivFin s ⟨x, hx⟩, by simp [e]⟩
  exact ⟨_, e, he, fun a => hsN ((Fintype.equivFin s).symm a).2, by rw [hrange, hspan]⟩
end Formalism.LFunctionChainParameters.LLcv
