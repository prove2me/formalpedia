-- Prove2me | solution 1 for Formalism.UG.P.double_coset_indicator_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:23:36.549545+00:00
-- url     : https://prove2.me/submissions/d2843dd6-29bc-41a9-84da-6c0ca53ea83f

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Theorems.Thm_Formalism_UG_P_mem_dc_iff
import Theorems.Thm_Formalism_UG_P_ind_biInv
import Theorems.Thm_Formalism_UG_P_dc_stable
import Theorems.Thm_Formalism_UG_P_mem_hecke_iff
import Theorems.Thm_Formalism_UG_P_dosetInd_of_not_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.DosetIndMem := by
  unfold Formalism.UG.DosetIndMem
  intro G _ K k _ g
  rw [mem_hecke_iff]
  refine ⟨ind_biInv k K _ (fun a b x hx => dc_stable K g a b x hx), ?_⟩
  refine ⟨{g}, fun x hx => ⟨g, Finset.mem_singleton_self g, (mem_dc_iff K g x).1 ?_⟩⟩
  by_contra h
  exact hx (dosetInd_of_not_mem k K g x h)
end Formalism.UG.P
