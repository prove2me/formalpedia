-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.Filt.relIndex_unipotent_conj_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:06.466113+00:00
-- url     : https://prove2.me/submissions/d8f3e058-2e45-4a2b-ae55-f92d88b9b127

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_InvSubOneBd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_FiltRelIndex
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexUnipotentConjSymm
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_sub_mono
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_sub_comm
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_sub_top
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_sub_bot
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_cj_subgroupOf
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_filt_relIndex
import Theorems.Thm_Formalism_L2_SG_Pf_RelativeIndexFlags_Filt_mem_cj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
variable {n : ℕ} {K : Type*} [Field K] (L : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
namespace Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
theorem _root_.solution (hLF : L ≤ FG n K 0) (X : Subgroup (Matrix.GeneralLinearGroup (Fin n) K))
    (g : Matrix.GeneralLinearGroup (Fin n) K) (hg : g ∈ L) (hX : X ≤ L) :
    X.relIndex (cj g X) = (cj g X).relIndex X := by
  have hY : cj g X ≤ L := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (mem_cj g X y).1 hy
    exact L.mul_mem (L.mul_mem hg (hX hx)) (L.inv_mem hg)
  have key : (X.subgroupOf L).relIndex (cj ⟨g, hg⟩ (X.subgroupOf L)) =
      (cj ⟨g, hg⟩ (X.subgroupOf L)).relIndex (X.subgroupOf L) :=
    filt_relIndex (fun k => (FG n K k).subgroupOf L) (sub_mono L) (sub_comm L hLF) n
      (sub_top L hLF) (sub_bot L) (X.subgroupOf L) ⟨g, hg⟩
  rw [← Subgroup.relIndex_subgroupOf hY, ← Subgroup.relIndex_subgroupOf hX,
    cj_subgroupOf L X g hg hX]
  exact key
end Formalism.L2.SG.Pf.RelativeIndexFlags.Filt
