-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.LOC.locTorsDual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:48.242313+00:00
-- url     : https://prove2.me/submissions/11301d1d-2e1d-4e6f-9cff-3f5c0d9e5e05

import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_Statement
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_LatticeDualProofs_LocDualOrth
import Theorems.Thm_P2M_Formalism_RepresentationBoundsCohomology_LOC_mem_annih__37a7288d66f3
import Theorems.Thm_Formalism_NG_annColength


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
namespace Formalism.RepresentationBoundsCohomology.LOC
theorem _root_.solution : StatLocTorsDual.{u} := by
  intro O A H _ _ _ _ _ _ _ pr M S a hS
  have hIm : (mulSub a M).map M.subtype ≤ M := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have h0 := Formalism.NG.annColength O A H pr M ((mulSub a M).map M.subtype) hIm
  rw [Submodule.comap_map_eq_of_injective M.injective_subtype] at h0
  refine le_trans ?_ h0
  have hSle : S ≤ annih pr ((mulSub a M).map M.subtype) := by
    intro s hs
    rw [mem_annih']
    rintro _ ⟨x, ⟨m, rfl⟩, rfl⟩
    have := (mem_annih' pr M _).1 (hS s hs) m m.2
    simpa only [LinearMap.lsmul_apply, Submodule.subtype_apply, Submodule.coe_smul, map_smul,
      LinearMap.smul_apply] using this
  let f : (S ⧸ (annih pr M).comap S.subtype) →ₗ[O]
      (annih pr ((mulSub a M).map M.subtype) ⧸
        (annih pr M).comap (annih pr ((mulSub a M).map M.subtype)).subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hSle) (by
      intro x hx
      exact hx)
  refine Module.length_le_of_injective f ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    intro hx
    have hx' : (Submodule.Quotient.mk (Submodule.inclusion hSle x) :
        (annih pr ((mulSub a M).map M.subtype) ⧸
          (annih pr M).comap (annih pr ((mulSub a M).map M.subtype)).subtype)) = 0 := hx
    have hx'' := (Submodule.Quotient.mk_eq_zero _).1 hx'
    exact (Submodule.Quotient.mk_eq_zero _).2 hx''
end Formalism.RepresentationBoundsCohomology.LOC
