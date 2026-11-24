-- Prove2me | solution 1 for Formalism.NG.burnside
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:43.380437+00:00
-- url     : https://prove2.me/submissions/f44e1277-6db9-4cb1-9cc6-ce11559622d8

import Definitions.Def_Formalism_CharacterColumnKernels_StatOntoLattice
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IdemNormalForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatBurnside := by
  intro k A V _ _ _ _ _ _ _ _ hS hsc f
  classical
  have := hS
  let F : Module.End (Module.End A V) V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun φ v => by
        obtain ⟨c, hc⟩ := hsc φ
        simp only [Module.End.smul_def, hc, RingHom.id_apply, f.map_smul] }
  obtain ⟨a, ha⟩ := jacobson_density F (Finset.univ.image (Module.finBasis k V))
  refine ⟨a, (Module.finBasis k V).ext fun i => ?_⟩
  have := ha (Module.finBasis k V i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  simpa [F] using this.symm
end Formalism.NG
