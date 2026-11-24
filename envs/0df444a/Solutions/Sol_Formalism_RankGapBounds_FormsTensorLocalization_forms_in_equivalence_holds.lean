-- Prove2me | solution 1 for Formalism.RankGapBounds.FormsTensorLocalization.forms_in_equivalence_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:08.553328+00:00
-- url     : https://prove2.me/submissions/3b5dedf8-59cd-4e7a-a833-e226f711e754

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.FormsTensorLocalization
open Formalism.UG
namespace Formalism.RankGapBounds.FormsTensorLocalization
theorem _root_.solution : FormsInEquiv := by
  intro G _ Γ K k _ W _ _ ρK U hU
  refine ⟨{ toFun := fun f => ⟨fun g => ((f : G → U) g : W),
              Submodule.mem_inf.2 ⟨fun γ g κ => congrArg Subtype.val (f.2 γ g κ),
                Submodule.mem_pi.2 fun g _ => ((f : G → U) g).2⟩⟩,
            invFun := fun φ => ⟨fun g => ⟨(φ : G → W) g,
                Submodule.mem_pi.1 (Submodule.mem_inf.1 φ.2).2 g (Set.mem_univ g)⟩,
              fun γ g κ => Subtype.ext ((Submodule.mem_inf.1 φ.2).1 γ g κ)⟩,
            map_add' := fun f f' => rfl,
            map_smul' := fun c f => rfl,
            left_inv := fun f => rfl,
            right_inv := fun φ => rfl }, fun f g => rfl⟩
end Formalism.RankGapBounds.FormsTensorLocalization
