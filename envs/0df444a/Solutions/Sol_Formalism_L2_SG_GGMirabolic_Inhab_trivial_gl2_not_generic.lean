-- Prove2me | solution 1 for Formalism.L2.SG.GGMirabolic.Inhab.trivial_gl2_not_generic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:57.655828+00:00
-- url     : https://prove2.me/submissions/8ce99c29-92e6-4fb7-9292-32a33688a6ca

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolicInhab
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_additive_char_one_ne_one
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_elementary_unipotent_is_unipotent
import Theorems.Thm_Formalism_L2_SG_GGMirabolic_Inhab_character_elementary_unipotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.GGMirabolic Formalism.L2.SG.GGMirabolic.Inhab
open Formalism.L2.SG.GGMirabolic
noncomputable section
open Classical
namespace Formalism.L2.SG.GGMirabolic.Inhab
theorem _root_.solution : ¬ Generic psi3 (Representation.trivial ℂ (GL (Fin 2) (ZMod 3)) ℂ) := by
  rintro ⟨ℓ, hℓ, hw⟩
  apply hℓ
  refine LinearMap.ext fun v => ?_
  have h := hw u12 elementary_unipotent_is_unipotent v
  rw [character_elementary_unipotent, Representation.trivial_apply] at h
  have h2 : (1 - psi3 1) * ℓ v = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3).symm additive_char_one_ne_one
  · simpa using h3
end Formalism.L2.SG.GGMirabolic.Inhab
