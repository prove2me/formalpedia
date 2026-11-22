-- Prove2me | solution 1 for Formalism.UG.P.glint_exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:59:00.756047+00:00
-- url     : https://prove2.me/submissions/d037235c-9a9b-4b79-aa83-3d6677e8a0ea

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Theorems.Thm_Bl_NearbyExistence_goal1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution (x : v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v ((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) < 1 := by
  first | exact Bl.NearbyExistence.goal1 .. | (apply Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> assumption) | (intros; apply @Bl.NearbyExistence.goal1 <;> assumption) | (apply @Bl.NearbyExistence.goal1 <;> first | assumption | infer_instance)
end Formalism.UG.P
