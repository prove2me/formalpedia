-- Prove2me | solution 1 for Formalism.MainNotions.J.ncard_places
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:32.15631+00:00
-- url     : https://prove2.me/submissions/5fa4077f-f847-4765-8ace-3af37f2ef288

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot
import Theorems.Thm_Formalism_MainNotions_J_pI_max
import Theorems.Thm_Formalism_MainNotions_J_img_places

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open Ideal NumberField IsDedekindDomain
variable (K : Type) [Field K] [NumberField K] (p : ℕ)
namespace Formalism.MainNotions.J
theorem _root_.solution (hp : p.Prime) :
    ({v : HeightOneSpectrum (𝓞 K) | ((p : ℕ) : 𝓞 K) ∈ v.asIdeal}).ncard =
      (IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card := by
  haveI := pI_max p hp
  rw [← Set.ncard_coe_finset, IsDedekindDomain.coe_primesOverFinset (pI_ne_bot p hp), ← img_places K p hp,
    Set.ncard_image_of_injective _ (fun v w h => HeightOneSpectrum.ext h)]
end Formalism.MainNotions.J
