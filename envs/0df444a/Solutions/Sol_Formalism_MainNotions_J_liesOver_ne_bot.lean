-- Prove2me | solution 1 for Formalism.MainNotions.J.liesOver_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:58.693529+00:00
-- url     : https://prove2.me/submissions/bc2c7f73-c4a8-4944-beb7-664393a70187

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot

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
theorem _root_.solution (hp : p.Prime) (I : Ideal (𝓞 K)) (hI : I.LiesOver (span {(p : ℤ)})) : I ≠ ⊥ := by
  intro h
  have h1 : (span {(p : ℤ)} : Ideal ℤ) = I.under ℤ := hI.over
  rw [h, Ideal.under, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at h1
  exact pI_ne_bot p hp h1
end Formalism.MainNotions.J
