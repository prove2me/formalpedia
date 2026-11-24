-- Prove2me | solution 1 for Formalism.MainNotions.J.ef_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:09.006515+00:00
-- url     : https://prove2.me/submissions/5cf691ca-8272-4ae4-a942-a4c6b231416f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_SfromGLt
import Theorems.Thm_Formalism_MainNotions_J_pI_ne_bot
import Theorems.Thm_Formalism_MainNotions_J_pI_max

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
theorem _root_.solution (hp : p.Prime) (P : Ideal (𝓞 K)) (hP : P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 K)) :
    1 ≤ (span {(p : ℤ)}).ramificationIdx' P * (span {(p : ℤ)}).inertiaDeg' P := by
  haveI := pI_max p hp
  obtain ⟨hPp, hPl⟩ := (IsDedekindDomain.mem_primesOverFinset_iff (pI_ne_bot p hp) (𝓞 K)).mp hP
  have he : 0 < (span {(p : ℤ)}).ramificationIdx' P := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ (pI_ne_bot p hp)]
    exact Ideal.ramificationIdx_pos P ℤ
  have hf : 0 < (span {(p : ℤ)}).inertiaDeg' P := Ideal.inertiaDeg'_pos _ _
  exact Nat.mul_pos he hf
end Formalism.MainNotions.J
