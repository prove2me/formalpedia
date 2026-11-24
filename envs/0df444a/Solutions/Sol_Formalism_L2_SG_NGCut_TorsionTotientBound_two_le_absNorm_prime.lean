-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.two_le_absNorm_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:44.275085+00:00
-- url     : https://prove2.me/submissions/b1b23a29-5aac-4282-b6fe-d42ced7df9ba

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TwoLeAbsNormPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
variable {E : Type} [Field E] [NumberField E]
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution {P : Ideal (𝓞 E)} (hP : P.IsPrime) (h0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  have h2 : Ideal.absNorm P ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0
  omega
end Formalism.L2.SG.NGCut.TorsionTotientBound
