-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.absNorm_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:41.597911+00:00
-- url     : https://prove2.me/submissions/4d1ca636-912c-4eea-b7b7-1a4773cec36b

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
theorem _root_.solution (σ : 𝓞 E ≃+* 𝓞 E) (I : Ideal (𝓞 E)) :
    Ideal.absNorm (I.map σ) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv I (I.map σ) σ rfl).toEquiv.symm
end Formalism.L2.SG.NGCut.TorsionTotientBound
