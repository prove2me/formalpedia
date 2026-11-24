-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.lpprime_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:09.582394+00:00
-- url     : https://prove2.me/submissions/051604bd-9c0e-4508-b96c-3c49f9c5f221

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]
    (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t D cStar : ℕ) (hc : 4 * (D + 1) ≤ cStar) : LPprime (W := W) p n' ι σ w r lam0 t D 1 cStar :=
  ⟨hc, fun _ _ => ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
    fun i => i.elim0, 0, by simp, ⟨0, 0, fun _ i => i.elim0⟩⟩⟩
end Formalism.MainNotions.G.Inhab
