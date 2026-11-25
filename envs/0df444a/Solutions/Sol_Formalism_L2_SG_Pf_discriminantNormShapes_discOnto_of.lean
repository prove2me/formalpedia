-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.discOnto_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:16:10.142983+00:00
-- url     : https://prove2.me/submissions/d5ed664d-cee2-469d-b087-6a3c58a60157

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOnto
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapes
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_akCount_eq_skSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution (hU : UDModel) (hO : OrbitCount) : DiscOnto := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ _ hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk
  have ha : ∀ i, a i ≠ 0 := by
    obtain ⟨-, -, -, -, h5⟩ := hb
    exact h5
  rw [akCount_eq_skSet h𝔭 hb k, hO K F hK 𝔭 h𝔭 _ a ha k hk,
    hU K F V hK h hsymm hpos L hL hint 𝔭 h𝔭 b a hb k hk]
end Formalism.L2.SG.Pf.discriminantNormShapes
