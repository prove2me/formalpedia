-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.gl_action_preserves_space
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:28:52.945846+00:00
-- url     : https://prove2.me/submissions/c5e33a0f-2c06-4366-abf6-ddbc38cd7d62

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_LatDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Vanish
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKillsDegreeZero
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_castSucc_mem_erase
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_pol
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_glAct_le
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_free
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_xsp
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_typesLE_glStable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K s : ℕ}
variable (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (i j : Fin s) (o : ℕ) :
    ∀ x ∈ XSp p (setLast LL o) J M (Fin.last s),
      glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j) x ∈ XSp p (setLast LL o) J M (Fin.last s) := by
  intro x hx
  rw [mem_xsp] at hx ⊢
  obtain ⟨hxP, hxF, hxk⟩ := hx
  refine ⟨Formalism.CountingSumsFrames.glAct_pol (setLast LL o) (K + 1) _ _ x hxP,
    glAct_free LL (K + 1) _ _ (Fin.last K, Fin.last s) (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne x hxF,
    fun k => ⟨fun hk => ⟨?_, ?_⟩, fun hk => ?_⟩⟩
  · exact ycond_glAct_le (setLast LL o) (Nat.le_succ K) (M k) _ _ ((hxk k).1 hk).1
  · exact typesLE_glStable (setLast LL o) (K + 1) _ (M k) _ _ (castSucc_mem_erase i) (castSucc_mem_erase j) x
      ((hxk k).1 hk).2
  · exact ycond_glAct_le (setLast LL o) (by omega) (M k) _ _ ((hxk k).2 hk)
end Formalism.InvariantFactorPaths.L4
