-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.ycond_snoc_fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:14.509304+00:00
-- url     : https://prove2.me/submissions/1d567aaa-922b-4553-980b-867e9abbf840

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff___2f0e7d943746
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_snoc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (M : WithTop ℤ) (b : Fin r →₀ ℕ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hF : F ∈ YCond p (LL.snoc n) j M) :
    coeffη b F ∈ YCond p LL j M := by
  refine ycond_map p (LL.snoc n) LL j j M (coeffη b)
    (fun c d G => coeffη_glAct p LL n j hj c d b G) (fun G m hm => ?_) F hF
  refine ⟨comb b m, ?_, ?_⟩
  · rw [mem_support_iff, ← coeff_coeffη']
    exact mem_support_iff.1 hm
  · rw [wt_snoc LL n j hj, llPart_comb]
end Formalism.GM.FrozenVariableComponents
