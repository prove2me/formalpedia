-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.ycond_snoc_bwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:57:13.574008+00:00
-- url     : https://prove2.me/submissions/4b841537-001b-46b5-ac60-f3a138c7c39a

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff_coeff__74c68bcb778a
import Theorems.Thm_P2M_Formalism_GM_FrozenVariableComponents_coeff__glAct_bf3d36ac81c2
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_snoc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_ycond_stable
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_wt_le_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (LL : Letters N) (n j : ℕ) (hj : j ≤ N) (M : WithTop ℤ)
    (F : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hF : ∀ b, coeffη b F ∈ YCond p LL j M) :
    F ∈ YCond p (LL.snoc n) j M := by
  have hmem : (⨅ b : Fin r →₀ ℕ, (Formalism.GM.M.YCond p LL j M).comap (coeffη b)) ∈
      {S | S ≤ MvPolynomial.restrictSupport ℚ_[p]
        {m : Fin (N + 1) × Fin r →₀ ℕ | ((Formalism.GM.M.wt (LL.snoc n) j 0 m : ℤ) : WithTop ℤ) ≤ M} ∧
        Formalism.GM.M.GlStable p (LL.snoc n) j S} := by
    refine ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      have hG' : coeffη (etaPart m) G ∈ Formalism.GM.M.YCond p LL j M :=
        (Submodule.mem_iInf _).1 hG (etaPart m)
      have hm' : llPart m ∈ (coeffη (etaPart m) G).support := by
        rw [mem_support_iff, coeff_coeffη]
        exact mem_support_iff.1 (Finset.mem_coe.1 hm)
      show ((Formalism.GM.M.wt (LL.snoc n) j 0 m : ℤ) : WithTop ℤ) ≤ M
      rw [wt_snoc LL n j hj]
      exact wt_le_of_mem p LL j M _ hG' _ hm'
    · intro c d G hG
      refine (Submodule.mem_iInf _).2 (fun b => ?_)
      rw [Submodule.mem_comap, coeffη_glAct p LL n j hj c d b G]
      exact ycond_stable p LL j M c d _ ((Submodule.mem_iInf _).1 hG b)
  have hle : (⨅ b : Fin r →₀ ℕ, (Formalism.GM.M.YCond p LL j M).comap (coeffη b)) ≤
      Formalism.GM.M.YCond p (LL.snoc n) j M := by
    unfold Formalism.GM.M.YCond
    exact le_sSup hmem
  exact hle ((Submodule.mem_iInf _).2 (fun b => hF b))
end Formalism.GM.FrozenVariableComponents
