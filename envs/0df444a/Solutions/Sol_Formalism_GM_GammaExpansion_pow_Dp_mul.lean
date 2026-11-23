-- Prove2me | solution 1 for Formalism.GM.GammaExpansion.pow_Dp_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:56.513002+00:00
-- url     : https://prove2.me/submissions/ebe96938-a810-42f4-9902-9fd9f6b72c67

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
import Theorems.Thm_Formalism_GM_GammaExpansion_Dp_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable {R σ : Type} [CommSemiring R]
namespace Formalism.GM.GammaExpansion
theorem _root_.solution (v : σ) (a b : MvPolynomial σ R) (m : ℕ) :
    (Dp v ^ m) (a * b) = ∑ i ∈ range (m + 1), m.choose i • ((Dp v ^ i) a * (Dp v ^ (m - i)) b) := by
  have hl : ∀ x y : MvPolynomial σ R, Dp v (x * y) = x * Dp v y + y * Dp v x := fun x y => by
    simp only [Dp_apply, Derivation.leibniz, smul_eq_mul]
  have hs : ∀ (j : ℕ) (x : MvPolynomial σ R), (Dp v ^ (j + 1)) x = Dp v ((Dp v ^ j) x) := by
    intro j x; rw [pow_succ'] <;> rfl
  have key : ∀ n, (Dp v ^ n) (a * b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • ((Dp v ^ ij.1) a * (Dp v ^ ij.2) b) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => (Dp v ^ i) a * (Dp v ^ j) b), hs, ih, map_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ij hij => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
      have hsym : n.choose ij.2 = n.choose ij.1 := by rw [← hij, Nat.choose_symm_add]
      beta_reduce
      rw [map_nsmul, hl, hs, hs, hsym]
      ring
  rw [key, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => m.choose i • ((Dp v ^ i) a * (Dp v ^ j) b))]
end Formalism.GM.GammaExpansion
