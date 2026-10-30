-- Prove2me | solution 1 for DerivativeChainContinuation.last_derivative_unique_nearest
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:39:51.611227+00:00
-- url     : https://prove2.me/submissions/0171e16f-20c6-41d3-be26-5d37dbe5a595

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_last_derivative_strict_midpoint
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators


theorem solution (n : ℕ) (a : Fin (n+3) → ℝ)
    (b : Fin (n+2) → ℝ) (ha : Monotone a) (hb : Monotone b)
    (hinter : ∀ i : Fin (n+2), a i.castSucc ≤ b i ∧ b i ≤ a i.succ)
    (hder : (realRootProduct a).derivative = C (n+3 : ℝ)*realRootProduct b)
    (i : Fin (n+3)) (hi : a i ≠ a (Fin.last (n+2))) :
    |a (Fin.last (n+2))-b (Fin.last (n+1))| <
      |a i-b (Fin.last (n+1))| := by
  have hyB : b (Fin.last (n+1)) ≤ a (Fin.last (n+2)) := by
    simpa using (hinter (Fin.last (n+1))).2
  have hyA := (hinter (Fin.last (n+1))).1
  have hi' : i < Fin.last (n+2) := lt_of_le_of_ne (Fin.le_last _) (by
    intro hh; exact hi (congrArg a hh))
  have hiA : a i ≤ a (Fin.last (n+1)).castSucc := ha (by
    change i.val ≤ n+1
    have h : i.val < n+2 := hi'
    omega)
  by_cases hg : a (Fin.last (n+1)).castSucc < a (Fin.last (n+2))
  · have hm := last_derivative_strict_midpoint n a b ha hb hinter hder hg
    have hiy : a i < b (Fin.last (n+1)) := by linarith
    rw [abs_of_nonneg (sub_nonneg.mpr hyB),abs_of_neg (sub_neg.mpr hiy)]
    linarith
  · have he : a (Fin.last (n+1)).castSucc = a (Fin.last (n+2)) :=
      le_antisymm (ha (Fin.le_last _)) (le_of_not_gt hg)
    have hy : b (Fin.last (n+1))=a (Fin.last (n+2)) := by linarith
    rw [hy,sub_self,abs_zero]
    exact abs_pos.mpr (sub_ne_zero.mpr hi)
