-- Prove2me | solution 1 for BooleanFun.totalInfluence_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:35.043149+00:00
-- url     : https://prove2.me/submissions/d3fed999-13f3-4353-bf45-adbc7d285efc

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_influence_eq_sum_fourier

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (f : BooleanFunc n) : totalInfluence f = ∑ S, S.card * (𝓕 f S) ^ 2 := by
  unfold totalInfluence
  conv =>
    enter [1, 2, i]
    rw [influence_eq_sum_fourier f i, sum_filter]
  rw [sum_comm]
  simp
end BooleanFun
