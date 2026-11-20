-- Prove2me | solution 1 for BooleanFun.covariance_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:09:15.982478+00:00
-- url     : https://prove2.me/submissions/be821bf0-78e3-4b07-9c3d-eda4fd8d1af6

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_expectation_eq_fourier
import Theorems.Thm_BooleanFun_inner_eq_expectation
import Theorems.Thm_BooleanFun_inner_eq_sum_fourier

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution (f g : BooleanFunc n) : covariance f g = ∑ S ∈ {S : Finset (Fin n) | S.Nonempty}, 𝓕 f S * 𝓕 g S := by
  unfold covariance
  rw [← inner_eq_expectation, inner_eq_sum_fourier]
  simp [Finset.nonempty_iff_ne_empty, Finset.filter_ne', expectation_eq_fourier]
end BooleanFun
