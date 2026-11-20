-- Prove2me | solution 1 for BooleanFun.eq_sum_fourier_of_fourier_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:09:37.656017+00:00
-- url     : https://prove2.me/submissions/c727319b-42c0-4505-b309-07fd2a56c598

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_walsh_fourier
import Theorems.Thm_BooleanFun_fourier_eq_zero_iff_fourier_weight_eq

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {k : ℕ} {f : BooleanFunc n} (h : fourierWeight k f = ‖f‖ ^ 2):
    f = ∑ S ∈ {S|S.card = k}, 𝓕 f S • χ S := by
  have hf : ∑ S ∈ {S | S.card ≠ k}, 𝓕 f S • χ S = 0 := by
    rw [sum_eq_zero]
    intro S hS
    rw [smul_eq_zero]
    left
    simp at hS
    exact fourier_eq_zero_iff_fourier_weight_eq.mpr h S hS
  calc
    f = ∑ S, 𝓕 f S•χ S                     := walsh_fourier f
    _ = ∑ S ∈ {S | S.card = k}, 𝓕 f S•χ S +
      ∑ S ∈ {S | S.card ≠ k}, 𝓕 f S•χ S     := by rw [sum_filter_add_sum_filter_not]
    _ = ∑ S ∈ {S | S.card = k}, 𝓕 f S•χ S    := by rw [hf, add_zero]
end BooleanFun
