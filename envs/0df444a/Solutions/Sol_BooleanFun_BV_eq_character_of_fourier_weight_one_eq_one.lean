-- Prove2me | solution 1 for BooleanFun.BV.eq_character_of_fourier_weight_one_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:13:31.774625+00:00
-- url     : https://prove2.me/submissions/5072815c-de62-4e3e-83ca-2a2356a9f913

import Definitions.Def_BooleanFun_Basic
import Definitions.Def_BooleanFun_BooleanValued
import Theorems.Thm_P2M_BooleanFun_BV_eq_character_of_fourier_weight_one_eq_one__544717a48388

set_option autoImplicit false
noncomputable section
open BooleanFun
open BooleanFun Finset Function Fin RealInnerProductSpace
variable {n : ℕ} {f g : BooleanFunc n} {x : Fin n → Fin 2}
open BooleanFun.BV
namespace BooleanFun.BV
theorem _root_.solution (hbv : BooleanValued f) (hn : n>0)
    (hf : fourierWeight 1 f = 1):
    ∃ i, ∃ c : ℝ, f = c•χ {i} := by
  obtain ⟨S, hS, hS'⟩ := eq_character_of_fourier_weight_one_eq_one' hbv hn hf
  obtain ⟨i, hi⟩ := card_eq_one.mp hS
  use i
  rwa [hi] at hS'
end BooleanFun.BV
