-- Prove2me | solution 1 for BooleanFun.multiplier_walsh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:09:52.630974+00:00
-- url     : https://prove2.me/submissions/5ab64745-1905-4fff-987b-bc6ff65d6472

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_fourier_walsh

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {m : ℕ → ℝ} {S : Finset (Fin n)} : multiplier m (χ S) = (m S.card)•χ S := by
  unfold multiplier
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  conv => enter [1, 2, S']; rw [fourier_walsh]
  simp
end BooleanFun
