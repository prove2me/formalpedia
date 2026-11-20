-- Prove2me | solution 1 for BooleanFun.noise_stability_eq_sum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:10:14.911464+00:00
-- url     : https://prove2.me/submissions/e150218d-f0c1-40b9-bfee-2c469e5cb133

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_walsh_inner_eq
import Theorems.Thm_BooleanFun_walsh_fourier

set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {ρ : ℝ} : noise_stability ρ f = ∑ S, ρ^(S.card) * |𝓕 f S|^2 := by
  unfold noise_stability
  nth_rewrite 1 [walsh_fourier f]
  simp only [noise_operator, multiplier, LinearMap.coe_mk, AddHom.coe_mk]
  rewrite [sum_inner]
  conv => enter [1, 2, S]; rw [inner_smul_left, inner_sum];
          enter [2, 2, S']; rw [inner_smul_right, inner_smul_right, walsh_inner_eq]
  congr! 1; simp; ring
end BooleanFun
