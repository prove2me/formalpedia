-- Prove2me | solution 1 for BooleanFun.fourier_eq_zero_iff_fourier_weight_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:06:32.323269+00:00
-- url     : https://prove2.me/submissions/783fc698-7037-4993-93db-ef36cef50c15

import Definitions.Def_BooleanFun_Auxiliary
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.CharP.Pi
import Definitions.Def_BooleanFun_Basic
import Theorems.Thm_BooleanFun_walsh_plancherel
import Theorems.Thm_BooleanFun_rw_ite_left


set_option autoImplicit false
open BooleanFun
open Real BigOperators Function Finset Pi
open RealInnerProductSpace
noncomputable section
variable {α : Type*}
variable {n : ℕ} {f g : BooleanFunc n} {x y : Fin n → Fin 2} {i : Fin n}
variable {S S' : Finset (Fin n)} {v : Fin 2}
namespace BooleanFun
theorem _root_.solution {k : ℕ} {f : BooleanFunc n}:
    (∀ S, S.card ≠ k → 𝓕 f S = 0) ↔ fourierWeight k f = ‖f‖ ^ 2 := by
  constructor
  · intro h
    have h : ∀ S, S.card ≠ k → |𝓕 f S|^2 = 0 := by intro S hS; simp; exact h S hS
    symm
    rw [walsh_plancherel]
    calc
      _ = fourierWeight k f + ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2 := by
        rw [sum_filter_add_sum_filter_not]
      _ = fourierWeight k f + ∑ S, if S.card ≠ k then |𝓕 f S|^2 else 0 := by
        rw [sum_filter]
      _ = fourierWeight k f := by
        conv => {enter [1, 2, 2, S]; rw [rw_ite_left (h S), ite_self]}; simp
  · intro h S hS
    have : ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2 = 0 := by
      symm
      calc
        0 = ‖f‖^2 - ‖f‖^2                           := (sub_self _).symm
        _ = ∑ S, |𝓕 f S|^2 - fourierWeight k f      := by rw [h, walsh_plancherel]
        _ = ∑ S ∈ {S | S.card = k}, |𝓕 f S|^2 + ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2
          - fourierWeight k f                       := by rw [sum_filter_add_sum_filter_not]
        _ = ∑ S ∈ {S | S.card ≠ k}, |𝓕 f S|^2       := by rw [add_comm, add_sub_assoc, sub_self, add_zero]
    have := (sum_eq_zero_iff_of_nonneg <| by intro S _; apply pow_two_nonneg).mp this
    specialize this S (by simp [hS])
    rw [sq_abs, pow_eq_zero_iff (by trivial)] at this
    assumption
end BooleanFun
