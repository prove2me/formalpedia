-- Prove2me | solution 1 for BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:42:56.308452+00:00
-- url     : https://prove2.me/submissions/ab67c824-6ace-4150-ba9a-49cdc160068f

import Mathlib
import Definitions.Def_ChapterNavierStokesDeficiency
namespace BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat

@[simp] theorem defState_coe : ((defState : L2N) : ℕ → ℂ) = defFun := rfl

theorem defState_ne_zero : defState ≠ 0 := by
  intro h
  have h0 : ((defState : L2N) : ℕ → ℂ) 0 = 0 := by rw [h]; simp
  simp [defState_coe, defFun] at h0

theorem jacobiFun_defFun (n : ℕ) : jacobiFun defFun n = Complex.I * defFun n := by
  cases n with
  | zero =>
    simp only [jacobiFun, defFun, jacobiWeight, pow_one, pow_zero]
    push_cast
    ring
  | succ m =>
    simp only [jacobiFun, defFun, jacobiWeight, pow_succ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring

theorem defState_deficiency (v : lpFiniteModes ℕ) :
    (inner ℂ ((jacobiOp v : lpFiniteModes ℕ) : L2N) defState : ℂ)
      = inner ℂ ((v : lpFiniteModes ℕ) : L2N) (Complex.I • defState) := by
  obtain ⟨N, hN⟩ := exists_tail_zero v.2
  have hlhs := inner_eq_sum_range (f := ((jacobiOp v : lpFiniteModes ℕ) : L2N))
    (g := defState) (N := N + 1) (by simpa using jacobiFun_tail_zero hN)
  have hrhs := inner_eq_sum_range (f := ((v : lpFiniteModes ℕ) : L2N))
    (g := Complex.I • defState) (N := N + 1) (fun n hn => hN n (by omega))
  rw [hlhs, hrhs, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have hsmul : ∀ n, ((Complex.I • defState : L2N) : ℕ → ℂ) n = jacobiFun defFun n := by
    intro n
    rw [jacobiFun_defFun]
    simp
  simp only [jacobiOp_coe, defState_coe, hsmul]
  rw [jacobi_wronskian]
  rw [hN N le_rfl, hN (N + 1) (by omega)]
  simp

theorem jacobiOp_not_hasZeroDeficiencyOn :
    ¬ HasZeroDeficiencyOn (lpFiniteModes ℕ) jacobiOp := by
  intro hzero
  exact defState_ne_zero (hzero.1 defState fun v => defState_deficiency v)

end BookProof.NavierStokesFlow.JacobiDeficiency

namespace BookProof.FarisLavine
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.JacobiDeficiency

theorem not_farisLavine_criterion_of_relative_bound :
    ¬ (∀ (D' : Submodule ℂ L2N) (H' N' : D' →ₗ[ℂ] D') (a b : ℝ),
        Dense (D' : Set L2N) →
        (∀ x y : D', (inner ℂ (H' x : L2N) (y : L2N) : ℂ) = inner ℂ (x : L2N) (H' y : L2N)) →
        (∀ v : D', ‖(H' v : L2N)‖ ≤ a * ‖(N' v : L2N)‖) →
        (∀ v : D', ‖(inner ℂ (v : L2N) ((H' (N' v) : L2N) - (N' (H' v) : L2N)) : ℂ)‖
          ≤ b * ‖(inner ℂ (v : L2N) (N' v : L2N) : ℂ)‖) →
        HasZeroDeficiencyOn D' H') := by
  intro hcrit
  refine jacobiOp_not_hasZeroDeficiencyOn ?_
  refine hcrit (lpFiniteModes ℕ) jacobiOp jacobiOp 1 0 lpFiniteModes_dense jacobiOp_symmetric
    (fun v => by simp) (fun v => by simp)

end BookProof.FarisLavine

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.JacobiDeficiency

theorem solution :
    ¬ (∀ (D' : Submodule ℂ L2N) (H' N' : D' →ₗ[ℂ] D') (a b : ℝ),
        Dense (D' : Set L2N) →
        (∀ x y : D', (inner ℂ (H' x : L2N) (y : L2N) : ℂ) = inner ℂ (x : L2N) (H' y : L2N)) →
        (∀ v : D', ‖(H' v : L2N)‖ ≤ a * ‖(N' v : L2N)‖) →
        (∀ v : D', ‖(inner ℂ (v : L2N) ((H' (N' v) : L2N) - (N' (H' v) : L2N)) : ℂ)‖
          ≤ b * ‖(inner ℂ (v : L2N) (N' v : L2N) : ℂ)‖) →
        HasZeroDeficiencyOn D' H') := by
  exact BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound

#print axioms solution
