-- Prove2me | solution 1 for CubicTurning.balanced_central_mass
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:27:55.573364+00:00
-- url     : https://prove2.me/submissions/585b2a28-0736-4ce4-9382-c5f24d140942

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning
































theorem chain_endpoint_membership (a b c : ℂ) (z : Fin 3 → ℂ)
    (hz : DerivativeChainPrivate.IsChain ![a,b,c] z) : z 2=a ∨ z 2=b ∨ z 2=c := by
  have h:=hz 2
  simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ] at h
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using h
































end CubicTurning

open CubicTurning in
theorem solution {n : ℕ} (t : ℝ) (ht : 0<t)
    (L : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)) :
    (∑ i, if L.paths i 2=sharpCentral t then L.weights i else 0)=1/3 := by
  have hb : sharpOuterPlus t≠sharpCentral t := by
    intro h
    have hh:=congrArg Complex.im h
    simp [sharpCentral,sharpOuterPlus] at hh
    linarith
  have hc : sharpOuterMinus t≠sharpCentral t := by
    intro h
    have hh:=congrArg Complex.im h
    simp [sharpCentral,sharpOuterMinus] at hh
    linarith
  have him (i : Fin n) : (L.paths i 2).im=
      if L.paths i 2=sharpCentral t then t else -t/2 := by
    obtain ha|ha|ha := chain_endpoint_membership _ _ _ (L.paths i) (L.actual i)
    · rw [ha]; simp [sharpCentral]
    · rw [ha,if_neg hb]; rfl
    · rw [ha,if_neg hc]; rfl
  have hsum : ∑ i,L.weights i*(L.paths i 2).im=0 := by
    simpa [Complex.mul_im] using congrArg Complex.im L.balanced
  have hi (i : Fin n) : L.weights i*(L.paths i 2).im=
      (3*t/2)*(if L.paths i 2=sharpCentral t then L.weights i else 0)-(t/2)*L.weights i := by
    rw [him]
    split_ifs <;> ring
  have he := Finset.sum_congr (s₁:=Finset.univ) (s₂:=Finset.univ) rfl (fun i _ => hi i)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.mul_sum,L.total] at he
  rw [hsum] at he
  apply (mul_left_cancel₀ (show 3*t/2≠0 by positivity))
  nlinarith [he]
