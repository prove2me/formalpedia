-- Prove2me | solution 1 for DerivativeChainExtremal.actual_circle_zero_critical_iff_centroid
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:51:56.418545+00:00
-- url     : https://prove2.me/submissions/d4c27239-6c8e-4981-af60-3be664742b51

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
set_option autoImplicit false
namespace DerivativeChainExtremal
open Polynomial DerivativeChainContinuation
theorem actual_circle_zero_derivative (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (hunit : ∀ z∈p.roots, ‖z‖=1) :
    p.derivative.eval 0 = p.eval 0*(-starRingEnd ℂ p.roots.sum) := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  have hp0 : p.eval 0 ≠ 0 := by
    intro he
    have hh := hunit 0 ((mem_roots hpne).mpr he)
    norm_num at hh
  rw [(IsAlgClosed.splits p).eval_derivative_eq_eval_mul_sum hp0]
  congr 1
  have he : p.roots.map (fun z : ℂ => 1/(0-z)) =
      p.roots.map (fun z : ℂ => -starRingEnd ℂ z) := by
    apply Multiset.map_congr rfl
    intro z hz
    simp [Complex.inv_def,Complex.normSq_eq_norm_sq,hunit z hz]
  rw [he]
  have hs (s : Multiset ℂ) :
      (s.map (fun z : ℂ => -starRingEnd ℂ z)).sum = -starRingEnd ℂ s.sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih => simp [ih,map_add,add_comm]
  exact hs p.roots
end DerivativeChainExtremal
open Polynomial DerivativeChainContinuation DerivativeChainExtremal in
theorem solution (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (hunit : ∀ z∈p.roots, ‖z‖=1) :
    p.derivative.eval 0=0 ↔ rootCentroid p=0 := by
  have hpne : p ≠ 0 := by intro h; simp [h] at hp
  have hp0 : p.eval 0 ≠ 0 := by
    intro he
    have hh := hunit 0 ((mem_roots hpne).mpr he)
    norm_num at hh
  have hn : (p.natDegree:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [actual_circle_zero_derivative p hp hunit,rootCentroid]
  simp [hp0,hn]
