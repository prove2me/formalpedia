-- Prove2me | solution 1 for FamousTheorems.hensels_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:50.417565+00:00
-- url     : https://prove2.me/submissions/6665625d-3823-4485-90ea-4746c32fadce

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {R : Type u_1} [inst_1 : CommSemiring R] 
    [inst_2 : Algebra R ℤ_[p]] {F : Polynomial R} {a : ℤ_[p]}, 
    ‖(Polynomial.aeval a) F‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ^ 2 → 
    ∃ z, 
    (Polynomial.aeval z) F = 0 ∧ 
    ‖z - a‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ∧ 
    ‖(Polynomial.aeval z) (Polynomial.derivative F)‖ = ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ ∧ 
    ∀ (z' : ℤ_[p]), 
    (Polynomial.aeval z') F = 0 → ‖z' - a‖ < ‖(Polynomial.aeval a) (Polynomial.derivative F)‖ → z' = z :=
  @_root_.hensels_lemma
