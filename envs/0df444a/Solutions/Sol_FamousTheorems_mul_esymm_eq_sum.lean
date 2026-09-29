-- Prove2me | solution 1 for FamousTheorems.mul_esymm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:38.115715+00:00
-- url     : https://prove2.me/submissions/20bc0440-fafa-4372-bd36-250c13dd477b

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ (σ : Type u_1) [inst : Fintype σ] (R : Type u_2) [inst_1 : CommRing R] (k : ℕ), 
    ↑k * MvPolynomial.esymm σ R k = 
    (-1) ^ (k + 1) * 
    ∑ a ∈ Finset.HasAntidiagonal.antidiagonal k with a.1 < k, 
    (-1) ^ a.1 * MvPolynomial.esymm σ R a.1 * MvPolynomial.psum σ R a.2 :=
  @_root_.MvPolynomial.mul_esymm_eq_sum
