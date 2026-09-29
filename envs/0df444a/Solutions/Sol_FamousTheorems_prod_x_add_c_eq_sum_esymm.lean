-- Prove2me | solution 1 for FamousTheorems.prod_x_add_c_eq_sum_esymm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:53.276875+00:00
-- url     : https://prove2.me/submissions/7ec636fd-1751-48c3-ac1d-5283b97aaec3

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {R : Type u_1} [inst : CommSemiring R] (s : Multiset R), 
    (Multiset.map (fun r => Polynomial.X + Polynomial.C r) s).prod = 
    ∑ j ∈ Finset.range (s.card + 1), Polynomial.C (s.esymm j) * Polynomial.X ^ (s.card - j) :=
  @_root_.Multiset.prod_X_add_C_eq_sum_esymm
