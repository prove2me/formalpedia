-- Prove2me | solution 1 for FamousTheorems.num_dvd_of_is_root
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:20.94939+00:00
-- url     : https://prove2.me/submissions/99b87da6-0e47-4bda-a005-270c5d5a1b78

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {A : Type u_1} {K : Type u_2} [inst : CommRing A] [inst_1 : IsDomain A] 
    [inst_2 : UniqueFactorizationMonoid A] [inst_3 : Field K] [inst_4 : Algebra A K] [inst_5 : IsFractionRing A K] 
    {p : Polynomial A} {r : K}, (Polynomial.aeval r) p = 0 → IsFractionRing.num A r ∣ p.coeff 0 :=
  @_root_.num_dvd_of_is_root
