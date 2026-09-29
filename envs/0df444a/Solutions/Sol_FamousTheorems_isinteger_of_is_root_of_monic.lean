-- Prove2me | solution 1 for FamousTheorems.isinteger_of_is_root_of_monic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:54.321078+00:00
-- url     : https://prove2.me/submissions/ae75d4c9-88fd-4f60-b02a-c2a70849959f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {A : Type u_1} {K : Type u_2} [inst : CommRing A] [IsDomain A] 
    [UniqueFactorizationMonoid A] [inst_3 : Field K] [inst_4 : Algebra A K] [IsFractionRing A K] {p : Polynomial A}, 
    p.Monic → ∀ {r : K}, (Polynomial.aeval r) p = 0 → IsLocalization.IsInteger A r :=
  @_root_.isInteger_of_is_root_of_monic
