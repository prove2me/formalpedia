-- Prove2me | solution 1 for FamousTheorems.exists_hasderivwithinat_eq_of_gt_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:39.900844+00:00
-- url     : https://prove2.me/submissions/60c71621-2622-4226-a918-1a024c82f6bf

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {a b : ℝ} {f f' : ℝ → ℝ}, 
    a ≤ b → (∀ x ∈ Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) → ∀ {m : ℝ}, f' a < m → m < f' b → m ∈ f' '' Ioo a b :=
  @_root_.exists_hasDerivWithinAt_eq_of_gt_of_lt
