-- Prove2me | solution 1 for FamousTheorems.isbigo_asympbound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:31.566727+00:00
-- url     : https://prove2.me/submissions/692f30ad-3c81-4711-8a40-e83e2a3e710b

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {α : Type u_1} [inst : Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} 
    {r : α → ℕ → ℕ} [inst_1 : Nonempty α] (R : AkraBazziRecurrence T g a b r), 
    T =O[atTop] AkraBazziRecurrence.asympBound g a b :=
  @_root_.AkraBazziRecurrence.isBigO_asympBound
