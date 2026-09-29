-- Prove2me | solution 1 for FamousTheorems.exists_eq_forall_mem_icc_hasderivwithinat
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:00.655643+00:00
-- url     : https://prove2.me/submissions/b447b0ce-8570-4062-96d1-9858301ea51e

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E → E} {tmin tmax : ℝ} {t₀ : ↑(Icc tmin tmax)} {x₀ x : E} 
    {a r L K : NNReal}, 
    IsPicardLindelof f t₀ x₀ a r L K → 
    x ∈ Metric.closedBall x₀ ↑r → ∃ α, α ↑t₀ = x ∧ ∀ t ∈ Icc tmin tmax, HasDerivWithinAt α (f t (α t)) (Icc tmin tmax) t :=
  @_root_.IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt
