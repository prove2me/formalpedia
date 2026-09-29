-- Prove2me | solution 1 for FamousTheorems.thales_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:53.462346+00:00
-- url     : https://prove2.me/submissions/56d07bc3-076d-41bf-9b90-7538e0730c1f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {V : Type u_1} {P : Type u_2} [inst : NormedAddCommGroup V] 
    [inst_1 : InnerProductSpace ℝ V] [inst_2 : MetricSpace P] [inst_3 : NormedAddTorsor V P] {p₁ p₂ p₃ : P} 
    {s : EuclideanGeometry.Sphere P}, s.IsDiameter p₁ p₃ → (EuclideanGeometry.angle p₁ p₂ p₃ = Real.pi / 2 ↔ p₂ ∈ s) :=
  @_root_.EuclideanGeometry.Sphere.thales_theorem
