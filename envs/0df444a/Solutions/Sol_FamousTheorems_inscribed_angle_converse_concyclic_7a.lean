-- Prove2me | solution 1 for FamousTheorems.inscribed_angle_converse_concyclic_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:08:00.121162+00:00
-- url     : https://prove2.me/submissions/bc1ba7c0-ded8-48db-b78b-a2e7c9be7f40

import Mathlib

open EuclideanGeometry

theorem solution {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)] {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) :=
  cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn
