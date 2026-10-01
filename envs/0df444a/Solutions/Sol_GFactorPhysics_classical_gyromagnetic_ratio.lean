-- Prove2me | solution 1 for GFactorPhysics.classical_gyromagnetic_ratio
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-23T21:20:31.798712+00:00
-- url     : https://prove2.me/submissions/85f22095-3ae2-4708-97d8-6f877b4658b1

import Definitions.Def_GFactorPhysics_Defs

set_option autoImplicit false

open GFactorPhysics

theorem solution {n : ℕ} (q m : Fin n → ℝ) (r v : Fin n → Fin 3 → ℝ)
    (hm : ∀ i, 0 < m i) (κ : ℝ) (hq : ∀ i, q i = κ * m i) :
    classicalMagneticMoment q r v =
      diracMagneticMoment 1 (∑ i, q i) (∑ i, m i) (classicalAngularMomentum m r v) := by
  classical
  by_cases vazio : n = 0
  · subst n
    simp [classicalMagneticMoment, classicalAngularMomentum, diracMagneticMoment]
  have hn : 0 < n := Nat.pos_of_ne_zero vazio
  have massa : 0 < ∑ i, m i := by
    apply Finset.sum_pos
    · intro i _
      exact hm i
    · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have carga : ∑ i, q i = κ * ∑ i, m i := by
    simp_rw [hq]
    exact (Finset.mul_sum ..).symm
  have razao : (1 : ℝ) * (∑ i, q i) / (2 * ∑ i, m i) = κ / 2 := by
    rw [carga]
    field_simp [ne_of_gt massa]
  unfold classicalMagneticMoment diracMagneticMoment classicalAngularMomentum
  rw [razao, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [smul_smul, hq]
  congr 1
  ring
