-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_of_re_conj_mul_pos
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T10:07:47.401747+00:00
-- url     : https://prove2.me/submissions/3cf5cc9f-9801-4857-aa55-c67a2d5e4d27

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_zero_of_forall_ne_ray



namespace FiniteEnergyPlane

theorem hasLoopWind_of_re_conj_mul_pos_aux {f g : ℝ → ℂ} {k : ℤ} (hg : HasLoopWind g k)
    (hf : Continuous f) (hper : Function.Periodic f 1)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (g t) * f t).re) : HasLoopWind f k := by
  obtain ⟨hgc, hgp, hg0, -⟩ := id hg
  set q : ℝ → ℂ := fun t => f t / g t with hq
  have hqc : Continuous q := hf.div hgc hg0
  have hqp : Function.Periodic q 1 := fun t => by simp only [hq, hper t, hgp t]
  have hqre : ∀ t, 0 < (q t).re := by
    intro t
    have hgt := hg0 t
    have hc : starRingEnd ℂ (g t) ≠ 0 := by simpa using hgt
    have : q t = (starRingEnd ℂ (g t) * f t) / ((Complex.normSq (g t) : ℝ) : ℂ) := by
      simp only [hq]
      rw [Complex.normSq_eq_conj_mul_self]
      field_simp
    rw [this, Complex.div_ofReal_re]
    exact div_pos (hpos t) (Complex.normSq_pos.2 hgt)
  have hq0 : HasLoopWind q 0 := by
    refine hasLoopWind_zero_of_forall_ne_ray q hqc hqp (-1) (by norm_num) fun t s hs h => ?_
    have := hqre t
    rw [h] at this
    simp at this
    linarith
  have hm := hasLoopWind_mul hg hq0
  rw [add_zero] at hm
  have hfe : (fun t => g t * q t) = f := by
    funext t; simp only [hq]; field_simp [hg0 t]
  rwa [hfe] at hm

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {f g : ℝ → ℂ} {k : ℤ} (hg : HasLoopWind g k)
    (hf : Continuous f) (hper : Function.Periodic f 1)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (g t) * f t).re) : HasLoopWind f k :=
  FiniteEnergyPlane.hasLoopWind_of_re_conj_mul_pos_aux hg hf hper hpos
