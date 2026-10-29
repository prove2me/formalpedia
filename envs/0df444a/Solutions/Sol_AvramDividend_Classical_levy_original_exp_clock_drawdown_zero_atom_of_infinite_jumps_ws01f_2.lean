-- Prove2me | solution 2 for AvramDividend.Classical.levy_original_exp_clock_drawdown_zero_atom_of_infinite_jumps_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:42:47.311161+00:00
-- url     : https://prove2.me/submissions/19103555-3fb3-4ec9-82e7-dc70c0385479

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f

open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (q φ p lam m : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hp : 0 < p) (hlam : 0 < lam)
    (hlamroot : X.ψ (φ + lam) - q = p)
    (hm : 0 < m) (hmderiv : HasDerivAt X.ψ m (φ + lam))
    (hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ φ)))) :
    (P.prod (expMeasure p))
      {z : Ω × ℝ | runningSup X z.2.toNNReal z.1 -
        X.X z.2.toNNReal z.1 = 0} = 0 := by
  have h := levy_tilted_clock_drawdown_zero_atom_of_infinite_jumps_ws01f X hjump q φ p lam m
    hq hφ hroot hp hlam hlamroot hm hmderiv hJoint
  rw [withDensity_apply_eq_zero hJoint] at h
  have he : {z : Ω × ℝ | ENNReal.ofReal (Real.exp (φ * X.X (Real.toNNReal z.2) z.1 -
      (Real.toNNReal z.2 : ℝ) * X.ψ φ)) ≠ 0} = Set.univ := by
    ext z; simp [Real.exp_pos]
  rw [he, Set.univ_inter] at h
  exact h
