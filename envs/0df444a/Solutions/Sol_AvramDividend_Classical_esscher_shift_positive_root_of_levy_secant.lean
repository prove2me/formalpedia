-- Prove2me | solution 1 for AvramDividend.Classical.esscher_shift_positive_root_of_levy_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:51:53.346722+00:00
-- url     : https://prove2.me/submissions/46ea352c-bddf-4990-aaf7-85cb417651a4

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_shifted_increment_lower
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Source-specific shifted Lévy roots without an additional standing assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi p : ℝ)
    (hq : 0 < q) (hphi : 0 < phi) (hroot : X.ψ phi = q)
    (hp : 0 < p) :
    ∃ lambda : ℝ, 0 < lambda ∧ X.ψ (phi + lambda) - q = p := by
  let theta : ℝ := (p + 1) * phi / q
  have hp1 : 0 < p + 1 := by linarith
  have htheta : 0 < theta := by
    dsimp [theta]
    exact div_pos (mul_pos hp1 hphi) hq
  have hsec := levy_psi_root_shifted_increment_lower
    X q phi theta hq hphi htheta hroot
  have hfactor : (q / phi) * theta = p + 1 := by
    dsimp [theta]
    field_simp [ne_of_gt hphi, ne_of_gt hq]
    <;> ring
  have hhigh : p + q ≤ X.ψ (phi + theta) := by
    rw [hfactor] at hsec
    linarith
  have hphiB : phi ≤ phi + theta := by linarith
  have hsubset : Icc phi (phi + theta) ⊆ Ici (0 : ℝ) := by
    intro t ht
    exact le_trans hphi.le ht.1
  have hcont : ContinuousOn X.ψ (Icc phi (phi + theta)) :=
    (levy_laplace_exponent_continuousOn_nonnegative X).mono hsubset
  have hval : p + q ∈ Icc (X.ψ phi) (X.ψ (phi + theta)) := by
    change X.ψ phi ≤ p + q ∧ p + q ≤ X.ψ (phi + theta)
    constructor
    · rw [hroot]
      linarith
    · exact hhigh
  obtain ⟨u, hu, heq⟩ := (intermediate_value_Icc hphiB hcont) hval
  have hgt : phi < u := by
    by_contra hn
    have hu_eq : u = phi := le_antisymm (le_of_not_gt hn) hu.1
    rw [hu_eq, hroot] at heq
    linarith
  refine ⟨u - phi, by linarith, ?_⟩
  have hadd : phi + (u - phi) = u := by ring
  rw [hadd, heq]
  ring
