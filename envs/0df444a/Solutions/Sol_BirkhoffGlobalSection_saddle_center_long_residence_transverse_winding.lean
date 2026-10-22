-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_long_residence_transverse_winding
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T03:06:06.078584+00:00
-- url     : https://prove2.me/submissions/cdb26e9c-5322-431d-b9f3-e5915c37f1f3

import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_ambient_rotation_bounded_loss
import Theorems.Thm_BirkhoffGlobalSection_saddle_center_local_ambient_rotation_growth
import Theorems.Thm_BirkhoffGlobalSection_periodic_ambient_rotation_transverse_comparison
import Theorems.Thm_BirkhoffGlobalSection_left_energy_component_geometry
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian
open scoped ContDiff

private theorem vertical_secondDerivative_pos (μ c : ℝ) (s : Phase) (hs : s ∈ U)
    (v : Phase) (hv : v ≠ 0) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    0 < fderiv ℝ (fun x => fderiv ℝ (leviCivitaHamiltonian μ c) x v) s v := by
  rw [(leviCivita_explicit_derivatives μ c).2.1 s hs v v]
  have hsum : (∑ k, ∑ l, v k * v l * kHess μ c s k l) = v 2 ^ 2 + v 3 ^ 2 := by
    simp [Fin.sum_univ_four, hv0, hv1, kHess, kHessR, hP, hZ, dZ, dD, hD,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      pow_two]
  rw [hsum]
  have hn : v 2 ≠ 0 ∨ v 3 ≠ 0 := by
    by_contra h
    simp only [not_or, not_not] at h
    apply hv
    ext i
    fin_cases i <;> simp [hv0, hv1, h.1, h.2]
  rcases hn with h2 | h3
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h2) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h3)


theorem solution :
    ∃ U : Set Phase, IsOpen U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ U ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ U ∧
      ∃ ε η L : ℝ, 0 < ε ∧ 0 < η ∧ 0 < L ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            L < T →
            (∃ a : ℝ, ∀ t ∈ Set.Icc a (a + L), x t ∈ U) →
            HasTransverseWindingAboveOne (leviCivitaHamiltonian μ c) x T := by
  obtain ⟨C, _, hloss⟩ := hamiltonian_ambient_rotation_bounded_loss
  obtain ⟨U, hU, hp, hm, ε, η, L, hε, hη, hL, hgrowth⟩ :=
    saddle_center_local_ambient_rotation_growth (C + 6 * Real.pi)
  refine ⟨U, hU, hp, hm, ε, η, L, hε, hη, hL, ?_⟩
  intro μ c hμ0 hμ1 hμε hcη hsub x T hx hLT hsegment
  have hregular : ∀ t : ℝ,
      ContDiffAt ℝ ∞ (leviCivitaHamiltonian μ c) (x t) ∧
      fderiv ℝ (leviCivitaHamiltonian μ c) (x t) ≠ 0 := by
    intro t
    exact (left_energy_component_geometry μ c hμ0 hμ1 hsub).2.1 (x t) (hx.2.1 t)
  have hvertical : ∀ (t : ℝ) (v : Phase), v ≠ 0 → v 0 = 0 → v 1 = 0 →
      0 < fderiv ℝ (fun s => fderiv ℝ (leviCivitaHamiltonian μ c) s v) (x t) v := by
    intro t v hv hv0 hv1
    have hs : x t ∈ regularEnergyLocus μ c :=
      connectedComponentIn_subset _ _ (hx.2.1 t)
    exact vertical_secondDerivative_pos μ c (x t) hs.2 v hv hv0 hv1
  intro Y hY0 hYode v hv htrans θ hθ hpolar
  have hY : IsHamiltonianVariationalSolution (leviCivitaHamiltonian μ c) x Y :=
    ⟨hY0, hYode⟩
  obtain ⟨α, hα, hcompare⟩ := periodic_ambient_rotation_transverse_comparison
    (leviCivitaHamiltonian μ c) (leftEnergyComponent μ c) x T hx hregular Y hY
  obtain ⟨a, ha⟩ := hsegment
  have hlocal := hgrowth μ c hμ0 hμ1 hμε hcη hsub x hx.2.1 hx.2.2.1 Y hY α hα a ha
  have hrest := hloss (leviCivitaHamiltonian μ c) x (fun t => (hregular t).1)
    hx.2.2.1 hvertical Y hY α hα (a + L) (a + T) (by linarith)
  have hperiod := hcompare v hv htrans θ hθ hpolar a
  linarith
