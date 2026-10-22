-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_no_short_subcritical_orbits
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T21:09:59.303863+00:00
-- url     : https://prove2.me/submissions/b1149d29-c24c-4889-b690-3cd70cf3342f

import Theorems.Thm_BirkhoffGlobalSection_saddle_center_no_short_return
import Theorems.Thm_BirkhoffGlobalSection_periodic_hamiltonian_solution_shift

open BirkhoffGlobalSection

theorem solution
    (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U)
    (L : ℝ) (hL : 0 < L) :
    ∃ V : Set Phase, IsOpen V ∧ V ⊆ U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ V ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ V) →
            L < T := by
  obtain ⟨V, hVo, hVU, hVp, hVm, ε, η, hε, hη, hnoret⟩ :=
    saddle_center_no_short_return U hU hplus hminus L hL
  refine ⟨V, hVo, hVU, hVp, hVm, ε, η, hε, hη, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub x T hx hvisit
  obtain ⟨t₀, ht₀⟩ := hvisit
  have hshift := periodic_hamiltonian_solution_shift μ c x T
    hx.2.1 hx.2.2.1 hx.2.2.2
  by_contra hcon
  rw [not_lt] at hcon
  exact hnoret μ c hμ0 hμ1 hμ hc hsub x T hx ⟨t₀, ht₀⟩
    t₀ ht₀ T hx.1 hcon (hshift t₀)
