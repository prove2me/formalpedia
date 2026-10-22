-- Prove2me | solution 1 for BirkhoffGlobalSection.eh_left_convex_body_away_from_critical
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T17:18:53.598634+00:00
-- url     : https://prove2.me/submissions/9a505026-e33a-4354-8315-0034376cf577

import Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_local_subcritical
import Theorems.Thm_BirkhoffGlobalSection_eh_left_convex_body_low_energy_tail
import Mathlib.Topology.Order.Compact

open BirkhoffGlobalSection Filter Set
open scoped Topology

set_option autoImplicit false

/-- Compactness turns energy windows around each point of a compact energy set
into one mass radius. -/
private theorem uniform_mass_radius_on_compact
    (P : ℝ → ℝ → Prop) (K : Set ℝ) (hK : IsCompact K)
    (hloc : ∀ c₀ ∈ K, ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, |μ - 1 / 2| < ε → |c - c₀| < η → P μ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ c : ℝ, |μ - 1 / 2| < ε → c ∈ K → P μ c := by
  have hev : ∀ᶠ μ in 𝓝 (1 / 2 : ℝ), ∀ c ∈ K, P μ c := by
    apply hK.eventually_forall_of_forall_eventually
    intro c₀ hc₀
    obtain ⟨ε, η, hε, hη, hP⟩ := hloc c₀ hc₀
    have hmass : ∀ᶠ z : ℝ × ℝ in 𝓝 ((1 / 2 : ℝ), c₀), |z.1 - 1 / 2| < ε :=
      (isOpen_lt (continuous_fst.sub continuous_const).abs
        continuous_const).mem_nhds (by simpa using hε)
    have henergy : ∀ᶠ z : ℝ × ℝ in 𝓝 ((1 / 2 : ℝ), c₀), |z.2 - c₀| < η :=
      (isOpen_lt (continuous_snd.sub continuous_const).abs
        continuous_const).mem_nhds (by simpa using hη)
    filter_upwards [hmass, henergy] with z hm hc
    exact hP z.1 z.2 hm hc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨ε, hε, fun μ c hμ hc => hball (by simpa [Metric.mem_ball, Real.dist_eq] using hμ) c hc⟩

theorem solution (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε → 2 + η ≤ c → belowFirstCriticalValue μ c →
        ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
          (0 : Phase) ∈ interior B ∧
          ehLeftEnergyComponent μ c = frontier B ∧
          HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B) := by
  let P : ℝ → ℝ → Prop := fun μ c =>
    0 < μ → μ < 1 → belowFirstCriticalValue μ c →
      ∃ B : Set Phase, IsCompact B ∧ Convex ℝ B ∧
        (0 : Phase) ∈ interior B ∧
        ehLeftEnergyComponent μ c = frontier B ∧
        HasPositiveTangentialHessianOn (ehLeftHamiltonian μ c) (frontier B)
  obtain ⟨εtail, C, hεtail, htail⟩ := eh_left_convex_body_low_energy_tail
  have hloc : ∀ c₀ ∈ Icc (2 + η) C, ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
      ∀ μ c : ℝ, |μ - 1 / 2| < ε → |c - c₀| < r → P μ c := by
    intro c₀ hc₀
    obtain ⟨ε, r, hε, hr, h⟩ := eh_left_convex_body_local_subcritical c₀ (by linarith [hc₀.1])
    exact ⟨ε, r, hε, hr, fun μ c hμ hc h0 h1 hsub => h μ c h0 h1 hμ hc hsub⟩
  obtain ⟨εmid, hεmid, hmid⟩ :=
    uniform_mass_radius_on_compact P (Icc (2 + η) C) isCompact_Icc hloc
  refine ⟨min εtail εmid, lt_min hεtail hεmid, ?_⟩
  intro μ c hμ0 hμ1 hμ hc hsub
  by_cases hfar : C ≤ c
  · exact htail μ c hμ0 hμ1 (lt_of_lt_of_le hμ (min_le_left _ _)) hfar hsub
  · exact hmid μ c (lt_of_lt_of_le hμ (min_le_right _ _)) ⟨hc, (not_le.mp hfar).le⟩ hμ0 hμ1 hsub
