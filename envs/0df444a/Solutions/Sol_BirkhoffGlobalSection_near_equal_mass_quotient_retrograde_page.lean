-- Prove2me | solution 1 for BirkhoffGlobalSection.near_equal_mass_quotient_retrograde_page
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T21:07:18.807482+00:00
-- url     : https://prove2.me/submissions/1d23e264-ceb8-4386-902d-cd147c2b97ce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_near_critical
import Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_local_subcritical
import Theorems.Thm_BirkhoffGlobalSection_quotient_retrograde_page_low_energy_tail
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

open BirkhoffGlobalSection Filter Set
open scoped Topology

set_option autoImplicit false

/-- Compactness makes a locally valid two-parameter statement uniform in
the first parameter while the second parameter ranges over a compact set. -/
private theorem uniform_on_compact_energy_set
    (P : ℝ → ℝ → Prop) (a : ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hloc : ∀ c₀ ∈ K, ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ μ c : ℝ, |μ - a| < ε → |c - c₀| < η → P μ c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ c : ℝ, |μ - a| < ε → c ∈ K → P μ c := by
  have hev : ∀ᶠ μ in 𝓝 a, ∀ c ∈ K, P μ c := by
    apply hK.eventually_forall_of_forall_eventually
    intro c₀ hc₀
    obtain ⟨ε, η, hε, hη, hP⟩ := hloc c₀ hc₀
    have hmass : ∀ᶠ z : ℝ × ℝ in 𝓝 (a, c₀), |z.1 - a| < ε :=
      (isOpen_lt (continuous_fst.sub continuous_const).abs
        continuous_const).mem_nhds (by simpa using hε)
    have henergy : ∀ᶠ z : ℝ × ℝ in 𝓝 (a, c₀), |z.2 - c₀| < η :=
      (isOpen_lt (continuous_snd.sub continuous_const).abs
        continuous_const).mem_nhds (by simpa using hη)
    filter_upwards [hmass, henergy] with z hm hc
    exact hP z.1 z.2 hm hc
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨ε, hε, ?_⟩
  intro μ c hμ hc
  exact hball (by simpa [Metric.mem_ball, Real.dist_eq] using hμ) c hc

theorem solution :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ c : ℝ, 0 < μ → μ < 1 →
        |μ - 1 / 2| < ε₀ → belowFirstCriticalValue μ c →
        ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
          IsLeviCivitaHamiltonianFlow μ c φ →
          ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
            (δ : AntipodalPeriodicTrajectory φ),
            IsGeometricBirkhoffRetrogradeTrajectory φ δ →
            RationalDiskLikeGlobalSurfaceOfSection φ hanti
              (antipodalTrajectoryDoubleLift φ hanti δ) := by
  let P : ℝ → ℝ → Prop := fun μ c =>
    0 < μ → μ < 1 → belowFirstCriticalValue μ c →
      ∀ (φ : Flow ℝ (LeftEnergyState μ c)),
        IsLeviCivitaHamiltonianFlow μ c φ →
        ∀ (hanti : IsAntipodallyEquivariantFlow μ c φ)
          (δ : AntipodalPeriodicTrajectory φ),
          IsGeometricBirkhoffRetrogradeTrajectory φ δ →
          RationalDiskLikeGlobalSurfaceOfSection φ hanti
            (antipodalTrajectoryDoubleLift φ hanti δ)
  obtain ⟨εcrit, η, hεcrit, hη, hcrit⟩ :=
    quotient_retrograde_page_near_critical
  obtain ⟨εtail, C, hεtail, htail⟩ :=
    quotient_retrograde_page_low_energy_tail
  have hloc : ∀ c₀ ∈ Icc (2 + η / 2) C,
      ∃ ε r : ℝ, 0 < ε ∧ 0 < r ∧
        ∀ μ c : ℝ, |μ - 1 / 2| < ε → |c - c₀| < r → P μ c := by
    intro c₀ hc₀
    have hc₀' : 2 < c₀ := by
      have := hc₀.1
      linarith
    obtain ⟨ε, r, hε, hr, hlocal⟩ :=
      quotient_retrograde_page_local_subcritical c₀ hc₀'
    refine ⟨ε, r, hε, hr, ?_⟩
    intro μ c hμ hc hμ0 hμ1 hsub φ hφ hanti δ hδ
    exact hlocal μ c hμ0 hμ1 hμ hc hsub φ hφ hanti δ hδ
  obtain ⟨εmid, hεmid, hmid⟩ :=
    uniform_on_compact_energy_set P (1 / 2) (Icc (2 + η / 2) C) isCompact_Icc hloc
  refine ⟨min εcrit (min εtail εmid), lt_min hεcrit (lt_min hεtail hεmid), ?_⟩
  intro μ c hμ0 hμ1 hμ hsub φ hφ hanti δ hδ
  have hμcrit : |μ - 1 / 2| < εcrit := lt_of_lt_of_le hμ (min_le_left _ _)
  have hμrest : |μ - 1 / 2| < min εtail εmid :=
    lt_of_lt_of_le hμ (min_le_right _ _)
  have hμtail : |μ - 1 / 2| < εtail := lt_of_lt_of_le hμrest (min_le_left _ _)
  have hμmid : |μ - 1 / 2| < εmid := lt_of_lt_of_le hμrest (min_le_right _ _)
  by_cases hnear : c < 2 + η
  · exact hcrit μ c hμ0 hμ1 hμcrit hnear hsub φ hφ hanti δ hδ
  by_cases hfar : C ≤ c
  · exact htail μ c hμ0 hμ1 hμtail hfar hsub φ hφ hanti δ hδ
  have hc : c ∈ Icc (2 + η / 2) C := by
    constructor <;> linarith
  exact hmid μ c hμmid hc hμ0 hμ1 hsub φ hφ hanti δ hδ
