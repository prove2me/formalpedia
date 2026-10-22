-- Prove2me | solution 1 for BirkhoffGlobalSection.birkhoff_near_crossing_curve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-25T09:17:59.489965+00:00
-- url     : https://prove2.me/submissions/77d555e1-be09-40dc-97dd-b26627e501ec
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffShootingArcs
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_arc_continuity
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_arc_small
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_near_arc_end
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Theorems.Thm_BirkhoffGlobalSection_leftCollisionPoint_mem_leftEnergyComponent
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

open BirkhoffGlobalSection Set Filter Topology

/-- The first bad parameter of an open-at-good-points family that is good near `0`. -/
lemma first_bad_parameter (G : ℝ → Prop)
    (hopen : ∀ r₀ > 0, G r₀ → ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ → G r)
    (hsmall : ∃ ε > 0, ∀ r ∈ Ioo 0 ε, G r) (R : ℝ) (hR : 0 < R) (hbadR : ¬ G R) :
    ∃ b > 0, (∀ r ∈ Ioo 0 b, G r) ∧ ¬ G b := by
  obtain ⟨ε, hε, hεG⟩ := hsmall
  set A : Set ℝ := {b' | 0 < b' ∧ ∀ r ∈ Ioo 0 b', G r} with hA
  have hεA : ε ∈ A := ⟨hε, hεG⟩
  have hbdd : BddAbove A := by
    refine ⟨R, fun b' hb' => ?_⟩
    by_contra h
    push Not at h
    exact hbadR (hb'.2 R ⟨hR, h⟩)
  set b := sSup A
  have hεb : ε ≤ b := le_csSup hbdd hεA
  have hgood : ∀ r ∈ Ioo 0 b, G r := by
    intro r hr
    obtain ⟨b', hb', hrb'⟩ := exists_lt_of_lt_csSup ⟨ε, hεA⟩ hr.2
    exact hb'.2 r ⟨hr.1, hrb'⟩
  refine ⟨b, lt_of_lt_of_le hε hεb, hgood, fun hGb => ?_⟩
  obtain ⟨δ, hδ, hδG⟩ := hopen b (lt_of_lt_of_le hε hεb) hGb
  have hmem : b + δ / 2 ∈ A := by
    refine ⟨by linarith, fun r hr => ?_⟩
    rcases lt_or_ge r b with h | h
    · exact hgood r ⟨hr.1, h⟩
    · exact hδG r (by rw [abs_lt]; constructor <;> linarith [hr.2])
  have := le_csSup hbdd hmem
  linarith

lemma nearStart_coords (μ c r : ℝ) :
    nearShootingStart μ c r 0 = r ∧ nearShootingStart μ c r 1 = 0 ∧
      nearShootingStart μ c r 2 = 0 := by
  simp [nearShootingStart]

lemma near_arc_unique {μ c : ℝ} (φ : Flow ℝ (LeftEnergyState μ c)) (x : LeftEnergyState μ c)
    (τ₁ τ₂ : ℝ) (h₁ : IsNearShootingArc φ x τ₁) (h₂ : IsNearShootingArc φ x τ₂) : τ₁ = τ₂ := by
  rcases lt_trichotomy τ₁ τ₂ with h | h | h
  · have := (h₂.2.1 (-τ₁) ⟨by linarith, by linarith [h₁.1]⟩).1
    rw [h₁.2.2.2] at this; exact absurd this (lt_irrefl 0)
  · exact h
  · have := (h₁.2.1 (-τ₂) ⟨by linarith, by linarith [h₂.1]⟩).1
    rw [h₂.2.2.2] at this; exact absurd this (lt_irrefl 0)

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ b : ℝ, 0 < b ∧ ∃ α : ℝ, -1 < α ∧ α < -(Real.sqrt 2 / 2) ∧
      ∃ S : ℝ → LeftEnergyState μ c, ∃ T : ℝ → ℝ,
        ContinuousOn (fun r : ℝ =>
          shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase)) (Set.Ioo 0 b) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sqrt 2 / 2, 0)) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin b (Set.Iio b)) (nhds (α, 0)) ∧
        ∀ r ∈ Set.Ioo 0 b,
          ((S r : LeftEnergyState μ c) : Phase) 1 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 2 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 0 ≠ 0 ∧
          0 < T r ∧
          (∀ t ∈ Set.Ioo (-T r) 0,
            0 < relativePosition μ ((φ t (S r) : LeftEnergyState μ c) : Phase) 0 ∧
            relativePosition μ ((φ t (S r) : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          relativePosition μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
          relativePosition μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase) 0 = 0 := by
  set G : ℝ → Prop := fun r => ∃ x : LeftEnergyState μ c,
    (x : Phase) = nearShootingStart μ c r ∧ ∃ τ : ℝ, IsNearShootingArc φ x τ with hG
  have hopen : ∀ r₀ > 0, G r₀ → ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ → G r := by
    rintro r₀ hr₀ ⟨x₀, hx₀, τ₀, harc⟩
    obtain ⟨δ, hδ, h⟩ := birkhoff_near_arc_continuity μ c hμ0 hμ1 hc φ hφ r₀ hr₀ x₀ τ₀ hx₀ harc 1
      one_pos
    exact ⟨δ, hδ, fun r hr => by
      obtain ⟨x, hx, τ, hτ, -⟩ := h r hr
      exact ⟨x, hx, τ, hτ⟩⟩
  obtain ⟨ε, hε, hεG, hlim0⟩ := birkhoff_near_arc_small μ c hμ0 hμ1 hc φ hφ
  have hbad1 : ¬ G 1 := by
    rintro ⟨x, hx, -⟩
    obtain ⟨ρ, hρ, hbound⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
    have := hbound x x.2
    rw [hx] at this
    simp [leviCivitaPosition, nearShootingStart] at this
    nlinarith
  obtain ⟨b, hb, hgood, hbadb⟩ := first_bad_parameter G hopen ⟨ε, hε, hεG⟩ 1 one_pos hbad1
  obtain ⟨α, hα1, hα2, hlimb⟩ := birkhoff_near_arc_end μ c hμ0 hμ1 hc φ hφ b hb hgood hbadb
  have : Nonempty (LeftEnergyState μ c) :=
    ⟨⟨_, leftCollisionPoint_mem_leftEnergyComponent μ c hμ0 hμ1⟩⟩
  set S : ℝ → LeftEnergyState μ c := fun r => Classical.epsilon (fun x : LeftEnergyState μ c =>
    (x : Phase) = nearShootingStart μ c r ∧ ∃ τ : ℝ, IsNearShootingArc φ x τ) with hS
  set T : ℝ → ℝ := fun r => Classical.epsilon (fun τ : ℝ => IsNearShootingArc φ (S r) τ) with hT
  have hST : ∀ r, G r → (S r : Phase) = nearShootingStart μ c r ∧ IsNearShootingArc φ (S r) (T r) := by
    intro r hr
    have h1 := Classical.epsilon_spec (p := fun x : LeftEnergyState μ c =>
      (x : Phase) = nearShootingStart μ c r ∧ ∃ τ : ℝ, IsNearShootingArc φ x τ) hr
    exact ⟨h1.1, Classical.epsilon_spec (p := fun τ : ℝ => IsNearShootingArc φ (S r) τ) h1.2⟩
  -- identify any realization with the chosen one
  have hid : ∀ r, G r → ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = nearShootingStart μ c r → IsNearShootingArc φ x τ → x = S r ∧ τ = T r := by
    intro r hr x τ hx harc
    obtain ⟨h1, h2⟩ := hST r hr
    have hxS : x = S r := Subtype.ext (hx.trans h1.symm)
    subst hxS
    exact ⟨rfl, near_arc_unique φ _ τ (T r) harc h2⟩
  set F : ℝ → ℝ × ℝ := fun r =>
    shootingCoordinates μ ((φ (-T r) (S r) : LeftEnergyState μ c) : Phase) with hF
  refine ⟨b, hb, α, hα1, hα2, S, T, ?_, ?_, ?_, ?_⟩
  · intro r₀ hr₀
    rw [Metric.continuousWithinAt_iff]
    intro e he
    obtain ⟨h1, h2⟩ := hST r₀ (hgood r₀ hr₀)
    obtain ⟨δ, hδ, h⟩ := birkhoff_near_arc_continuity μ c hμ0 hμ1 hc φ hφ r₀ hr₀.1 (S r₀) (T r₀)
      h1 h2 e he
    refine ⟨δ, hδ, fun r hr hdist => ?_⟩
    obtain ⟨x, hx, τ, harc, hd⟩ := h r (by rwa [Real.dist_eq] at hdist)
    obtain ⟨rfl, rfl⟩ := hid r (hgood r hr) x τ hx harc
    exact hd
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, h⟩ := hlim0 e he
    refine ⟨min δ ε, lt_min hδ hε, fun r hr hdist => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hdist
    have hrε : r < ε := lt_of_lt_of_le hdist (min_le_right _ _)
    obtain ⟨h1, h2⟩ := hST r (hεG r ⟨hr, hrε⟩)
    exact h r ⟨hr, lt_of_lt_of_le hdist (min_le_left _ _)⟩ (S r) (T r) h1 h2
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, h⟩ := hlimb e he
    refine ⟨min δ b, lt_min hδ hb, fun r hr hdist => ?_⟩
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by simpa using hr)] at hdist
    have hr0 : 0 < r := by linarith [min_le_right δ b]
    obtain ⟨h1, h2⟩ := hST r (hgood r ⟨hr0, hr⟩)
    exact h r ⟨by linarith [min_le_left δ b], hr⟩ (S r) (T r) h1 h2
  · intro r hr
    obtain ⟨h1, h2⟩ := hST r (hgood r hr)
    obtain ⟨c0, c1, c2⟩ := nearStart_coords μ c r
    refine ⟨by rw [h1]; exact c1, by rw [h1]; exact c2, by rw [h1, c0]; exact hr.1.ne', h2.1,
      h2.2.1, h2.2.2.1, h2.2.2.2⟩
