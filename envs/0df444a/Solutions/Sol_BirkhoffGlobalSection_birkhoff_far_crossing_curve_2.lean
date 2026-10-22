-- Prove2me | solution 2 for BirkhoffGlobalSection.birkhoff_far_crossing_curve
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-26T21:38:31.616111+00:00
-- url     : https://prove2.me/submissions/e1925f03-35f0-46b1-975b-5898dc00fdd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_strictMonoOn
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_continuity
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_small
import Theorems.Thm_BirkhoffGlobalSection_birkhoff_far_arc_end
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

open BirkhoffGlobalSection Set Filter Topology

set_option autoImplicit false

/-- The right endpoint of the initial interval of good parameters is bad.
This is the supremum construction used in Birkhoff's continuation argument. -/
private theorem first_bad_parameter (G : ℝ → Prop)
    (hopen : ∀ r₀ > 0, G r₀ → ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ → G r)
    (hsmall : ∃ ε > 0, ∀ r ∈ Ioo 0 ε, G r)
    (R : ℝ) (hR : 0 < R) (hbadR : ¬ G R) :
    ∃ b > 0, (∀ r ∈ Ioo 0 b, G r) ∧ ¬ G b := by
  obtain ⟨ε, hε, hεG⟩ := hsmall
  let A : Set ℝ := {a | 0 < a ∧ ∀ r ∈ Ioo 0 a, G r}
  have hεA : ε ∈ A := ⟨hε, hεG⟩
  have hbdd : BddAbove A := by
    refine ⟨R, fun a ha => ?_⟩
    by_contra h
    exact hbadR (ha.2 R ⟨hR, lt_of_not_ge h⟩)
  let b := sSup A
  have hεb : ε ≤ b := le_csSup hbdd hεA
  have hb : 0 < b := lt_of_lt_of_le hε hεb
  have hgood : ∀ r ∈ Ioo 0 b, G r := by
    intro r hr
    obtain ⟨a, ha, hra⟩ := exists_lt_of_lt_csSup ⟨ε, hεA⟩ hr.2
    exact ha.2 r ⟨hr.1, hra⟩
  refine ⟨b, hb, hgood, ?_⟩
  intro hGb
  obtain ⟨δ, hδ, hδG⟩ := hopen b hb hGb
  have hmem : b + δ / 2 ∈ A := by
    refine ⟨by linarith, fun r hr => ?_⟩
    rcases lt_or_ge r b with hrb | hrb
    · exact hgood r ⟨hr.1, hrb⟩
    · apply hδG r
      rw [abs_lt]
      constructor <;> linarith [hr.2]
  have := le_csSup hbdd hmem
  linarith

/-- Strict horizontal monotonicity makes the crossing time unique. -/
private theorem far_arc_time_unique (μ c : ℝ)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) (x : LeftEnergyState μ c)
    (τ₁ τ₂ : ℝ) (h₁ : IsFarShootingArc φ x τ₁)
    (h₂ : IsFarShootingArc φ x τ₂) : τ₁ = τ₂ := by
  rcases lt_trichotomy τ₁ τ₂ with h | h | h
  · have hm := birkhoff_far_arc_strictMonoOn μ c φ hφ x τ₂ h₂
      ⟨h₁.1.le, h.le⟩ ⟨h₂.1.le, le_rfl⟩ h
    dsimp only at hm
    rw [h₁.2.2.2.1, h₂.2.2.2.1] at hm
    exact (lt_irrefl _ hm).elim
  · exact h
  · have hm := birkhoff_far_arc_strictMonoOn μ c φ hφ x τ₁ h₁
      ⟨h₂.1.le, h.le⟩ ⟨h₁.1.le, le_rfl⟩ h
    dsimp only at hm
    rw [h₁.2.2.2.1, h₂.2.2.2.1] at hm
    exact (lt_irrefl _ hm).elim

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c)
    (φ : Flow ℝ (LeftEnergyState μ c))
    (hφ : IsLeviCivitaHamiltonianFlow μ c φ) :
    ∃ b : ℝ, 0 < b ∧ ∃ E : ℝ × ℝ,
      (((E.1 = -1 ∨ E.1 = 1) ∧ 0 < E.2) ∨ (E.2 = 0 ∧ Real.sqrt 2 / 2 < E.1)) ∧
      ∃ S : ℝ → LeftEnergyState μ c, ∃ T : ℝ → ℝ,
        ContinuousOn (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) (Set.Ioo 0 b) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.sqrt 2 / 2), 0)) ∧
        Filter.Tendsto (fun r : ℝ =>
          shootingCoordinates μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase))
          (nhdsWithin b (Set.Iio b)) (nhds E) ∧
        ∀ r ∈ Set.Ioo 0 b,
          ((S r : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 3 = 0 ∧
          ((S r : LeftEnergyState μ c) : Phase) 1 ≠ 0 ∧
          0 < T r ∧
          (∀ u ∈ Set.Ioo 0 (T r),
            relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 1 < 0) ∧
          relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 1 < 0 ∧
          StrictMonoOn
            (fun u : ℝ => relativePosition μ ((φ u (S r) : LeftEnergyState μ c) : Phase) 0)
            (Set.Icc 0 (T r)) ∧
          relativePosition μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase) 0 = 0 ∧
          0 < jacobiVelocity
            (leviCivitaToJacobi μ ((φ (T r) (S r) : LeftEnergyState μ c) : Phase)) 0 := by
  classical
  let G : ℝ → Prop := fun r => ∃ x : LeftEnergyState μ c,
    (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ
  have hopen : ∀ r₀ > 0, G r₀ → ∃ δ > 0, ∀ r : ℝ, |r - r₀| < δ → G r := by
    rintro r₀ hr₀ ⟨x₀, hx₀, τ₀, harc⟩
    obtain ⟨δ, hδ, h⟩ := birkhoff_far_arc_continuity μ c hμ0 hμ1 hc φ hφ
      r₀ hr₀ x₀ τ₀ hx₀ harc 1 one_pos
    refine ⟨δ, hδ, ?_⟩
    intro r hr
    obtain ⟨x, hx, τ, hτ, -⟩ := h r hr
    exact ⟨x, hx, τ, hτ⟩
  obtain ⟨ε, hε, hεG, hlim0⟩ := birkhoff_far_arc_small μ c hμ0 hμ1 hc φ hφ
  have hbad1 : ¬ G 1 := by
    rintro ⟨x, hx, -⟩
    obtain ⟨ρ, hρ, hbound⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
    have hpos := hbound x x.2
    rw [hx] at hpos
    simp [leviCivitaPosition, farShootingStart] at hpos
    nlinarith
  obtain ⟨b, hb, hgood, hbadb⟩ := first_bad_parameter G hopen ⟨ε, hε, hεG⟩ 1 one_pos hbad1
  obtain ⟨E, hE, hlimb⟩ := birkhoff_far_arc_end μ c hμ0 hμ1 hc φ hφ b hb hgood hbadb
  obtain ⟨x₀, -⟩ := hεG (ε / 2) ⟨by linarith, by linarith⟩
  have : Nonempty (LeftEnergyState μ c) := ⟨x₀⟩
  let S : ℝ → LeftEnergyState μ c := fun r => Classical.epsilon
    (fun x => (x : Phase) = farShootingStart μ c r ∧ ∃ τ : ℝ, IsFarShootingArc φ x τ)
  let T : ℝ → ℝ := fun r => Classical.epsilon (fun τ => IsFarShootingArc φ (S r) τ)
  have hST : ∀ r, G r → (S r : Phase) = farShootingStart μ c r ∧
      IsFarShootingArc φ (S r) (T r) := by
    intro r hr
    have hs := Classical.epsilon_spec hr
    exact ⟨hs.1, Classical.epsilon_spec hs.2⟩
  have hid : ∀ r, G r → ∀ x : LeftEnergyState μ c, ∀ τ : ℝ,
      (x : Phase) = farShootingStart μ c r → IsFarShootingArc φ x τ →
      x = S r ∧ τ = T r := by
    intro r hr x τ hx harc
    obtain ⟨hs, ht⟩ := hST r hr
    have hxS : x = S r := Subtype.ext (hx.trans hs.symm)
    subst x
    exact ⟨rfl, far_arc_time_unique μ c φ hφ _ τ (T r) harc ht⟩
  refine ⟨b, hb, E, hE, S, T, ?_, ?_, ?_, ?_⟩
  · intro r₀ hr₀
    rw [Metric.continuousWithinAt_iff]
    intro e he
    obtain ⟨hs, ht⟩ := hST r₀ (hgood r₀ hr₀)
    obtain ⟨δ, hδ, h⟩ := birkhoff_far_arc_continuity μ c hμ0 hμ1 hc φ hφ
      r₀ hr₀.1 (S r₀) (T r₀) hs ht e he
    refine ⟨δ, hδ, ?_⟩
    intro r hr hdist
    obtain ⟨x, hx, τ, harc, hd⟩ := h r (by rwa [Real.dist_eq] at hdist)
    obtain ⟨rfl, rfl⟩ := hid r (hgood r hr) x τ hx harc
    exact hd
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, h⟩ := hlim0 e he
    refine ⟨min δ ε, lt_min hδ hε, ?_⟩
    intro r hr hdist
    rw [Real.dist_eq, sub_zero, abs_of_pos hr] at hdist
    have hrε : r < ε := lt_of_lt_of_le hdist (min_le_right _ _)
    obtain ⟨hs, ht⟩ := hST r (hεG r ⟨hr, hrε⟩)
    exact h r ⟨hr, lt_of_lt_of_le hdist (min_le_left _ _)⟩ (S r) (T r) hs ht
  · rw [Metric.tendsto_nhdsWithin_nhds]
    intro e he
    obtain ⟨δ, hδ, h⟩ := hlimb e he
    refine ⟨min δ b, lt_min hδ hb, ?_⟩
    intro r hr hdist
    rw [Real.dist_eq, abs_sub_comm, abs_of_pos (by simpa using hr)] at hdist
    have hr0 : 0 < r := by linarith [min_le_right δ b]
    obtain ⟨hs, ht⟩ := hST r (hgood r ⟨hr0, hr⟩)
    exact h r ⟨by linarith [min_le_left δ b], hr⟩ (S r) (T r) hs ht
  · intro r hr
    obtain ⟨hs, ht⟩ := hST r (hgood r hr)
    refine ⟨?_, ?_, ?_, ht.1, ht.2.1, ht.2.2.1,
      birkhoff_far_arc_strictMonoOn μ c φ hφ _ _ ht, ht.2.2.2.1,
      ht.2.2.2.2 _ ⟨ht.1, le_rfl⟩⟩
    · simp [hs, farShootingStart]
    · simp [hs, farShootingStart]
    · simpa [hs, farShootingStart] using hr.1.ne'
