-- Prove2me | solution 1 for FiniteEnergyPlane.exists_tendsto_of_upcrossing_levels
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T00:05:43.834331+00:00
-- url     : https://prove2.me/submissions/726b91f5-b012-44b6-9884-1068ec7c92ac

import Mathlib



/-! A function that can cross levels of every scale only upward converges. -/

namespace FiniteEnergyPlane

open Filter Topology Set

/-- Once above a level that can only be crossed upward, a function stays above it. -/
theorem le_of_upcrossing_level_aux (α α' : ℝ → ℝ) (s₁ l : ℝ)
    (hd : ∀ s ≥ s₁, HasDerivAt α (α' s) s) (hb : ∀ s ≥ s₁, α s = l → 0 < α' s)
    (hl : l ≤ α s₁) : ∀ s ≥ s₁, l ≤ α s := by
  intro s hs
  have h := image_le_of_deriv_right_lt_deriv_boundary' (f := fun x => -α x)
    (f' := fun x => -α' x) (a := s₁) (b := s) (B := fun _ => -l) (B' := fun _ => 0)
    (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt.neg)
    (fun x hx => (hd x hx.1).neg.hasDerivWithinAt) (by simpa using hl) continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _) (fun x hx heq => by
      have := hb x hx.1 (by linarith)
      linarith) ⟨hs, le_rfl⟩

  linarith

theorem exists_tendsto_of_upcrossing_levels_aux (α α' : ℝ → ℝ) (s₀ δ₀ : ℝ)
    (hd : ∀ s ≥ s₀, HasDerivAt α (α' s) s)
    (hlev : ∀ δ > 0, ∃ S : ℝ, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ s ≥ S, α s = l → 0 < α' s)
    (hup : ∀ μ > δ₀, ∃ᶠ s in atTop, α s < μ) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ Tendsto α atTop (𝓝 μ) := by
  -- staying above a level from a starting time `s₁ ≥ max S s₀`
  have key : ∀ S l s₁, max S s₀ ≤ s₁ → (∀ s ≥ S, α s = l → 0 < α' s) → l ≤ α s₁ →
      ∀ s ≥ s₁, l ≤ α s := fun S l s₁ hs₁ hb hl =>
    le_of_upcrossing_level_aux α α' s₁ l
      (fun s hs => hd s ((le_max_right _ _).trans (hs₁.trans hs)))
      (fun s hs => hb s ((le_max_left _ _).trans (hs₁.trans hs))) hl
  obtain ⟨S1, hS1⟩ := hlev 1 one_pos
  obtain ⟨l1, hl1, hb1⟩ := hS1 (α (max S1 s₀) - 1)
  have hlow := key S1 l1 (max S1 s₀) le_rfl hb1 (by linarith [hl1.2])
  set I := {l : ℝ | ∀ᶠ s in atTop, l ≤ α s}
  have hI : l1 ∈ I := eventually_atTop.2 ⟨_, hlow⟩
  have hIb : ∀ l ∈ I, l ≤ δ₀ := by
    intro l hl
    by_contra h
    push_neg at h
    obtain ⟨s, hs1, hs2⟩ := ((hup ((l + δ₀) / 2) (by linarith)).and_eventually hl).exists
    linarith
  have hne : I.Nonempty := ⟨l1, hI⟩
  have hbdd : BddAbove I := ⟨δ₀, hIb⟩
  refine ⟨sSup I, csSup_le hne hIb, tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩⟩
  · obtain ⟨l, hl, hbl⟩ := exists_lt_of_lt_csSup hne hb
    exact hl.mono fun s hs => lt_of_lt_of_le hbl hs
  · by_contra hcon
    rw [not_eventually] at hcon
    set μ := sSup I
    obtain ⟨S, hS⟩ := hlev ((b - μ) / 2) (by linarith)
    obtain ⟨l, hl, hbl⟩ := hS (μ + (b - μ) / 4)
    obtain ⟨s₂, hs₂, hαs₂⟩ := frequently_atTop.1 hcon (max S s₀)
    push_neg at hαs₂
    have hst := key S l s₂ hs₂ hbl (by linarith [hl.2])
    have : l ∈ I := eventually_atTop.2 ⟨s₂, hst⟩
    have := le_csSup hbdd this
    linarith [hl.1]

end FiniteEnergyPlane

open FiniteEnergyPlane

open Filter Topology

theorem solution (α α' : ℝ → ℝ) (s₀ δ₀ : ℝ)
    (hd : ∀ s ≥ s₀, HasDerivAt α (α' s) s)
    (hlev : ∀ δ > 0, ∃ S : ℝ, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ s ≥ S, α s = l → 0 < α' s)
    (hup : ∀ μ > δ₀, ∃ᶠ s in atTop, α s < μ) :
    ∃ μ : ℝ, μ ≤ δ₀ ∧ Tendsto α atTop (𝓝 μ) :=
  exists_tendsto_of_upcrossing_levels_aux α α' s₀ δ₀ hd hlev hup
