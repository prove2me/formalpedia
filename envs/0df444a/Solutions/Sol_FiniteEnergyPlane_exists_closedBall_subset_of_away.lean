-- Prove2me | solution 1 for FiniteEnergyPlane.exists_closedBall_subset_of_away
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T17:59:34.004812+00:00
-- url     : https://prove2.me/submissions/ed54ba54-dd3c-468d-b200-6456d9664ad0

import Definitions.Def_FiniteEnergyPlane_Setting



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Uniform closed discs around points of an exhaustion of a finitely punctured plane. -/
theorem exists_closedBall_subset_of_away_aux (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (z : ℕ → ℂ)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ m : ℕ, ∀ k, m ≤ k → closedBall (z k) ρ ⊆ U k := by
  obtain ⟨δ, hδ, hzδ⟩ := haway
  -- compact pieces away from `Γ` lie in a single `U m`
  have hK : ∀ R' : ℝ, ∃ m : ℕ,
      {w : ℂ | ‖w‖ ≤ R' ∧ ∀ γ ∈ Γ, δ / 2 ≤ ‖w - γ‖} ⊆ U m := by
    intro R'
    set K := {w : ℂ | ‖w‖ ≤ R' ∧ ∀ γ ∈ Γ, δ / 2 ≤ ‖w - γ‖} with hKdef
    have hKc : IsCompact K := by
      refine (isCompact_closedBall (0 : ℂ) R').of_isClosed_subset ?_ ?_
      · refine (isClosed_le continuous_norm continuous_const).inter ?_
        have he : {a : ℂ | ∀ γ ∈ Γ, δ / 2 ≤ ‖a - γ‖} = ⋂ γ ∈ Γ, {a : ℂ | δ / 2 ≤ ‖a - γ‖} := by
          ext; simp
        change IsClosed {a : ℂ | ∀ γ ∈ Γ, δ / 2 ≤ ‖a - γ‖}
        rw [he]
        exact isClosed_biInter fun γ _ =>
          isClosed_le continuous_const (continuous_id.sub continuous_const).norm
      · intro w hw
        simpa [mem_closedBall, dist_zero_right] using hw.1
    have hKU : K ⊆ ⋃ k, U k := by
      rw [hUunion]
      intro w hw hwΓ
      have := hw.2 w hwΓ
      rw [sub_self, norm_zero] at this
      linarith
    exact hKc.elim_directed_cover U hUo hKU hUmono.directed_le
  have hρ : (0 : ℝ) < min (δ / 2) 1 := lt_min (by linarith) one_pos
  have hdist : ∀ k, ∀ y ∈ closedBall (z k) (min (δ / 2) 1), ∀ γ ∈ Γ, δ / 2 ≤ ‖y - γ‖ := by
    intro k y hy γ hγ
    rw [mem_closedBall, dist_eq_norm] at hy
    have h1 := hzδ k γ hγ
    have h2 := norm_sub_le_norm_sub_add_norm_sub (z k) y γ
    have h3 : ‖z k - y‖ = ‖y - z k‖ := norm_sub_rev _ _
    have h4 := min_le_left (δ / 2) 1
    linarith
  have hnorm : ∀ k, ∀ y ∈ closedBall (z k) (min (δ / 2) 1), ‖y‖ ≤ ‖z k‖ + 1 := by
    intro k y hy
    rw [mem_closedBall, dist_eq_norm] at hy
    have := norm_le_norm_add_norm_sub' y (z k)
    have h4 := min_le_right (δ / 2) 1
    linarith
  rcases hbdd with ⟨R, hR⟩ | ⟨m₁, R, hR⟩
  · obtain ⟨m, hm⟩ := hK (R + 1)
    refine ⟨_, hρ, m, fun k hk y hy => hUmono hk (hm ⟨?_, hdist k y hy⟩)⟩
    linarith [hnorm k y hy, hR k]
  · obtain ⟨m₂, hm₂⟩ := hK R
    refine ⟨_, hρ, max m₁ m₂, fun k hk y hy => ?_⟩
    by_cases hy' : R < ‖y‖
    · exact hUmono (le_of_max_le_left hk) (hR hy')
    · exact hUmono (le_of_max_le_right hk) (hm₂ ⟨not_lt.1 hy', hdist k y hy⟩)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (z : ℕ → ℂ)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ m : ℕ, ∀ k, m ≤ k → closedBall (z k) ρ ⊆ U k :=
  exists_closedBall_subset_of_away_aux Γ U hUo hUmono hUunion z haway hbdd
