-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_grid_ae_stop_future_increment_cylinder_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T16:09:42.570636+00:00
-- url     : https://prove2.me/submissions/38cb8db1-4966-418a-949e-a211528dc2d5

import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_horizon_laws_consistent_on_past_events
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

namespace AV_0042

theorem meas_X {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0) :
    Measurable (X.X t) :=
  (chat04_levy_joint_time_state_measurable X).comp (measurable_const.prodMk measurable_id)

end AV_0042

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (T u : ℝ≥0) (τ : Ω → ℝ≥0) (grid : Finset ℝ≥0)
    (hgrid : ∀ᵐ ω ∂(P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))), τ ω ∈ grid)
    (hT : ∀ s ∈ grid, s + u ≤ T)
    (hstop : ∀ s ∈ grid, MeasurableSet[𝓕 s] {ω : Ω | τ ω = s})
    (A : Set Ω) (hA : MeasurableSet A)
    (hHistory : ∀ s ∈ grid,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω = s}))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
      (A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))
      ((X.X u) ⁻¹' B) := by
  set Q := P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))) with hQ
  set G : Set Ω := {ω | τ ω ∈ grid} with hG
  have hGc : Q Gᶜ = 0 := by
    rw [ae_iff] at hgrid; simpa [G, compl_setOf] using hgrid
  have hGae : G =ᵐ[Q] (univ : Set Ω) := by
    rw [ae_eq_univ]; exact hGc
  have hcong : ∀ S : Set Ω, Q S = Q (S ∩ G) := by
    intro S
    apply measure_congr
    have := (ae_eq_refl S).inter hGae
    simpa using this.symm
  have hmeasS : ∀ s ∈ grid, MeasurableSet (A ∩ {ω : Ω | τ ω = s}) :=
    fun s hs => 𝓕.le s _ (hHistory s hs)
  have hmeasI : ∀ s : ℝ≥0, MeasurableSet
      ((fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B) :=
    fun s => ((AV_0042.meas_X X (s+u)).sub (AV_0042.meas_X X s)) hB
  have hdisj : ∀ (F : ℝ≥0 → Set Ω), (∀ s, F s ⊆ {ω | τ ω = s}) →
      Set.PairwiseDisjoint (↑grid) F := by
    intro F hF a _ b _ hab
    refine Set.disjoint_left.mpr ?_
    intro ω h1 h2
    exact hab ((hF a h1).symm.trans (hF b h2))
  have e1 : A ∩ {ω : Ω | X.X (τ ω + u) ω - X.X (τ ω) ω ∈ B} ∩ G =
      ⋃ s ∈ grid, (A ∩ {ω : Ω | τ ω = s}) ∩
        (fun ω => X.X (s + u) ω - X.X s ω) ⁻¹' B := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, mem_preimage, G]
    constructor
    · rintro ⟨⟨hA, hE⟩, hg⟩
      exact ⟨τ ω, hg, ⟨hA, rfl⟩, hE⟩
    · rintro ⟨s, hs, ⟨hA, rfl⟩, hE⟩
      exact ⟨⟨hA, hE⟩, hs⟩
  have e2 : A ∩ G = ⋃ s ∈ grid, (A ∩ {ω : Ω | τ ω = s}) := by
    ext ω
    simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, G]
    constructor
    · rintro ⟨hA, hg⟩
      exact ⟨τ ω, hg, hA, rfl⟩
    · rintro ⟨s, hs, hA, rfl⟩
      exact ⟨hA, hs⟩
  rw [hcong, e1, hcong A, e2,
    measure_biUnion_finset (hdisj _ (fun s => fun ω h => h.1.2))
      (fun s hs => (hmeasS s hs).inter (hmeasI s)),
    measure_biUnion_finset (hdisj _ (fun s => fun ω h => h.2))
      (fun s hs => hmeasS s hs), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [hQ, esscher_terminal_increment_cylinder_factorization X θ hθ s u T (hT s hs) _
    (hHistory s hs) B hB]
  congr 1
  have hsT : s ≤ T := le_trans (le_self_add) (hT s hs)
  exact chat04_esscher_finite_horizon_laws_consistent_on_past_events X θ hθ s T hsT _
    (hHistory s hs)
