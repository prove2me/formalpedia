-- Prove2me | solution 1 for DataDrivenRO.Guarantee.strict_separation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:02:50.704481+00:00
-- url     : https://prove2.me/submissions/ec859894-14e2-40d3-a4da-9d8a4279c707

import Mathlib
import Definitions.Def_DataDrivenRO_Guarantee_Setting

open MeasureTheory

open DataDrivenRO.Guarantee in
theorem solution {d k : ℕ} (U : Set (Fin d → ℝ)) (hne : U.Nonempty) (hconv : Convex ℝ U)
    (hcpt : IsCompact U) (f : (Fin d → ℝ) → (Fin k → ℝ) → ℝ) (xstar : Fin k → ℝ)
    (hf : ConcaveOn ℝ Set.univ (fun u => f u xstar)) (hfeas : ∀ u ∈ U, f u xstar ≤ 0)
    (t : ℝ) (ht : 0 < t) :
    ∃ (v : Fin d → ℝ) (v₀ : ℝ), (∀ u ∈ U, u ⬝ᵥ v < v₀) ∧ (∀ u, t ≤ f u xstar → v₀ < u ⬝ᵥ v) := by
  have hcont : Continuous (fun u => f u xstar) :=
    continuousOn_univ.mp (hf.continuousOn isOpen_univ)
  have hSconv : Convex ℝ {u : Fin d → ℝ | t ≤ f u xstar} := by
    have := hf.convex_ge t
    simpa using this
  have hSclosed : IsClosed {u : Fin d → ℝ | t ≤ f u xstar} :=
    isClosed_le continuous_const hcont
  have hdisj : Disjoint U {u : Fin d → ℝ | t ≤ f u xstar} := by
    rw [Set.disjoint_left]
    intro u hu hS
    have h1 := hfeas u hu
    simp only [Set.mem_setOf_eq] at hS
    linarith
  obtain ⟨g, a, b, h1, hab, h2⟩ :=
    geometric_hahn_banach_compact_closed hconv hcpt hSconv hSclosed hdisj
  have key : ∀ u : Fin d → ℝ,
      g u = u ⬝ᵥ (fun i => g (fun j => if i = j then 1 else 0)) := by
    intro u
    have := LinearMap.pi_apply_eq_sum_univ (g : (Fin d → ℝ) →ₗ[ℝ] ℝ) u
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this, dotProduct]
  refine ⟨fun i => g (fun j => if i = j then 1 else 0), a, ?_, ?_⟩
  · intro u hu
    rw [← key]
    exact h1 u hu
  · intro u hu
    rw [← key]
    exact lt_trans hab (h2 u hu)
