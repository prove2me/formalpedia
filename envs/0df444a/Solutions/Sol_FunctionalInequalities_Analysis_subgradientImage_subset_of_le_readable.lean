-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradientImage_subset_of_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:33:20.093014+00:00
-- url     : https://prove2.me/submissions/0819bf45-736c-45d5-b2f3-f8b73c6014c9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient
import Theorems.Thm_FunctionalInequalities_Analysis_support_of_max_readable

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section LT12ASubgradientImageMonotone
open Set
open scoped Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- **Monotonicity of subgradient images under comparison** (Gutiérrez, *The Monge–Ampère
equation*, Lemma 1.4.1; weak Letwin route, comparison principle): if `u ≤ v` on a
bounded open `Ω` and `u = v` on its frontier, then `∂v(Ω) ⊆ ∂u(Ω)`. -/
theorem solution
    [FiniteDimensional ℝ E] {u v : E → ℝ} (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (heq : ∀ x ∈ frontier Ω, u x = v x) : FunctionalInequalities.Analysis.subgradientImage v Ω ⊆ FunctionalInequalities.Analysis.subgradientImage u Ω := by
  rintro p ⟨x₀, hx₀, hp⟩
  let w : E → ℝ := fun z => v x₀ + ⟪p, z - x₀⟫ - u z
  have huc : Continuous u := by
    apply continuousOn_univ.mp
    exact hu.continuousOn isOpen_univ
  have hvc : Continuous v := by
    apply continuousOn_univ.mp
    exact hv.continuousOn isOpen_univ
  have hlin : Continuous (fun z : E => ⟪p, z - x₀⟫) := by
    fun_prop
  have hwc : Continuous w := by
    have hwc' : Continuous ((fun _ : E => v x₀) + (fun z : E => ⟪p, z - x₀⟫) - u) :=
      (continuous_const.add hlin).sub huc
    convert hwc' using 1
    ext z
    simp [w]
  have hcompact : IsCompact (closure Ω) := hb.isCompact_closure
  have hnonempty : (closure Ω).Nonempty :=
    ⟨x₀, subset_closure hx₀⟩
  obtain ⟨x₁, hx₁, hmax⟩ :=
    hcompact.exists_isMaxOn hnonempty hwc.continuousOn
  by_cases hx₁Ω : x₁ ∈ Ω
  · refine ⟨x₁, hx₁Ω, ?_⟩
    exact FunctionalInequalities.Analysis.support_of_max_readable hu hΩ x₀ x₁ p (v x₀) hx₁Ω (by
      simpa [w] using hmax)
  · have hwx₀ : 0 ≤ w x₀ := by
      simpa [w] using hle x₀ hx₀
    have hax : 0 ≤ w x₁ :=
      hwx₀.trans (hmax (subset_closure hx₀))
    have hfront : x₁ ∈ frontier Ω := by
      rw [← closure_sdiff_interior]
      exact ⟨hx₁, by simpa [hΩ.interior_eq] using hx₁Ω⟩
    have heqx₁ : u x₁ = v x₁ := heq x₁ hfront
    have hupper : w x₁ ≤ 0 := by
      have hp₁ := hp x₁
      rw [← heqx₁] at hp₁
      dsimp [w]
      linarith
    have hax0 : w x₁ = 0 := le_antisymm hupper hax
    have hwx₀zero : w x₀ = 0 := by
      apply le_antisymm
      · simpa [hax0] using hmax (subset_closure hx₀)
      · exact hwx₀
    have hmax₀ : IsMaxOn w (closure Ω) x₀ := by
      intro z hz
      have hzmax := hmax hz
      simpa [hax0, hwx₀zero] using hzmax
    refine ⟨x₀, hx₀, ?_⟩
    exact FunctionalInequalities.Analysis.support_of_max_readable hu hΩ x₀ x₀ p (v x₀) hx₀ (by
      simpa [w] using hmax₀)
