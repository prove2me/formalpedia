-- Prove2me | solution 1 for DupacovaWets.Consistency.consistency_of_measurable_estimates
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:16:56.209462+00:00
-- url     : https://prove2.me/submissions/a0f6e2ff-bcd2-4c8f-804d-ce844b3768cf

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect
import Definitions.Def_DupacovaWets_Consistency_ExtendedFunctions
import Definitions.Def_DupacovaWets_Consistency_Assumptions
import Definitions.Def_DupacovaWets_Consistency_Multifunction
import Theorems.Thm_DupacovaWets_Consistency_epiConverges_inf_argmin
import Theorems.Thm_DupacovaWets_Consistency_expectFn_epiConverges
import Theorems.Thm_DupacovaWets_Consistency_argmin_measurable
import Theorems.Thm_DupacovaWets_Consistency_exists_measurable_selection
open MeasureTheory Filter Topology
open DupacovaWets.Consistency

theorem solution {n : ℕ} {Ξ : Type*} [TopologicalSpace Ξ] [PolishSpace Ξ] [MeasurableSpace Ξ] [BorelSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    {Z : Type*} [mZ : MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (𝔽 : Filtration ℕ mZ) (Pν : ℕ → Z → Measure Ξ)
    (f : EuclideanSpace ℝ (Fin n) → Ξ → EReal) (S : Set (EuclideanSpace ℝ (Fin n)))
    (h34 : Assumption3_4 f S) (h35 : Assumption3_5 f S P μ 𝔽 Pν)
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : IsCompact D)
    (hDne : ∀ k, ∀ᵐ ζ ∂μ, (argminSet (expectFn (Pν k ζ) f) ∩ D).Nonempty)
    (xstar : EuclideanSpace ℝ (Fin n)) (hx : argminSet (expectFn P f) ∩ D = {xstar}) :
    (∃ x : ℕ → Z → EuclideanSpace ℝ (Fin n), (∀ k, Measurable[𝔽 k] (x k)) ∧
        (∀ᵐ ζ ∂μ, ∀ k, x k ζ ∈ argminSet (expectFn (Pν k ζ) f)) ∧
        (∀ᵐ ζ ∂μ, Tendsto (fun k => x k ζ) atTop (𝓝 xstar))) ∧
      ∀ᵐ ζ ∂μ, Tendsto (fun k => ⨅ y, expectFn (Pν k ζ) f y) atTop (𝓝 (⨅ y, expectFn P f y)) := by
  classical
  obtain ⟨Z₀, hZ₀m, hZ₀, hcl, hmeas⟩ :=
    argmin_measurable P μ 𝔽 Pν f S h34 h35
  have hepi := expectFn_epiConverges P μ 𝔽 Pν f S h34 h35
  -- measurable selections on the subtype `Z₀`
  have hsel : ∀ k, ∃ h : Z → EuclideanSpace ℝ (Fin n), Measurable[𝔽 k] h ∧
      ∀ ζ ∈ Z₀, (argminSet (expectFn (Pν k ζ) f) ∩ D).Nonempty →
        h ζ ∈ argminSet (expectFn (Pν k ζ) f) ∩ D := by
    intro k
    letI mT : MeasurableSpace Z₀ := MeasurableSpace.comap Subtype.val (𝔽 k)
    let Γ : Z₀ → Set (EuclideanSpace ℝ (Fin n)) :=
      fun t => argminSet (expectFn (Pν k t.1) f) ∩ D
    have hΓc : ∀ t, IsClosed (Γ t) := fun t => (hcl t.1 t.2 k).inter hD.isClosed
    have hΓm : IsMeasurableMultifunction Γ := by
      intro F hF
      obtain ⟨B, hB, hBeq⟩ := hmeas k (D ∩ F) (hD.isClosed.inter hF)
      have : {t : Z₀ | (Γ t ∩ F).Nonempty} = Subtype.val ⁻¹' B := by
        ext t
        have h := congrArg (fun s : Set Z => t.1 ∈ s) hBeq
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, eq_iff_iff] at h
        simp only [Set.mem_setOf_eq, Set.mem_preimage, Γ, Set.inter_assoc]
        constructor
        · intro hne; exact (h.mp ⟨t.2, hne⟩).2
        · intro hb; exact (h.mpr ⟨t.2, hb⟩).2
      rw [this]
      exact ⟨B, hB, rfl⟩
    obtain ⟨-, x', hx'm, hx'⟩ := exists_measurable_selection Γ hΓc hΓm
    by_cases hne : Nonempty (EuclideanSpace ℝ (Fin n))
    · obtain ⟨h, hm, rfl⟩ := Measurable.exists_eq_measurable_comp (mY := 𝔽 k) (f := (Subtype.val : Z₀ → Z)) (g := x') hx'm
      exact ⟨h, hm, fun ζ hζ hn => hx' ⟨ζ, hζ⟩ hn⟩
    · exact absurd ⟨0⟩ hne
  choose x hxm hxsel using hsel
  -- the good set
  have hgood : ∀ᵐ ζ ∂μ, ζ ∈ Z₀ ∧
      (∀ k, (argminSet (expectFn (Pν k ζ) f) ∩ D).Nonempty) ∧
      EpiConverges (fun k => expectFn (Pν k ζ) f) (expectFn P f) := by
    have h0 : ∀ᵐ ζ ∂μ, ζ ∈ Z₀ := by
      rw [ae_iff]; simpa [Set.compl_def] using hZ₀
    filter_upwards [h0, ae_all_iff.mpr hDne, hepi] with ζ h1 h2 h3
    exact ⟨h1, h2, h3.1⟩
  have hmem : ∀ᵐ ζ ∂μ, ∀ k, x k ζ ∈ argminSet (expectFn (Pν k ζ) f) ∩ D := by
    filter_upwards [hgood] with ζ hζ k
    exact hxsel k ζ hζ.1 (hζ.2.1 k)
  have hconv : ∀ᵐ ζ ∂μ, Tendsto (fun k => x k ζ) atTop (𝓝 xstar) := by
    filter_upwards [hgood, hmem] with ζ hζ hm
    have M0 := (epiConverges_inf_argmin _ _ hζ.2.2).2.1
    by_contra hnot
    rw [tendsto_atTop_nhds] at hnot
    push_neg at hnot
    obtain ⟨U, hxU, hU, hfreq⟩ := hnot
    have hfr : ∃ᶠ k in atTop, x k ζ ∉ U := by
      rw [frequently_atTop]; intro N
      obtain ⟨k, hk, hkU⟩ := hfreq N
      exact ⟨k, hk, hkU⟩
    obtain ⟨φ, hφ, hφU⟩ := extraction_of_frequently_atTop hfr
    obtain ⟨y, hyD, ψ, hψ, hlim⟩ := hD.tendsto_subseq (fun j => (hm (φ j)).2)
    have hy := (M0 (φ ∘ ψ) (hφ.comp hψ) (fun j => x (φ (ψ j)) ζ) y
      (fun j => (hm (φ (ψ j))).1) hlim).1
    have hyx : y = xstar := by
      have : y ∈ argminSet (expectFn P f) ∩ D := ⟨hy, hyD⟩
      rw [hx] at this; exact this
    subst hyx
    have := (tendsto_atTop_nhds.mp hlim) U hxU hU
    obtain ⟨N, hN⟩ := this
    exact hφU (ψ N) (hN N le_rfl)
  refine ⟨⟨x, hxm, ?_, hconv⟩, ?_⟩
  · filter_upwards [hmem] with ζ h k using (h k).1
  · filter_upwards [hgood, hmem, hconv] with ζ hζ hm hc
    have M0 := (epiConverges_inf_argmin _ _ hζ.2.2).2.1
    exact (M0 id strictMono_id (fun k => x k ζ) xstar (fun k => (hm k).1) hc).2
