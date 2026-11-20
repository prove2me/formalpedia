-- Prove2me | solution 1 for EgorovsTheorem.egorov_theorem
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:19:41.119623+00:00
-- url     : https://prove2.me/submissions/8fe556c6-0e88-4bd1-9bce-b5ab8c6f3dcb

import Mathlib

open MeasureTheory Filter Topology Set

namespace EgorovsTheorem

theorem _root_.solution
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (E : Set X) (hE : MeasurableSet E) (hμE : μ E < ⊤)
    (f : ℕ → X → EReal)
    (hf : ∀ k, Measurable (fun x : ↥E => f k ↑x))
    (hf_fin : ∀ k, ∀ᵐ x ∂(μ.restrict E), f k x ≠ ⊥ ∧ f k x ≠ ⊤)
    (g : X → EReal)
    (hconv : ∀ᵐ x ∂(μ.restrict E), g x ≠ ⊥ ∧ g x ≠ ⊤ ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∃ A : Set X, A ⊆ E ∧ MeasurableSet A ∧
      μ (E \ A) < ENNReal.ofReal ε ∧
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k ≥ N, ∀ x ∈ A,
        g x - (δ : EReal) < f k x ∧ f k x < g x + (δ : EReal) := by
  have hf' : ∀ k, AEMeasurable (f k) (μ.restrict E) := fun k =>
    (aemeasurable_restrict_iff_comap_subtype hE).mpr (hf k).aemeasurable
  clear hf
  intro ε hε
  set ν := μ.restrict E with hμ
  haveI : IsFiniteMeasure ν := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hμE⟩
  have hmt : Measurable EReal.toReal := by fun_prop
  -- real limit
  have hG : AEMeasurable (fun x => (g x).toReal) ν := by
    refine aemeasurable_of_tendsto_metrizable_ae' (f := fun k x => (f k x).toReal)
      (fun k => hmt.comp_aemeasurable (hf' k)) ?_
    filter_upwards [hconv] with x hx
    exact (EReal.tendsto_toReal hx.2.1 hx.1).comp hx.2.2
  set Gm := hG.mk _ with hGm
  set F : ℕ → X → EReal := fun k => (hf' k).mk _ with hF
  let Pg : X → Prop := fun x =>
    (∀ k, f k x = F k x) ∧ (∀ k, f k x ≠ ⊥ ∧ f k x ≠ ⊤) ∧ g x ≠ ⊥ ∧ g x ≠ ⊤ ∧
      (g x).toReal = Gm x ∧ Tendsto (fun k => f k x) atTop (𝓝 (g x))
  have hPg : ∀ᵐ x ∂ν, Pg x := by
    have h1 : ∀ᵐ x ∂ν, ∀ k, f k x = F k x := ae_all_iff.mpr fun k => (hf' k).ae_eq_mk
    have h2 : ∀ᵐ x ∂ν, ∀ k, f k x ≠ ⊥ ∧ f k x ≠ ⊤ := ae_all_iff.mpr hf_fin
    filter_upwards [h1, h2, hconv, hG.ae_eq_mk] with x a b c d
    exact ⟨a, b, c.1, c.2.1, d, c.2.2⟩
  obtain ⟨N0, hN0sub, hN0m, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hPg)
  -- Egorov
  have hφm : ∀ k, StronglyMeasurable (fun x => (F k x).toReal) :=
    fun k => (hmt.comp (hf' k).measurable_mk).stronglyMeasurable
  have hconvR : ∀ᵐ x ∂ν, Tendsto (fun k => (F k x).toReal) atTop (𝓝 (Gm x)) := by
    filter_upwards [hPg] with x hx
    obtain ⟨a, b, c, d, e, h⟩ := hx
    have := (EReal.tendsto_toReal d c).comp h
    rw [e] at this
    convert this using 2 with k
    simp [a k]
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨t, htm, htμ, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto' hφm
    hG.measurable_mk.stronglyMeasurable hconvR hε3
  set K0 := E \ (t ∪ N0) with hK0
  have hK0m : MeasurableSet K0 := hE.diff (htm.union hN0m)
  refine ⟨K0, diff_subset, hK0m, ?_, ?_⟩
  · have ht : μ (E ∩ t) ≤ ENNReal.ofReal (ε / 3) := by
      rw [inter_comm, ← Measure.restrict_apply htm]; exact htμ
    have hN : μ (E ∩ N0) = 0 := by
      rw [inter_comm, ← Measure.restrict_apply hN0m]; exact hN0
    have hsub : E \ K0 ⊆ (E ∩ t) ∪ (E ∩ N0) := by
      intro x ⟨hxE, hxK⟩
      by_cases h2 : x ∈ t
      · exact Or.inl ⟨hxE, h2⟩
      · by_cases h3 : x ∈ N0
        · exact Or.inr ⟨hxE, h3⟩
        · exact absurd ⟨hxE, fun h => h.elim h2 h3⟩ hxK
    calc μ (E \ K0) ≤ μ ((E ∩ t) ∪ (E ∩ N0)) := measure_mono hsub
      _ ≤ μ (E ∩ t) + μ (E ∩ N0) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (ε / 3) := by rw [hN, add_zero]; exact ht
      _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)
  · intro δ hδ
    have hu := Metric.tendstoUniformlyOn_iff.mp hunif δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp hu
    refine ⟨N, fun k hk x hx => ?_⟩
    have hxK := hx
    have hxt : x ∈ tᶜ := fun h => hxK.2 (Or.inl h)
    have hxP : Pg x := by
      by_contra h
      exact hxK.2 (Or.inr (hN0sub h))
    obtain ⟨a, b, c, d, e, -⟩ := hxP
    have hd := hN k hk x hxt
    rw [Real.dist_eq] at hd
    change |Gm x - (F k x).toReal| < δ at hd
    rw [← e, ← a k] at hd
    have hg' : g x = ((g x).toReal : EReal) := (EReal.coe_toReal d c).symm
    have hf' : f k x = ((f k x).toReal : EReal) := (EReal.coe_toReal (b k).2 (b k).1).symm
    rw [hg', hf', ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff]
    constructor <;> [linarith [(abs_lt.mp hd).2]; linarith [(abs_lt.mp hd).1]]

end EgorovsTheorem
