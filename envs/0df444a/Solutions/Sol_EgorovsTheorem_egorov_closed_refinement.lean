-- Prove2me | solution 1 for EgorovsTheorem.egorov_closed_refinement
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T09:17:57.393588+00:00
-- url     : https://prove2.me/submissions/92f0d584-5396-4451-8227-60a9c81cdf34

import Mathlib

open MeasureTheory Filter Topology Set

namespace EgorovsTheorem

theorem _root_.solution
    (n : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (hE : NullMeasurableSet E volume)
    (hμE : volume E < ⊤)
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ∀ k, AEMeasurable (f k) (volume.restrict E))
    (hf_fin : ∀ k, ∀ᵐ x ∂(volume.restrict E), f k x ≠ ⊥ ∧ f k x ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin n) → EReal)
    (hconv : ∀ᵐ x ∂(volume.restrict E), g x ≠ ⊥ ∧ g x ≠ ⊤ ∧
      Tendsto (fun k => f k x) atTop (𝓝 (g x))) :
    ∀ ε : ℝ, 0 < ε → ∃ A : Set (EuclideanSpace ℝ (Fin n)), A ⊆ E ∧ IsClosed A ∧
      volume (E \ A) < ENNReal.ofReal ε ∧
      ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ k ≥ N, ∀ x ∈ A,
        g x - (δ : EReal) < f k x ∧ f k x < g x + (δ : EReal) := by
  intro ε hε
  set μ := volume.restrict E with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hμE⟩
  have hmt : Measurable EReal.toReal := by fun_prop
  -- real limit
  have hG : AEMeasurable (fun x => (g x).toReal) μ := by
    refine aemeasurable_of_tendsto_metrizable_ae' (f := fun k x => (f k x).toReal)
      (fun k => hmt.comp_aemeasurable (hf k)) ?_
    filter_upwards [hconv] with x hx
    exact (EReal.tendsto_toReal hx.2.1 hx.1).comp hx.2.2
  set Gm := hG.mk _ with hGm
  set F : ℕ → EuclideanSpace ℝ (Fin n) → EReal := fun k => (hf k).mk _ with hF
  let Pg : EuclideanSpace ℝ (Fin n) → Prop := fun x =>
    (∀ k, f k x = F k x) ∧ (∀ k, f k x ≠ ⊥ ∧ f k x ≠ ⊤) ∧ g x ≠ ⊥ ∧ g x ≠ ⊤ ∧
      (g x).toReal = Gm x ∧ Tendsto (fun k => f k x) atTop (𝓝 (g x))
  have hPg : ∀ᵐ x ∂μ, Pg x := by
    have h1 : ∀ᵐ x ∂μ, ∀ k, f k x = F k x := ae_all_iff.mpr fun k => (hf k).ae_eq_mk
    have h2 : ∀ᵐ x ∂μ, ∀ k, f k x ≠ ⊥ ∧ f k x ≠ ⊤ := ae_all_iff.mpr hf_fin
    filter_upwards [h1, h2, hconv, hG.ae_eq_mk] with x a b c d
    exact ⟨a, b, c.1, c.2.1, d, c.2.2⟩
  obtain ⟨N0, hN0sub, hN0m, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hPg)
  -- Egorov
  have hφm : ∀ k, StronglyMeasurable (fun x => (F k x).toReal) :=
    fun k => (hmt.comp (hf k).measurable_mk).stronglyMeasurable
  have hconvR : ∀ᵐ x ∂μ, Tendsto (fun k => (F k x).toReal) atTop (𝓝 (Gm x)) := by
    filter_upwards [hPg] with x hx
    obtain ⟨a, b, c, d, e, h⟩ := hx
    have := (EReal.tendsto_toReal d c).comp h
    rw [e] at this
    convert this using 2 with k
    simp [a k]
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨t, htm, htμ, hunif⟩ := tendstoUniformlyOn_of_ae_tendsto' hφm
    hG.measurable_mk.stronglyMeasurable hconvR hε3
  obtain ⟨E', hE'sub, hE'm, hE'ae⟩ := hE.exists_measurable_subset_ae_eq
  set K0 := E' \ (t ∪ N0) with hK0
  have hK0m : MeasurableSet K0 := hE'm.diff (htm.union hN0m)
  have hK0fin : volume K0 ≠ ⊤ :=
    ((measure_mono (diff_subset.trans hE'sub)).trans_lt hμE).ne
  obtain ⟨A, hAsub, hAcl, hAμ⟩ := hK0m.exists_isClosed_diff_lt hK0fin
    (ENNReal.ofReal_pos.mpr hε3).ne'
  refine ⟨A, hAsub.trans (diff_subset.trans hE'sub), hAcl, ?_, ?_⟩
  · have hEE' : volume (E \ E') = 0 := by
      have := hE'ae
      rw [ae_eq_set] at this
      exact this.2
    have ht : volume (E ∩ t) ≤ ENNReal.ofReal (ε / 3) := by
      rw [inter_comm, ← Measure.restrict_apply htm]; exact htμ
    have hN : volume (E ∩ N0) = 0 := by
      rw [inter_comm, ← Measure.restrict_apply hN0m]; exact hN0
    have hsub : E \ A ⊆ (E \ E') ∪ (E ∩ t) ∪ (E ∩ N0) ∪ (K0 \ A) := by
      intro x ⟨hxE, hxA⟩
      by_cases h1 : x ∈ E'
      · by_cases h2 : x ∈ t
        · exact Or.inl (Or.inl (Or.inr ⟨hxE, h2⟩))
        · by_cases h3 : x ∈ N0
          · exact Or.inl (Or.inr ⟨hxE, h3⟩)
          · exact Or.inr ⟨⟨h1, fun h => h.elim h2 h3⟩, hxA⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hxE, h1⟩))
    calc volume (E \ A) ≤ volume ((E \ E') ∪ (E ∩ t) ∪ (E ∩ N0) ∪ (K0 \ A)) := measure_mono hsub
      _ ≤ volume (E \ E') + volume (E ∩ t) + volume (E ∩ N0) + volume (K0 \ A) := by
          refine (measure_union_le _ _).trans ?_
          gcongr
          refine (measure_union_le _ _).trans ?_
          gcongr
          exact measure_union_le _ _
      _ < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) := by
          rw [hEE', hN, zero_add, add_zero]
          have h3 : ENNReal.ofReal (ε / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
          calc volume (E ∩ t) + volume (K0 \ A) < ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) :=
                ENNReal.add_lt_add_of_le_of_lt (ht.trans_lt ENNReal.ofReal_lt_top).ne ht hAμ
            _ ≤ _ := le_self_add
      _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε3.le hε3.le, ← ENNReal.ofReal_add (by positivity) hε3.le]
          congr 1; ring
  · intro δ hδ
    have hu := Metric.tendstoUniformlyOn_iff.mp hunif δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp hu
    refine ⟨N, fun k hk x hx => ?_⟩
    have hxK := hAsub hx
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
