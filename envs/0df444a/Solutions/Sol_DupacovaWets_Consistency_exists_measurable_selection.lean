-- Prove2me | solution 1 for DupacovaWets.Consistency.exists_measurable_selection
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T06:26:00.976575+00:00
-- url     : https://prove2.me/submissions/5403641d-d93f-47f3-a13e-2d6f84f229aa

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_Multifunction
open MeasureTheory Filter Topology Set
open DupacovaWets.Consistency

namespace DW7Aux

variable {T : Type*} [MeasurableSpace T] {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem hit_meas (G : T → Set E) (hG : IsMeasurableMultifunction G) (F : Set E) (hF : IsClosed F) :
    MeasurableSet {t | (G t ∩ F).Nonempty} := hG F hF

/-- One lexicographic step: minimize a continuous `ℓ` over `G t`. -/
theorem step (G : T → Set E) (hGc : ∀ t, IsClosed (G t)) (hG : IsMeasurableMultifunction G)
    (ℓ : E → ℝ) (hℓ : Continuous ℓ) (hcpt : ∀ t a, IsCompact (G t ∩ {y | ℓ y ≤ a})) :
    ∃ c : T → ℝ, Measurable c ∧
      (∀ t, (G t).Nonempty → (∃ y ∈ G t, ℓ y = c t) ∧ ∀ y ∈ G t, c t ≤ ℓ y) ∧
      IsMeasurableMultifunction (fun t => G t ∩ {y | ℓ y = c t}) := by
  classical
  have hmin : ∀ t, (G t).Nonempty → ∃ y ∈ G t, ∀ z ∈ G t, ℓ y ≤ ℓ z := by
    intro t ⟨y0, hy0⟩
    obtain ⟨y, hy, hmin⟩ := (hcpt t (ℓ y0)).exists_isMinOn ⟨y0, hy0, (le_refl (ℓ y0) : y0 ∈ {y | ℓ y ≤ ℓ y0})⟩ hℓ.continuousOn
    refine ⟨y, hy.1, fun z hz => ?_⟩
    by_cases hzl : ℓ z ≤ ℓ y0
    · exact hmin ⟨hz, hzl⟩
    · push_neg at hzl; exact (hmin ⟨hy0, (le_refl (ℓ y0) : y0 ∈ {y | ℓ y ≤ ℓ y0})⟩).trans hzl.le
  let c : T → ℝ := fun t => if h : (G t).Nonempty then ℓ (hmin t h).choose else 0
  have hc : ∀ t, (G t).Nonempty → (∃ y ∈ G t, ℓ y = c t) ∧ ∀ y ∈ G t, c t ≤ ℓ y := by
    intro t h
    have hs := (hmin t h).choose_spec
    refine ⟨⟨_, hs.1, by simp [c, h]⟩, fun y hy => ?_⟩
    simpa [c, h] using hs.2 y hy
  have hdom : MeasurableSet {t | (G t).Nonempty} := by
    simpa using hG univ isClosed_univ
  have hcm : Measurable c := by
    refine measurable_of_Iic fun a => ?_
    have heq : c ⁻¹' Iic a = ({t | (G t ∩ {y | ℓ y ≤ a}).Nonempty}) ∪
        ({t | (G t).Nonempty}ᶜ ∩ {_t | (0 : ℝ) ≤ a}) := by
      ext t
      simp only [mem_preimage, mem_Iic, mem_union, mem_setOf_eq, mem_inter_iff, mem_compl_iff]
      by_cases h : (G t).Nonempty
      · obtain ⟨⟨y, hy, hyc⟩, hle⟩ := hc t h
        constructor
        · intro hca; exact Or.inl ⟨y, hy, by simp only [mem_setOf_eq]; linarith⟩
        · rintro (⟨z, hz, hza⟩ | ⟨h', _⟩)
          · exact (hle z hz).trans hza
          · exact absurd h h'
      · have : c t = 0 := by simp [c, h]
        rw [this]
        constructor
        · intro h0; exact Or.inr ⟨h, h0⟩
        · rintro (⟨z, hz, _⟩ | ⟨_, h0⟩)
          · exact absurd ⟨z, hz⟩ h
          · exact h0
    rw [heq]
    exact (hG _ (isClosed_le hℓ continuous_const)).union (hdom.compl.inter (MeasurableSet.const _))
  refine ⟨c, hcm, hc, ?_⟩
  intro F hF
  have heq : {t | ((G t ∩ {y | ℓ y = c t}) ∩ F).Nonempty} =
      ⋂ j : ℕ, ⋃ q : ℚ, ({t | (q : ℝ) < c t + 1 / ((j : ℝ) + 1)} ∩
        {t | (G t ∩ (F ∩ {y | ℓ y ≤ q})).Nonempty}) := by
    ext t
    simp only [mem_setOf_eq, mem_iInter, mem_iUnion, mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hy, hyc⟩, hyF⟩ j
      have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show c t < c t + 1 / ((j : ℝ) + 1) by linarith)
      refine ⟨q, hq2, y, hy, hyF, ?_⟩
      simp only [mem_setOf_eq]; rw [hyc]; exact hq1.le
    · intro h
      choose q hq y hy using h
      have hyG : ∀ j, y j ∈ G t ∩ {z | ℓ z ≤ c t + 1} := by
        intro j
        refine ⟨(hy j).1, ?_⟩
        have h1 : ℓ (y j) ≤ q j := (hy j).2.2
        have h2 : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        simp only [mem_setOf_eq]; linarith [hq j]
      obtain ⟨a, ha, ψ, hψ, hlim⟩ := (hcpt t (c t + 1)).tendsto_subseq hyG
      have haF : a ∈ F := hF.mem_of_tendsto hlim (Eventually.of_forall fun j => (hy (ψ j)).2.1)
      have hle : ℓ a ≤ c t := by
        have h1 : Tendsto (fun j => ℓ (y (ψ j))) atTop (𝓝 (ℓ a)) := (hℓ.tendsto a).comp hlim
        have h2 : Tendsto (fun j => c t + 1 / ((ψ j : ℝ) + 1)) atTop (𝓝 (c t + 0)) :=
          tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop)
        rw [add_zero] at h2
        refine le_of_tendsto_of_tendsto' h1 h2 fun j => ?_
        exact ((hy (ψ j)).2.2).trans (hq (ψ j)).le
      have hne : (G t).Nonempty := ⟨a, ha.1⟩
      exact ⟨a, ⟨ha.1, le_antisymm hle ((hc t hne).2 a ha.1)⟩, haF⟩
  rw [heq]
  refine MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_
  exact (measurableSet_lt measurable_const (hcm.add measurable_const)).inter
    (hG _ (hF.inter (isClosed_le hℓ continuous_const)))

end DW7Aux

open DW7Aux in
theorem solution {T : Type*} [MeasurableSpace T] {m : ℕ}
    (Γ : T → Set (EuclideanSpace ℝ (Fin m))) (hclosed : ∀ t, IsClosed (Γ t))
    (hmeas : IsMeasurableMultifunction Γ) :
    MeasurableSet {t | (Γ t).Nonempty} ∧
      ∃ x : T → EuclideanSpace ℝ (Fin m), Measurable x ∧ ∀ t, (Γ t).Nonempty → x t ∈ Γ t := by
  classical
  have hdom : MeasurableSet {t | (Γ t).Nonempty} := by simpa using hmeas univ isClosed_univ
  refine ⟨hdom, ?_⟩
  -- first step: minimize the norm
  obtain ⟨c0, -, hc0, hG1m⟩ := step Γ hclosed hmeas (fun y => ‖y‖) continuous_norm (by
    intro t a
    have : Γ t ∩ {y | ‖y‖ ≤ a} = Γ t ∩ Metric.closedBall 0 a := by
      ext y; simp
    rw [this]; exact (isCompact_closedBall 0 a).inter_left (hclosed t))
  have claim : ∀ k : ℕ, k ≤ m → ∃ G : T → Set (EuclideanSpace ℝ (Fin m)),
      (∀ t, IsCompact (G t)) ∧ IsMeasurableMultifunction G ∧ (∀ t, G t ⊆ Γ t) ∧
      (∀ t, (Γ t).Nonempty → (G t).Nonempty) ∧
      ∃ c : ℕ → T → ℝ, ∀ t, ∀ y ∈ G t, ∀ j : Fin m, j.val < k → y j = c j.val t := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun t => Γ t ∩ {y | ‖y‖ = c0 t}, fun t => ?_, hG1m, fun t => inter_subset_left,
        fun t h => ?_, fun _ _ => 0, fun t y _ j hj => absurd hj (Nat.not_lt_zero _)⟩
      · have : Γ t ∩ {y | ‖y‖ = c0 t} ⊆ Metric.closedBall 0 (c0 t) := by
          intro y hy; simp [hy.2.le]
        exact (isCompact_closedBall 0 (c0 t)).of_isClosed_subset
          ((hclosed t).inter (isClosed_eq continuous_norm continuous_const)) this
      · obtain ⟨⟨y, hy, hyc⟩, -⟩ := hc0 t h
        exact ⟨y, hy, hyc⟩
    | succ k ih =>
      intro hk
      obtain ⟨G, hGc, hGm, hGΓ, hGne, c, hc⟩ := ih (Nat.le_of_succ_le hk)
      let i₀ : Fin m := ⟨k, hk⟩
      have hℓ : Continuous (fun y : EuclideanSpace ℝ (Fin m) => y i₀) :=
        (EuclideanSpace.proj (𝕜 := ℝ) i₀).continuous
      obtain ⟨c', -, hc', hG'm⟩ := step G (fun t => (hGc t).isClosed) hGm _ hℓ
        (fun t a => (hGc t).inter_right (isClosed_le hℓ continuous_const))
      refine ⟨fun t => G t ∩ {y | y i₀ = c' t},
        fun t => (hGc t).inter_right (isClosed_eq hℓ continuous_const), hG'm,
        fun t => inter_subset_left.trans (hGΓ t), fun t h => ?_,
        fun j t => if j = k then c' t else c j t, ?_⟩
      · obtain ⟨⟨y, hy, hyc⟩, -⟩ := hc' t (hGne t h)
        exact ⟨y, hy, hyc⟩
      · intro t y hy j hj
        by_cases hjk : j.val = k
        · have : j = i₀ := Fin.ext hjk
          subst this
          simp only [if_pos hjk]
          exact hy.2
        · simp only [if_neg hjk]
          exact hc t y hy.1 j (by omega)
  obtain ⟨G, hGc, hGm, hGΓ, hGne, c, hc⟩ := claim m le_rfl
  have hsub : ∀ t, ∀ y ∈ G t, ∀ z ∈ G t, y = z := by
    intro t y hy z hz
    ext j
    rw [hc t y hy j j.isLt, hc t z hz j j.isLt]
  let x : T → EuclideanSpace ℝ (Fin m) := fun t => if h : (G t).Nonempty then h.some else 0
  have hxG : ∀ t, (G t).Nonempty → x t ∈ G t := by
    intro t h; simp only [x, dif_pos h]; exact h.some_mem
  refine ⟨x, ?_, fun t h => hGΓ t (hxG t (hGne t h))⟩
  have hGdom : MeasurableSet {t | (G t).Nonempty} := by simpa using hGm univ isClosed_univ
  refine measurable_of_isClosed fun F hF => ?_
  have heq : x ⁻¹' F = {t | (G t ∩ F).Nonempty} ∪ ({t | (G t).Nonempty}ᶜ ∩ {_t | (0 : EuclideanSpace ℝ (Fin m)) ∈ F}) := by
    ext t
    simp only [mem_preimage, mem_union, mem_setOf_eq, mem_inter_iff, mem_compl_iff]
    by_cases h : (G t).Nonempty
    · constructor
      · intro hx; exact Or.inl ⟨x t, hxG t h, hx⟩
      · rintro (⟨y, hy, hyF⟩ | ⟨h', _⟩)
        · rw [hsub t (x t) (hxG t h) y hy]; exact hyF
        · exact absurd h h'
    · have : x t = 0 := by simp only [x, dif_neg h]
      rw [this]
      constructor
      · intro h0; exact Or.inr ⟨h, h0⟩
      · rintro (⟨y, hy, _⟩ | ⟨_, h0⟩)
        · exact absurd ⟨y, hy⟩ h
        · exact h0
  rw [heq]
  exact (hGm F hF).union (hGdom.compl.inter (MeasurableSet.const _))
