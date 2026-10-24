-- Prove2me | solution 1 for ContextualAuctions.Existence.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:17:40.071236+00:00
-- url     : https://prove2.me/submissions/c7d055ff-e80d-45ea-937e-2dfa9d590e3e

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Theorems.Thm_ContextualAuctions_Existence_proposition_1
import Theorems.Thm_ContextualAuctions_Existence_proposition_2

open MeasureTheory ContextualAuctions.Existence

theorem solution (M : Model) (hM : M.Standing) :
    ∃ μ : (Fin M.d → ℝ) × ℝ → ℝ, IsPacing M μ ∧ IsSFPE M (beta M μ) := by
  classical
  have := hM.probG
  obtain ⟨μ, hμ, hae⟩ := proposition_2 M hM
  obtain ⟨Θ', -, hΘm, hG, hopt⟩ := proposition_1 M hM
  refine ⟨μ, hμ, ?_, ?_⟩
  · -- joint measurability of β^μ
    have hval : Measurable (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => val q.1 q.2) := by
      unfold val
      apply Finset.measurable_sum
      intro i _
      exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).mul
        ((measurable_pi_apply i).comp measurable_snd)
    have hpaced : Measurable
        (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => paced μ q.1 q.2) := by
      unfold paced
      exact hval.div (measurable_const.add (hμ.1.comp measurable_fst))
    -- the set S = {((α, x), θ) | paced μ θ α ≤ x}
    have hS : MeasurableSet
        {p : ((Fin M.d → ℝ) × ℝ) × ((Fin M.d → ℝ) × ℝ) | paced μ p.2 p.1.1 ≤ p.1.2} := by
      apply measurableSet_le
      · exact hpaced.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst))
      · exact measurable_snd.comp measurable_fst
    have hH : Measurable (fun p : (Fin M.d → ℝ) × ℝ => H M μ p.1 p.2) := by
      unfold H
      have := measurable_measure_prodMk_left (ν := M.G) hS
      exact (this.ennreal_toReal).pow_const _
    -- integral part
    have hint1 : ∀ (a b : ((Fin M.d → ℝ) × ℝ) → ℝ), Measurable a → Measurable b →
        StronglyMeasurable (fun p : (Fin M.d → ℝ) × ℝ =>
          ∫ s in Set.Ioc (a p) (b p), H M μ p.1 s) := by
      intro a b ha hb
      have hg : Measurable (fun q : ((Fin M.d → ℝ) × ℝ) × ℝ =>
          Set.indicator {q : ((Fin M.d → ℝ) × ℝ) × ℝ | a q.1 < q.2 ∧ q.2 ≤ b q.1}
            (fun q => H M μ q.1.1 q.2) q) := by
        apply Measurable.indicator
        · exact hH.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
        · exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
            (measurableSet_le measurable_snd (hb.comp measurable_fst))
      have := (hg.stronglyMeasurable).integral_prod_right' (ν := (volume : Measure ℝ))
      convert this using 2 with p
      rw [← integral_indicator measurableSet_Ioc]
      congr 1
    have hI : Measurable (fun p : (Fin M.d → ℝ) × ℝ => ∫ s in (M.r p.1)..p.2, H M μ p.1 s) := by
      have h1 := (hint1 (fun p => M.r p.1) (fun p => p.2)
        (hM.measurable_r.comp measurable_fst) measurable_snd).measurable
      have h2 := (hint1 (fun p => p.2) (fun p => M.r p.1) measurable_snd
        (hM.measurable_r.comp measurable_fst)).measurable
      have := h1.sub h2
      convert this using 1
      funext p
      simp [intervalIntegral]
    have hsig : Measurable (fun p : (Fin M.d → ℝ) × ℝ => sigma M μ p.1 p.2) := by
      unfold sigma
      refine Measurable.ite (measurableSet_lt measurable_snd
        (hM.measurable_r.comp measurable_fst)) measurable_snd ?_
      refine Measurable.ite (measurableSet_eq_fun hH measurable_const) measurable_const ?_
      exact measurable_snd.sub (hI.div hH)
    have : Function.uncurry (beta M μ) =
        (fun p : (Fin M.d → ℝ) × ℝ => sigma M μ p.1 p.2) ∘
          (fun q : ((Fin M.d → ℝ) × ℝ) × (Fin M.d → ℝ) => (q.2, paced μ q.1 q.2)) := by
      funext q; rfl
    rw [this]
    exact hsig.comp (measurable_snd.prodMk hpaced)
  · have hΘ' : ∀ᵐ θ ∂M.G, θ ∈ Θ' := by
      rw [ae_iff]
      have : M.G Θ'ᶜ = 0 := by
        rw [measure_compl hΘm (measure_ne_top _ _), hG, measure_univ, tsub_self]
      simpa [Set.compl_def] using this
    filter_upwards [hae, hΘ'] with θ hθ hθ'
    exact hopt μ hμ θ hθ' (μ θ) hθ.1 hθ.2
