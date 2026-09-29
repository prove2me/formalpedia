-- Prove2me | solution 1 for BanditAlgorithm.pmMinimaxRegret_le_policy_of_unit_losses
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:06:54.600226+00:00
-- url     : https://prove2.me/submissions/27f31470-0773-4e1b-b10d-2de904d4a262

import Definitions.Def_PartialMonitoringGame
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

private lemma integrable_finite_pm
    {α : Type*} [Finite α] [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) : Integrable f μ := by
  obtain ⟨K, hK⟩ := Finite.exists_le (fun x : α => ‖f x‖)
  exact Integrable.of_bound hf.aestronglyMeasurable K
    (Filter.Eventually.of_forall hK)

theorem _root_.solution
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 1 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (π : PMPolicy k 𝕊) :
    pmMinimaxRegret G n ≤ ⨆ i : Fin n → Fin d, pmRegret G π n i := by
  classical
  unfold pmMinimaxRegret
  apply ciInf_le
  refine ⟨-(n : ℝ), ?_⟩
  rintro w ⟨ρ, rfl⟩
  by_cases hseq : Nonempty (Fin n → Fin d)
  · letI : Nonempty (Fin n → Fin d) := hseq
    let i₀ : Fin n → Fin d := Classical.choice hseq
    let a₀ : Fin k := ⟨0, hk⟩
    have hint :
        -(n : ℝ) ≤ ∫ h, (∑ t, (G.L (h t).1 (i₀ t) - G.L a₀ (i₀ t)))
          ∂(pmMeasure G ρ n i₀) := by
      have hfun : ∀ h : PMHistory k 𝕊 n,
          -(n : ℝ) ≤ ∑ t, (G.L (h t).1 (i₀ t) - G.L a₀ (i₀ t)) := by
        intro h
        have hterm : ∀ t : Fin n,
            (-1 : ℝ) ≤ G.L (h t).1 (i₀ t) - G.L a₀ (i₀ t) := by
          intro t
          have hplay := hL (h t).1 (i₀ t)
          have hcomp := hL a₀ (i₀ t)
          rcases hplay with ⟨hplay₀, hplay₁⟩
          rcases hcomp with ⟨hcomp₀, hcomp₁⟩
          linarith
        calc
          -(n : ℝ) = ∑ _t : Fin n, (-1 : ℝ) := by simp
          _ ≤ ∑ t, (G.L (h t).1 (i₀ t) - G.L a₀ (i₀ t)) :=
            Finset.sum_le_sum fun t ht => hterm t
      have hconst : Integrable (fun _h : PMHistory k 𝕊 n => -(n : ℝ))
          (pmMeasure G ρ n i₀) := integrable_const _
      have hsum : Integrable
          (fun h : PMHistory k 𝕊 n =>
            ∑ t, (G.L (h t).1 (i₀ t) - G.L a₀ (i₀ t)))
          (pmMeasure G ρ n i₀) :=
        integrable_finite_pm (by
          apply Finset.measurable_sum
          intro t ht
          exact ((measurable_of_countable
            (fun c : Fin k => G.L c (i₀ t))).comp
              (measurable_fst.comp (measurable_pi_apply t))).sub measurable_const)
      have hmono := integral_mono hconst hsum hfun
      simpa using hmono
    calc
      -(n : ℝ) ≤ ∫ h, (∑ t, (G.L (h t).1 (i₀ t) - G.L a₀ (i₀ t)))
          ∂(pmMeasure G ρ n i₀) := hint
      _ ≤ pmRegret G ρ n i₀ := by
        unfold pmRegret
        exact le_ciSup (f := fun a : Fin k =>
          ∫ h, (∑ t, (G.L (h t).1 (i₀ t) - G.L a (i₀ t)))
            ∂(pmMeasure G ρ n i₀)) (Finite.bddAbove_range _) a₀
      _ ≤ ⨆ i : Fin n → Fin d, pmRegret G ρ n i :=
        le_ciSup (Finite.bddAbove_range _) i₀
  · haveI : IsEmpty (Fin n → Fin d) := not_nonempty_iff.mp hseq
    simp

end BanditAlgorithm
