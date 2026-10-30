-- Prove2me | solution 1 for FiniteMemQL.Convergence.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:39:33.353563+00:00
-- url     : https://prove2.me/submissions/42c28cfb-f1cf-4915-8faf-fbab7e0cc269

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace Aux_FMQ_B1

open FiniteMemQL.Convergence
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

lemma tv_bdd (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    BddAbove {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|} := by
  refine ⟨(μ Set.univ).toReal + (ν Set.univ).toReal, ?_⟩
  rintro r ⟨A, hA, rfl⟩
  have h1 : (μ A).toReal ≤ (μ Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
  have h2 : (ν A).toReal ≤ (ν Set.univ).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
  have h3 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν A).toReal := ENNReal.toReal_nonneg
  rw [abs_le]; constructor <;> linarith

lemma le_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : Set X)
    (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν :=
  le_csSup (tv_bdd μ ν) ⟨A, hA, rfl⟩

/-- One-sided bound: for `0 ≤ G ≤ 1`, `∫ G dμ - ∫ G dν ≤ tvDist μ ν` (Hahn decomposition). -/
lemma lint_sub_le_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (G : X → ℝ≥0∞) (hGm : Measurable G) (hG1 : ∀ x, G x ≤ 1) :
    (∫⁻ x, G x ∂μ).toReal - (∫⁻ x, G x ∂ν).toReal ≤ MarkovChainCLT.tvDist μ ν := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition ν μ
  have hsm := hs.measurableSet
  have hle : ν.restrict s ≤ μ.restrict s := hs.le_on
  have hge : μ.restrict sᶜ ≤ ν.restrict sᶜ := hs.ge_on_compl
  have hfinG : ∀ (m : Measure X) [IsFiniteMeasure m], ∫⁻ x, G x ∂m ≠ ∞ := by
    intro m _
    refine ne_top_of_le_ne_top (measure_ne_top m Set.univ) ?_
    calc ∫⁻ x, G x ∂m ≤ ∫⁻ _, 1 ∂m := lintegral_mono hG1
      _ = m Set.univ := by rw [lintegral_one]
  -- decomposition of ∫ G dμ
  have h1 : ∫⁻ x, G x ∂μ = ∫⁻ x in s, G x ∂μ + ∫⁻ x in sᶜ, G x ∂μ :=
    (lintegral_add_compl _ hsm).symm
  have h2 : ∫⁻ x in sᶜ, G x ∂μ ≤ ∫⁻ x in sᶜ, G x ∂ν := lintegral_mono' hge le_rfl
  have h3 : ∫⁻ x in s, G x ∂μ = ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s)
      + ∫⁻ x in s, G x ∂ν := by
    rw [← lintegral_add_measure, Measure.sub_add_cancel_of_le hle]
  have h4 : ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s) ≤ μ s - ν s := by
    calc ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s) ≤ ∫⁻ _, 1 ∂(μ.restrict s - ν.restrict s) :=
          lintegral_mono hG1
      _ = (μ.restrict s - ν.restrict s) Set.univ := lintegral_one
      _ = μ s - ν s := by
          rw [Measure.sub_apply MeasurableSet.univ hle, Measure.restrict_apply_univ,
            Measure.restrict_apply_univ]
  have h5 : ∫⁻ x, G x ∂ν = ∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂ν :=
    (lintegral_add_compl _ hsm).symm
  have key : ∫⁻ x, G x ∂μ ≤ (μ s - ν s) + ∫⁻ x, G x ∂ν := by
    rw [h1, h3, h5]
    calc ∫⁻ x, G x ∂(μ.restrict s - ν.restrict s) + ∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂μ
        ≤ (μ s - ν s) + ∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂ν := by gcongr
      _ = (μ s - ν s) + (∫⁻ x in s, G x ∂ν + ∫⁻ x in sᶜ, G x ∂ν) := by rw [add_assoc]
  have hνs : ν s ≤ μ s := by
    have := hle s ; simpa [Measure.restrict_apply_univ] using
      (Measure.le_iff'.1 hle Set.univ)
  have hfin1 : μ s - ν s ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ s) tsub_le_self
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin1, hfinG ν⟩) key
  rw [ENNReal.toReal_add hfin1 (hfinG ν), ENNReal.toReal_sub_of_le hνs (measure_ne_top μ s)]
    at hreal
  have := le_tv μ ν s hsm
  have := le_abs_self ((μ s).toReal - (ν s).toReal)
  linarith

lemma tv_symm (μ ν : Measure X) : MarkovChainCLT.tvDist μ ν = MarkovChainCLT.tvDist ν μ := by
  unfold MarkovChainCLT.tvDist
  congr 1
  ext r
  simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨A, hA, rfl⟩ <;> exact ⟨A, hA, abs_sub_comm _ _⟩

lemma lint_abs_le_tv (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (G : X → ℝ≥0∞) (hGm : Measurable G) (hG1 : ∀ x, G x ≤ 1) :
    |(∫⁻ x, G x ∂μ).toReal - (∫⁻ x, G x ∂ν).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  rw [abs_le]
  have a := lint_sub_le_tv μ ν G hGm hG1
  have b := lint_sub_le_tv ν μ G hGm hG1
  rw [tv_symm ν μ] at b
  constructor <;> linarith

lemma normalize_univ_le (μ : Measure X) : FiniteMemQL.Convergence.normalize μ Set.univ ≤ 1 := by
  unfold FiniteMemQL.Convergence.normalize
  rw [Measure.smul_apply, smul_eq_mul]
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · rw [h0, mul_zero]; exact zero_le_one
  rcases eq_or_ne (μ Set.univ) ⊤ with ht | ht
  · rw [ht]; simp
  · rw [ENNReal.inv_mul_cancel h0 ht]

end Aux_FMQ_B1

open FiniteMemQL.Convergence Aux_FMQ_B1 in
theorem solution {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    {N : ℕ} (π πs : Measure X) [IsProbabilityMeasure π] [IsProbabilityMeasure πs]
    (I : Window Y U N) (u : U) :
    MarkovChainCLT.tvDist (predYMeasure M π I u) (predYMeasure M πs I u) ≤
      MarkovChainCLT.tvDist (post M π I) (post M πs I) := by
  have hfinpost : ∀ p : Measure X, IsFiniteMeasure (post M p I) := fun p =>
    ⟨lt_of_le_of_lt (normalize_univ_le _) ENNReal.one_lt_top⟩
  have hTm : Measurable (fun x => M.T (x, u)) :=
    M.T.measurable.comp (measurable_id.prodMk measurable_const)
  -- the predictive law as an integral against the posterior
  have hrep : ∀ (p : Measure X) (A : Set Y), MeasurableSet A →
      predYMeasure M p I u A = ∫⁻ x, (∫⁻ x', M.O x' A ∂(M.T (x, u))) ∂(post M p I) := by
    intro p A hA
    unfold predYMeasure predict
    rw [Measure.bind_apply hA M.O.measurable.aemeasurable,
      Measure.lintegral_bind hTm.aemeasurable (M.O.measurable_coe hA).aemeasurable]
  have hGm : ∀ A : Set Y, MeasurableSet A →
      Measurable (fun x => ∫⁻ x', M.O x' A ∂(M.T (x, u))) := by
    intro A hA
    exact (Measurable.lintegral_kernel (κ := M.T.comap (fun x => (x, u)) (by fun_prop))
      (M.O.measurable_coe hA))
  have hG1 : ∀ A : Set Y, ∀ x, ∫⁻ x', M.O x' A ∂(M.T (x, u)) ≤ 1 := by
    intro A x
    calc ∫⁻ x', M.O x' A ∂(M.T (x, u)) ≤ ∫⁻ _, 1 ∂(M.T (x, u)) :=
          lintegral_mono fun x' => prob_le_one
      _ = 1 := by rw [lintegral_one, measure_univ]
  refine csSup_le ⟨0, ∅, MeasurableSet.empty, by simp⟩ ?_
  rintro r ⟨A, hA, rfl⟩
  rw [hrep π A hA, hrep πs A hA]
  exact lint_abs_le_tv _ _ _ (hGm A hA) (hG1 A)
