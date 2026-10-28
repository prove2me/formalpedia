-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.properties_1_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:07:48.129429+00:00
-- url     : https://prove2.me/submissions/7e6cddee-4f6c-4dff-bba0-d3c983235a9a

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory
open FirstPriceLearning.ContextLowerBound

namespace CLBH

lemma gap_nonneg (M α T : ℕ) : 0 ≤ gap M α T := Real.sqrt_nonneg _

lemma gap_le (M α T : ℕ) (hT : (α + 1) * M ≤ T) : gap M α T ≤ 1 / 4 := by
  unfold gap
  rw [show (1 / 4 : ℝ) = Real.sqrt (1 / 16) by
    rw [show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · have hTr : (0 : ℝ) < T := by exact_mod_cast hpos
    rw [div_le_iff₀ (by positivity)]
    have : ((((α + 1) * M : ℕ)) : ℝ) ≤ T := by exact_mod_cast hT
    linarith

lemma gap_pos (M α T : ℕ) (hM : 0 < M) (hT : (α + 1) * M ≤ T) : 0 < gap M α T := by
  unfold gap
  apply Real.sqrt_pos.mpr
  have hK : 0 < (α + 1) * M := by positivity
  have hTp : 0 < T := lt_of_lt_of_le hK hT
  have h1 : (0 : ℝ) < (((α + 1) * M : ℕ) : ℝ) := by exact_mod_cast hK
  have h2 : (0 : ℝ) < T := by exact_mod_cast hTp
  positivity

lemma hardMean_bounds (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : 0 ≤ hardMean M α T u c a ∧ hardMean M α T u c a ≤ 1 := by
  have h1 := gap_nonneg M α T
  have h2 := gap_le M α T hT
  unfold hardMean
  split_ifs <;> constructor <;> linarith

lemma bern_prob (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsProbabilityMeasure (bernoulliReal p) := by
  constructor
  simp only [bernoulliReal, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

lemma integral_bern (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : ∫ x, x ∂(bernoulliReal p) = p := by
  unfold bernoulliReal
  rw [integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [ENNReal.toReal_ofReal h0]
  · exact (integrable_dirac (by simp)).smul_measure (by simp)
  · exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma hardLaw_prob (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    IsProbabilityMeasure (hardLaw M α T u) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  unfold hardLaw
  infer_instance

lemma map_coord (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) :
    (hardLaw M α T u).map (fun x => x c a) = bernoulliReal (hardMean M α T u c a) := by
  have : ∀ c a, IsProbabilityMeasure (bernoulliReal (hardMean M α T u c a)) := fun c a =>
    bern_prob _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2
  have h1 := (measurePreserving_eval
    (fun c => Measure.pi fun a => bernoulliReal (hardMean M α T u c a)) c).map_eq
  have h2 := (measurePreserving_eval (fun a => bernoulliReal (hardMean M α T u c a)) a).map_eq
  have : (fun x : Fin M → Act M α → ℝ => x c a) =
      (Function.eval a : (Act M α → ℝ) → ℝ) ∘ (Function.eval c : (Fin M → Act M α → ℝ) → _) := rfl
  rw [this, ← Measure.map_map (measurable_pi_apply a) (measurable_pi_apply c)]
  unfold hardLaw
  rw [h1, h2]

lemma meanReward_hard (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) : meanReward (hardLaw M α T u) c a = hardMean M α T u c a := by
  unfold meanReward
  have hm : Measurable (fun x : Fin M → Act M α → ℝ => x c a) :=
    (measurable_pi_apply a).comp (measurable_pi_apply c)
  have := integral_map (μ := hardLaw M α T u) hm.aemeasurable
    (aestronglyMeasurable_id (μ := (hardLaw M α T u).map (fun x => x c a)))
  simp only [id] at this
  rw [← this, map_coord M α T hT u c a]
  exact integral_bern _ (hardMean_bounds M α T hT u c a).1 (hardMean_bounds M α T hT u c a).2

end CLBH
namespace CLBH

/-- The maximal mean reward under context `c` is attained at `(c, u c)`. -/
lemma hardMean_le_opt (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M)
    (a : Act M α) (ha : a ≠ (c, u c)) :
    hardMean M α T u c a + gap M α T ≤ hardMean M α T u c (c, u c) ∧
    (a.1 ≠ c → hardMean M α T u c a + 1 / 4 ≤ hardMean M α T u c (c, u c)) := by
  have h1 := gap_nonneg M α T
  have h2 := gap_le M α T hT
  obtain ⟨i, j⟩ := a
  have hne : ¬ (i = c ∧ j = u c) := fun h => ha (Prod.ext h.1 h.2)
  unfold hardMean
  simp only
  by_cases hic : i = c
  · subst hic
    have hj : j ≠ u i := fun h => hne ⟨rfl, h⟩
    refine ⟨?_, fun h => absurd rfl h⟩
    simp only [if_true]
    split_ifs <;> first | linarith | (exfalso; simp_all) | simp_all
  · refine ⟨?_, fun _ => ?_⟩ <;> simp only [hic, if_false, if_true] <;> split_ifs <;> linarith

lemma opt_eq (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) (c : Fin M) :
    optReward (hardLaw M α T u) c = hardMean M α T u c (c, u c) := by
  haveI : Nonempty (Act M α) := ⟨(c, u c)⟩
  unfold optReward
  simp_rw [meanReward_hard M α T hT u c]
  apply le_antisymm
  · apply ciSup_le
    intro a
    by_cases ha : a = (c, u c)
    · rw [ha]
    · have := (hardMean_le_opt M α T hT u c a ha).1
      linarith [gap_nonneg M α T]
  · exact le_ciSup (Set.finite_range _).bddAbove (c, u c)

end CLBH

theorem solution (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    (∀ (c : Fin M) (a : Act M α),
      meanReward (hardLaw M α T u) c a ∈ Set.Icc (0 : ℝ) 1 ∧
        (meanReward (hardLaw M α T u) c a ≠ 0 →
          meanReward (hardLaw M α T u) c a ∈ Set.Icc (1 / 4 : ℝ) (3 / 4))) ∧
    (∀ (c : Fin M) (a : Act M α), a ≠ (c, u c) →
      meanReward (hardLaw M α T u) c a < meanReward (hardLaw M α T u) c (c, u c)) ∧
    (∀ (c : Fin M) (a : Act M α), a ≠ (c, u c) →
      gap M α T ≤ optReward (hardLaw M α T u) c - meanReward (hardLaw M α T u) c a) ∧
    (∀ (c : Fin M) (a : Act M α), a.1 ≠ c →
      (1 / 4 : ℝ) ≤ optReward (hardLaw M α T u) c - meanReward (hardLaw M α T u) c a) := by
  have g0 := CLBH.gap_nonneg M α T
  have g1 := CLBH.gap_le M α T hT
  refine ⟨fun c a => ?_, fun c a ha => ?_, fun c a ha => ?_, fun c a ha => ?_⟩
  · rw [CLBH.meanReward_hard M α T hT u c a]
    unfold hardMean
    split_ifs <;> refine ⟨⟨by linarith, by linarith⟩, fun h => ?_⟩ <;>
      first | exact absurd rfl h | exact ⟨by linarith, by linarith⟩
  · rw [CLBH.meanReward_hard M α T hT u c a, CLBH.meanReward_hard M α T hT u c]
    have hM : 0 < M := Fin.pos c
    have := (CLBH.hardMean_le_opt M α T hT u c a ha).1
    linarith [CLBH.gap_pos M α T hM hT]
  · rw [CLBH.opt_eq M α T hT u c, CLBH.meanReward_hard M α T hT u c a]
    linarith [(CLBH.hardMean_le_opt M α T hT u c a ha).1]
  · have ha' : a ≠ (c, u c) := fun h => ha (by rw [h])
    rw [CLBH.opt_eq M α T hT u c, CLBH.meanReward_hard M α T hT u c a]
    linarith [(CLBH.hardMean_le_opt M α T hT u c a ha').2 ha]
