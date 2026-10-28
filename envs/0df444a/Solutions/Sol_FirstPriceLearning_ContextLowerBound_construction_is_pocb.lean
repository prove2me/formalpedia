-- Prove2me | solution 1 for FirstPriceLearning.ContextLowerBound.construction_is_pocb
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T06:09:56.181697+00:00
-- url     : https://prove2.me/submissions/2878c533-1fdb-4d68-9c3c-e683dc46e49f

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

namespace CLBH

lemma bern_Icc (p : ℝ) : bernoulliReal p (Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  unfold bernoulliReal
  have hs : MeasurableSet (Set.Icc (0 : ℝ) 1)ᶜ := measurableSet_Icc.compl
  simp [Measure.dirac_apply' _ hs]

lemma hardLaw_support (M α T : ℕ) (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    hardLaw M α T u {x | ∀ c a, x c a ∈ Set.Icc (0 : ℝ) 1}ᶜ = 0 := by
  have h : ∀ᵐ x ∂(hardLaw M α T u), ∀ c a, x c a ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_all_iff]; intro c
    rw [ae_all_iff]; intro a
    have hm : Measurable (fun x : Fin M → Act M α → ℝ => x c a) :=
      (measurable_pi_apply a).comp (measurable_pi_apply c)
    have : ∀ᵐ y ∂((hardLaw M α T u).map (fun x => x c a)), y ∈ Set.Icc (0 : ℝ) 1 := by
      rw [map_coord M α T hT u c a, ae_iff]
      have := bern_Icc (hardMean M α T u c a)
      rwa [Set.compl_def] at this
    exact ae_of_ae_map hm.aemeasurable this
  rw [ae_iff] at h
  simpa [Set.compl_setOf] using h

end CLBH

theorem solution (M α T : ℕ) (hα : 1 ≤ α) (hM : 1 ≤ M)
    (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    IsPartiallyOrderedContextualBandit (feedbackGraph M α) (hardLaw M α T u)
        (fun c₁ c₂ : Fin M => c₁ ≤ c₂) ∧
      HasIndependenceNumber (feedbackGraph M α) α ∧
      HasOrderIndependenceNumber (fun c₁ c₂ : Fin M => c₁ ≤ c₂) 1 := by
  have hloop : ∀ a : Act M α, ¬ feedbackGraph M α a a := by
    intro a h
    rcases h with h | ⟨_, h1, h2⟩
    · exact lt_irrefl _ h
    · exact h1 h2
  have htrans : ∀ a b d : Act M α, feedbackGraph M α a b → feedbackGraph M α b d →
      feedbackGraph M α a d := by
    intro a b d h1 h2
    rcases h1 with h1 | ⟨e1, n1, z1⟩ <;> rcases h2 with h2 | ⟨e2, n2, z2⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl (e2 ▸ h1)
    · exact Or.inl (e1 ▸ h2)
    · exact absurd z1 n2
  refine ⟨⟨⟨CLBH.hardLaw_prob M α T hT u, CLBH.hardLaw_support M α T hT u, hloop⟩, htrans,
    inferInstance, fun c => (c, u c), ?_, ?_⟩, ?_, ?_⟩
  · intro c a
    by_cases ha : a = (c, u c)
    · rw [ha]
    · rw [CLBH.meanReward_hard M α T hT u c a, CLBH.meanReward_hard M α T hT u c]
      linarith [(CLBH.hardMean_le_opt M α T hT u c a ha).1, CLBH.gap_nonneg M α T]
  · intro c₁ c₂ h
    rcases eq_or_lt_of_le h with h | h
    · left; rw [h]
    · right; exact Or.inl h
  · refine ⟨⟨(Finset.univ : Finset (Fin α)).map ⟨fun j => (⟨0, hM⟩, j.succ.cast (by omega)), ?_⟩,
      ?_, by simp⟩, ?_⟩
    · intro j₁ j₂ h
      simp only [Prod.mk.injEq, true_and] at h
      have := congrArg Fin.val h
      simp at this
      exact Fin.ext this
    · intro a ha b hb hab hE
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk] at ha hb
      obtain ⟨j₁, rfl⟩ := ha
      obtain ⟨j₂, rfl⟩ := hb
      rcases hE with h | ⟨_, _, h⟩
      · exact lt_irrefl _ h
      · have := congrArg Fin.val h
        simp at this
    · intro S hS
      -- all members share the first coordinate
      have hsame : ∀ x ∈ S, ∀ y ∈ S, x.1 = y.1 := by
        intro x hx y hy
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact hS x hx y hy (fun e => hne (by rw [e])) (Or.inl h)
        · exact hS y hy x hx (fun e => hne (by rw [e])) (Or.inl h)
      by_cases h0 : ∃ x ∈ S, x.2 = 0
      · obtain ⟨x, hx, hx0⟩ := h0
        have : S ⊆ {x} := by
          intro y hy
          rw [Finset.mem_singleton]
          by_contra hyx
          have h1 := hsame y hy x hx
          have hy0 : y.2 ≠ 0 := by
            intro hy0; exact hyx (Prod.ext h1 (by rw [hy0, hx0]))
          exact hS y hy x hx hyx (Or.inr ⟨h1, hy0, hx0⟩)
        calc S.card ≤ ({x} : Finset (Act M α)).card := Finset.card_le_card this
          _ = 1 := Finset.card_singleton x
          _ ≤ α := hα
      · push_neg at h0
        have hinj : Set.InjOn (fun x : Act M α => x.2) S := by
          intro x hx y hy h
          exact Prod.ext (hsame x hx y hy) h
        calc S.card ≤ ((Finset.univ : Finset (Fin (α + 1))).filter (· ≠ 0)).card := by
              apply Finset.card_le_card_of_injOn (fun x : Act M α => x.2) _ hinj
              intro x hx
              simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
              exact h0 x hx
          _ = α := by
              rw [Finset.filter_ne' Finset.univ (0 : Fin (α + 1)), Finset.card_erase_of_mem
                (Finset.mem_univ _)]
              simp
  · refine ⟨⟨{⟨0, hM⟩}, ?_, by simp⟩, ?_⟩
    · intro x hx y hy hxy
      simp only [Finset.mem_singleton] at hx hy
      exact absurd (hx.trans hy.symm) hxy
    · intro S hS
      apply Finset.card_le_one.mpr
      intro x hx y hy
      by_contra hxy
      have := hS x hx y hy hxy
      rcases le_total x y with h | h
      · exact this.1 h
      · exact this.2 h
