-- Prove2me | solution 1 for ConsistentSubmodular.exists_joint_rounding
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:42.573191+00:00
-- url     : https://prove2.me/submissions/0a035000-22de-49bd-80db-cd78d0ada566

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SharedThreshold
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_exists_good_positive_of_sum_failure_lt_one
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_expect_pushforward
import Theorems.Thm_ConsistentSubmodular_FiniteLaw_product_selected_probability
import Theorems.Thm_ConsistentSubmodular_exists_sharedThreshold
import Theorems.Thm_ConsistentSubmodular_sharedThresholdSample_recourse_expectation
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_lower_tail_le
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_card_upper_tail

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_univ [Fintype ι] (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation Finset.univ p v = finiteExpectation p v := by
  simp [sampleExpectation, finiteExpectation, subsetWeight, bernoulliWeight,
    Finset.compl_eq_univ_sdiff]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem weight_le_probability (E : Ω → Prop) (ω : Ω) (hE : E ω) :
    μ.weight ω ≤ μ.probability E := by
  classical
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun a => if E a then μ.weight a else 0)
    (fun a _ => by split_ifs; exact μ.nonnegative a; rfl) (Finset.mem_univ ω)
  simpa only [probability, hE, ite_true] using h

theorem expect_sum {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i, X i ω) = ∑ i, μ.expect (X i) := by
  unfold expect
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem probability_eq_expect (E : Ω → Prop) [DecidablePred E] :
    μ.probability E = μ.expect (fun ω => if E ω then 1 else 0) := by
  classical
  unfold probability expect
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

/-- Markov's estimate, with no division or positivity convention at zero. -/
theorem markov {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) :
    a * μ.probability (fun ω => a ≤ X ω) ≤ μ.expect X := by
  classical
  unfold probability expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ X ω
  · simp only [h, ite_true]
    nlinarith [mul_nonneg (μ.nonnegative ω) (sub_nonneg.mpr h)]
  · simp only [h, ite_false, mul_zero]
    exact mul_nonneg (μ.nonnegative ω) (hX ω)

end FiniteLaw

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.FiniteLaw

variable {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)

theorem probability_not (E : Ω → Prop) : μ.probability (fun ω => ¬E ω) = 1 - μ.probability E := by
  classical
  unfold probability
  rw [← μ.sum_one, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

variable {A : κ → Type*} [∀ i, Fintype (A i)]

theorem coordinate_positive_of_product_positive (laws : ∀ i, FiniteLaw (A i))
    (ω : ∀ i, A i) (h : 0 < (product laws).weight ω) (i : κ) :
    0 < (laws i).weight (ω i) := by
  classical
  apply lt_of_le_of_ne ((laws i).nonnegative (ω i))
  intro hz
  have hp : (product laws).weight ω = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hz.symm
  linarith

/-- Any independent finite coordinate laws reproduce the Bernoulli law of
their coordinatewise inclusion events. -/
theorem product_selected_expectation (laws : ∀ i, FiniteLaw (A i))
    (select : ∀ i, A i → Prop) (v : Finset κ → ℝ) :
    (product laws).expect (fun ω => v (selectedSet select ω)) =
      finiteExpectation (fun i => (laws i).probability (select i)) v := by
  rw [expect_pushforward]
  simp only [product_selected_probability, finiteExpectation]

end ConsistentSubmodular.FiniteLaw

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

namespace SharedThreshold

variable {d : ℕ} {z : Fin d → ℝ} (T : SharedThreshold z)

theorem inactive_of_zero (t : Fin d) (hz : z t = 0) (ω : Fin T.cellCount)
    (hω : 0 < T.law.weight ω) : t ∉ T.active ω := by
  intro ht
  have h := T.law.weight_le_probability (fun a => t ∈ T.active a) ω ht
  rw [T.inclusion, hz] at h
  linarith

theorem active_of_one (t : Fin d) (hz : z t = 1) (ω : Fin T.cellCount)
    (hω : 0 < T.law.weight ω) : t ∈ T.active ω := by
  by_contra ht
  have h := T.law.weight_le_probability (fun a => t ∉ T.active a) ω ht
  rw [T.law.probability_not, T.inclusion, hz] at h
  linarith

theorem intersection_probability (s t : Fin d) :
    T.law.probability (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = min (z s) (z t) := by
  rcases le_total (z s) (z t) with hst | hts
  · have heq : (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = (fun ω => s ∈ T.active ω) := by
      funext ω
      exact propext ⟨And.left, fun hs => ⟨hs, T.ordered ω s t hst hs⟩⟩
    rw [heq, T.inclusion, min_eq_left hst]
  · have heq : (fun ω => s ∈ T.active ω ∧ t ∈ T.active ω) = (fun ω => t ∈ T.active ω) := by
      funext ω
      exact propext ⟨And.right, fun ht => ⟨T.ordered ω t s hts ht, ht⟩⟩
    rw [heq, T.inclusion, min_eq_right hts]

end SharedThreshold

variable {n d : ℕ}

theorem sharedThresholdSample_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (t : Fin d)
    (v : Finset (Fin n) → ℝ) :
    (FiniteLaw.product (fun e => (T e).law)).expect (fun ω => v (sharedThresholdSample T ω t)) =
      finiteExpectation (z t) v := by
  unfold sharedThresholdSample
  rw [FiniteLaw.product_selected_expectation]
  have hp : (fun e => (T e).law.probability (fun a => t ∈ (T e).active a)) = z t :=
    funext (fun e => (T e).inclusion t)
  rw [hp]

theorem sharedThresholdSample_intersection_expectation {z : Fin d → Fin n → ℝ}
    (T : ∀ e, SharedThreshold (fun t => z t e)) (s t : Fin d)
    (v : Finset (Fin n) → ℝ) :
    (FiniteLaw.product (fun e => (T e).law)).expect
      (fun ω => v (sharedThresholdSample T ω s ∩ sharedThresholdSample T ω t)) =
      finiteExpectation (fun e => min (z s e) (z t e)) v := by
  have hsample (ω : ∀ e, Fin (T e).cellCount) :
      sharedThresholdSample T ω s ∩ sharedThresholdSample T ω t =
        FiniteLaw.selectedSet (fun e a => s ∈ (T e).active a ∧ t ∈ (T e).active a) ω := by
    ext e
    simp [sharedThresholdSample, FiniteLaw.selectedSet]
  simp_rw [hsample]
  rw [FiniteLaw.product_selected_expectation]
  have hp : (fun e => (T e).law.probability (fun a => s ∈ (T e).active a ∧ t ∈ (T e).active a)) =
      (fun e => min (z s e) (z t e)) := funext (fun e => (T e).intersection_probability s t)
  rw [hp]

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

/-- The lower tail (37) for the strict event `G(S) < μ - a`. -/
theorem sampleExpectation_lower_tail (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (G : Finset ι → ℝ)
    (hmono : ∀ A B, A ⊆ B → G A ≤ G B)
    (hsub : ∀ A B, G (A ∪ B) + G (A ∩ B) ≤ G A + G B)
    {c M a : ℝ} (hc : 0 < c) (hcap : ∀ A e, G (insert e A) - G A ≤ c) (hM : 0 < M)
    (hmean : sampleExpectation U p G - G ∅ ≤ M) (ha : 0 ≤ a) :
    sampleExpectation U p (fun S => if G S < sampleExpectation U p G - a then 1 else 0) ≤
      Real.exp (-(a ^ 2) / (2 * c * M)) := by
  refine (sampleExpectation_mono U p hp fun S _ => ?_).trans
    (sampleExpectation_lower_tail_le U p hp G hmono hsub hc hcap hM hmean ha)
  split_ifs with h h'
  · exact le_rfl
  · exact absurd h.le h'
  · exact zero_le_one
  · exact le_rfl

end ConsistentSubmodular

end

end

section

noncomputable section

open scoped BigOperators

set_option maxHeartbeats 2000000

namespace ConsistentSubmodular

theorem Objective.insert_sub_le_singleton {n : ℕ} (f : Objective n) (A : Finset (Fin n))
    (e : Fin n) : f.value (insert e A) - f.value A ≤ f.value {e} - f.value ∅ := by
  have h := f.submodular A {e}
  have hm := f.monotone ∅ (A ∩ {e}) (Finset.empty_subset _)
  have hu : A ∪ {e} = insert e A := by
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
    tauto
  rw [hu] at h
  linarith

end ConsistentSubmodular

end

end

section

open scoped BigOperators
set_option maxHeartbeats 2000000
open ConsistentSubmodular

theorem solution {n d : ℕ} {ι ε : Type*} [Fintype ι] [Fintype ε]
    (z : Fin d → Fin n → ℝ) (hz : ∀ t e, 0 ≤ z t e ∧ z t e ≤ 1)
    (g : ι → Objective n) (left right : ι → Fin d) (edgeLeft edgeRight : ε → Fin d)
    (κ L M a b R pSize pValue pCost : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hb2 : b ≤ 2 * κ) (hR : 0 < R) (hL : 0 < L) (hM : 0 < M)
    (hsize : ∀ t, ∑ e, z t e ≤ κ)
    (hcap : ∀ i e, (g i).value {e} - (g i).value ∅ ≤ L)
    (hmean : ∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
      (g i).value ≤ M)
    (hsizeBudget : Real.exp (-(b ^ 2) / (4 * κ)) ≤ pSize)
    (hvalueBudget : Real.exp (-(a ^ 2) / (2 * L * M)) ≤ pValue)
    (hcostBudget : (∑ j, ∑ e, |z (edgeLeft j) e - z (edgeRight j) e|) ≤ R * pCost)
    (hbudget : (d : ℝ) * pSize + (Fintype.card ι : ℝ) * pValue + pCost < 1) :
    ∃ S : Fin d → Finset (Fin n),
      (∀ t e, z t e = 0 → e ∉ S t) ∧
      (∀ t e, z t e = 1 → e ∈ S t) ∧
      (∀ t, (S t).card ≤ κ + b) ∧
      (∀ i, finiteExpectation (fun e => min (z (left i) e) (z (right i) e))
        (g i).value - a ≤ (g i).value (S (left i) ∩ S (right i))) ∧
      (∑ j, (recourse (S (edgeLeft j)) (S (edgeRight j)) : ℝ)) < R ∧
      (∀ s t, (∀ e, z s e = z t e) → S s = S t) := by
  classical
  let T := fun e => Classical.choice (exists_sharedThreshold (fun t => z t e) (fun t => hz t e))
  let μ := FiniteLaw.product (fun e => (T e).law)
  let sample := fun ω t => sharedThresholdSample T ω t
  let size := fun t ω => ((sample ω t).card : ℝ)
  let value := fun i ω => (g i).value (sample ω (left i) ∩ sample ω (right i))
  let cost := fun ω => ∑ j, (recourse (sample ω (edgeLeft j)) (sample ω (edgeRight j)) : ℝ)
  have hvalueMean (i) : μ.expect (value i) =
      finiteExpectation (fun e => min (z (left i) e) (z (right i) e)) (g i).value :=
    sharedThresholdSample_intersection_expectation T (left i) (right i) (g i).value
  have hcostMean : μ.expect cost ≤ R * pCost := by
    dsimp only [cost]
    rw [μ.expect_sum]
    simpa only [μ, sample, sharedThresholdSample_recourse_expectation] using hcostBudget
  let bad : Fin d ⊕ (ι ⊕ Unit) → (∀ e, Fin (T e).cellCount) → Prop :=
    Sum.elim (fun t ω => κ + b < size t ω)
      (Sum.elim (fun i ω => value i ω < μ.expect (value i) - a)
        (fun _ ω => R ≤ cost ω))
  have hprobSize (t) : μ.probability (bad (.inl t)) ≤ pSize := by
    calc μ.probability (bad (.inl t))
        = finiteExpectation (z t) (fun S => if κ + b < (S.card : ℝ) then 1 else 0) := by
          rw [μ.probability_eq_expect, ← sharedThresholdSample_expectation T t]
          rfl
      _ = sampleExpectation Finset.univ (z t)
            (fun S => if κ + b < (S.card : ℝ) then 1 else 0) := (sampleExpectation_univ _ _).symm
      _ ≤ Real.exp (-(b ^ 2) / (4 * κ)) :=
          sampleExpectation_card_upper_tail Finset.univ (z t) (fun e _ => hz t e) (hsize t) hb hb2
      _ ≤ pSize := hsizeBudget
  have hprobValue (i) : μ.probability (bad (.inr (.inl i))) ≤ pValue := by
    let p := fun e => min (z (left i) e) (z (right i) e)
    have hp : ∀ e ∈ (Finset.univ : Finset (Fin n)), 0 ≤ p e ∧ p e ≤ 1 :=
      fun e _ => ⟨le_min (hz _ e).1 (hz _ e).1, (min_le_left _ _).trans (hz _ e).2⟩
    have hE : μ.expect (value i) = sampleExpectation Finset.univ p (g i).value := by
      rw [hvalueMean, sampleExpectation_univ]
    have hmean' : sampleExpectation Finset.univ p (g i).value - (g i).value ∅ ≤ M := by
      rw [sampleExpectation_univ]
      linarith [hmean i, (g i).nonnegative ∅]
    calc μ.probability (bad (.inr (.inl i)))
        = finiteExpectation p (fun S => if (g i).value S <
            sampleExpectation Finset.univ p (g i).value - a then 1 else 0) := by
          rw [μ.probability_eq_expect, ← sharedThresholdSample_intersection_expectation T]
          simp only [bad, value, hE, Sum.elim_inr, Sum.elim_inl]
          rfl
      _ = sampleExpectation Finset.univ p (fun S => if (g i).value S <
            sampleExpectation Finset.univ p (g i).value - a then 1 else 0) :=
          (sampleExpectation_univ _ _).symm
      _ ≤ Real.exp (-(a ^ 2) / (2 * L * M)) :=
          sampleExpectation_lower_tail Finset.univ p hp (g i).value (g i).monotone
            (g i).submodular hL (fun A e => ((g i).insert_sub_le_singleton A e).trans (hcap i e))
            hM hmean' ha
      _ ≤ pValue := hvalueBudget
  have hprobCost : μ.probability (bad (.inr (.inr ()))) ≤ pCost := by
    have h := (μ.markov (X := cost) (fun ω => Finset.sum_nonneg (fun j _ => Nat.cast_nonneg _)) R).trans hcostMean
    exact (mul_le_mul_iff_right₀ hR).mp h
  have hfailure : (∑ i, μ.probability (bad i)) < 1 := by
    have hS := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hprobSize t)
    have hV := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hprobValue i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS hV
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fintype.sum_unique]
    linarith
  obtain ⟨ω, hω, hgood⟩ := μ.exists_good_positive_of_sum_failure_lt_one bad hfailure
  refine ⟨sample ω, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t e he
    have hpos := FiniteLaw.coordinate_positive_of_product_positive (fun e => (T e).law) ω hω e
    have hnot := (T e).inactive_of_zero t he (ω e) hpos
    simpa [sample, sharedThresholdSample, FiniteLaw.selectedSet] using hnot
  · intro t e he
    have hpos := FiniteLaw.coordinate_positive_of_product_positive (fun e => (T e).law) ω hω e
    have hin := (T e).active_of_one t he (ω e) hpos
    simpa [sample, sharedThresholdSample, FiniteLaw.selectedSet] using hin
  · intro t
    exact le_of_not_gt (hgood (.inl t))
  · intro i
    have h := le_of_not_gt (hgood (.inr (.inl i)))
    change _ ≤ value i ω
    rw [← hvalueMean]
    exact h
  · exact lt_of_not_ge (hgood (.inr (.inr ())))
  · intro s t hst
    ext e
    simp only [sample, sharedThresholdSample, FiniteLaw.selectedSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(T e).ordered (ω e) s t (hst e).le,
      (T e).ordered (ω e) t s (hst e).symm.le⟩

end
