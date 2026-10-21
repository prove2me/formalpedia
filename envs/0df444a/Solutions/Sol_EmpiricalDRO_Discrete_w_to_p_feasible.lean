-- Prove2me | solution 1 for EmpiricalDRO.Discrete.w_to_p_feasible
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T17:48:22.044468+00:00
-- url     : https://prove2.me/submissions/1594eeb5-3a1f-43fd-a195-d76f60d5ea92

import Mathlib
import Definitions.Def_EmpiricalDRO_Discrete_Setting

-- Mathematics: Henry Lam, arXiv:1605.09349v1, Proposition 1, proof p.24.
-- Formal model: mikedeng1; platform statement review: Shuze Chen.
-- Research directed by Alexander Richard Towell (queelius).
-- Lean formalization developed with substantial OpenAI Codex assistance.

open Finset EmpiricalDRO.Discrete EmpiricalDRO.Coverage PhiDivRobust.Counterpart
namespace EmpiricalAggregation

lemma coe_sum_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, EReal.coe_add, ih]

lemma burg_nonneg (x : ℝ) : 0 ≤ burg x := by
  unfold burg
  split_ifs with h
  · exact_mod_cast (show 0 ≤ -Real.log x + x - 1 by linarith [Real.log_le_sub_one_of_pos h])
  · exact le_top

lemma weights_positive {n : ℕ} (hn : 0 < n) (η : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ probUncertaintySet burg (fun _ => (1 : ℝ) / n) η) :
    ∀ j, 0 < w j := by
  have hq : 0 < (1 : ℝ) / n := by positivity
  intro j
  by_contra hj
  have hz : w j = 0 := le_antisymm (le_of_not_gt hj) (hw.1 j)
  have hnon : ∀ i ∈ (univ : Finset (Fin n)),
      0 ≤ ((1 / (n : ℝ) : ℝ) : EReal) * burg (w i / (1 / (n : ℝ))) := by
    intro i _
    exact mul_nonneg (by exact_mod_cast hq.le) (burg_nonneg _)
  have hle := (Finset.single_le_sum hnon (mem_univ j)).trans hw.2.2
  simp only [hz, zero_div, burg, lt_self_iff_false, ↓reduceIte,
    EReal.coe_mul_top_of_pos hq] at hle
  exact (EReal.coe_lt_top η).not_ge hle

lemma divergence_real {n : ℕ} (hn : 0 < n) (w : Fin n → ℝ)
    (hp : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) :
    phiDiv burg w (fun _ => (1 : ℝ) / n) =
      ((-(1 / (n : ℝ)) * ∑ i, Real.log ((n : ℝ) * w i) : ℝ) : EReal) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hq : 0 < (1 : ℝ) / n := by positivity
  have he (i : Fin n) :
      ((1 / (n : ℝ) : ℝ) : EReal) * burg (w i / (1 / (n : ℝ))) =
      ((-(1 / (n : ℝ)) * Real.log ((n : ℝ) * w i) + w i - 1 / n : ℝ) : EReal) := by
    rw [burg, if_pos (div_pos (hp i) hq), ← EReal.coe_mul]
    congr 1
    simp only [one_div, div_inv_eq_mul]
    rw [mul_comm (w i) (n : ℝ)]
    field_simp
    <;> ring
  unfold phiDiv
  simp_rw [he]
  rw [← coe_sum_real]
  congr 1
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, hs,
    sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  <;> ring

lemma group_sum {n k : ℕ} (c : Fin n → Fin k) (f : Fin n → ℝ) :
    (∑ i, ∑ j ∈ univ.filter (fun j => c j = i), f j) = ∑ j, f j := by
  classical
  exact Finset.sum_fiberwise_of_maps_to (fun j _ => mem_univ (c j)) f

lemma class_log {n k : ℕ} (hn : 0 < n) (c : Fin n → Fin k)
    (w : Fin n → ℝ) (hw : ∀ j, 0 < w j) (i : Fin k) :
    -(phat c i) * Real.log ((∑ j ∈ univ.filter (fun j => c j = i), w j) / phat c i) ≤
      ∑ j ∈ univ.filter (fun j => c j = i), -(1 / (n : ℝ)) * Real.log ((n : ℝ) * w j) := by
  classical
  let s := univ.filter (fun j => c j = i)
  change -((s.card : ℝ) / n) * Real.log ((∑ j ∈ s, w j) / ((s.card : ℝ) / n)) ≤
    ∑ j ∈ s, -(1 / (n : ℝ)) * Real.log ((n : ℝ) * w j)
  by_cases hs : s = ∅
  · simp [hs]
  have hm : 0 < (s.card : ℝ) := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr hs)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
    (t := s) (w := fun _ => 1 / (s.card : ℝ)) (p := fun j => (n : ℝ) * w j)
    (fun _ _ => by positivity)
    (by simp [sum_const, nsmul_eq_mul, ne_of_gt hm])
    (fun j _ => show 0 < (n : ℝ) * w j from mul_pos hn0 (hw j))
  simp only [smul_eq_mul, ← mul_sum] at hj
  have he : (1 / (s.card : ℝ)) * ∑ j ∈ s, (n : ℝ) * w j =
      (∑ j ∈ s, w j) / ((s.card : ℝ) / n) := by
    rw [← mul_sum]
    field_simp
  simp only [← mul_sum] at he
  rw [he] at hj
  have hh := mul_le_mul_of_nonneg_left hj (show 0 ≤ (s.card : ℝ) / n by positivity)
  have hc : (s.card : ℝ) / n * ((1 / (s.card : ℝ)) * ∑ j ∈ s, Real.log ((n : ℝ) * w j)) =
      (1 / (n : ℝ)) * ∑ j ∈ s, Real.log ((n : ℝ) * w j) := by field_simp
  rw [hc] at hh
  rw [← mul_sum]
  nlinarith

end EmpiricalAggregation
#print axioms EmpiricalAggregation.divergence_real
#print axioms EmpiricalAggregation.class_log

open EmpiricalAggregation

theorem solution {n k : ℕ} (hn : 0 < n) (c : Fin n → Fin k)
    (a : Fin k → ℝ) (η : ℝ) (w : Fin n → ℝ)
    (hw : w ∈ probUncertaintySet burg (fun _ => (1 : ℝ) / n) η) :
    let p : Fin k → ℝ := fun i => ∑ j ∈ univ.filter (fun j => c j = i), w j
    p ∈ burgBall (phat c) η ∧ ∑ i, p i * a i = ∑ j, w j * a (c j) := by
  classical
  dsimp only
  have hp := weights_positive hn η w hw
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    exact sum_nonneg (fun j _ => (hp j).le)
  · exact (group_sum c w).trans hw.2.1
  · intro i hi
    have hc : (univ.filter (fun j => c j = i)).card = 0 := by
      have : (count c i : ℝ) = 0 := ((div_eq_zero_iff).mp hi).resolve_right hn0
      exact_mod_cast this
    simp [card_eq_zero.mp hc]
  · intro i hi
    have hs : (univ.filter (fun j => c j = i)).Nonempty := by
      by_contra hh
      have he := not_nonempty_iff_eq_empty.mp hh
      have : phat c i = 0 := by simp [phat, count, he]
      linarith
    exact sum_pos (fun j _ => hp j) hs
  · have hj := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin k))) => class_log hn c w hp i)
    rw [group_sum c _, ← mul_sum] at hj
    have hd := hw.2.2
    rw [divergence_real hn w hp hw.2.1] at hd
    have hb : -(1 / (n : ℝ)) * ∑ j, Real.log ((n : ℝ) * w j) ≤ η := by exact_mod_cast hd
    calc
      -∑ i, phat c i * Real.log ((∑ j ∈ univ.filter (fun j => c j = i), w j) / phat c i)
          = ∑ i, -(phat c i) * Real.log ((∑ j ∈ univ.filter (fun j => c j = i), w j) / phat c i) := by
            simp only [neg_mul, sum_neg_distrib]
      _ ≤ _ := hj
      _ ≤ η := hb
  · calc
      ∑ i, (∑ j ∈ univ.filter (fun j => c j = i), w j) * a i
          = ∑ i, ∑ j ∈ univ.filter (fun j => c j = i), w j * a (c j) := by
            apply sum_congr rfl
            intro i _
            rw [sum_mul]
            apply sum_congr rfl
            intro j hj
            rw [(mem_filter.mp hj).2]
      _ = _ := group_sum c _

#print axioms solution
