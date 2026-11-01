-- Prove2me | solution 1 for DynDoubleAuction.TwoSided.lemma_5_2_constraints
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:26:30.911414+00:00
-- url     : https://prove2.me/submissions/a26e4996-9f3b-4085-896a-a5dc3a8fee78

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided
open MeasureTheory Filter Topology

lemma buyers_nonempty {n : ℕ} (hn : 1 ≤ n) : (Finset.univ.erase (0 : Fin (n + 1))).Nonempty :=
  ⟨⟨1, by omega⟩, by simp [Fin.ext_iff]⟩

lemma maxBuyer_eq {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) :
    maxBuyer v = (Finset.univ.erase (0 : Fin (n + 1))).sup' (buyers_nonempty hn) v := by
  unfold maxBuyer; simp [buyers_nonempty hn]

lemma le_maxBuyer {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hi : i ≠ 0) :
    v i ≤ maxBuyer v := by
  rw [maxBuyer_eq hn]; exact Finset.le_sup' v (by simp [hi])

lemma maxBuyer_attained {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) :
    ∃ i, i ≠ 0 ∧ maxBuyer v = v i := by
  obtain ⟨i, hi, h⟩ := Finset.exists_mem_eq_sup' (buyers_nonempty hn) v
  exact ⟨i, by simpa using hi, by rw [maxBuyer_eq hn, h]⟩

lemma maxBuyer_le {n : ℕ} (hn : 1 ≤ n) (v : Fin (n + 1) → ℝ) (C : ℝ)
    (h : ∀ i, i ≠ 0 → v i ≤ C) : maxBuyer v ≤ C := by
  obtain ⟨i, hi, he⟩ := maxBuyer_attained hn v; rw [he]; exact h i hi

lemma measurable_maxBuyer {n : ℕ} (hn : 1 ≤ n) :
    Measurable (fun v : Fin (n + 1) → ℝ => maxBuyer v) := by
  have : (fun v : Fin (n + 1) → ℝ => maxBuyer v) =
      (Finset.univ.erase (0 : Fin (n + 1))).sup' (buyers_nonempty hn)
        (fun i (v : Fin (n + 1) → ℝ) => v i) := by
    funext v; rw [maxBuyer_eq hn, Finset.sup'_apply]
  rw [this]
  exact Finset.measurable_sup' _ (fun i _ => measurable_pi_apply i)

section rules
variable {n : ℕ} (M : Market n) (T t : ℕ) (w v : Fin (n + 1) → ℝ)

open Classical in
lemma rq_med (h : Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).q i = if i = 0 then (if v 0 ≤ maxBuyer v then 1 else 0)
      else (if isWinner v i then 1 else 0) := by
  classical
  simp [rule, h]

lemma rz_med (h : Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).z i = v i * (rule M T t w v).q i := by
  simp [rule, h]

lemma ru_med (h : Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).u i = w i + max (maxBuyer v - v 0) 0 - wlow M := by
  simp [rule, h]

lemma rq_nmed (h : ¬ Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).q i = if i = 0 then min 1 (w 0 / mu M) * (if v 0 ≤ M.r then 1 else 0)
      else M.α i * min 1 (w i / mu M) * (if v 0 ≤ M.r then 1 else 0) := by
  simp [rule, h]

lemma rz_nmed (h : ¬ Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).z i = if i = 0 then M.r * (rule M T t w v).q 0 else 0 := by
  simp [rule, h]

lemma ru_nmed (h : ¬ Medium M T t (w 0)) (i : Fin (n + 1)) :
    (rule M T t w v).u i = max (w i - mu M) 0 := by
  simp [rule, h]

end rules

lemma winner_unique {n : ℕ} (v : Fin (n + 1) → ℝ) (i j : Fin (n + 1))
    (hi : isWinner v i) (hj : isWinner v j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := hj.2.2.2 i hi.1 h; linarith [hi.2.2.1, hj.2.2.1]
  · exact h
  · have := hi.2.2.2 j hj.1 h; linarith [hi.2.2.1, hj.2.2.1]

open Classical in
lemma winners_sum_le {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (if isWinner v i then (1:ℝ) else 0)) ≤
      (if v 0 ≤ maxBuyer v then 1 else 0) := by
  rw [Finset.sum_boole]
  by_cases hw : ∃ i, isWinner v i
  · obtain ⟨i, hi⟩ := hw
    have h0 : v 0 ≤ maxBuyer v := by linarith [hi.2.1, hi.2.2.1]
    rw [if_pos h0]
    have : ((Finset.univ.erase (0 : Fin (n + 1))).filter (fun i => isWinner v i)).card ≤ 1 :=
      Finset.card_le_one.2 (fun a ha b hb =>
        winner_unique v a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2)
    exact_mod_cast this
  · push_neg at hw
    have : ((Finset.univ.erase (0 : Fin (n + 1))).filter (fun i => isWinner v i)) = ∅ :=
      Finset.filter_eq_empty_iff.2 (fun x _ => hw x)
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]; split_ifs <;> norm_num

end DynDoubleAuction.TwoSided

namespace DynDoubleAuction.TwoSided
open MeasureTheory

lemma maxBuyer_congr {n : ℕ} (hn : 1 ≤ n) (v v' : Fin (n + 1) → ℝ)
    (h : ∀ i, i ≠ 0 → v i = v' i) : maxBuyer v = maxBuyer v' := by
  rw [maxBuyer_eq hn, maxBuyer_eq hn]
  exact Finset.sup'_congr _ rfl (fun i hi => h i (by simpa using hi))

end DynDoubleAuction.TwoSided

open DynDoubleAuction.TwoSided MeasureTheory in
theorem solution {n : ℕ} (M : Market n) (hM : Standing M)
    (T t : ℕ) (ht : 1 ≤ t ∧ t ≤ T) (c : ℝ)
    (hc : 0 ≤ c ∧ c ≤ wbar M T t) :
    (∀ v : Fin (n + 1) → ℝ,
      (∀ j, v j ∈ Set.Icc 0 M.vbar) →
      (∀ j, (rule M T t (fun _ => c) v).q j ∈ Set.Icc 0 1 ∧
        0 ≤ periodUtility (rule M T t (fun _ => c) v) j (v j) ∧
        0 ≤ (rule M T t (fun _ => c) v).z j) ∧
      (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
        (rule M T t (fun _ => c) v).q i) ≤
        (rule M T t (fun _ => c) v).q 0) ∧
    (∀ j : Fin (n + 1),
      (∫ v, periodUtility (rule M T t (fun _ => c) v) j (v j) +
        (rule M T t (fun _ => c) v).u j ∂M.F) = c) ∧
    (∀ j : Fin (n + 1), ∀ vhat : Fin (n + 1) → ℝ,
      (∀ i, vhat i ∈ Set.Icc 0 M.vbar) →
      ∀ x y : ℝ, x ∈ Set.Icc 0 M.vbar → y ∈ Set.Icc 0 M.vbar →
      let truthful := rule M T t (fun _ => c) (Function.update vhat j x)
      let deviating := rule M T t (fun _ => c) (Function.update vhat j y)
      periodUtility deviating j x + deviating.u j ≤
        periodUtility truthful j x + truthful.u j) := by
  classical
  obtain ⟨hn, hP, hvb, hae, hr, hα, hαmu, hαsum, hmw, hmu⟩ := hM
  have hmu0 : mu M ≠ 0 := hmu.ne'
  set m := min 1 (c / mu M) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (div_nonneg hc.1 hmu.le)
  have hm1 : m ≤ 1 := min_le_left _ _
  have hmmu : m * mu M = min (mu M) c := by
    rw [hm, min_mul_of_nonneg _ _ hmu.le, one_mul, div_mul_cancel₀ _ hmu0]
  have hmK : m * mu M + max (c - mu M) 0 = c := by
    rw [hmmu]; rcases le_total (mu M) c with h | h
    · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h, max_eq_right (by linarith)]; ring
  -- integrability facts
  have hX_int : Integrable (fun v : Fin (n + 1) → ℝ => max (maxBuyer v - v 0) 0) M.F := by
    refine Integrable.of_bound ?_ M.vbar ?_
    · exact (((measurable_maxBuyer hn).sub (measurable_pi_apply 0)).max
        measurable_const).aestronglyMeasurable
    · filter_upwards [hae] with v hv
      have hB := maxBuyer_le hn v M.vbar (fun i _ => (hv i).2)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [(hv 0).1]) hvb.le
  by_cases hmed : Medium M T t c
  · have hq := fun v => rq_med M T t (fun _ => c) v hmed
    have hz := fun v => rz_med M T t (fun _ => c) v hmed
    have hu := fun v => ru_med M T t (fun _ => c) v hmed
    have hutil : ∀ v j, periodUtility (rule M T t (fun _ => c) v) j (v j) = 0 := by
      intro v j; unfold periodUtility; split_ifs with h
      · subst h; rw [hz]; ring
      · rw [hz]; ring
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      refine ⟨fun j => ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hq]; constructor <;> split_ifs <;> norm_num
      · rw [hutil]
      · rw [hz]; refine mul_nonneg (hv j).1 ?_; rw [hq]; split_ifs <;> norm_num
      · rw [hq v 0]; simp only [if_true]
        calc (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (rule M T t (fun _ => c) v).q i)
            = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (if isWinner v i then (1:ℝ) else 0) := by
              refine Finset.sum_congr rfl (fun i hi => ?_)
              rw [hq, if_neg (Finset.ne_of_mem_erase hi)]
          _ ≤ _ := winners_sum_le v
    · intro j
      have : (fun v => periodUtility (rule M T t (fun _ => c) v) j (v j) +
          (rule M T t (fun _ => c) v).u j) =
          fun v => c + max (maxBuyer v - v 0) 0 - wlow M := by
        funext v; rw [hutil, hu]; ring
      rw [this, integral_sub (by fun_prop) (integrable_const _),
        integral_add (integrable_const _) hX_int]
      simp [wlow]
    · intro j vhat hvhat x y hx hy
      dsimp only
      unfold periodUtility
      rw [hu, hu]
      by_cases hj : j = 0
      · subst hj
        simp only [if_true]
        rw [hz, hz, hq, hq]
        simp only [if_true, Function.update_self]
        have hBB : maxBuyer (Function.update vhat 0 y) = maxBuyer (Function.update vhat 0 x) :=
          maxBuyer_congr hn _ _ (fun i hi => by simp [hi])
        rw [hBB]
        set B := maxBuyer (Function.update vhat 0 x)
        split_ifs with h1 h2 h2
        · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
        · rw [max_eq_left (by linarith)]; linarith [le_max_left (B - x) 0]
        · rw [max_eq_right (by linarith)]; linarith [le_max_right (B - x) 0]
        · rw [max_eq_right (by linarith)]; linarith [le_max_right (B - x) 0]
      · simp only [hj, if_false]
        rw [hz, hz, hq, hq]
        simp only [hj, if_false, Function.update_self, Function.update_of_ne (Ne.symm hj)]
        set Bx := maxBuyer (Function.update vhat j x)
        set By := maxBuyer (Function.update vhat j y)
        have hxB : x ≤ Bx := by
          have := le_maxBuyer hn (Function.update vhat j x) j hj
          simpa using this
        have hrest : ∀ i, i ≠ 0 → i ≠ j → vhat i ≤ Bx := by
          intro i hi hij
          have := le_maxBuyer hn (Function.update vhat j x) i hi
          simpa [Function.update_of_ne hij] using this
        split_ifs with hw hw'
        · -- deviating report wins
          obtain ⟨-, h0, hyB, -⟩ := hw
          simp only [Function.update_self, Function.update_of_ne (Ne.symm hj)] at h0 hyB
          rw [show By = y from hyB.symm, max_eq_left (by linarith)]
          linarith [le_max_left (Bx - vhat 0) 0]
        · obtain ⟨-, h0, hyB, -⟩ := hw
          simp only [Function.update_self, Function.update_of_ne (Ne.symm hj)] at h0 hyB
          rw [show By = y from hyB.symm, max_eq_left (by linarith)]
          linarith [le_max_left (Bx - vhat 0) 0]
        · simp only [mul_zero, sub_zero]
          rcases le_or_gt By Bx with hle | hlt
          · have := max_le_max_right 0 (sub_le_sub_right hle (vhat 0)); linarith
          · obtain ⟨i0, hi0, hie⟩ := maxBuyer_attained hn (Function.update vhat j y)
            by_cases hij : i0 = j
            · subst hij
              simp only [Function.update_self] at hie
              by_cases h0 : vhat 0 ≤ y
              · exfalso; apply hw
                refine ⟨hj, ?_, ?_, ?_⟩
                · simpa [Function.update_of_ne (Ne.symm hj)] using h0
                · simp only [Function.update_self]; exact hie.symm
                · intro j' hj'0 hj'lt
                  simp only [Function.update_self, Function.update_of_ne (ne_of_lt hj'lt)]
                  linarith [hrest j' hj'0 (ne_of_lt hj'lt)]
              · rw [max_eq_right (by linarith)]; linarith [le_max_right (Bx - vhat 0) 0]
            · exfalso
              simp only [Function.update_of_ne hij] at hie
              linarith [hrest i0 hi0 hij]
        · simp only [mul_zero, sub_zero]
          rcases le_or_gt By Bx with hle | hlt
          · have := max_le_max_right 0 (sub_le_sub_right hle (vhat 0)); linarith
          · obtain ⟨i0, hi0, hie⟩ := maxBuyer_attained hn (Function.update vhat j y)
            by_cases hij : i0 = j
            · subst hij
              simp only [Function.update_self] at hie
              by_cases h0 : vhat 0 ≤ y
              · exfalso; apply hw
                refine ⟨hj, ?_, ?_, ?_⟩
                · simpa [Function.update_of_ne (Ne.symm hj)] using h0
                · simp only [Function.update_self]; exact hie.symm
                · intro j' hj'0 hj'lt
                  simp only [Function.update_self, Function.update_of_ne (ne_of_lt hj'lt)]
                  linarith [hrest j' hj'0 (ne_of_lt hj'lt)]
              · rw [max_eq_right (by linarith)]; linarith [le_max_right (Bx - vhat 0) 0]
            · exfalso
              simp only [Function.update_of_ne hij] at hie
              linarith [hrest i0 hi0 hij]
  · have hq := fun v => rq_nmed M T t (fun _ => c) v hmed
    have hz := fun v => rz_nmed M T t (fun _ => c) v hmed
    have hu := fun v => ru_nmed M T t (fun _ => c) v hmed
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      refine ⟨fun j => ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [hq]
        have := hα j
        split_ifs with h1 h2 <;> simp only [mul_one, mul_zero, Set.mem_Icc, le_refl, zero_le_one,
          and_self]
        · exact ⟨hm0, hm1⟩
        · exact ⟨mul_nonneg (this h1).1 hm0,
            by nlinarith [(this h1).1, (this h1).2]⟩
      · unfold periodUtility
        split_ifs with h1
        · subst h1; rw [hz, if_pos rfl, hq, if_pos rfl]
          split_ifs with h2
          · nlinarith
          · simp
        · rw [hz, if_neg h1, hq, if_neg h1]
          split_ifs with h2
          · have := (hα j h1).1; have := (hv j).1
            simp only [mul_one, sub_zero]; positivity
          · simp
      · rw [hz]; split_ifs with h1
        · rw [hq, if_pos rfl]; apply mul_nonneg hr.1; apply mul_nonneg hm0; split_ifs <;> norm_num
        · exact le_refl 0
      · calc (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), (rule M T t (fun _ => c) v).q i)
            = (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), M.α i) *
                (m * (if v 0 ≤ M.r then 1 else 0)) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl (fun i hi => ?_)
              rw [hq, if_neg (Finset.ne_of_mem_erase hi)]; ring
          _ ≤ 1 * (m * (if v 0 ≤ M.r then 1 else 0)) := by
              apply mul_le_mul_of_nonneg_right hαsum
              apply mul_nonneg hm0; split_ifs <;> norm_num
          _ = _ := by rw [hq, if_pos rfl]; ring
    · intro j
      by_cases hj : j = 0
      · subst hj
        have : (fun v : Fin (n + 1) → ℝ => periodUtility (rule M T t (fun _ => c) v) 0 (v 0) +
            (rule M T t (fun _ => c) v).u 0) =
            fun v => m * max (M.r - v 0) 0 + max (c - mu M) 0 := by
          funext v; unfold periodUtility; rw [if_pos rfl, hz, if_pos rfl, hq, if_pos rfl, hu]
          split_ifs with h
          · rw [max_eq_left (a := M.r - v 0) (by linarith)]; ring
          · rw [max_eq_right (a := M.r - v 0) (by linarith)]; ring
        rw [this]
        have hint : Integrable (fun v : Fin (n + 1) → ℝ => max (M.r - v 0) 0) M.F := by
          refine Integrable.of_bound ?_ M.vbar ?_
          · exact ((measurable_const.sub (measurable_pi_apply 0)).max
              measurable_const).aestronglyMeasurable
          · filter_upwards [hae] with v hv
            rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
            exact max_le (by linarith [(hv 0).1, hr.2]) hvb.le
        rw [integral_add (hint.const_mul m) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        rw [← mu, hmK]
      · have : (fun v : Fin (n + 1) → ℝ => periodUtility (rule M T t (fun _ => c) v) j (v j) +
            (rule M T t (fun _ => c) v).u j) =
            fun v => (M.α j * m) * (v j * if v 0 ≤ M.r then 1 else 0) + max (c - mu M) 0 := by
          funext v; unfold periodUtility; rw [if_neg hj, hz, if_neg hj, hq, if_neg hj, hu]; ring
        rw [this]
        have hint : Integrable (fun v : Fin (n + 1) → ℝ => v j * if v 0 ≤ M.r then 1 else 0)
            M.F := by
          refine Integrable.of_bound ?_ M.vbar ?_
          · exact ((measurable_pi_apply j).mul (Measurable.ite
              (measurableSet_le (measurable_pi_apply 0) measurable_const)
              measurable_const measurable_const)).aestronglyMeasurable
          · filter_upwards [hae] with v hv
            rw [Real.norm_eq_abs]
            split_ifs
            · rw [mul_one, abs_of_nonneg (hv j).1]; exact (hv j).2
            · simp [hvb.le]
        rw [integral_add (hint.const_mul _) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
        rw [mul_comm (M.α j) m, mul_assoc, hαmu j hj, hmK]
    · intro j vhat hvhat x y hx hy
      dsimp only
      unfold periodUtility
      rw [hu, hu]
      by_cases hj : j = 0
      · subst hj
        simp only [if_true]
        rw [hz, hz, if_pos rfl, if_pos rfl, hq, hq, if_pos rfl, if_pos rfl]
        simp only [Function.update_self]
        split_ifs with h1 h2 h2
        · linarith
        · nlinarith
        · nlinarith
        · linarith
      · simp only [hj, if_false]
        rw [hz, hz, if_neg hj, if_neg hj, hq, hq, if_neg hj, if_neg hj]
        simp only [Function.update_of_ne (Ne.symm hj), le_refl]
