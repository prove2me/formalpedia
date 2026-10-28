-- Prove2me | solution 1 for FirstPriceLearning.GraphFeedback.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T12:08:15.640618+00:00
-- url     : https://prove2.me/submissions/e0f52de3-628e-4774-a717-fdc00e2e9cde

import Mathlib
import Definitions.Def_FirstPriceLearning_GraphFeedback_FeedbackGraph

open FirstPriceLearning.GraphFeedback

namespace GFL10

open Classical

variable {n : ℕ} (E : Fin n → Fin n → Prop)

/-- Undirected adjacency of distinct vertices. -/
def adj (u v : Fin n) : Prop := u ≠ v ∧ (E u v ∨ E v u)

/-- Undirected degree of `v` inside `U`. -/
noncomputable def deg (U : Finset (Fin n)) (v : Fin n) : ℕ := (U.filter (fun u => adj E u v)).card

/-- Out-degree of `v` inside `U`, self-loops excluded. -/
noncomputable def od (U : Finset (Fin n)) (v : Fin n) : ℕ :=
  (U.filter (fun u => u ≠ v ∧ E v u)).card

/-- Caro–Wei: there is an independent subset of size at least `∑ 1/(d(v)+1)`. -/
lemma caro_wei : ∀ k (U : Finset (Fin n)), U.card = k →
    ∃ S ⊆ U, IsIndependentSet E S ∧
      ∑ v ∈ U, (1 : ℝ) / (deg E U v + 1) ≤ S.card := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U hU
  rcases U.eq_empty_or_nonempty with h | hne
  · subst h
    exact ⟨∅, Finset.Subset.refl _, by intro a ha; simp at ha, by simp⟩
  obtain ⟨v, hv, hmin⟩ := U.exists_min_image (deg E U) hne
  set F := U.filter (fun u => adj E u v)
  set N := insert v F
  have hvF : v ∉ F := by
    intro h; rw [Finset.mem_filter] at h; exact h.2.1 rfl
  have hNU : N ⊆ U := Finset.insert_subset hv (Finset.filter_subset _ _)
  set U' := U \ N
  have hvU' : v ∉ U' := by simp [U', N]
  have hlt : U'.card < k := by
    rw [← hU]
    apply Finset.card_lt_card
    exact ⟨Finset.sdiff_subset, fun h => hvU' (h hv)⟩
  obtain ⟨S', hS'U, hS'i, hS'c⟩ := ih _ hlt U' rfl
  have hvS' : v ∉ S' := fun h => hvU' (hS'U h)
  refine ⟨insert v S', Finset.insert_subset hv (hS'U.trans Finset.sdiff_subset), ?_, ?_⟩
  · -- independence
    have hfar : ∀ a ∈ S', a ≠ v ∧ ¬ E a v ∧ ¬ E v a := by
      intro a ha
      have haU' := hS'U ha
      rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_filter] at haU'
      obtain ⟨haU, hn⟩ := haU'
      have hav : a ≠ v := fun h => hn (Or.inl h)
      have hadj : ¬ adj E a v := fun h => hn (Or.inr ⟨haU, h⟩)
      exact ⟨hav, fun h1 => hadj ⟨hav, Or.inl h1⟩, fun h1 => hadj ⟨hav, Or.inr h1⟩⟩
    intro a ha b hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact (hfar b hb).2.2
    · exact (hfar a ha).2.1
    · exact hS'i a ha b hb hab
  · rw [Finset.card_insert_of_notMem hvS', Nat.cast_succ]
    rw [← Finset.sum_sdiff hNU]
    have h1 : ∑ u ∈ N, (1 : ℝ) / (deg E U u + 1) ≤ 1 := by
      have hcardN : (N.card : ℝ) = deg E U v + 1 := by
        rw [Finset.card_insert_of_notMem hvF]; simp [deg, F]
      calc ∑ u ∈ N, (1 : ℝ) / (deg E U u + 1) ≤ ∑ _u ∈ N, (1 : ℝ) / (deg E U v + 1) := by
            apply Finset.sum_le_sum
            intro u hu
            apply one_div_le_one_div_of_le (by positivity)
            have := hmin u (hNU hu)
            exact_mod_cast Nat.add_le_add_right this 1
        _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardN]
            field_simp
    have h2 : ∑ u ∈ U', (1 : ℝ) / (deg E U u + 1) ≤ S'.card := by
      refine le_trans (Finset.sum_le_sum fun u _ => ?_) hS'c
      apply one_div_le_one_div_of_le (by positivity)
      have : deg E U' u ≤ deg E U u := by
        unfold deg
        exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
      exact_mod_cast Nat.add_le_add_right this 1
    linarith

/-- Turán-type bound: `|U|² ≤ α ∑ (d(v)+1)`. -/
lemma turan (α : ℕ) (hα : IndepNumberLE E α) (U : Finset (Fin n)) :
    (U.card : ℝ) ^ 2 ≤ α * ∑ v ∈ U, ((deg E U v : ℝ) + 1) := by
  obtain ⟨S, -, hSi, hSc⟩ := caro_wei E _ U rfl
  have hSa : (S.card : ℝ) ≤ α := by exact_mod_cast hα S hSi
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq U (fun v => 1 / Real.sqrt ((deg E U v : ℝ) + 1))
    (fun v => Real.sqrt ((deg E U v : ℝ) + 1))
  have e1 : ∀ v ∈ U, 1 / Real.sqrt ((deg E U v : ℝ) + 1) * Real.sqrt ((deg E U v : ℝ) + 1) = 1 :=
    fun v _ => by
      have : 0 < Real.sqrt ((deg E U v : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      field_simp
  have e2 : ∀ v ∈ U, (1 / Real.sqrt ((deg E U v : ℝ) + 1)) ^ 2 = 1 / ((deg E U v : ℝ) + 1) :=
    fun v _ => by rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have e3 : ∀ v ∈ U, Real.sqrt ((deg E U v : ℝ) + 1) ^ 2 = (deg E U v : ℝ) + 1 :=
    fun v _ => Real.sq_sqrt (by positivity)
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at hcs
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hpos : 0 ≤ ∑ v ∈ U, ((deg E U v : ℝ) + 1) := Finset.sum_nonneg fun _ _ => by positivity
  calc (U.card : ℝ) ^ 2 ≤ (∑ v ∈ U, 1 / ((deg E U v : ℝ) + 1)) * ∑ v ∈ U, ((deg E U v : ℝ) + 1) :=
        hcs
    _ ≤ α * ∑ v ∈ U, ((deg E U v : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (hSc.trans hSa) hpos

/-- Degrees are at most twice the out-degrees in total. -/
lemma sum_deg_le (U : Finset (Fin n)) :
    ∑ v ∈ U, deg E U v ≤ 2 * ∑ v ∈ U, od E U v := by
  have h1 : ∀ v ∈ U, deg E U v ≤ (U.filter (fun u => u ≠ v ∧ E u v)).card + od E U v := by
    intro v _
    unfold deg od
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro u hu
    rw [Finset.mem_filter] at hu
    unfold adj at hu
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hu.2.2 with h | h
    · exact Or.inl ⟨hu.1, hu.2.1, h⟩
    · exact Or.inr ⟨hu.1, hu.2.1, h⟩
  have h2 : ∑ v ∈ U, (U.filter (fun u => u ≠ v ∧ E u v)).card = ∑ v ∈ U, od E U v := by
    unfold od
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro u _
    apply Finset.sum_congr rfl; intro w _
    congr 1
    apply propext
    exact ⟨fun h => ⟨fun e => h.1 e.symm, h.2⟩, fun h => ⟨fun e => h.1 e.symm, h.2⟩⟩
  have := Finset.sum_le_sum h1
  rw [Finset.sum_add_distrib, h2] at this
  omega

/-- Some vertex covers a `1/(2α)` fraction of `U`. -/
lemma big_vertex (α : ℕ) (hα : IndepNumberLE E α) (U : Finset (Fin n)) (hU : U.Nonempty) :
    ∃ v ∈ U, (U.card : ℝ) ≤ 2 * α * (1 + od E U v) := by
  have ht := turan E α hα U
  have hs := sum_deg_le E U
  have hs' : (∑ v ∈ U, (deg E U v : ℝ)) ≤ 2 * ∑ v ∈ U, (od E U v : ℝ) := by exact_mod_cast hs
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at ht
  -- ∑ (2α(1+od) - |U|) ≥ 0
  have hsum : ∑ _v ∈ U, (U.card : ℝ) ≤ ∑ v ∈ U, 2 * α * (1 + (od E U v : ℝ)) := by
    rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, mul_one]
    have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg _
    nlinarith
  obtain ⟨v, hv, h⟩ := Finset.exists_le_of_sum_le hU hsum
  exact ⟨v, hv, h⟩

lemma greedy (α : ℕ) (hα : IndepNumberLE E α) : ∀ k (U : Finset (Fin n)), U.card = k →
    ∃ W : Finset (Fin n), (∀ u ∈ U, u ∈ W ∨ ∃ w ∈ W, E w u) ∧
      (W.card : ℝ) ≤ (if k = 0 then 0 else 2 * α * Real.log k + 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U hU
  rcases U.eq_empty_or_nonempty with h | hne
  · subst h
    simp only [Finset.card_empty] at hU
    subst hU
    exact ⟨∅, by simp, by simp⟩
  have hk : k ≠ 0 := by rw [← hU]; exact (Finset.card_pos.2 hne).ne'
  have hα1 : 1 ≤ α := by
    obtain ⟨a, _⟩ := hne
    have := hα {a} (by intro x hx y hy hxy; simp at hx hy; exact absurd (hx.trans hy.symm) hxy)
    simpa using this
  obtain ⟨v, hv, hbig⟩ := big_vertex E α hα U hne
  set F := U.filter (fun u => u ≠ v ∧ E v u)
  have hvF : v ∉ F := by simp [F]
  set U' := U \ insert v F
  have hsub : insert v F ⊆ U := Finset.insert_subset hv (Finset.filter_subset _ _)
  have hcard' : U'.card + (1 + od E U v) = k := by
    rw [← hU, ← Finset.card_sdiff_add_card_eq_card hsub, Finset.card_insert_of_notMem hvF]
    simp only [od, F]; ring
  have hlt : U'.card < k := by omega
  obtain ⟨W', hW'c, hW'b⟩ := ih _ hlt U' rfl
  refine ⟨insert v W', ?_, ?_⟩
  · intro u hu
    by_cases hu' : u ∈ U'
    · rcases hW'c u hu' with h | ⟨w, hw, hwu⟩
      · exact Or.inl (Finset.mem_insert_of_mem h)
      · exact Or.inr ⟨w, Finset.mem_insert_of_mem hw, hwu⟩
    · simp only [U', Finset.mem_sdiff, not_and, not_not] at hu'
      rcases Finset.mem_insert.1 (hu' hu) with h | h
      · exact Or.inl (h ▸ Finset.mem_insert_self _ _)
      · exact Or.inr ⟨v, Finset.mem_insert_self _ _, (Finset.mem_filter.1 h).2.2⟩
  · rw [if_neg hk]
    have hW : ((insert v W').card : ℝ) ≤ W'.card + 1 := by
      exact_mod_cast Finset.card_insert_le v W'
    have hkpos : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    have hlogk : 0 ≤ Real.log k := Real.log_nonneg hkpos
    have hα1' : (1 : ℝ) ≤ α := by exact_mod_cast hα1
    by_cases h0 : U'.card = 0
    · rw [if_pos h0] at hW'b
      nlinarith
    · rw [if_neg h0] at hW'b
      -- k' ≤ k (1 - 1/(2α))
      have hk'pos : (0 : ℝ) < U'.card := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hrel : (U'.card : ℝ) + (1 + od E U v) = k := by exact_mod_cast hcard'
      have hk' : (U'.card : ℝ) ≤ k * (1 - 1 / (2 * α)) := by
        have : (k : ℝ) / (2 * α) ≤ 1 + od E U v := by
          rw [div_le_iff₀ (by positivity)]; rw [hU] at hbig; linarith
        have : (k : ℝ) * (1 - 1 / (2 * α)) = k - k / (2 * α) := by ring
        linarith
      have hq : 0 < 1 - 1 / (2 * (α : ℝ)) := by
        have : 1 / (2 * (α : ℝ)) ≤ 1 / 2 := by
          apply one_div_le_one_div_of_le (by norm_num); linarith
        linarith
      have hlog : Real.log U'.card ≤ Real.log k + Real.log (1 - 1 / (2 * α)) := by
        rw [← Real.log_mul (by linarith) hq.ne']
        exact Real.log_le_log hk'pos hk'
      have hlog2 : Real.log (1 - 1 / (2 * (α : ℝ))) ≤ -(1 / (2 * α)) := by
        have := Real.log_le_sub_one_of_pos hq; linarith
      have : 2 * (α : ℝ) * Real.log U'.card ≤ 2 * α * Real.log k - 1 := by
        have h2a : 0 < 2 * (α : ℝ) := by positivity
        have : 2 * (α : ℝ) * (1 / (2 * α)) = 1 := by field_simp
        nlinarith
      linarith

end GFL10

theorem solution (n : ℕ) (hn : 2 ≤ n) (E : Fin n → Fin n → Prop) (α : ℕ)
    (hα : IndepNumberLE E α) :
    ∃ V : Finset (Fin n), (V.card : ℝ) ≤ 50 * α * Real.log n ∧ IsWeaklyDominating E V := by
  obtain ⟨W, hWc, hWb⟩ := GFL10.greedy E α hα n Finset.univ (by simp)
  have hn0 : n ≠ 0 := by omega
  rw [if_neg hn0] at hWb
  refine ⟨W, ?_, fun v => hWc v (Finset.mem_univ _)⟩
  have hα1 : 1 ≤ α := by
    have := hα {⟨0, by omega⟩} (by
      intro x hx y hy hxy; simp at hx hy; exact absurd (hx.trans hy.symm) hxy)
    simpa using this
  have hα1' : (1 : ℝ) ≤ α := by exact_mod_cast hα1
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog2 : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  nlinarith
