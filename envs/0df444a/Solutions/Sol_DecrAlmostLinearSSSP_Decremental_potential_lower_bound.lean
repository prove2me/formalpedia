-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.potential_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:03:19.259776+00:00
-- url     : https://prove2.me/submissions/fcaef5cc-e793-4f2e-8d32-f04e3fba4329

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Potential


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma Walk.suffix_of_vertex {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v w : Fin n} {es : List (Fin k)} (h : Walk g active u v es)
    (hw : w ∈ u :: es.map g.head) :
    ∃ fs, Walk g active w v fs ∧ fs.IsSuffix es ∧
      (w :: fs.map g.head).IsSuffix (u :: es.map g.head) := by
  induction h generalizing w with
  | nil v =>
    simp only [List.map_nil, List.mem_singleton] at hw
    subst w
    exact ⟨[], .nil v, List.suffix_refl _, List.suffix_refl _⟩
  | @cons u v es e he h ih =>
    rw [List.map_cons, List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact ⟨e :: es, .cons (u := g.tail e) e he h, List.suffix_refl _, List.suffix_refl _⟩
    · obtain ⟨fs, hf, hs, hv⟩ := ih hw
      exact ⟨fs, hf, hs.trans (List.suffix_cons _ _),
        hv.trans (List.suffix_cons _ _)⟩

lemma Walk.erase_cycles {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) :
    ∃ fs, Walk g active u v fs ∧ fs.Sublist es ∧ (u :: fs.map g.head).Nodup := by
  classical
  induction h with
  | nil v => exact ⟨[], .nil v, List.Sublist.refl [], by simp⟩
  | @cons u v es e he h ih =>
    obtain ⟨fs, hf, hsub, hnodup⟩ := ih
    by_cases hm : g.tail e ∈ g.head e :: fs.map g.head
    · obtain ⟨gs, hg, hs, hv⟩ := hf.suffix_of_vertex hm
      exact ⟨gs, hg, (hs.sublist.trans hsub).trans (List.sublist_cons_self _ _),
        hnodup.sublist hv.sublist⟩
    · refine ⟨e :: fs, .cons (u := g.tail e) e he hf, hsub.cons_cons e, ?_⟩
      simpa only [List.map_cons, List.nodup_cons] using And.intro hm hnodup

lemma Reachable.short_walk {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} (h : Reachable g active u v) :
    ∃ es, Walk g active u v es ∧ es.length < n := by
  obtain ⟨es, hw⟩ := h
  obtain ⟨fs, hf, _, hn⟩ := hw.erase_cycles
  refine ⟨fs, hf, ?_⟩
  have hc := hn.length_le_card
  simpa only [List.length_cons, List.length_map, Fintype.card_fin, Nat.succ_le_iff] using hc

lemma Walk.cost_telescope {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es)
    (p : Fin n → ℝ) :
    (es.map fun e => p (g.tail e) - p (g.head e)).sum = p u - p v := by
  induction h with
  | nil v => simp
  | cons e he h ih => simpa only [List.map_cons, List.sum_cons, ih] using
      (sub_add_sub_cancel (p (g.tail e)) (p (g.head e)) (p _))

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma Walk.incoming {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (hne : u ≠ v) :
    ∃ e, g.head e = v := by
  induction h with
  | nil v => exact False.elim (hne rfl)
  | @cons u v es e he h ih =>
    by_cases hv : g.head e = v
    · exact ⟨e, hv⟩
    · exact ih hv

lemma core_indegree_pos (b : Core) (v : Fin b.input.n) (hv : v ≠ b.input.source) :
    1 ≤ indegree b v := by
  classical
  obtain ⟨es, hw⟩ := b.initially_reachable v
  obtain ⟨e, he⟩ := hw.incoming hv.symm
  simp only [indegree, if_neg hv]
  exact Finset.one_le_card.mpr ⟨e, by simp [he]⟩

lemma core_A_ge (b : Core) : 32 ≤ A b := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast (b.two.trans b.valid.1)
  have he := b.valid.2.2.2.1
  have he' := b.valid.2.2.2.2.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 1 ≤ logarithm2 (b.input.size + 1) := by
    unfold logarithm2
    apply (le_div_iff₀ hlog2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ b.input.size + 1)
  have ha : 32 * logarithm2 (b.input.size + 1) / b.input.accuracy ≤ A b := by
    exact Nat.le_ceil _
  have h32 : 32 ≤ 32 * logarithm2 (b.input.size + 1) / b.input.accuracy := by
    apply (le_div_iff₀ he).mpr
    nlinarith
  exact h32.trans ha

lemma core_Q_ge (b : Core) : 4 * (b.input.n : ℝ) ≤ Q b := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hw : (1 : ℝ) ≤ b.input.W := by exact_mod_cast b.valid.2.2.1
  dsimp [Q, H]
  nlinarith [mul_le_mul hn hw (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (0 : ℝ) ≤ b.input.n)]

lemma core_cost_bounds (b : Core) (active : Finset (Fin b.input.k)) (e : Fin b.input.k) :
    0 ≤ cost b active (.inl e) ∧ cost b active (.inl e) ≤ 1 / (8 * b.input.n) := by
  have hn : (0 : ℝ) < b.input.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) b.two)
  have hw : (0 : ℝ) < b.input.W := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) b.valid.2.2.1)
  have hH : 0 < H b := by dsimp [H]; positivity
  have hQ : 0 < Q b := by dsimp [Q]; positivity
  have hedge : (b.input.weight e : ℝ) ≤ H b := by
    have he : (b.input.weight e : ℝ) ≤ b.input.W := by exact_mod_cast (b.valid.2.2.2.2.2 e).2
    have hn' : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
    dsimp [H]
    nlinarith
  have he : cost b active (.inl e) ≤ H b / Q b := by
    simp only [cost]
    split_ifs
    · exact div_le_div_of_nonneg_right hedge hQ.le
    · exact le_rfl
  refine ⟨?_, he.trans ?_⟩
  · simp only [cost]
    split_ifs <;> positivity
  · dsimp [Q]
    field_simp
    ring_nf
    exact le_rfl

lemma core_coefficient_bounds (b : Core) (e : Edge b) :
    1 ≤ coefficient b e ∧ coefficient b e ≤ A b * b.input.size := by
  have hA : 1 ≤ A b := le_trans (by norm_num) (core_A_ge b)
  have hm : (1 : ℝ) ≤ b.input.size := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) (b.two.trans b.valid.1))
  cases e with
  | inl e =>
    simp only [coefficient]
    constructor
    · rfl
    · nlinarith
  | inr v =>
    have hq : (1 : ℝ) ≤ indegree b v.val := by exact_mod_cast core_indegree_pos b v.val v.property
    have hqm : (indegree b v.val : ℝ) ≤ b.input.size := by
      have hqk : indegree b v.val ≤ b.input.k := by
        simp only [indegree, if_neg v.property]
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact_mod_cast hqk.trans b.valid.2.1
    simp only [coefficient]
    constructor
    · nlinarith
    · exact mul_le_mul_of_nonneg_left hqm (by linarith)

lemma core_coefficient_sum (b : Core) :
    (∑ e, coefficient b e) ≤ 2 * A b * (b.input.size : ℝ) ^ 2 := by
  have hc : Fintype.card (Edge b) ≤ 2 * b.input.size := by
    rw [Fintype.card_sum]
    have hv : Fintype.card (ReturnVertex b) ≤ b.input.n := by
      simpa only [ReturnVertex, Fintype.card_fin] using
        (Fintype.card_subtype_le (fun v : Fin b.input.n => v ≠ b.input.source))
    simpa only [Fintype.card_fin, two_mul] using Nat.add_le_add b.valid.2.1 (hv.trans b.valid.1)
  calc
    (∑ e, coefficient b e) ≤ ∑ _ : Edge b, A b * b.input.size :=
      Finset.sum_le_sum fun e _ => (core_coefficient_bounds b e).2
    _ = Fintype.card (Edge b) * (A b * b.input.size) := by simp
    _ ≤ (2 * b.input.size) * (A b * b.input.size) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by
        have := core_A_ge b
        positivity)
    _ = 2 * A b * (b.input.size : ℝ) ^ 2 := by ring

lemma core_kappa_bounds (b : Core) :
    0 < kappa b ∧ kappa b ≤ 1 ∧
      4 * (b.input.n : ℝ) * A b * (b.input.size : ℝ) ^ 2 * kappa b ≤ 1 := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have hA := core_A_ge b
  have hQ := core_Q_ge b
  have hQpos : 0 < Q b := by linarith
  have hpos : 0 < A b * b.input.size * Q b := by positivity
  have hge : 1 ≤ A b * b.input.size * Q b := by
    have h1 : (1 : ℝ) ≤ A b := by linarith
    have h2 : (1 : ℝ) ≤ b.input.size := by linarith
    have h3 : (1 : ℝ) ≤ Q b := by linarith
    calc
      1 = 1 * 1 * 1 := by norm_num
      _ ≤ A b * b.input.size * Q b :=
        mul_le_mul (mul_le_mul h1 h2 (by norm_num) (by positivity)) h3 (by norm_num) (by positivity)
  have hsq : 4 * (b.input.n : ℝ) ≤ A b * (Q b) ^ 2 := by
    have hq : 1 ≤ Q b := by linarith
    have hqq : Q b ≤ (Q b) ^ 2 := by nlinarith
    have hqa : (Q b) ^ 2 ≤ A b * (Q b) ^ 2 := by nlinarith [sq_nonneg (Q b)]
    linarith
  have hbig : 4 * (b.input.n : ℝ) * A b * (b.input.size : ℝ) ^ 2 ≤
      (A b * b.input.size * Q b) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hsq (show 0 ≤ A b * (b.input.size : ℝ) ^ 2 by positivity)
    nlinarith only [hh]
  simp only [kappa, zpow_neg, zpow_ofNat, ← one_div]
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_one (by positivity : (0 : ℝ) < (A b * b.input.size * Q b) ^ 2)).mpr
    nlinarith
  · rw [mul_one_div]
    exact (div_le_one (by positivity)).mpr hbig

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma short_closed_slack_walk (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (e : Edge b) :
    ∃ es : List (Edge b), es.length ≤ b.input.n ∧
      (es.map (slack b active p)).sum + slack b active p e ≤ 1 / 8 := by
  have hn : (0 : ℝ) < b.input.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) b.two)
  have path_bound (v : Fin b.input.n) :
      ∃ es : List (Fin b.input.k), es.length < b.input.n ∧
        (es.map (fun a => cost b active (.inl a))).sum ≤ (es.length : ℝ) / (8 * b.input.n) ∧
        (es.map (fun a => slack b active p (.inl a))).sum =
          (es.map (fun a => cost b active (.inl a))).sum + p b.input.source - p v := by
    obtain ⟨es, he, hl⟩ := (b.initially_reachable v).short_walk
    refine ⟨es, hl, ?_, ?_⟩
    · calc
        (es.map (fun a => cost b active (.inl a))).sum ≤
            (es.map fun _ => (1 : ℝ) / (8 * b.input.n)).sum :=
          List.sum_le_sum fun a _ => (core_cost_bounds b active a).2
        _ = (es.length : ℝ) / (8 * b.input.n) := by simp [div_eq_mul_inv]
    · simp only [slack, incidence, tail, head]
      rw [List.sum_map_add, he.cost_telescope p]
      ring
  cases e with
  | inl e =>
    obtain ⟨es, hl, hc, ht⟩ := path_bound (b.input.graph.tail e)
    let r : ReturnVertex b := ⟨b.input.graph.head e, b.no_incoming_source e⟩
    refine ⟨es.map Sum.inl ++ [Sum.inr r], ?_, ?_⟩
    · simpa using hl
    · simp only [List.map_append, List.map_map, List.map_singleton, List.sum_append,
        List.sum_singleton, Function.comp_def]
      rw [ht]
      have he := (core_cost_bounds b active e).2
      have hlen : (es.length : ℝ) + 1 ≤ b.input.n := by exact_mod_cast hl
      have hsum : (es.map (fun a => cost b active (.inl a))).sum + cost b active (.inl e) ≤
          ((es.length : ℝ) + 1) / (8 * b.input.n) := by
        calc
          _ ≤ (es.length : ℝ) / (8 * b.input.n) + 1 / (8 * b.input.n) := add_le_add hc he
          _ = _ := by ring
      have hfinal : ((es.length : ℝ) + 1) / (8 * b.input.n) ≤ 1 / 8 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * b.input.n)).mpr
        nlinarith
      dsimp [slack, incidence, cost, tail, head, r] at *
      linarith [hsum.trans hfinal]
  | inr v =>
    obtain ⟨es, hl, hc, ht⟩ := path_bound v.val
    refine ⟨es.map Sum.inl, ?_, ?_⟩
    · simpa using hl.le
    · simp only [List.map_map, Function.comp_def]
      rw [ht]
      have hlen : (es.length : ℝ) ≤ b.input.n := by exact_mod_cast hl.le
      have hfinal : (es.length : ℝ) / (8 * b.input.n) ≤ 1 / 8 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * b.input.n)).mpr
        nlinarith
      dsimp [slack, incidence, cost, tail, head] at *
      linarith [hc.trans hfinal]

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma clippedLog_ge_log_bound {κ t L : ℝ} (hκ : 0 < κ) (hκL : κ ≤ L) (ht : t ≤ L) :
    -Real.log L ≤ clippedLog κ t := by
  unfold clippedLog
  split_ifs with h
  · exact neg_le_neg (Real.log_le_log (hκ.trans_le h) ht)
  · have hlog : Real.log κ ≤ Real.log L := Real.log_le_log hκ hκL
    have hdiv : t / κ ≤ 1 := (div_le_one hκ).mpr (le_of_not_ge h)
    linarith

lemma clippedLog_nonneg {κ t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (ht : t ≤ 1) :
    0 ≤ clippedLog κ t := by
  simpa using clippedLog_ge_log_bound hκ hκ1 ht

lemma clippedLog_negative_lower {κ t L N : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hL : 0 < L) (hN : 0 < N) (ht : t < -L / (2 * N)) :
    L / (2 * N * κ) ≤ clippedLog κ t := by
  have ht0 : t < 0 := lt_trans ht (div_neg_of_neg_of_pos (neg_neg_of_pos hL) (by positivity) : -L / (2 * N) < 0)
  rw [clippedLog, if_neg (by linarith)]
  have hlog : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1
  have hdiv : L / (2 * N * κ) ≤ -t / κ := by
    rw [div_mul_eq_div_div]
    apply div_le_div_of_nonneg_right _ hκ.le
    simpa only [neg_div, neg_neg] using (neg_le_neg ht.le)
  rw [neg_div] at hdiv
  linarith

lemma potential_floor (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) : 0 ≤ potential b active p := by
  classical
  obtain ⟨hκ, hκ1, hκsmall⟩ := core_kappa_bounds b
  have hn : (0 : ℝ) < b.input.n := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) b.two)
  by_cases hall : ∀ e, slack b active p e ≤ 1
  · exact Finset.sum_nonneg fun e _ => mul_nonneg
      (le_trans (by norm_num) (core_coefficient_bounds b e).1)
      (clippedLog_nonneg hκ hκ1 (hall e))
  · push Not at hall
    obtain ⟨e, he⟩ := hall
    obtain ⟨eMax, _, hmax⟩ := Finset.exists_max_image Finset.univ (slack b active p)
      (show (Finset.univ : Finset (Edge b)).Nonempty from ⟨e, Finset.mem_univ _⟩)
    let L := slack b active p eMax
    have hL : 1 < L := he.trans_le (hmax e (Finset.mem_univ _))
    have hLb : ∀ e, slack b active p e ≤ L := fun e => hmax e (Finset.mem_univ _)
    obtain ⟨es, hlen, hsum⟩ := short_closed_slack_walk b active p eMax
    have hnegative : ∃ a, slack b active p a < -L / (2 * b.input.n) := by
      by_contra! hno
      have hs : (es.map fun _ => -L / (2 * b.input.n)).sum ≤
          (es.map (slack b active p)).sum := List.sum_le_sum fun a _ => hno a
      have hlen' : (es.length : ℝ) ≤ b.input.n := by exact_mod_cast hlen
      have hmul : -(L / 2) ≤ (es.length : ℝ) * (-L / (2 * b.input.n)) := by
        have hh := mul_le_mul_of_nonpos_right hlen' (show -L / (2 * b.input.n) ≤ 0 by exact (div_neg_of_neg_of_pos (by linarith) (by positivity)).le)
        have hid : (b.input.n : ℝ) * (-L / (2 * b.input.n)) = -(L / 2) := by field_simp <;> ring
        linarith
      have hsum' : (es.map (slack b active p)).sum + L ≤ 1 / 8 := hsum
      have hs' : (es.length : ℝ) * (-L / (2 * b.input.n)) ≤ (es.map (slack b active p)).sum := by
        simpa using hs
      linarith
    obtain ⟨a, ha⟩ := hnegative
    have hlog : 0 ≤ Real.log L := Real.log_nonneg hL.le
    have hlogL : Real.log L ≤ L := le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
    have hterm (e : Edge b) :
        -coefficient b e * Real.log L + (if e = a then L / (2 * b.input.n * kappa b) else 0) ≤
          coefficient b e * clippedLog (kappa b) (slack b active p e) := by
      have hmu := (core_coefficient_bounds b e).1
      have hmu0 : 0 ≤ coefficient b e := by linarith
      by_cases hea : e = a
      · subst e
        simp only [eq_self_iff_true, ite_true]
        have hψ := clippedLog_negative_lower hκ hκ1 (by linarith : 0 < L) hn ha
        have htpos : 0 ≤ clippedLog (kappa b) (slack b active p a) := by
          exact le_trans (by positivity) hψ
        have hmuψ : clippedLog (kappa b) (slack b active p a) ≤
            coefficient b a * clippedLog (kappa b) (slack b active p a) := by nlinarith
        have hmulog : 0 ≤ coefficient b a * Real.log L := mul_nonneg hmu0 hlog
        nlinarith only [hψ, hmuψ, hmulog]
      · simp only [if_neg hea, add_zero]
        have hh := mul_le_mul_of_nonneg_left
          (clippedLog_ge_log_bound hκ (hκ1.trans hL.le) (hLb e)) hmu0
        nlinarith only [hh]
    have htotal := Finset.sum_le_sum (s := Finset.univ) fun e _ => hterm e
    have hrewrite : (∑ e : Edge b,
        (-coefficient b e * Real.log L + (if e = a then L / (2 * b.input.n * kappa b) else 0))) =
        -(∑ e : Edge b, coefficient b e) * Real.log L + L / (2 * b.input.n * kappa b) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    rw [hrewrite] at htotal
    have hS := core_coefficient_sum b
    have hcost : 2 * A b * (b.input.size : ℝ) ^ 2 ≤ 1 / (2 * b.input.n * kappa b) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (b.input.n : ℝ) * kappa b)).mpr
      nlinarith only [hκsmall]
    have hS0 : 0 ≤ ∑ e : Edge b, coefficient b e := Finset.sum_nonneg fun e _ =>
      le_trans (by norm_num) (core_coefficient_bounds b e).1
    have hbound : (∑ e : Edge b, coefficient b e) * Real.log L ≤ L / (2 * b.input.n * kappa b) := by
      calc
        _ ≤ (∑ e : Edge b, coefficient b e) * L := mul_le_mul_of_nonneg_left hlogL hS0
        _ ≤ (2 * A b * (b.input.size : ℝ) ^ 2) * L := mul_le_mul_of_nonneg_right hS (by linarith)
        _ ≤ (1 / (2 * b.input.n * kappa b)) * L := mul_le_mul_of_nonneg_right hcost (by linarith)
        _ = L / (2 * b.input.n * kappa b) := by ring
    dsimp [potential]
    linarith only [htotal, hbound]

end DecrAlmostLinearSSSP.Decremental

open DecrAlmostLinearSSSP.Decremental

theorem solution (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) :
    0 ≤ potential b active p := by
  exact potential_floor b active p
