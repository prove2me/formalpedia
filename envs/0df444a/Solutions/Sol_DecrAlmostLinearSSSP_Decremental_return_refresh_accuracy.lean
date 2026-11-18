-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.return_refresh_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:20:18.598745+00:00
-- url     : https://prove2.me/submissions/b38ccdfe-e3c6-4380-af18-659fb7b59116

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_stable_labels


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

lemma K_inverse_square_bound (K : ℝ) (hK : 32 ≤ K) :
    0 < K ^ (-2 : ℤ) ∧ K ^ (-2 : ℤ) ≤ 1 / 1024 := by
  have hKpos : 0 < K := by linarith
  refine ⟨zpow_pos hKpos _, ?_⟩
  simp only [zpow_neg, zpow_ofNat, ← one_div]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < K ^ 2) (by norm_num : (0 : ℝ) < 1024)).mpr
  nlinarith

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma capacity_pos (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (e : Edge b) : 0 < capacity b active p e := by
  have hc := (core_coefficient_bounds b e).1
  have hk := (core_kappa_bounds b).1
  unfold capacity
  exact div_pos (by linarith) (lt_of_lt_of_le hk (le_max_right _ _))

lemma gradient_update (b : Core) (f : Edge b → ℝ) (e : Edge b) (t : ℝ) (v : Fin b.input.n) :
    gradient b (Function.update f e t) v = gradient b f v -
      (if v = tail b e then t - f e else 0) + (if v = head b e then t - f e else 0) := by
  classical
  have hfun : (fun d => ((if head b d = v then Function.update f e t d else 0) -
      (if tail b d = v then Function.update f e t d else 0))) =
      Function.update (fun d => ((if head b d = v then f d else 0) -
        (if tail b d = v then f d else 0))) e
        ((if head b e = v then t else 0) - (if tail b e = v then t else 0)) := by
    funext d
    by_cases hd : d = e
    · subst d; simp
    · simp [Function.update_of_ne hd]
  unfold gradient
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ e)]
  clear hfun
  have hsum := Finset.add_sum_erase Finset.univ
    (fun d : Edge b => ((if head b d = v then f d else 0) -
      (if tail b d = v then f d else 0))) (Finset.mem_univ e)
  rw [← hsum, Finset.sdiff_singleton_eq_erase]
  simp only [@eq_comm _ v (tail b e), @eq_comm _ v (head b e)]
  by_cases hhead : head b e = v <;> by_cases htail : tail b e = v
  all_goals simp only [hhead, htail, if_true, if_false]
  all_goals ring

lemma gradient_dot (b : Core) (f : Edge b → ℝ) (x : Fin b.input.n → ℝ) :
    dot (gradient b f) x = - ∑ e, f e * incidence b x e := by
  classical
  unfold dot gradient incidence
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner (e : Edge b) :
      (∑ v, ((if head b e = v then f e else 0) - (if tail b e = v then f e else 0)) * x v) =
        -(f e * (x (tail b e) - x (head b e))) := by
    simp_rw [sub_mul, ite_mul, zero_mul]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  simp_rw [hinner]
  rw [Finset.sum_neg_distrib]

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

noncomputable def cacheModel (b : Core) (s : State b) (e : Edge b) : ℝ :=
  coefficient b e / max (cost b s.active e + initialLabel b (tail b e) -
    initialLabel b (head b e) + s.baseline e) (kappa b)

structure CacheInvariant (b : Core) (K : ℝ) (s : State b) : Prop where
  model : ∀ e, s.cache e = cacheModel b s e
  gradient_eq : s.cachedGradient = gradient b s.cache
  detector : ∀ e, e ∉ s.pending →
    |s.cache e * (s.y (tail b e) - s.y (head b e) - s.baseline e)| < K ^ (-2 : ℤ)

lemma cache_model_positive (b : Core) (s : State b) (e : Edge b) : 0 < cacheModel b s e := by
  have hmu := (core_coefficient_bounds b e).1
  have hk := (core_kappa_bounds b).1
  unfold cacheModel
  exact div_pos (by linarith) (lt_of_lt_of_le hk (le_max_right _ _))

lemma refresh_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K) (s : State b) (e : Edge b)
    (hmodel : ∀ d, d ≠ e → s.cache d = cacheModel b s d)
    (hgrad : s.cachedGradient = gradient b s.cache)
    (hdet : ∀ d, d ∉ s.pending →
      |s.cache d * (s.y (tail b d) - s.y (head b d) - s.baseline d)| < K ^ (-2 : ℤ)) :
    CacheInvariant b K (refresh b s e) := by
  classical
  constructor
  · intro d
    by_cases hd : d = e
    · subst d
      simp only [refresh, cacheModel, Function.update_self, capacity, slack, incidence, labels]
      congr 2
      ring
    · simpa only [refresh, cacheModel, Function.update_of_ne hd] using hmodel d hd
  · ext v
    change s.cachedGradient v - (if v = tail b e then capacity b s.active (labels b s) e - s.cache e else 0) +
      (if v = head b e then capacity b s.active (labels b s) e - s.cache e else 0) =
        gradient b (Function.update s.cache e (capacity b s.active (labels b s) e)) v
    rw [gradient_update, hgrad]
  · intro d hnot
    by_cases hd : d = e
    · subst d
      simp only [refresh, Function.update_self, sub_self, mul_zero, abs_zero]
      exact zpow_pos hK _
    · have hnot' : d ∉ s.pending := by
        intro hmem
        apply hnot
        simp only [refresh, List.mem_filter, decide_eq_true_eq]
        exact ⟨hmem, hd⟩
      simpa only [refresh, Function.update_of_ne hd] using hdet d hnot'

lemma initial_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K) :
    CacheInvariant b K (initializeState b) := by
  classical
  constructor
  · intro e
    simp only [initializeState, cacheModel, capacity, slack, incidence, Pi.zero_apply]
    congr 2
    ring
  · rfl
  · intro e _
    simp only [initializeState, Pi.zero_apply, sub_self, mul_zero, abs_zero]
    exact zpow_pos hK _

lemma toggle_cacheInvariant (b : Core) (K : ℝ) (s : State b) (r : CutReply b)
    (hs : CacheInvariant b K s) : CacheInvariant b K (toggle b K s r) := by
  classical
  refine ⟨hs.model, hs.gradient_eq, ?_⟩
  intro e he
  simpa only [toggle, List.mem_filter, Finset.mem_toList, Finset.mem_univ, true_and,
    decide_eq_true_eq, not_le] using he

lemma delete_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K) (s : State b) (e : Fin b.input.k)
    (hs : CacheInvariant b K s) : CacheInvariant b K (deleteState b s e) := by
  classical
  apply refresh_cacheInvariant b K hK
  · intro d hd
    have hm := hs.model d
    cases d with
    | inl d =>
      have hde : d ≠ e := by simpa using hd
      simpa only [cacheModel, cost, Finset.mem_erase, hde, ne_eq, not_false_eq_true, true_and] using hm
    | inr d => exact hm
  · exact hs.gradient_eq
  · exact hs.detector

lemma attained_cacheInvariant (b : Core) (K : ℝ) (hK : 0 < K)
    (choose : State b → CutReply b) (s : State b) (hs : Attained b K choose s) :
    CacheInvariant b K s := by
  induction hs with
  | start => exact initial_cacheInvariant b K hK
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · rw [repairStep, if_neg hstop]
      cases hp : s.pending with
      | nil =>
        simp only []
        by_cases hz : s.nonzeroEntries = 0
        · rw [if_pos hz]
          refine ⟨ih.model, ih.gradient_eq, ?_⟩
          intro e _
          exact ih.detector e (by simp [hp])
        · rw [if_neg hz]
          by_cases ht : (choose s).G / (choose s).U ≥ -1 / (4 * K)
          · simp only [freshReply, ht, if_true]
            refine ⟨ih.model, ih.gradient_eq, ?_⟩
            intro e _
            exact ih.detector e (by simp [hp])
          · simp only [freshReply, ht, if_false]
            exact toggle_cacheInvariant b K s (choose s) ih
      | cons e es =>
        simp only []
        exact refresh_cacheInvariant b K hK s e (fun d _ => ih.model d) ih.gradient_eq ih.detector
  | deletion hs hstop e he ih => exact delete_cacheInvariant b K hK _ e ih

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma refresh_sample_baseline (b : Core) (s : State b) (e : Edge b)
    (hs : ∀ v : ReturnVertex b, s.sample v.val = initialLabel b v.val + s.baseline (.inr v)) :
    ∀ v : ReturnVertex b, (refresh b s e).sample v.val =
      initialLabel b v.val + (refresh b s e).baseline (.inr v) := by
  classical
  intro v
  cases e with
  | inl e =>
    have he : (Sum.inr v : Edge b) ≠ Sum.inl e := by intro h; cases h
    simpa only [refresh, Function.update_of_ne he] using hs v
  | inr w =>
    by_cases hv : v = w
    · subst w
      simp only [refresh, Function.update_self, labels, tail, head]
      ring
    · have hval : v.val ≠ w.val := fun h => hv (Subtype.ext h)
      have he : (Sum.inr v : Edge b) ≠ Sum.inr w := fun h => hv (Sum.inr.inj h)
      simpa only [refresh, Function.update_of_ne hval, Function.update_of_ne he] using hs v

lemma attained_sample_baseline (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) :
    ∀ v : ReturnVertex b, s.sample v.val = initialLabel b v.val + s.baseline (.inr v) := by
  induction hs with
  | start => intro v; simp [initializeState]
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · rw [repairStep, if_neg hstop]
      cases hp : s.pending with
      | nil =>
        simp only []
        split_ifs <;> exact ih
      | cons e es => exact refresh_sample_baseline b s e ih
  | @deletion s hs hstop e he ih => exact refresh_sample_baseline b _ (.inl e) ih

lemma core_A_accuracy (b : Core) : 32 ≤ A b * b.input.accuracy := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have he := b.valid.2.2.2.1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : 1 ≤ logarithm2 (b.input.size + 1) := by
    unfold logarithm2
    apply (le_div_iff₀ hlog2).mpr
    simpa using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ b.input.size + 1)
  have ha : 32 * logarithm2 (b.input.size + 1) / b.input.accuracy ≤ A b := Nat.le_ceil _
  have hh := (div_le_iff₀ he).mp ha
  nlinarith

lemma attained_stopped_drained (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) : Stable b s → s.pending = [] := by
  induction hs with
  | start => simp [Stable, initializeState]
  | @repair s hs ih =>
    intro hstable
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih hstop
    · change (repairStep b K choose s).stopped = true at hstable
      cases hp : s.pending with
      | nil =>
        by_cases hz : s.nonzeroEntries = 0
        · simp only [repairStep, if_neg hstop, hp, if_pos hz]
        · by_cases ht : (choose s).G / (choose s).U ≥ -1 / (4 * K)
          · simp only [repairStep, if_neg hstop, hp, if_neg hz, freshReply, if_pos ht]
          · simp only [repairStep, if_neg hstop, hp, if_neg hz, freshReply, if_neg ht, toggle] at hstable
            exact False.elim (hstop hstable)
      | cons e es =>
        simp only [repairStep, if_neg hstop, hp, refresh] at hstable
        exact False.elim (hstop hstable)
  | @deletion s hs hstop e he ih => simp [Stable, deleteState, refresh]

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma sample_accuracy_of_drift {p sample κ mu eps r : ℝ}
    (hk : 0 < κ) (hp : κ < p) (hmu : 0 < mu)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hmueps : 32 ≤ mu * eps) (hr : r ≤ 1)
    (hdrift : |(mu / max sample κ) * (p - sample)| ≤ r) :
    (1 - eps / 8) * p ≤ sample ∧ sample ≤ (1 + eps / 8) * p := by
  let w := |p - sample|
  have hw : 0 ≤ w := abs_nonneg _
  have ht : 0 < max sample κ := lt_of_lt_of_le hk (le_max_right _ _)
  have hbound : mu * w ≤ max sample κ := by
    have hd : mu / max sample κ * w ≤ r := by
      simpa only [abs_mul, abs_of_pos (div_pos hmu ht)] using hdrift
    rw [div_mul_eq_mul_div] at hd
    have hh := (div_le_iff₀ ht).mp hd
    have hh' := mul_le_mul_of_nonneg_right hr ht.le
    linarith
  have hm : max sample κ ≤ p + w := by
    apply max_le
    · have hh := neg_le_abs (p - sample)
      dsimp [w]
      linarith
    · linarith
  have h1 := mul_le_mul_of_nonneg_right hmueps hw
  have h2 := mul_le_mul_of_nonneg_left (hbound.trans hm) heps.le
  have h3 := mul_le_mul_of_nonneg_right heps1 hw
  have hw' : w ≤ (eps / 8) * p := by nlinarith only [h1, h2, h3, hw]
  obtain ⟨hl, hu⟩ := abs_le.mp hw'
  constructor <;> linarith

lemma return_accuracy (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (choose : State b → CutReply b) (hcut : CutQuality b K choose)
    (s : State b) (hs : Attained b K choose s) (hstable : Stable b s) :
    ∀ v, v ≠ b.input.source →
      (1 - b.input.accuracy / 8) * labels b s v ≤ s.sample v ∧
      s.sample v ≤ (1 + b.input.accuracy / 8) * labels b s v := by
  intro v hv
  let r : ReturnVertex b := ⟨v, hv⟩
  have hi := attained_cacheInvariant b K (by linarith : 0 < K) choose s hs
  have hsample := attained_sample_baseline b K choose s hs r
  have hdrain := attained_stopped_drained b K choose s hs hstable
  have hsource : labels b s b.input.source = 0 := by simp [labels, initialLabel]
  have hpositive := (stable_labels b K hK choose hcut s hs hstable).2.1 (.inr r)
  simp only [slack, cost, incidence, tail, head, hsource, sub_zero, zero_add] at hpositive
  have hcache : s.cache (.inr r) =
      (A b * indegree b v) / max (s.sample v) (kappa b) := by
    rw [hi.model]
    unfold cacheModel
    simp only [coefficient, cost, tail, head]
    have hsrc : initialLabel b b.input.source = 0 := by simp [initialLabel]
    rw [hsrc, zero_add, sub_zero, ← hsample]
  have hdelta : s.y v - s.y b.input.source - s.baseline (.inr r) = labels b s v - s.sample v := by
    rw [hsample]
    dsimp [labels]
    ring
  have hd := (hi.detector (.inr r) (by simp [hdrain])).le
  simp only [tail, head] at hd
  rw [hcache, hdelta] at hd
  have hq : (1 : ℝ) ≤ indegree b v := by exact_mod_cast core_indegree_pos b v hv
  have hA := core_A_ge b
  have hAeps := core_A_accuracy b
  have heps := b.valid.2.2.2.1
  have hmu : 0 < A b * indegree b v := by positivity
  have hmueps : 32 ≤ (A b * indegree b v) * b.input.accuracy := by
    have hh := mul_le_mul_of_nonneg_right hq (show 0 ≤ A b * b.input.accuracy by positivity)
    nlinarith only [hh, hAeps]
  exact sample_accuracy_of_drift (core_kappa_bounds b).1 hpositive hmu heps b.valid.2.2.2.2.1
    hmueps ((K_inverse_square_bound K hK).2.trans (by norm_num)) hd

end DecrAlmostLinearSSSP.Decremental

open DecrAlmostLinearSSSP.Decremental

theorem solution (b : Core) (K : ℝ) (hK : 32 ≤ K)
    (choose : State b → CutReply b) (hcut : CutQuality b K choose)
    (s : State b) (hs : Attained b K choose s) (hstable : Stable b s) :
    ∀ v, v ≠ b.input.source →
      (1 - b.input.accuracy / 8) * labels b s v ≤ s.sample v ∧
      s.sample v ≤ (1 + b.input.accuracy / 8) * labels b s v := by
  exact return_accuracy b K hK choose hcut s hs hstable
