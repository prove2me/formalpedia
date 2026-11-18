-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.toggle_descent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:31:26.327134+00:00
-- url     : https://prove2.me/submissions/fa42d4e2-37ff-4ba5-966b-202b9f737812

import Definitions.Def_DecrAlmostLinearSSSP_Decremental_Algorithm
import Theorems.Thm_DecrAlmostLinearSSSP_Decremental_cache_accuracy


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

lemma sum_replace_two {n : ℕ} (f g : Fin n → ℕ) (a z : Fin n) (haz : a ≠ z)
    (heq : ∀ v, v ≠ a → v ≠ z → g v = f v) :
    (∑ v, g v) = (∑ v, f v) + g a + g z - f a - f z := by
  classical
  have hsum (f : Fin n → ℕ) : (∑ v, f v) =
      f a + f z + ∑ v ∈ (Finset.univ.erase a).erase z, f v := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ a)]
    rw [← Finset.add_sum_erase (Finset.univ.erase a) f (a := z) (by simp [haz.symm])]
    omega
  have hr : (∑ v ∈ (Finset.univ.erase a).erase z, g v) =
      ∑ v ∈ (Finset.univ.erase a).erase z, f v := by
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
    exact heq v hv.2 hv.1
  rw [hsum f, hsum g, hr]
  omega

lemma refresh_counter (b : Core) (s : State b) (e : Edge b)
    (hc : s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v)) :
    (refresh b s e).nonzeroEntries = ∑ v, nonzero ((refresh b s e).cachedGradient v) := by
  classical
  let a := tail b e
  let z := head b e
  let d := capacity b s.active (labels b s) e - s.cache e
  let g : Fin b.input.n → ℝ := fun v => s.cachedGradient v - (if v = a then d else 0) +
    (if v = z then d else 0)
  change (if a = z then s.nonzeroEntries else
    s.nonzeroEntries + nonzero (g a) + nonzero (g z) -
      nonzero (s.cachedGradient a) - nonzero (s.cachedGradient z)) = ∑ v, nonzero (g v)
  by_cases haz : a = z
  · rw [if_pos haz, hc]
    apply Finset.sum_congr rfl
    intro v _
    dsimp [g]
    rw [haz]
    congr 1
    ring
  · rw [if_neg haz, hc]
    symm
    apply sum_replace_two _ _ a z haz
    intro v hva hvz
    simp only [g, if_neg hva, if_neg hvz, sub_zero, add_zero]

lemma attained_counter (b : Core) (K : ℝ) (choose : State b → CutReply b)
    (s : State b) (hs : Attained b K choose s) :
    s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v) := by
  induction hs with
  | start => rfl
  | @repair s hs ih =>
    by_cases hstop : s.stopped = true
    · simpa only [repairStep, if_pos hstop] using ih
    · rw [repairStep, if_neg hstop]
      cases hp : s.pending with
      | nil =>
        simp only []
        split_ifs <;> exact ih
      | cons e es => exact refresh_counter b s e ih
  | @deletion s hs hstop e he ih => exact refresh_counter b _ (.inl e) ih

lemma zero_counter_gradient (b : Core) (s : State b)
    (hc : s.nonzeroEntries = ∑ v, nonzero (s.cachedGradient v))
    (hz : s.nonzeroEntries = 0) : s.cachedGradient = 0 := by
  funext v
  have hv : nonzero (s.cachedGradient v) ≤ ∑ w, nonzero (s.cachedGradient w) :=
    Finset.single_le_sum (f := fun w => nonzero (s.cachedGradient w)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  rw [← hc, hz] at hv
  change s.cachedGradient v = 0
  by_contra hne
  simp only [nonzero, if_neg hne] at hv
  omega

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma clippedLog_secant_upper {κ a b : ℝ} (hk : 0 < κ) :
    clippedLog κ b - clippedLog κ a ≤ (a - b) / max b κ := by
  by_cases ha : κ ≤ a <;> by_cases hb : κ ≤ b
  · have hap : 0 < a := hk.trans_le ha
    have hbp : 0 < b := hk.trans_le hb
    have hl := Real.log_le_sub_one_of_pos (div_pos hap hbp)
    rw [Real.log_div hap.ne' hbp.ne'] at hl
    simp only [clippedLog, if_pos ha, if_pos hb, max_eq_left hb, sub_div, div_self hbp.ne']
    linarith
  · have hap : 0 < a := hk.trans_le ha
    have hl := Real.log_le_sub_one_of_pos (div_pos hap hk)
    rw [Real.log_div hap.ne' hk.ne'] at hl
    simp only [clippedLog, if_pos ha, if_neg hb, max_eq_right (le_of_not_ge hb), sub_div]
    linarith
  · have hbp : 0 < b := hk.trans_le hb
    have hl := Real.log_le_sub_one_of_pos (div_pos hk hbp)
    rw [Real.log_div hk.ne' hbp.ne'] at hl
    have hdiv : (κ - a) / b ≤ (κ - a) / κ :=
      div_le_div_of_nonneg_left (by linarith : 0 ≤ κ - a) hk hb
    rw [sub_div, sub_div, div_self hk.ne'] at hdiv
    simp only [clippedLog, if_neg ha, if_pos hb, max_eq_left hb, sub_div, div_self hbp.ne']
    linarith
  · simp only [clippedLog, if_neg ha, if_neg hb, max_eq_right (le_of_not_ge hb), sub_div]
    linarith

lemma clippedLog_remainder {κ a d : ℝ} (hk : 0 < κ) :
    clippedLog κ (a + d) - clippedLog κ a + d / max a κ ≤
      d ^ 2 / (max a κ * max (a + d) κ) := by
  have ht : 0 < max a κ := lt_of_lt_of_le hk (le_max_right _ _)
  have hu : 0 < max (a + d) κ := lt_of_lt_of_le hk (le_max_right _ _)
  have hs := clippedLog_secant_upper (a := a) (b := a + d) hk
  have hd : |max (a + d) κ - max a κ| ≤ |d| := by
    simpa only [add_sub_cancel_left] using abs_max_sub_max_le_abs (a + d) a κ
  have hprod : d * (max (a + d) κ - max a κ) ≤ d ^ 2 := by
    calc
      _ ≤ |d * (max (a + d) κ - max a κ)| := le_abs_self _
      _ = |d| * |max (a + d) κ - max a κ| := abs_mul _ _
      _ ≤ |d| * |d| := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = d ^ 2 := by rw [← sq_abs]; ring
  have halg : (a - (a + d)) / max (a + d) κ + d / max a κ =
      d * (max (a + d) κ - max a κ) / (max a κ * max (a + d) κ) := by
    field_simp
    ring
  calc
    _ ≤ (a - (a + d)) / max (a + d) κ + d / max a κ := by linarith only [hs]
    _ = _ := halg
    _ ≤ _ := div_le_div_of_nonneg_right hprod (by positivity)

lemma weighted_clippedLog_remainder {κ a d mu q : ℝ} (hk : 0 < κ) (hmu : 1 ≤ mu)
    (hq : q < 1) (hd : |d| ≤ q * max a κ) :
    mu * (clippedLog κ (a + d) - clippedLog κ a + d / max a κ) ≤
      ((mu / max a κ) * |d|) ^ 2 / (1 - q) := by
  let t := max a κ
  let u := max (a + d) κ
  have ht : 0 < t := lt_of_lt_of_le hk (le_max_right _ _)
  have hu : 0 < u := lt_of_lt_of_le hk (le_max_right _ _)
  have hmu0 : 0 < mu := by linarith
  have hq0 : 0 < 1 - q := by linarith
  have hdiff : |u - t| ≤ |d| := by
    simpa only [add_sub_cancel_left] using abs_max_sub_max_le_abs (a + d) a κ
  have hden : (1 - q) * t ≤ mu * u := by
    have hh := (abs_le.mp hdiff).1
    have hm : u ≤ mu * u := by nlinarith only [hmu, hu.le]
    nlinarith only [hh, hd, hm]
  have hfrac : mu * (d ^ 2 / (t * u)) ≤ ((mu / t) * |d|) ^ 2 / (1 - q) := by
    have hmult := mul_le_mul_of_nonneg_right hden
      (show 0 ≤ mu * d ^ 2 * t by positivity)
    have hid : ((mu / t) * |d|) ^ 2 / (1 - q) =
        mu ^ 2 * d ^ 2 / (t ^ 2 * (1 - q)) := by
      rw [mul_pow, div_pow, sq_abs]
      field_simp
      <;> ring
    rw [hid, ← mul_div_assoc]
    apply (div_le_div_iff₀ (by positivity : 0 < t * u) (by positivity : 0 < t ^ 2 * (1 - q))).mpr
    nlinarith only [hmult]
  exact (mul_le_mul_of_nonneg_left (clippedLog_remainder (a := a) (d := d) hk) hmu0.le).trans hfrac

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma potential_remainder (b : Core) (active : Finset (Fin b.input.k))
    (p x : Fin b.input.n → ℝ) (q : ℝ) (hq : q < 1)
    (hnorm : norm b (capacity b active p) x ≤ q) :
    potential b active (fun v => p v + x v) - potential b active p -
      dot (gradient b (capacity b active p)) x ≤ q ^ 2 / (1 - q) := by
  classical
  let f := capacity b active p
  have hf (e : Edge b) : 0 < f e := capacity_pos b active p e
  have hterm (e : Edge b) : f e * |incidence b x e| ≤ norm b f x :=
    Finset.single_le_sum (fun d _ => mul_nonneg (hf d).le (abs_nonneg _)) (Finset.mem_univ e)
  have hdelta (e : Edge b) : |incidence b x e| ≤ q * max (slack b active p e) (kappa b) := by
    have hk := (core_kappa_bounds b).1
    have ht : 0 < max (slack b active p e) (kappa b) := lt_of_lt_of_le hk (le_max_right _ _)
    have hh := (hterm e).trans hnorm
    change (coefficient b e / max (slack b active p e) (kappa b)) * |incidence b x e| ≤ q at hh
    rw [div_mul_eq_mul_div] at hh
    have hm := (div_le_iff₀ ht).mp hh
    have hmu := (core_coefficient_bounds b e).1
    have hle : |incidence b x e| ≤ coefficient b e * |incidence b x e| := by
      nlinarith only [hmu, abs_nonneg (incidence b x e)]
    exact hle.trans hm
  have hpoint (e : Edge b) := weighted_clippedLog_remainder
    (a := slack b active p e) (d := incidence b x e) (q := q)
    (core_kappa_bounds b).1 (core_coefficient_bounds b e).1 hq (hdelta e)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun e _ => hpoint e
  have hslack (e : Edge b) : slack b active (fun v => p v + x v) e =
      slack b active p e + incidence b x e := by dsimp [slack, incidence]; ring
  have hleft : (∑ e, coefficient b e *
      (clippedLog (kappa b) (slack b active p e + incidence b x e) -
        clippedLog (kappa b) (slack b active p e) +
          incidence b x e / max (slack b active p e) (kappa b))) =
      potential b active (fun v => p v + x v) - potential b active p -
        dot (gradient b f) x := by
    rw [gradient_dot]
    simp only [potential, hslack, sub_neg_eq_add]
    simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro e _
    dsimp [f, capacity]
    ring
  rw [hleft] at hsum
  have hr : (∑ e, ((coefficient b e / max (slack b active p e) (kappa b)) * |incidence b x e|) ^ 2 / (1 - q)) =
      (∑ e, (f e * |incidence b x e|) ^ 2) / (1 - q) := by
    rw [Finset.sum_div]
    rfl
  rw [hr] at hsum
  have hsquares : (∑ e, (f e * |incidence b x e|) ^ 2) ≤ (norm b f x) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun e _ => mul_nonneg (hf e).le (abs_nonneg _))
  have hn0 : 0 ≤ norm b f x := Finset.sum_nonneg fun e _ => mul_nonneg (hf e).le (abs_nonneg _)
  have hsq : (norm b f x) ^ 2 ≤ q ^ 2 := by nlinarith only [hnorm, hn0]
  exact hsum.trans (div_le_div_of_nonneg_right (hsquares.trans hsq) (by linarith))

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

def cutDirection {n : ℕ} (C : Finset (Fin n)) (tau : ℝ) (v : Fin n) : ℝ :=
  if v ∈ C then tau else 0

lemma physical_norm_cut {n k : ℕ} (h : Physical n k) (C : Finset (Fin n))
    (tau : ℝ) (ht : 0 ≤ tau) :
    physicalNorm h (cutDirection C tau) = tau * cutCapacity h C := by
  classical
  unfold physicalNorm cutCapacity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ha : h.graph.tail e ∈ C <;> by_cases hb : h.graph.head e ∈ C
  all_goals simp [cutDirection, ha, hb, abs_of_nonneg ht, mul_comm]

lemma dot_cut {n : ℕ} (g : Fin n → ℝ) (C : Finset (Fin n)) (tau : ℝ) :
    dot g (cutDirection C tau) = tau * ∑ v ∈ C, g v := by
  classical
  calc
    dot g (cutDirection C tau) = ∑ v ∈ C, g v * cutDirection C tau v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ C)
      intro v _ hv
      simp only [cutDirection, if_neg hv, mul_zero]
    _ = ∑ v ∈ C, tau * g v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp only [cutDirection, if_pos hv, mul_comm]
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma cachedPhysical_norm_eq (b : Core) (s : State b) (x : Fin b.input.n → ℝ) :
    physicalNorm (cachedPhysical b s) x = norm b s.cache x := by
  classical
  simp only [physicalNorm, cachedPhysical, norm]
  exact Equiv.sum_comp (Fintype.equivFin (Edge b)).symm (fun e : Edge b => s.cache e * |incidence b x e|)

lemma toggle_potential (b : Core) (K : ℝ) (s : State b) (r : CutReply b) :
    potential b (toggle b K s r).active (labels b (toggle b K s r)) =
      potential b s.active (fun v => labels b s v + cutDirection r.cut (1 / (K ^ 2 * r.U)) v) := by
  classical
  unfold potential
  apply Finset.sum_congr rfl
  intro e _
  congr 2
  dsimp [slack, incidence, labels, toggle, cutDirection]
  split_ifs <;> ring

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
namespace DecrAlmostLinearSSSP.Decremental

lemma toggle_numeric_bounds (K : ℝ) (hK : 32 ≤ K) :
    0 < 1 / (K ^ 2 - 1) ∧ 1 / (K ^ 2 - 1) < 1 ∧
    K ^ (-2 : ℤ) * (1 / (K ^ 2 - 1)) ≤ 2 / K ^ 4 ∧
    (1 / (K ^ 2 - 1)) ^ 2 / (1 - 1 / (K ^ 2 - 1)) ≤ 2 / K ^ 4 ∧
    1 / (8 * K ^ 3) ≤ 1 / (4 * K ^ 3) - 4 / K ^ 4 := by
  have hKpos : 0 < K := by linarith
  have h1 : 0 < K ^ 2 - 1 := by nlinarith
  have h2 : 0 < K ^ 2 - 2 := by nlinarith
  have hq : 1 / (K ^ 2 - 1) < 1 := (div_lt_one h1).mpr (by nlinarith)
  refine ⟨by positivity, hq, ?_, ?_, ?_⟩
  · have hid : K ^ (-2 : ℤ) * (1 / (K ^ 2 - 1)) = 1 / ((K ^ 2 - 1) * K ^ 2) := by
      simp only [zpow_neg, zpow_ofNat, ← one_div]
      field_simp [hKpos.ne', h1.ne', h2.ne', show (-2 + K ^ 2) ≠ 0 by linarith]
      <;> ring
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < (K ^ 2 - 1) * K ^ 2) (by positivity : 0 < K ^ 4)).mpr
    nlinarith [sq_nonneg K]
  · have hid : (1 / (K ^ 2 - 1)) ^ 2 / (1 - 1 / (K ^ 2 - 1)) =
        1 / ((K ^ 2 - 1) * (K ^ 2 - 2)) := by
      field_simp [hKpos.ne', h1.ne', h2.ne']
      <;> ring_nf
      <;> nlinarith only [mul_inv_cancel₀ (show (-2 + K ^ 2) ≠ 0 by linarith)]
    rw [hid]
    apply (div_le_div_iff₀ (by positivity : 0 < (K ^ 2 - 1) * (K ^ 2 - 2)) (by positivity : 0 < K ^ 4)).mpr
    have ht : 0 ≤ K ^ 2 * (K ^ 2 - 6) := mul_nonneg (sq_nonneg _) (by nlinarith)
    nlinarith only [ht]
  · have hid : 1 / (4 * K ^ 3) - 4 / K ^ 4 - 1 / (8 * K ^ 3) = (K - 32) / (8 * K ^ 4) := by
      field_simp [hKpos.ne', h1.ne', h2.ne', show (-2 + K ^ 2) ≠ 0 by linarith]
      <;> ring
    have hh : 0 ≤ (K - 32) / (8 * K ^ 4) := div_nonneg (sub_nonneg.mpr hK) (by positivity)
    linarith only [hid, hh]

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma actual_toggle_descent (b : Core) (K : ℝ) (hK : 32 ≤ K) (choose : State b → CutReply b)
    (hcut : CutQuality b K choose) (s : State b) (hs : Attained b K choose s)
    (hrunning : s.stopped = false) (hdrain : s.pending = []) (hnonzero : s.nonzeroEntries ≠ 0)
    (htest : (choose s).G / (choose s).U < -1 / (4 * K)) :
    potential b s.active (labels b s) -
      potential b (repairStep b K choose s).active (labels b (repairStep b K choose s)) ≥
        1 / (8 * K ^ 3) := by
  classical
  have hKpos : 0 < K := by linarith
  have hgrad : s.cachedGradient ≠ 0 := by
    intro hg
    have hc := attained_counter b K choose s hs
    rw [hg] at hc
    simp only [Pi.zero_apply, nonzero, if_true, Finset.sum_const_zero] at hc
    exact hnonzero hc
  let r := choose s
  have hqual := hcut s hs hdrain hgrad
  have hU : 0 < r.U := hqual.2.1
  let tau : ℝ := 1 / (K ^ 2 * r.U)
  let x := cutDirection r.cut tau
  let q : ℝ := 1 / (K ^ 2 - 1)
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hr := K_inverse_square_bound K hK
  obtain ⟨hqpos, hq1, herrornum, hremnum, hlast⟩ := toggle_numeric_bounds K hK
  obtain ⟨hedge, herror, hnorm⟩ := cache_accuracy b K hK choose hcut s hs hdrain
  have hxcache : norm b s.cache x ≤ 1 / K ^ 2 := by
    rw [← cachedPhysical_norm_eq, physical_norm_cut _ _ _ htau]
    have hh := mul_le_mul_of_nonneg_left hqual.2.2.2.1 htau
    have hid : tau * r.U = 1 / K ^ 2 := by dsimp [tau]; field_simp
    exact hh.trans hid.le
  have hx : norm b (capacity b s.active (labels b s)) x ≤ q := by
    have hh := (hnorm x).1.trans hxcache
    have hr1 : 0 < 1 - K ^ (-2 : ℤ) := by linarith only [hr.2]
    have hn : norm b (capacity b s.active (labels b s)) x ≤ (1 / K ^ 2) / (1 - K ^ (-2 : ℤ)) :=
      (le_div_iff₀ hr1).mpr (by simpa only [mul_comm] using hh)
    have hid : (1 / K ^ 2) / (1 - K ^ (-2 : ℤ)) = q := by
      dsimp [q]
      simp only [zpow_neg, zpow_ofNat, ← one_div]
      field_simp
      <;> ring
    exact hn.trans hid.le
  have hcx : dot s.cachedGradient x = tau * r.G := by
    rw [dot_cut]
    have hG : r.G = ∑ v ∈ r.cut, s.cachedGradient v := hqual.2.2.1
    rw [← hG]
  have htest' : tau * r.G ≤ -1 / (4 * K ^ 3) := by
    have hleft : tau * r.G = ((choose s).G / (choose s).U) / K ^ 2 := by
      dsimp [tau, r]
      field_simp
      <;> ring
    have hright : (-1 / (4 * K)) / K ^ 2 = -1 / (4 * K ^ 3) := by
      field_simp
      <;> ring
    rw [hleft, ← hright]
    exact div_le_div_of_nonneg_right htest.le (sq_nonneg K)
  have hslope : dot (gradient b (capacity b s.active (labels b s))) x ≤
      -1 / (4 * K ^ 3) + 2 / K ^ 4 := by
    have he := herror x
    rw [show dot (fun v => gradient b (capacity b s.active (labels b s)) v - s.cachedGradient v) x =
      dot (gradient b (capacity b s.active (labels b s))) x - dot s.cachedGradient x from
        by simp only [dot, sub_mul, Finset.sum_sub_distrib]] at he
    have hh := (abs_le.mp he).2
    have hmul := mul_le_mul_of_nonneg_left hx hr.1.le
    rw [hcx] at hh
    nlinarith only [hh, hmul, herrornum, htest']
  have hrem := potential_remainder b s.active (labels b s) x q hq1 hx
  have hstep : repairStep b K choose s = toggle b K s r := by
    simp only [repairStep, hrunning, Bool.false_eq_true, if_false, hdrain, hnonzero,
      freshReply, not_le.mpr htest, r]
  rw [hstep, toggle_potential]
  change potential b s.active (labels b s) - potential b s.active (fun v => labels b s v + x v) ≥ _
  dsimp [q] at hrem
  rw [neg_div] at hslope
  simp only [div_eq_mul_inv] at hrem hremnum hslope hlast ⊢
  nlinarith only [hrem, hremnum, hslope, hlast]

end DecrAlmostLinearSSSP.Decremental

open DecrAlmostLinearSSSP.Decremental

theorem solution (b : Core) (K : ℝ) (hK : 32 ≤ K) (choose : State b → CutReply b)
    (hcut : CutQuality b K choose) (s : State b) (hs : Attained b K choose s)
    (hrunning : s.stopped = false) (hdrain : s.pending = []) (hnonzero : s.nonzeroEntries ≠ 0)
    (htest : (choose s).G / (choose s).U < -1 / (4 * K)) :
    potential b s.active (labels b s) -
      potential b (repairStep b K choose s).active (labels b (repairStep b K choose s)) ≥
        1 / (8 * K ^ 3) := by
  exact actual_toggle_descent b K hK choose hcut s hs hrunning hdrain hnonzero htest
