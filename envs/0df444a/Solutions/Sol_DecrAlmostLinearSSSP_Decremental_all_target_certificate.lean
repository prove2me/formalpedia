-- Prove2me | solution 1 for DecrAlmostLinearSSSP.Decremental.all_target_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:56:53.509831+00:00
-- url     : https://prove2.me/submissions/5e14df6c-c51b-4b9d-aa4e-c93d532dbc37

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

lemma Walk.append {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v w : Fin n} {es fs : List (Fin k)} (h : Walk g active u v es)
    (h' : Walk g active v w fs) : Walk g active u w (es ++ fs) := by
  induction h with
  | nil v => exact h'
  | cons e he h ih => exact .cons (u := g.tail e) e he (ih h')

lemma Walk.eq_of_empty {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (hnil : es = []) : u = v := by
  induction h with
  | nil v => rfl
  | cons e he h ih => cases hnil

lemma Reachable.trans {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v w : Fin n} (h : Reachable g active u v) (h' : Reachable g active v w) :
    Reachable g active u w := by
  obtain ⟨es, he⟩ := h
  obtain ⟨fs, hf⟩ := h'
  exact ⟨es ++ fs, he.append hf⟩

noncomputable def shortEdgeLists (n k : ℕ) : Finset (List (Fin k)) :=
  Finset.univ.biUnion fun l : Fin n =>
    Finset.univ.image fun f : Fin l.val → Fin k => List.ofFn f

lemma mem_shortEdgeLists {n k : ℕ} (es : List (Fin k)) (hl : es.length < n) :
    es ∈ shortEdgeLists n k := by
  classical
  simp only [shortEdgeLists, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  refine ⟨⟨es.length, hl⟩, (fun j : Fin es.length => es.get j), ?_⟩
  exact List.ofFn_get es

lemma exists_min_weight_walk {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (u v : Fin n) (hr : Reachable g active u v) :
    ∃ es, Walk g active u v es ∧ es.length < n ∧
      ∀ fs, Walk g active u v fs → (es.map w).sum ≤ (fs.map w).sum := by
  classical
  let S := (shortEdgeLists n k).filter (Walk g active u v)
  have hs : S.Nonempty := by
    obtain ⟨es, he, hl⟩ := hr.short_walk
    exact ⟨es, Finset.mem_filter.mpr ⟨mem_shortEdgeLists es hl, he⟩⟩
  obtain ⟨es, hes, hmin⟩ := Finset.exists_min_image S (fun es => (es.map w).sum) hs
  have he : Walk g active u v es := (Finset.mem_filter.mp hes).2
  obtain ⟨gs, hg, hsub, hn⟩ := he.erase_cycles
  have hlen : gs.length < n := by
    have hh := hn.length_le_card
    simpa only [List.length_cons, List.length_map, Fintype.card_fin, Nat.succ_le_iff] using hh
  refine ⟨gs, hg, hlen, ?_⟩
  intro fs hf
  obtain ⟨ts, ht, hsubt, hnodup⟩ := hf.erase_cycles
  have hlt : ts.length < n := by
    have hh := hnodup.length_le_card
    simpa only [List.length_cons, List.length_map, Fintype.card_fin, Nat.succ_le_iff] using hh
  have hts : ts ∈ S := Finset.mem_filter.mpr ⟨mem_shortEdgeLists ts hlt, ht⟩
  have hgs : (gs.map w).sum ≤ (es.map w).sum :=
    List.Sublist.sum_le_sum (hsub.map w) (by intro x hx; obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; exact hw e)
  have hfs : (ts.map w).sum ≤ (fs.map w).sum :=
    List.Sublist.sum_le_sum (hsubt.map w) (by intro x hx; obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx; exact hw e)
  exact hgs.trans ((hmin ts hts).trans hfs)

lemma list_sum_ofReal {k : ℕ} (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (es : List (Fin k)) :
    (es.map (fun e => ENNReal.ofReal (w e))).sum = ENNReal.ofReal ((es.map w).sum) := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [ENNReal.ofReal_add (hw e) (List.sum_nonneg (by intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hw a))]

lemma distance_le_walk {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (w : Fin k → ℝ≥0∞) :
    distance g active w u v ≤ (es.map w).sum :=
  iInf_le_of_le es (iInf_le_of_le h le_rfl)

lemma distance_min_weight {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (u v : Fin n) (hr : Reachable g active u v) :
    ∃ es, Walk g active u v es ∧ es.length < n ∧
      distance g active (fun e => ENNReal.ofReal (w e)) u v = ENNReal.ofReal ((es.map w).sum) := by
  obtain ⟨es, he, hl, hmin⟩ := exists_min_weight_walk g active w hw u v hr
  refine ⟨es, he, hl, le_antisymm ?_ ?_⟩
  · simpa only [list_sum_ofReal w hw] using distance_le_walk he (fun e => ENNReal.ofReal (w e))
  · apply le_iInf
    intro fs
    apply le_iInf
    intro hf
    rw [list_sum_ofReal w hw]
    exact ENNReal.ofReal_le_ofReal (hmin fs hf)

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

noncomputable def cappedDistance {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (u v : Fin n) : ℝ :=
  (min (ENNReal.ofReal B) (distance g active (fun e => ENNReal.ofReal (w e)) u v)).toReal

lemma cappedDistance_bounds {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n) :
    0 ≤ cappedDistance g active w B u v ∧ cappedDistance g active w B u v ≤ B := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (min_le_left (ENNReal.ofReal B) (distance g active (fun e => ENNReal.ofReal (w e)) u v))
  simpa only [cappedDistance, ENNReal.toReal_ofReal hB] using hh

lemma distance_unreachable {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ≥0∞) (u v : Fin n) (hr : ¬ Reachable g active u v) :
    distance g active w u v = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro es
  apply le_iInf
  intro he
  exact False.elim (hr ⟨es, he⟩)

lemma cappedDistance_unreachable {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n) (hr : ¬ Reachable g active u v) :
    cappedDistance g active w B u v = B := by
  rw [cappedDistance, distance_unreachable g active _ u v hr, min_eq_left le_top, ENNReal.toReal_ofReal hB]

lemma cappedDistance_of_distance {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 ≤ c) (u v : Fin n)
    (hd : distance g active (fun e => ENNReal.ofReal (w e)) u v = ENNReal.ofReal c) :
    cappedDistance g active w B u v = min B c := by
  rw [cappedDistance, hd, ← ENNReal.ofReal_min, ENNReal.toReal_ofReal (le_min hB hc)]

lemma cappedDistance_self {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (B : ℝ) (hB : 0 ≤ B) (u : Fin n) :
    cappedDistance g active w B u u = 0 := by
  have hd : distance g active (fun e => ENNReal.ofReal (w e)) u u = 0 := by
    apply le_antisymm
    · simpa only [List.map_nil, List.sum_nil] using
        distance_le_walk (Walk.nil u : Walk g active u u []) (fun e => ENNReal.ofReal (w e))
    · exact zero_le
  rw [cappedDistance, hd, min_eq_right (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal B from zero_le), ENNReal.toReal_zero]


lemma cappedDistance_lt_walk {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n)
    (hcap : cappedDistance g active w B u v < B) :
    ∃ es, Walk g active u v es ∧ (es.map w).sum = cappedDistance g active w B u v := by
  classical
  have hr : Reachable g active u v := by
    by_contra hn
    rw [cappedDistance_unreachable g active w B hB u v hn] at hcap
    exact (lt_irrefl B) hcap
  obtain ⟨es, he, hl, hd⟩ := distance_min_weight g active w hw u v hr
  have hc : 0 ≤ (es.map w).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact hw e)
  have hmin := cappedDistance_of_distance g active w B _ hB hc u v hd
  have hh : (es.map w).sum < B := by
    by_contra hn
    rw [hmin, min_eq_left (not_lt.mp hn)] at hcap
    exact (lt_irrefl B) hcap
  exact ⟨es, he, by simpa only [min_eq_right hh.le] using hmin.symm⟩

lemma cappedDistance_edge {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (B : ℝ) (hB : 0 ≤ B) (t : Fin n)
    (e : Fin k) (he : e ∈ active) :
    cappedDistance g active w B (g.tail e) t ≤ w e + cappedDistance g active w B (g.head e) t := by
  classical
  by_cases hr : Reachable g active (g.head e) t
  · obtain ⟨es, hes, _, hd⟩ := distance_min_weight g active w hw (g.head e) t hr
    have hwalk : Walk g active (g.tail e) t (e :: es) := Walk.cons (u := g.tail e) e he hes
    have hru : Reachable g active (g.tail e) t := ⟨e :: es, hwalk⟩
    obtain ⟨fs, hfs, _, hdu⟩ := distance_min_weight g active w hw (g.tail e) t hru
    have he0 : 0 ≤ (es.map w).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hw a)
    have hf0 : 0 ≤ (fs.map w).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx; exact hw a)
    rw [cappedDistance_of_distance g active w B _ hB hf0 _ _ hdu,
      cappedDistance_of_distance g active w B _ hB he0 _ _ hd]
    have hle := distance_le_walk hwalk (fun e => ENNReal.ofReal (w e))
    rw [hdu, list_sum_ofReal w hw] at hle
    simp only [List.map_cons, List.sum_cons] at hle
    have hr0 : 0 ≤ w e + (es.map w).sum := add_nonneg (hw e) he0
    have hreal := (ENNReal.ofReal_le_ofReal_iff hr0).mp hle
    by_cases hsmall : (es.map w).sum ≤ B
    · rw [min_eq_right hsmall]
      exact (min_le_right _ _).trans hreal
    · rw [min_eq_left (le_of_not_ge hsmall)]
      exact (min_le_left _ _).trans (by linarith [hw e])
  · rw [cappedDistance_unreachable g active w B hB _ _ hr]
    exact (cappedDistance_bounds g active w B hB _ _).2.trans (by linarith [hw e])

lemma Walk.label_le_weight {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es)
    (p : Fin n → ℝ) (w : Fin k → ℝ)
    (he : ∀ e ∈ active, p (g.tail e) - p (g.head e) ≤ w e) :
    p u - p v ≤ (es.map w).sum := by
  induction h with
  | nil v => simp
  | cons e hm h ih =>
    simp only [List.map_cons, List.sum_cons]
    linarith [he e hm]

lemma cappedDistance_label_bound {n k : ℕ} (g : Digraph n k) (active : Finset (Fin k))
    (w : Fin k → ℝ) (hw : ∀ e, 0 ≤ w e) (B : ℝ) (hB : 0 ≤ B) (u v : Fin n)
    (p : Fin n → ℝ) (he : ∀ e ∈ active, p (g.tail e) - p (g.head e) ≤ w e)
    (hcap : cappedDistance g active w B u v < B) :
    p u ≤ p v + cappedDistance g active w B u v := by
  obtain ⟨es, hes, hd⟩ := cappedDistance_lt_walk g active w hw B hB u v hcap
  have hh := hes.label_le_weight p w he
  rw [hd] at hh
  linarith

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma indegree_le_count (b : Core) (v : Fin b.input.n) :
    indegree b v ≤ ∑ e : Fin b.input.k, if b.input.graph.head e = v then 1 else 0 := by
  classical
  unfold indegree
  split_ifs with hv
  · exact Nat.zero_le _
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]

lemma return_indegree_sum (b : Core) :
    (∑ v : ReturnVertex b, indegree b v.val) ≤ b.input.k := by
  classical
  let R : Finset (Fin b.input.n) := Finset.univ.filter (fun v => v ≠ b.input.source)
  have hsum : (∑ v : ReturnVertex b, indegree b v.val) = ∑ v ∈ R, indegree b v := by
    exact (Finset.sum_subtype R (by intro v; simp [R]) (indegree b)).symm
  rw [hsum]
  calc
    (∑ v ∈ R, indegree b v) ≤ ∑ v : Fin b.input.n, indegree b v :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ R) (fun _ _ _ => Nat.zero_le _)
    _ ≤ ∑ v : Fin b.input.n, ∑ e : Fin b.input.k, if b.input.graph.head e = v then 1 else 0 :=
      Finset.sum_le_sum fun v _ => indegree_le_count b v
    _ = b.input.k := by rw [Finset.sum_comm]; simp

lemma coefficient_sum_sharp (b : Core) :
    (∑ e, coefficient b e) ≤ 2 * A b * b.input.size := by
  have hq : (∑ v : ReturnVertex b, (indegree b v.val : ℝ)) ≤ b.input.size := by
    exact_mod_cast (return_indegree_sum b).trans b.valid.2.1
  have hk : (b.input.k : ℝ) ≤ b.input.size := by exact_mod_cast b.valid.2.1
  have hA := core_A_ge b
  have hm : (0 : ℝ) ≤ b.input.size := Nat.cast_nonneg _
  rw [Fintype.sum_sum_type]
  simp only [coefficient, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hq (show 0 ≤ A b by linarith)
  nlinarith

lemma core_cost_lower (b : Core) (active : Finset (Fin b.input.k)) (e : Fin b.input.k) :
    1 / Q b ≤ cost b active (.inl e) := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hw : (1 : ℝ) ≤ b.input.W := by exact_mod_cast b.valid.2.2.1
  have hQ : 0 < Q b := by have := core_Q_ge b; linarith
  have hH : 1 ≤ H b := by dsimp [H]; nlinarith [mul_le_mul hn hw (by norm_num) (by linarith)]
  simp only [cost]
  split_ifs
  · apply div_le_div_of_nonneg_right _ hQ.le
    exact_mod_cast (b.valid.2.2.2.2.2 e).1
  · exact div_le_div_of_nonneg_right hH hQ.le

lemma kappa_le_initial_slack (b : Core) : kappa b ≤ 1 / (2 * Q b) := by
  have hA := core_A_ge b
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ := core_Q_ge b
  have hQpos : 0 < Q b := by linarith
  have hAm : 1 ≤ A b * b.input.size := by nlinarith
  have hbig : 2 * Q b ≤ (A b * b.input.size * Q b) ^ 2 := by
    have hh : 2 ≤ A b * b.input.size * Q b := by nlinarith
    have hhi : Q b ≤ A b * b.input.size * Q b := by nlinarith
    nlinarith
  simp only [kappa, zpow_neg, zpow_ofNat, ← one_div]
  apply (div_le_div_iff₀ (by positivity : 0 < (A b * b.input.size * Q b) ^ 2) (by positivity : 0 < 2 * Q b)).mpr
  simpa only [one_mul] using hbig

lemma initial_slack_lower (b : Core) (e : Edge b) :
    1 / (2 * Q b) ≤ slack b Finset.univ (initialLabel b) e := by
  have hQpos : 0 < Q b := by
    have hQ := core_Q_ge b
    have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
    linarith
  cases e with
  | inl e =>
    have hc := core_cost_lower b Finset.univ e
    have hhead := b.no_incoming_source e
    by_cases htail : b.input.graph.tail e = b.input.source
    · have heq : slack b Finset.univ (initialLabel b) (.inl e) =
          cost b Finset.univ (.inl e) - 1 / (2 * Q b) := by
        simp [slack, incidence, tail, head, initialLabel, hhead, htail] <;> ring
      rw [heq]
      have hid : 1 / (2 * Q b) + 1 / (2 * Q b) = 1 / Q b := by ring
      linarith
    · have heq : slack b Finset.univ (initialLabel b) (.inl e) = cost b Finset.univ (.inl e) := by
        simp [slack, incidence, tail, head, initialLabel, hhead, htail] <;> ring
      rw [heq]
      have hh : 1 / (2 * Q b) ≤ 1 / Q b := by apply div_le_div_of_nonneg_left (by norm_num) hQpos; linarith
      exact hh.trans hc
  | inr v => simp [slack, cost, incidence, tail, head, initialLabel, v.property]

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

noncomputable def incomingCapacity (b : Core) (f : Edge b → ℝ) (R : Finset (Fin b.input.n)) : ℝ := by
  classical
  exact ∑ e, if tail b e ∉ R ∧ head b e ∈ R then f e else 0

noncomputable def outgoingCapacity (b : Core) (f : Edge b → ℝ) (R : Finset (Fin b.input.n)) : ℝ := by
  classical
  exact ∑ e, if tail b e ∈ R ∧ head b e ∉ R then f e else 0

lemma balanced_cut_bounds (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hb : Balanced b active p) (R : Finset (Fin b.input.n)) :
    incomingCapacity b (capacity b active p) R ≤ 2 * outgoingCapacity b (capacity b active p) R ∧
      outgoingCapacity b (capacity b active p) R ≤ 2 * incomingCapacity b (capacity b active p) R := by
  classical
  let x : Fin b.input.n → ℝ := fun v => (if v ∈ R then 1 else 0) -
    (if b.input.source ∈ R then 1 else 0)
  have hxs : x b.input.source = 0 := by dsimp [x]; ring
  have hinc (e : Edge b) : incidence b x e =
      (if tail b e ∈ R then 1 else 0) - (if head b e ∈ R then 1 else 0) := by
    dsimp [incidence, x]
    ring
  have hdot : dot (gradient b (capacity b active p)) x =
      incomingCapacity b (capacity b active p) R - outgoingCapacity b (capacity b active p) R := by
    rw [gradient_dot, ← Finset.sum_neg_distrib]
    unfold incomingCapacity outgoingCapacity
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [hinc]
    by_cases ht : tail b e ∈ R <;> by_cases hh : head b e ∈ R
    all_goals simp [ht, hh]
  have hnorm : norm b (capacity b active p) x =
      incomingCapacity b (capacity b active p) R + outgoingCapacity b (capacity b active p) R := by
    unfold norm incomingCapacity outgoingCapacity
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    rw [hinc]
    by_cases ht : tail b e ∈ R <;> by_cases hh : head b e ∈ R
    all_goals simp [ht, hh]
  have hh := hb x hxs
  rw [hdot, hnorm] at hh
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith

lemma incoming_core (b : Core) (f : Edge b → ℝ) (R : Finset (Fin b.input.n))
    (hs : b.input.source ∉ R) :
    incomingCapacity b f R =
      ∑ e : Fin b.input.k, if b.input.graph.tail e ∉ R ∧ b.input.graph.head e ∈ R then f (.inl e) else 0 := by
  classical
  unfold incomingCapacity
  rw [Fintype.sum_sum_type]
  simp only [tail, head, hs, and_false, if_false, Finset.sum_const_zero, add_zero]
  rfl

lemma outgoing_return_lower (b : Core) (f : Edge b → ℝ) (hf : ∀ e, 0 ≤ f e)
    (R : Finset (Fin b.input.n)) (hs : b.input.source ∉ R) :
    (∑ v : ReturnVertex b, if v.val ∈ R then f (.inr v) else 0) ≤ outgoingCapacity b f R := by
  classical
  unfold outgoingCapacity
  rw [Fintype.sum_sum_type]
  have hcore : 0 ≤ ∑ e : Fin b.input.k,
      if tail b (.inl e) ∈ R ∧ head b (.inl e) ∉ R then f (.inl e) else 0 := by
    apply Finset.sum_nonneg
    intro e _
    have hp := hf (.inl e)
    split_ifs <;> positivity
  simpa only [tail, head, hs, not_false_eq_true, and_true] using
    (le_add_of_nonneg_left hcore :
      (∑ v : ReturnVertex b, if v.val ∈ R then f (.inr v) else 0) ≤
        (∑ e : Fin b.input.k, if tail b (.inl e) ∈ R ∧ head b (.inl e) ∉ R then f (.inl e) else 0) +
        (∑ v : ReturnVertex b, if v.val ∈ R then f (.inr v) else 0))

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open Filter Set
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental

noncomputable def volumeRamp (a ell r : ℝ) : ℝ := min 1 (max 0 ((r - a) / ell))
noncomputable def volumeSlope (a ell r : ℝ) : ℝ := if a ≤ r ∧ r < a + ell then 1 / ell else 0

lemma volumeRamp_bounds (a ell r : ℝ) : 0 ≤ volumeRamp a ell r ∧ volumeRamp a ell r ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

lemma volumeRamp_zero {a ell r : ℝ} (hell : 0 < ell) (hr : r ≤ a) : volumeRamp a ell r = 0 := by
  have hh : (r - a) / ell ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hr) hell.le
  simp only [volumeRamp, max_eq_left hh]
  norm_num

lemma continuous_volumeRamp (a ell : ℝ) : Continuous (volumeRamp a ell) := by
  exact continuous_const.min (continuous_const.max ((continuous_id.sub continuous_const).div_const ell))

lemma hasDerivWithinAt_volumeRamp (a ell r : ℝ) (hell : 0 < ell) :
    HasDerivWithinAt (volumeRamp a ell) (volumeSlope a ell r) (Ici r) r := by
  by_cases ha : a ≤ r
  · by_cases hb : r < a + ell
    · simp only [volumeSlope, ha, hb, true_and, if_true]
      have hd := (((hasDerivAt_id r).sub_const a).div_const ell).hasDerivWithinAt (s := Ici r)
      apply hd.congr_of_eventuallyEq_of_mem _ (le_refl r)
      have hr : ∀ᶠ z in 𝓝[Ici r] r, r ≤ z := self_mem_nhdsWithin
      have hu : ∀ᶠ z in 𝓝[Ici r] r, z < a + ell := nhdsWithin_le_nhds (Iio_mem_nhds hb)
      filter_upwards [hr, hu] with z hzr hzu
      have hz0 : 0 ≤ (z - a) / ell := div_nonneg (by linarith) hell.le
      have hz1 : (z - a) / ell ≤ 1 := (div_le_one hell).mpr (by linarith)
      simp only [volumeRamp, max_eq_right hz0, min_eq_right hz1, id_eq]
    · simp only [volumeSlope, hb, and_false, if_false]
      have hd := (hasDerivAt_const r (1 : ℝ)).hasDerivWithinAt (s := Ici r)
      apply hd.congr_of_eventuallyEq_of_mem _ (le_refl r)
      have hr : ∀ᶠ z in 𝓝[Ici r] r, r ≤ z := self_mem_nhdsWithin
      filter_upwards [hr] with z hzr
      have hz1 : 1 ≤ (z - a) / ell := (le_div_iff₀ hell).mpr (by linarith)
      have hz0 : 0 ≤ (z - a) / ell := by linarith
      simp only [volumeRamp, max_eq_right hz0, min_eq_left hz1]
  · simp only [volumeSlope, ha, false_and, if_false]
    have hd := (hasDerivAt_const r (0 : ℝ)).hasDerivWithinAt (s := Ici r)
    apply hd.congr_of_eventuallyEq_of_mem _ (le_refl r)
    have hr : ∀ᶠ z in 𝓝[Ici r] r, z < a := nhdsWithin_le_nhds (Iio_mem_nhds (lt_of_not_ge ha))
    filter_upwards [hr] with z hz
    exact volumeRamp_zero hell hz.le

lemma log_growth_of_right_deriv (V D : ℝ → ℝ) (R c : ℝ) (hR : 0 ≤ R)
    (hV : ContinuousOn V (Icc 0 R)) (hpos : ∀ r ∈ Icc 0 R, 0 < V r)
    (hzero : V 0 = 1) (hd : ∀ r ∈ Ico 0 R, HasDerivWithinAt V (D r) (Ici r) r)
    (hbound : ∀ r ∈ Ico 0 R, c * V r ≤ D r) :
    c * R ≤ Real.log (V R) := by
  have hf : ContinuousOn (fun r => -Real.log (V r)) (Icc 0 R) :=
    (hV.log (fun r hr => (hpos r hr).ne')).neg
  have hcomp := image_le_of_liminf_slope_right_le_deriv_boundary
    (f := fun r => -Real.log (V r)) (B := fun r => -c * r) (B' := fun _ => -c)
    hf (by simp [hzero]) (continuous_const.mul continuous_id).continuousOn
    (fun r hr => by simpa only [mul_one, id_eq] using ((hasDerivWithinAt_id r (Ici r)).const_mul (-c)))
    (by
      intro r hr b hb
      have hv := hpos r (Ico_subset_Icc_self hr)
      have hh := (hd r hr).log hv.ne'
      have hder : -(D r / V r) ≤ -c := by
        have hm := (le_div_iff₀ hv).mpr (hbound r hr)
        linarith
      exact hh.neg.liminf_right_slope_le (hder.trans_lt hb))
    (show R ∈ Icc 0 R from ⟨hR, le_refl R⟩)
  linarith

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open Filter Set
open scoped Topology
namespace DecrAlmostLinearSSSP.Decremental

noncomputable def ballVolume {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (r : ℝ) : ℝ :=
  1 + ∑ e, volumeRamp (d (g.head e)) (ell e) r

noncomputable def ballVolumeSlope {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (r : ℝ) : ℝ :=
  ∑ e, volumeSlope (d (g.head e)) (ell e) r

lemma continuous_ballVolume {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ) (ell : Fin k → ℝ) :
    Continuous (ballVolume g d ell) := by
  exact continuous_const.add (continuous_finsetSum _ (fun e _ => continuous_volumeRamp _ _))

lemma ballVolume_deriv {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (hell : ∀ e, 0 < ell e) (r : ℝ) :
    HasDerivWithinAt (ballVolume g d ell) (ballVolumeSlope g d ell r) (Ici r) r := by
  have hh := HasDerivWithinAt.sum (u := Finset.univ)
    (fun e _ => hasDerivWithinAt_volumeRamp (d (g.head e)) (ell e) r (hell e))
  have hfun : ballVolume g d ell = (fun _ : ℝ => 1) + ∑ e, volumeRamp (d (g.head e)) (ell e) := by
    funext z
    simp only [ballVolume, Pi.add_apply, Finset.sum_apply]
  rw [hfun]
  simpa only [ballVolumeSlope, zero_add] using (hasDerivWithinAt_const r (Ici r) (1 : ℝ)).add hh

lemma ballVolume_bounds {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (r : ℝ) :
    1 ≤ ballVolume g d ell r ∧ ballVolume g d ell r ≤ k + 1 := by
  have hlo : 0 ≤ ∑ e, volumeRamp (d (g.head e)) (ell e) r :=
    Finset.sum_nonneg fun e _ => (volumeRamp_bounds _ _ _).1
  have hhi : (∑ e, volumeRamp (d (g.head e)) (ell e) r) ≤ k := by
    calc
      _ ≤ ∑ _ : Fin k, (1 : ℝ) := Finset.sum_le_sum fun e _ => (volumeRamp_bounds _ _ _).2
      _ = _ := by simp
  dsimp [ballVolume]
  constructor <;> linarith

lemma ballVolume_zero {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (hell : ∀ e, 0 < ell e) (hd : ∀ v, 0 ≤ d v) :
    ballVolume g d ell 0 = 1 := by
  unfold ballVolume
  have hz : (∑ e, volumeRamp (d (g.head e)) (ell e) 0) = 0 :=
    Finset.sum_eq_zero fun e _ => volumeRamp_zero (hell e) (hd _)
  rw [hz, add_zero]

lemma ballVolume_head_count {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (hell : ∀ e, 0 < ell e) (r : ℝ) :
    ballVolume g d ell r ≤ 1 + ∑ e, if d (g.head e) ≤ r then (1 : ℝ) else 0 := by
  unfold ballVolume
  have hs : (∑ e, volumeRamp (d (g.head e)) (ell e) r) ≤
      ∑ e, if d (g.head e) ≤ r then (1 : ℝ) else 0 := by
    apply Finset.sum_le_sum
    intro e _
    by_cases he : d (g.head e) ≤ r
    · simp only [if_pos he]
      exact (volumeRamp_bounds _ _ _).2
    · simp only [if_neg he]
      rw [volumeRamp_zero (hell e) (le_of_not_ge he)]

  linarith only [hs]

lemma ballVolume_slope_lower {n k : ℕ} (g : Digraph n k) (d : Fin n → ℝ)
    (ell : Fin k → ℝ) (hell : ∀ e, 0 < ell e)
    (htriangle : ∀ e, d (g.tail e) ≤ d (g.head e) + ell e) (r : ℝ) :
    (∑ e, if r < d (g.tail e) ∧ d (g.head e) ≤ r then 1 / ell e else 0) ≤
      ballVolumeSlope g d ell r := by
  apply Finset.sum_le_sum
  intro e _
  by_cases he : r < d (g.tail e) ∧ d (g.head e) ≤ r
  · have hh : r < d (g.head e) + ell e := he.1.trans_le (htriangle e)
    have hc : d (g.head e) ≤ r ∧ r < d (g.head e) + ell e := ⟨he.2, hh⟩
    rw [if_pos he, volumeSlope, if_pos hc]
  · simp only [if_neg he, volumeSlope]
    have hp := hell e
    split_ifs <;> positivity

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma indegree_eq_count (b : Core) (v : Fin b.input.n) (hv : v ≠ b.input.source) :
    indegree b v = ∑ e : Fin b.input.k, if b.input.graph.head e = v then 1 else 0 := by
  classical
  rw [indegree, if_neg hv, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma indegree_set_count (b : Core) (R : Finset (Fin b.input.n)) (hs : b.input.source ∉ R) :
    (∑ v ∈ R, (indegree b v : ℝ)) =
      ∑ e : Fin b.input.k, if b.input.graph.head e ∈ R then (1 : ℝ) else 0 := by
  classical
  calc
    (∑ v ∈ R, (indegree b v : ℝ)) =
        ∑ v ∈ R, ∑ e : Fin b.input.k, if b.input.graph.head e = v then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvs : v ≠ b.input.source := by intro h; subst v; exact hs hv
      exact_mod_cast indegree_eq_count b v hvs
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq]

lemma sum_return_on_set (b : Core) (R : Finset (Fin b.input.n)) (hs : b.input.source ∉ R)
    (f : Fin b.input.n → ℝ) :
    (∑ v : ReturnVertex b, if v.val ∈ R then f v.val else 0) = ∑ v ∈ R, f v := by
  classical
  let S := Finset.univ.filter (fun v : Fin b.input.n => v ≠ b.input.source)
  have hsub : R ⊆ S := by
    intro v hv
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hh
    subst v
    exact hs hv
  have hst : (∑ v : ReturnVertex b, if v.val ∈ R then f v.val else 0) =
      ∑ v ∈ S, if v ∈ R then f v else 0 := (Finset.sum_subtype (p := fun v : Fin b.input.n => v ≠ b.input.source) S (by intro v; simp [S])
    (fun v => if v ∈ R then f v else 0)).symm
  rw [hst]
  have hh : (∑ v ∈ R, if v ∈ R then f v else 0) = ∑ v ∈ S, if v ∈ R then f v else 0 := by
    apply Finset.sum_subset hsub
    intro v _ hv
    simp only [if_neg hv]
  rw [← hh]
  apply Finset.sum_congr rfl
  intro v hv
  simp only [if_pos hv]

lemma ballVolume_indegree_bound (b : Core) (d : Fin b.input.n → ℝ)
    (ell : Fin b.input.k → ℝ) (hell : ∀ e, 0 < ell e) (r : ℝ)
    (R : Finset (Fin b.input.n)) (hR : ∀ v, v ∈ R ↔ d v ≤ r)
    (hs : b.input.source ∉ R) (ht : ∃ t ∈ R, t ≠ b.input.source) :
    ballVolume b.input.graph d ell r ≤ 2 * ∑ v ∈ R, (indegree b v : ℝ) := by
  classical
  have hq : 1 ≤ ∑ v ∈ R, (indegree b v : ℝ) := by
    obtain ⟨t, ht, hts⟩ := ht
    have hl : (indegree b t : ℝ) ≤ ∑ v ∈ R, (indegree b v : ℝ) :=
      Finset.single_le_sum (fun v _ => Nat.cast_nonneg _) ht
    have hpos : (1 : ℝ) ≤ indegree b t := by exact_mod_cast core_indegree_pos b t hts
    exact hpos.trans hl
  have hv := ballVolume_head_count b.input.graph d ell hell r
  have hcnt : (∑ e : Fin b.input.k, if d (b.input.graph.head e) ≤ r then (1 : ℝ) else 0) =
      ∑ v ∈ R, (indegree b v : ℝ) := by
    rw [indegree_set_count b R hs]
    apply Finset.sum_congr rfl
    intro e _
    simp only [hR]
  rw [hcnt] at hv
  linarith

lemma return_capacity_lower (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (hsource : p b.input.source = 0) (R : Finset (Fin b.input.n)) (hs : b.input.source ∉ R)
    (P : ℝ) (hP : 0 < P) (hp : ∀ v ∈ R, max (p v) (kappa b) ≤ P) :
    A b / P * (∑ v ∈ R, (indegree b v : ℝ)) ≤ outgoingCapacity b (capacity b active p) R := by
  classical
  have hpre := outgoing_return_lower b (capacity b active p)
    (fun e => (capacity_pos b active p e).le) R hs
  have hsum : (∑ v : ReturnVertex b, if v.val ∈ R then capacity b active p (.inr v) else 0) =
      ∑ v ∈ R, A b * indegree b v / max (p v) (kappa b) := by
    simp only [capacity, coefficient, slack, cost, incidence, tail, head, hsource, sub_zero, zero_add]
    exact sum_return_on_set b R hs (fun v => A b * indegree b v / max (p v) (kappa b))
  rw [hsum] at hpre
  calc
    _ = ∑ v ∈ R, (A b * indegree b v) / P := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro v _; ring
    _ ≤ ∑ v ∈ R, A b * indegree b v / max (p v) (kappa b) := by
      apply Finset.sum_le_sum
      intro v hv
      have hA := core_A_ge b
      have hk := (core_kappa_bounds b).1
      exact div_le_div_of_nonneg_left (by positivity) (lt_of_lt_of_le hk (le_max_right _ _)) (hp v hv)
    _ ≤ _ := hpre

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

noncomputable def coreLength (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (e : Fin b.input.k) : ℝ :=
  max (slack b active p (.inl e)) (kappa b)

lemma coreLength_pos (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (e : Fin b.input.k) : 0 < coreLength b active p e :=
  lt_of_lt_of_le (core_kappa_bounds b).1 (le_max_right _ _)

lemma core_label_edge_bound (b : Core) (active : Finset (Fin b.input.k)) (p : Fin b.input.n → ℝ)
    (e : Fin b.input.k) : p (b.input.graph.tail e) - p (b.input.graph.head e) ≤ coreLength b active p e := by
  have hh : slack b active p (.inl e) ≤ coreLength b active p e := le_max_left _ _
  have hc := (core_cost_bounds b active e).1
  dsimp [slack, incidence, tail, head] at hh
  linarith

lemma coreDistance_lower (b : Core) (active : Finset (Fin b.input.k))
    (v : Fin b.input.n) (hv : v ≠ b.input.source) :
    ENNReal.ofReal (1 / Q b) ≤ coreDistance b active v := by
  classical
  unfold coreDistance distance
  apply le_iInf
  intro es
  apply le_iInf
  intro he
  rw [list_sum_ofReal _ (fun e => (core_cost_bounds b active e).1)]
  apply ENNReal.ofReal_le_ofReal
  have hne : es ≠ [] := by
    intro hh
    exact hv (he.eq_of_empty hh).symm
  cases es with
  | nil => exact False.elim (hne rfl)
  | cons e fs =>
    simp only [List.map_cons, List.sum_cons]
    have hr : 0 ≤ (fs.map (fun e => cost b active (.inl e))).sum := List.sum_nonneg (by
      intro x hx; obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx; exact (core_cost_bounds b active d).1)
    linarith [core_cost_lower b active e]

lemma coreDistance_ell_walk (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0)
    (t : Fin b.input.n) (es : List (Fin b.input.k)) (he : Walk b.input.graph Finset.univ b.input.source t es) :
    coreDistance b active t ≤ ENNReal.ofReal (p t + (es.map (coreLength b active p)).sum) := by
  have hcost := distance_le_walk he (fun e => ENNReal.ofReal (cost b active (.inl e)))
  rw [list_sum_ofReal _ (fun e => (core_cost_bounds b active e).1)] at hcost
  have ht : (es.map (fun e => slack b active p (.inl e))).sum =
      (es.map (fun e => cost b active (.inl e))).sum + p b.input.source - p t := by
    simp only [slack, incidence, tail, head]
    rw [List.sum_map_add, he.cost_telescope p]
    ring
  have hsum : (es.map (fun e => slack b active p (.inl e))).sum ≤
      (es.map (coreLength b active p)).sum := List.sum_le_sum (fun e _ => le_max_left _ _)
  rw [hs] at ht
  exact hcost.trans (ENNReal.ofReal_le_ofReal (by linarith only [ht, hsum]))

lemma coreDistance_capped_bound (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (B : ℝ) (hB : 0 ≤ B) (t : Fin b.input.n)
    (hcap : cappedDistance b.input.graph Finset.univ (coreLength b active p) B b.input.source t < B) :
    coreDistance b active t ≤ ENNReal.ofReal (p t +
      cappedDistance b.input.graph Finset.univ (coreLength b active p) B b.input.source t) := by
  obtain ⟨es, he, hcost⟩ := cappedDistance_lt_walk b.input.graph Finset.univ (coreLength b active p)
    (fun e => (coreLength_pos b active p e).le) B hB b.input.source t hcap
  simpa only [hcost] using coreDistance_ell_walk b active p hs t es he

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma growth_parameter_strict (b : Core) (P : ℝ) (hP : 0 < P) :
    Real.log (b.input.size + 1) <
      (A b / (4 * (1 + b.input.accuracy / 4) * P)) * (b.input.accuracy / 4 * P) := by
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have he := b.valid.2.2.2.1
  have he1 := b.valid.2.2.2.2.1
  have hlog : 0 < Real.log (b.input.size + 1) := Real.log_pos (by linarith)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hdiv : Real.log (b.input.size + 1) ≤ logarithm2 (b.input.size + 1) := by
    unfold logarithm2
    apply (le_div_iff₀ hlog2).mpr
    nlinarith
  have ha : 32 * logarithm2 (b.input.size + 1) / b.input.accuracy ≤ A b := Nat.le_ceil _
  have hmul := (div_le_iff₀ he).mp ha
  have hAe : 32 * Real.log (b.input.size + 1) ≤ A b * b.input.accuracy := by linarith
  have hdenpos : 0 < 16 * (1 + b.input.accuracy / 4) := by positivity
  have hden : 16 * (1 + b.input.accuracy / 4) ≤ 20 := by linarith
  have hden' := mul_le_mul_of_nonneg_left hden hlog.le
  have hstrict : Real.log (b.input.size + 1) < A b * b.input.accuracy /
      (16 * (1 + b.input.accuracy / 4)) := by
    apply (lt_div_iff₀ hdenpos).mpr
    nlinarith only [hAe, hden', hlog]
  have hid : (A b / (4 * (1 + b.input.accuracy / 4) * P)) * (b.input.accuracy / 4 * P) =
      A b * b.input.accuracy / (16 * (1 + b.input.accuracy / 4)) := by
    field_simp
    <;> ring
  rw [hid]
  exact hstrict

lemma kappa_certificate_small (b : Core) :
    (1 + b.input.accuracy / 4) * kappa b < 1 / Q b := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ : 0 < Q b := by have hh := core_Q_ge b; linarith
  have hk := (core_kappa_bounds b).1
  have hh := (le_div_iff₀ (by positivity : 0 < 2 * Q b)).mp (kappa_le_initial_slack b)
  have he1 := b.valid.2.2.2.2.1
  have heps := mul_le_mul_of_nonneg_right he1 (show 0 ≤ kappa b * Q b by positivity)
  apply (lt_div_iff₀ hQ).mpr
  nlinarith

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma backward_growth_cap (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p)
    (t : Fin b.input.n) (ht : t ≠ b.input.source) :
    let bt := max (p t) (kappa b)
    let r0 := b.input.accuracy / 4 * bt
    cappedDistance b.input.graph Finset.univ (coreLength b active p) (r0 + 1) b.input.source t ≤ r0 := by
  classical
  dsimp only
  let bt := max (p t) (kappa b)
  let r0 := b.input.accuracy / 4 * bt
  let B := r0 + 1
  let ell := coreLength b active p
  let d := fun v => cappedDistance b.input.graph Finset.univ ell B v t
  let P := (1 + b.input.accuracy / 4) * bt
  let c := A b / (4 * P)
  let V := ballVolume b.input.graph d ell
  let D := ballVolumeSlope b.input.graph d ell
  have hk := (core_kappa_bounds b).1
  have hA := core_A_ge b
  have heps := b.valid.2.2.2.1
  have hbt : 0 < bt := hk.trans_le (le_max_right _ _)
  have hr0 : 0 < r0 := by dsimp [r0]; positivity
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hP : 0 < P := by dsimp [P]; positivity
  have hPid : P = bt + r0 := by dsimp [P, r0]; ring
  have hell (e : Fin b.input.k) : 0 < ell e := coreLength_pos b active p e
  have hd0 (v : Fin b.input.n) : 0 ≤ d v := (cappedDistance_bounds b.input.graph Finset.univ ell B hB v t).1
  have hdt : d t = 0 := cappedDistance_self b.input.graph Finset.univ ell B hB t
  have htriangle (e : Fin b.input.k) : d (b.input.graph.tail e) ≤ d (b.input.graph.head e) + ell e := by
    have hh := cappedDistance_edge b.input.graph Finset.univ ell (fun e => (hell e).le) B hB t e (Finset.mem_univ e)
    dsimp [d] at *
    linarith only [hh]
  change d b.input.source ≤ r0
  by_contra hnot
  have hsource : r0 < d b.input.source := lt_of_not_ge hnot
  have hbound (r : ℝ) (hr : r ∈ Set.Ico 0 r0) : c * V r ≤ D r := by
    let R := Finset.univ.filter (fun v : Fin b.input.n => d v ≤ r)
    have hR (v : Fin b.input.n) : v ∈ R ↔ d v ≤ r := by simp [R]
    have hsR : b.input.source ∉ R := by
      simp only [hR]
      linarith only [hsource, hr.2]
    have htR : t ∈ R := (hR t).mpr (by rw [hdt]; exact hr.1)
    have hpR (v : Fin b.input.n) (hv : v ∈ R) : max (p v) (kappa b) ≤ P := by
      have hdv := (hR v).mp hv
      have hdvB : d v < B := by dsimp [B]; linarith only [hdv, hr.2]
      have hpv := cappedDistance_label_bound b.input.graph Finset.univ ell (fun e => (hell e).le)
        B hB v t p (fun e _ => core_label_edge_bound b active p e) hdvB
      have hpt : p t ≤ bt := le_max_left _ _
      have hkb : kappa b ≤ bt := le_max_right _ _
      apply max_le
      · rw [hPid]
        linarith only [hpv, hdv, hpt, hr.2]
      · rw [hPid]
        linarith only [hkb, hr0]
    have hvol : V r ≤ 2 * ∑ v ∈ R, (indegree b v : ℝ) :=
      ballVolume_indegree_bound b d ell hell r R hR hsR ⟨t, htR, ht⟩
    have hout := return_capacity_lower b active p hs R hsR P hP hpR
    have hbalance := (balanced_cut_bounds b active p hb R).2
    have hin : incomingCapacity b (capacity b active p) R ≤ D r := by
      have hsl := ballVolume_slope_lower b.input.graph d ell hell htriangle r
      have hsum : incomingCapacity b (capacity b active p) R =
          ∑ e : Fin b.input.k, if r < d (b.input.graph.tail e) ∧ d (b.input.graph.head e) ≤ r then 1 / ell e else 0 := by
        rw [incoming_core b _ R hsR]
        apply Finset.sum_congr rfl
        intro e _
        simp only [capacity, coefficient, ell, coreLength]
        have htail : b.input.graph.tail e ∉ R ↔ r < d (b.input.graph.tail e) := by simp [hR, not_le]
        simp only [htail, hR, not_le]
      rw [hsum]
      exact hsl
    have hcoef0 : 0 ≤ A b / P := by positivity
    have hmul := mul_le_mul_of_nonneg_left hvol hcoef0
    have hc : c = (A b / P) / 4 := by dsimp [c]; field_simp <;> ring
    rw [hc]
    nlinarith only [hmul, hout, hbalance, hin]
  have hgrowth := log_growth_of_right_deriv V D r0 c hr0.le
    (continuous_ballVolume b.input.graph d ell).continuousOn
    (fun r _ => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (ballVolume_bounds b.input.graph d ell r).1)
    (ballVolume_zero b.input.graph d ell hell hd0)
    (fun r _ => ballVolume_deriv b.input.graph d ell hell r) hbound
  have hupper : V r0 ≤ b.input.size + 1 := by
    have hk : (b.input.k : ℝ) ≤ b.input.size := by exact_mod_cast b.valid.2.1
    have hh := (ballVolume_bounds b.input.graph d ell r0).2
    linarith only [hh, hk]
  have hlog := Real.log_le_log
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (ballVolume_bounds b.input.graph d ell r0).1) hupper
  have hstrict : Real.log (b.input.size + 1) < c * r0 := by
    have hh := growth_parameter_strict b bt hbt
    have hid : (A b / (4 * (1 + b.input.accuracy / 4) * bt)) * (b.input.accuracy / 4 * bt) = c * r0 := by
      dsimp [c, P, r0]
      field_simp
      <;> ring
    rwa [hid] at hh
  linarith only [hgrowth, hlog, hstrict]

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma backward_certificate (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p)
    (t : Fin b.input.n) (ht : t ≠ b.input.source) :
    kappa b < p t ∧ 1 / (2 * Q b) ≤ p t ∧
      coreDistance b active t ≤ ENNReal.ofReal ((1 + b.input.accuracy / 4) * p t) := by
  let bt := max (p t) (kappa b)
  let r0 := b.input.accuracy / 4 * bt
  let B := r0 + 1
  let d := cappedDistance b.input.graph Finset.univ (coreLength b active p) B b.input.source t
  have hk := (core_kappa_bounds b).1
  have heps := b.valid.2.2.2.1
  have heps1 := b.valid.2.2.2.2.1
  have hbt : 0 < bt := hk.trans_le (le_max_right _ _)
  have hr0 : 0 < r0 := by dsimp [r0]; positivity
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hcap : d ≤ r0 := backward_growth_cap b active p hs hb t ht
  have hcapB : d < B := by dsimp [B]; linarith
  have hz := coreDistance_capped_bound b active p hs B hB t hcapB
  have hupper : coreDistance b active t ≤ ENNReal.ofReal (p t + r0) :=
    hz.trans (ENNReal.ofReal_le_ofReal (by linarith only [hcap]))
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ : 0 < Q b := by have hh := core_Q_ge b; linarith
  have hl := (coreDistance_lower b active t ht).trans hupper
  have hreal : 1 / Q b ≤ p t + r0 := by
    rcases ENNReal.ofReal_le_ofReal_iff'.mp hl with h | h
    · exact h
    · exact False.elim (not_le_of_gt (by positivity : 0 < 1 / Q b) h)
  have hpt : kappa b < p t := by
    by_contra hn
    have hpk : p t ≤ kappa b := le_of_not_gt hn
    have hbt' : bt = kappa b := max_eq_right hpk
    have hrid : r0 = b.input.accuracy / 4 * kappa b := by dsimp [r0]; rw [hbt']
    have hsmall := kappa_certificate_small b
    rw [hrid] at hreal
    nlinarith only [hreal, hpk, hsmall]
  have hrid : p t + r0 = (1 + b.input.accuracy / 4) * p t := by
    dsimp [r0, bt]
    rw [max_eq_left hpt.le]
    ring
  rw [hrid] at hupper hreal
  have htwo : 1 / (2 * Q b) ≤ p t := by
    have hp0 : 0 < p t := hk.trans hpt
    have hm := mul_le_mul_of_nonneg_right heps1 hp0.le
    have htemp : 1 / Q b ≤ 2 * p t := by nlinarith only [hreal, hm, hp0]
    have hid : 1 / (2 * Q b) = (1 / Q b) / 2 := by ring
    rw [hid]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    linarith only [htemp]
  exact ⟨hpt, htwo, hupper⟩

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma high_capacity_label_increase (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (e : Fin b.input.k)
    (he : 2 * Q b ≤ capacity b active p (.inl e)) :
    p (b.input.graph.tail e) < p (b.input.graph.head e) := by
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ : 0 < Q b := by have hh := core_Q_ge b; linarith
  have hk := (core_kappa_bounds b).1
  have ht : 0 < max (slack b active p (.inl e)) (kappa b) := hk.trans_le (le_max_right _ _)
  simp only [capacity, coefficient] at he
  have hh := (le_div_iff₀ ht).mp he
  have hsl : slack b active p (.inl e) ≤ 1 / (2 * Q b) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * Q b)).mpr
    have hm := mul_le_mul_of_nonneg_left (le_max_left (slack b active p (.inl e)) (kappa b))
      (show 0 ≤ 2 * Q b by positivity)
    nlinarith only [hh, hm]
  have hc := core_cost_lower b active e
  have hhalf : 1 / (2 * Q b) < 1 / Q b := by
    apply div_lt_div_of_pos_left (by norm_num) hQ
    linarith
  dsimp [slack, incidence, tail, head] at hsl
  linarith only [hsl, hc, hhalf]

lemma Walk.monotone_labels {n k : ℕ} {g : Digraph n k} {active : Finset (Fin k)}
    {u v : Fin n} {es : List (Fin k)} (h : Walk g active u v es) (p : Fin n → ℝ)
    (he : ∀ e ∈ active, p (g.tail e) ≤ p (g.head e)) : p u ≤ p v := by
  induction h with
  | nil v => exact le_refl _
  | cons e hm h ih => exact (he e hm).trans ih

lemma capacity_upper_successor (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p)
    (hlabels : ∀ v, v ≠ b.input.source → kappa b < p v ∧ 1 / (2 * Q b) ≤ p v)
    (e : Fin b.input.k) (he : 2 * Q b ≤ capacity b active p (.inl e)) :
    capacity b active p (.inl e) ≤ 12 * A b * b.input.size * Q b := by
  classical
  let f := capacity b active p
  let high := Finset.univ.filter (fun d : Fin b.input.k => 2 * Q b ≤ f (.inl d))
  let u := b.input.graph.tail e
  let v := b.input.graph.head e
  let R := Finset.univ.filter (fun w : Fin b.input.n => Reachable b.input.graph high v w)
  have hR (w : Fin b.input.n) : w ∈ R ↔ Reachable b.input.graph high v w := by simp [R]
  have hhigh (d : Fin b.input.k) (hd : d ∈ high) :
      p (b.input.graph.tail d) ≤ p (b.input.graph.head d) := by
    have hh : 2 * Q b ≤ f (.inl d) := (Finset.mem_filter.mp hd).2
    exact (high_capacity_label_increase b active p d hh).le
  have hvR : v ∈ R := (hR v).mpr ⟨[], Walk.nil v⟩
  have huR : u ∉ R := by
    intro hu
    obtain ⟨es, hes⟩ := (hR u).mp hu
    have hm := hes.monotone_labels p hhigh
    have hi := high_capacity_label_increase b active p e he
    linarith only [hm, hi]
  have hsR : b.input.source ∉ R := by
    intro hsource
    obtain ⟨es, hes⟩ := (hR b.input.source).mp hsource
    have hm := hes.monotone_labels p hhigh
    rw [hs] at hm
    have hp := (hlabels v (b.no_incoming_source e)).1
    have hk := (core_kappa_bounds b).1
    linarith only [hm, hp, hk]
  have houtcore (d : Fin b.input.k)
      (hdt : b.input.graph.tail d ∈ R) (hdh : b.input.graph.head d ∉ R) : f (.inl d) ≤ 2 * Q b := by
    by_contra hh
    have hd : d ∈ high := Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_of_not_ge hh⟩
    obtain ⟨es, hes⟩ := (hR _).mp hdt
    have hedge : Walk b.input.graph high (b.input.graph.tail d) (b.input.graph.head d) [d] :=
      Walk.cons (u := b.input.graph.tail d) d hd (Walk.nil _)
    exact hdh ((hR _).mpr ⟨es ++ [d], hes.append hedge⟩)
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hQ : 0 < Q b := by have hh := core_Q_ge b; linarith
  have hA := core_A_ge b
  have hreturn (w : ReturnVertex b) : f (.inr w) ≤ 2 * Q b * coefficient b (.inr w) := by
    have hp := hlabels w.val w.property
    have hp0 : 0 < p w.val := (core_kappa_bounds b).1.trans hp.1
    have hmu := (core_coefficient_bounds b (.inr w)).1
    change coefficient b (.inr w) / max (0 + (p w.val - p b.input.source)) (kappa b) ≤ _
    rw [hs, sub_zero, zero_add, max_eq_left hp.1.le]
    apply (div_le_iff₀ hp0).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * Q b)).mp hp.2
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ coefficient b (.inr w) by linarith)
    nlinarith only [hm]
  have hreturnsum : (∑ w : ReturnVertex b, coefficient b (.inr w)) ≤ 2 * A b * b.input.size := by
    have hh := coefficient_sum_sharp b
    rw [Fintype.sum_sum_type] at hh
    have hcore : 0 ≤ ∑ d : Fin b.input.k, coefficient b (.inl d) := by simp [coefficient]
    linarith
  have hout : outgoingCapacity b f R ≤ 6 * A b * b.input.size * Q b := by
    unfold outgoingCapacity
    rw [Fintype.sum_sum_type]
    have hc : (∑ d : Fin b.input.k, if tail b (.inl d) ∈ R ∧ head b (.inl d) ∉ R then f (.inl d) else 0) ≤
        (2 * Q b) * b.input.size := by
      calc
        _ ≤ ∑ _ : Fin b.input.k, 2 * Q b := by
          apply Finset.sum_le_sum
          intro d _
          split_ifs with hd
          · exact houtcore d hd.1 hd.2
          · positivity
        _ = 2 * Q b * b.input.k := by simp [mul_comm]
        _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast b.valid.2.1) (by positivity)
    have hr : (∑ w : ReturnVertex b, if tail b (.inr w) ∈ R ∧ head b (.inr w) ∉ R then f (.inr w) else 0) ≤
        2 * Q b * (2 * A b * b.input.size) := by
      calc
        _ ≤ ∑ w : ReturnVertex b, 2 * Q b * coefficient b (.inr w) := by
          apply Finset.sum_le_sum
          intro w _
          split_ifs
          · exact hreturn w
          · have hm := (core_coefficient_bounds b (.inr w)).1; positivity
        _ = _ := by rw [← Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hreturnsum (by positivity)
    have hm : (b.input.size : ℝ) ≤ A b * b.input.size := by nlinarith [show (0 : ℝ) ≤ b.input.size from Nat.cast_nonneg _]
    have hmQ := mul_le_mul_of_nonneg_right hm hQ.le
    nlinarith only [hc, hr, hmQ]
  have hin : f (.inl e) ≤ incomingCapacity b f R := by
    have hh := Finset.single_le_sum
      (f := fun d : Edge b => if tail b d ∉ R ∧ head b d ∈ R then f d else 0)
      (s := Finset.univ)
      (fun d _ => by split_ifs; exact (capacity_pos b active p d).le; rfl)
      (Finset.mem_univ (.inl e : Edge b))
    have hcross : tail b (.inl e) ∉ R ∧ head b (.inl e) ∈ R := ⟨huR, hvR⟩
    rw [if_pos hcross] at hh
    exact hh
  have hbalance := (balanced_cut_bounds b active p hb R).1
  change f (.inl e) ≤ _
  nlinarith only [hin, hbalance, hout]

end DecrAlmostLinearSSSP.Decremental


set_option autoImplicit false
open scoped ENNReal NNReal
namespace DecrAlmostLinearSSSP.Decremental

lemma balanced_strict_slacks (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p) :
    ∀ e, kappa b < slack b active p e := by
  have hlabels (v : Fin b.input.n) (hv : v ≠ b.input.source) :
      kappa b < p v ∧ 1 / (2 * Q b) ≤ p v := by
    have hh := backward_certificate b active p hs hb v hv
    exact ⟨hh.1, hh.2.1⟩
  have hn : (2 : ℝ) ≤ b.input.n := by exact_mod_cast b.two
  have hm : (2 : ℝ) ≤ b.input.size := by exact_mod_cast b.two.trans b.valid.1
  have hA := core_A_ge b
  have hQ := core_Q_ge b
  have hQpos : 0 < Q b := by linarith
  have hAm : 64 ≤ A b * b.input.size := by nlinarith
  have ht : 12 < A b * b.input.size * Q b := by
    have hh := mul_le_mul hAm (show 8 ≤ Q b by linarith) (by norm_num : (0 : ℝ) ≤ 8)
      (show 0 ≤ A b * b.input.size by positivity)
    nlinarith only [hh]
  have hthreshold : 12 * A b * b.input.size * Q b < 1 / kappa b := by
    have hkap : 1 / kappa b = (A b * b.input.size * Q b) ^ 2 := by
      simp [kappa, zpow_neg, zpow_ofNat]
    rw [hkap]
    have hh := mul_pos (show 0 < A b * b.input.size * Q b by positivity)
      (show 0 < A b * b.input.size * Q b - 12 by linarith)
    nlinarith only [hh]
  intro e
  cases e with
  | inr v => simpa only [slack, cost, incidence, tail, head, hs, sub_zero, zero_add] using (hlabels v.val v.property).1
  | inl e =>
    have hf : capacity b active p (.inl e) ≤ 12 * A b * b.input.size * Q b := by
      by_cases he : 2 * Q b ≤ capacity b active p (.inl e)
      · exact capacity_upper_successor b active p hs hb hlabels e he
      · have hl : 2 * Q b ≤ 12 * A b * b.input.size * Q b := by
          have hh := mul_le_mul_of_nonneg_right hAm hQpos.le
          nlinarith only [hh, hQpos]
        exact (le_of_not_ge he).trans hl
    have hf' := hf.trans_lt hthreshold
    by_contra hnot
    have hsl : slack b active p (.inl e) ≤ kappa b := le_of_not_gt hnot
    rw [capacity, coefficient, max_eq_right hsl] at hf'
    exact (lt_irrefl _) hf'

lemma feasible_label_distance (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0)
    (hslack : ∀ e, kappa b < slack b active p e) (v : Fin b.input.n) :
    ENNReal.ofReal (p v) ≤ coreDistance b active v := by
  unfold coreDistance distance
  apply le_iInf
  intro es
  apply le_iInf
  intro he
  rw [list_sum_ofReal _ (fun e => (core_cost_bounds b active e).1)]
  apply ENNReal.ofReal_le_ofReal
  have hh := he.label_le_weight (fun v => -p v) (fun e => cost b active (.inl e)) (by
    intro e _
    have hpos : 0 < slack b active p (.inl e) := (core_kappa_bounds b).1.trans (hslack _)
    dsimp [slack, incidence, tail, head] at hpos
    linarith only [hpos])
  simpa only [hs, neg_zero, zero_sub, neg_neg] using hh

lemma all_target_proof (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p) :
    AllTarget b active p := by
  have hstrict := balanced_strict_slacks b active p hs hb
  refine ⟨hstrict, ?_⟩
  intro v hv
  exact ⟨feasible_label_distance b active p hs hstrict v,
    (backward_certificate b active p hs hb v hv).2.2⟩

end DecrAlmostLinearSSSP.Decremental

open DecrAlmostLinearSSSP.Decremental

theorem solution (b : Core) (active : Finset (Fin b.input.k))
    (p : Fin b.input.n → ℝ) (hs : p b.input.source = 0) (hb : Balanced b active p) :
    AllTarget b active p := by
  exact all_target_proof b active p hs hb
