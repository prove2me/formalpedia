-- Prove2me | solution 1 for DetANN.HPIM.balance_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T05:56:05.457106+00:00
-- url     : https://prove2.me/submissions/41d745e3-fbea-4aa3-af8f-e9d451527f66

import Mathlib
import Definitions.Def_DetANN_HPIMBSP

namespace DetANN.HPIM

variable {m : ℕ}

namespace BSP

lemma sub_append : ∀ (T : BSP m) (p s : List Bool), T.sub (p ++ s) = (T.sub p).bind (·.sub s)
  | t, [], s => by simp [sub]
  | .leaf .., _ :: _, s => by simp [sub]
  | .cut _ _ l _, false :: p, s => by simp [sub, sub_append l p s]
  | .cut _ _ _ r, true :: p, s => by simp [sub, sub_append r p s]

lemma mem_paths_iff : ∀ (T : BSP m) (x : List Bool), x ∈ T.paths ↔ ∃ t, T.sub x = some t
  | .leaf .., [] => by simp [paths, sub]
  | .leaf .., _ :: _ => by simp [paths, sub]
  | .cut _ _ l r, [] => by simp [paths, sub]
  | .cut _ _ l r, false :: x => by
    simp only [paths, Finset.mem_insert, Finset.mem_union, Finset.mem_image, sub]
    rw [← mem_paths_iff l x]
    constructor
    · rintro (h | ⟨y, hy, he⟩ | ⟨y, hy, he⟩)
      · simp at h
      · simp only [List.cons.injEq, true_and] at he; exact he ▸ hy
      · simp at he
    · intro h; exact Or.inr (Or.inl ⟨x, h, rfl⟩)
  | .cut _ _ l r, true :: x => by
    simp only [paths, Finset.mem_insert, Finset.mem_union, Finset.mem_image, sub]
    rw [← mem_paths_iff r x]
    constructor
    · rintro (h | ⟨y, hy, he⟩ | ⟨y, hy, he⟩)
      · simp at h
      · simp at he
      · simp only [List.cons.injEq, true_and] at he; exact he ▸ hy
    · intro h; exact Or.inr (Or.inr ⟨x, h, rfl⟩)

lemma mem_paths_of_prefix {T : BSP m} {x y : List Bool} (hx : x ∈ T.paths) (h : y <+: x) :
    y ∈ T.paths := by
  obtain ⟨z, rfl⟩ := h
  obtain ⟨t, ht⟩ := (mem_paths_iff T _).1 hx
  rw [sub_append] at ht
  rcases hy : T.sub y with _ | ty
  · simp [hy] at ht
  · exact (mem_paths_iff T y).2 ⟨ty, hy⟩

lemma covers_sub : ∀ (T : BSP m) (p : List Bool) {t : BSP m}, T.Covers → T.sub p = some t →
    t.Covers
  | _, [], _, hT, h => by simp only [sub, Option.some.injEq] at h; exact h ▸ hT
  | .leaf .., _ :: _, _, _, h => by simp [sub] at h
  | .cut _ _ l _, false :: p, _, hT, h => covers_sub l p hT.2.1 h
  | .cut _ _ _ r, true :: p, _, hT, h => covers_sub r p hT.2.2 h

lemma sub_child {T : BSP m} {p : List Bool} {lo hi : Fin m → ℝ} {l r : BSP m}
    (h : T.sub p = some (.cut lo hi l r)) :
    T.sub (p ++ [false]) = some l ∧ T.sub (p ++ [true]) = some r := by
  rw [sub_append, sub_append, h]; simp [sub]

lemma not_mem_child_of_leaf {T : BSP m} {p : List Bool} {lo hi : Fin m → ℝ} {a : Option ℕ}
    (h : T.sub p = some (.leaf lo hi a)) (b : Bool) : p ++ [b] ∉ T.paths := by
  rw [mem_paths_iff, sub_append, h]; simp [sub]

end BSP


section Comp

variable (T : BSP m)

lemma mem_comp {p R x} : x ∈ comp T p R ↔ x ∈ T.paths ∧ p <+: x ∧ ∀ c ∈ R, ¬ c <+: x := by
  unfold comp; simp [Finset.mem_filter]

/-- `p` is a node with no removed prefix. -/
def Live (p : List Bool) (R : Finset (List Bool)) : Prop := p ∈ T.paths ∧ ∀ c ∈ R, ¬ c <+: p

lemma self_mem_comp {p R} (h : Live T p R) : p ∈ comp T p R :=
  (mem_comp T).2 ⟨h.1, List.prefix_refl _, h.2⟩

lemma live_of_mem_comp {p c R} (hc : c ∈ comp T p R) : Live T c R :=
  ⟨((mem_comp T).1 hc).1, ((mem_comp T).1 hc).2.2⟩

lemma comp_subset {p c R} (hc : c ∈ comp T p R) : comp T c R ⊆ comp T p R := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := (mem_comp T).1 hx
  exact (mem_comp T).2 ⟨h1, ((mem_comp T).1 hc).2.1.trans h2, h3⟩

lemma prefix_antisymm' {a b : List Bool} (h1 : a <+: b) (h2 : b <+: a) : a = b :=
  h1.eq_of_length (le_antisymm h1.length_le h2.length_le)

lemma not_mem_comp_of_ne {p c R} (hc : c ∈ comp T p R) (hne : c ≠ p) : p ∉ comp T c R := by
  intro hp
  exact hne (prefix_antisymm' ((mem_comp T).1 hp).2.1 ((mem_comp T).1 hc).2.1)

lemma comp_insert {p c R} (_hc : c ∈ comp T p R) :
    comp T p (insert c R) = comp T p R \ comp T c R := by
  ext x
  simp only [mem_comp, Finset.mem_sdiff, Finset.mem_insert, forall_eq_or_imp]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h2, h4⟩, fun h => h3 h.2.1⟩
  · rintro ⟨⟨h1, h2, h4⟩, h5⟩
    exact ⟨h1, h2, fun h => h5 ⟨h1, h, h4⟩, h4⟩

lemma card_comp_insert {p c R} (hc : c ∈ comp T p R) :
    (comp T p (insert c R)).card = (comp T p R).card - (comp T c R).card := by
  rw [comp_insert T hc, Finset.card_sdiff_of_subset (comp_subset T hc)]

lemma comp_split {p R} (h : Live T p R) :
    (comp T p R).card = 1 + (comp T (p ++ [false]) R).card + (comp T (p ++ [true]) R).card := by
  have hset : comp T p R = insert p (comp T (p ++ [false]) R ∪ comp T (p ++ [true]) R) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_union, mem_comp]
    constructor
    · rintro ⟨h1, ⟨t, rfl⟩, h3⟩
      rcases t with _ | ⟨b, t⟩
      · left; simp
      · right
        cases b
        · left; exact ⟨h1, ⟨t, by simp⟩, h3⟩
        · right; exact ⟨h1, ⟨t, by simp⟩, h3⟩
    · rintro (rfl | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact ⟨h.1, List.prefix_refl _, h.2⟩
      · exact ⟨h1, (List.prefix_append _ _).trans h2, h3⟩
      · exact ⟨h1, (List.prefix_append _ _).trans h2, h3⟩
  have hp : p ∉ comp T (p ++ [false]) R ∪ comp T (p ++ [true]) R := by
    simp only [Finset.mem_union, mem_comp]
    rintro (⟨-, h2, -⟩ | ⟨-, h2, -⟩) <;> · have := h2.length_le; simp at this
  have hdisj : Disjoint (comp T (p ++ [false]) R) (comp T (p ++ [true]) R) := by
    rw [Finset.disjoint_left]
    intro x h0 h1
    obtain ⟨-, ⟨s0, hs0⟩, -⟩ := (mem_comp T).1 h0
    obtain ⟨-, ⟨s1, hs1⟩, -⟩ := (mem_comp T).1 h1
    rw [← hs1] at hs0
    simp at hs0
  rw [hset, Finset.card_insert_of_notMem hp, Finset.card_union_of_disjoint hdisj]
  ring

/-- A nonempty component has a live root. -/
lemma live_of_nonempty {v R} (h : (comp T v R).Nonempty) : Live T v R := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨h1, h2, h3⟩ := (mem_comp T).1 hx
  exact ⟨BSP.mem_paths_of_prefix h1 h2, fun c hc hcv => h3 c hc (hcv.trans h2)⟩

end Comp


section Separator

variable (T : BSP m)

/-- The heavier child of a live node `u` (when `|comp u| ≥ 2`) is a nonempty component holding at
least half of `|comp u| − 1` nodes. -/
lemma heavy_child {u R} (h : Live T u R) (hk : 2 ≤ (comp T u R).card) :
    ∃ b : Bool, (comp T u R).card ≤ 2 * (comp T (u ++ [b]) R).card + 1 ∧
      1 ≤ (comp T (u ++ [b]) R).card ∧ u ++ [b] ∈ comp T u R ∧
      (comp T (u ++ [b]) R).card < (comp T u R).card := by
  have hs := comp_split T h
  have hmem : ∀ b, 1 ≤ (comp T (u ++ [b]) R).card → u ++ [b] ∈ comp T u R := by
    intro b hb
    have hl := live_of_nonempty T (Finset.card_pos.1 hb)
    exact (mem_comp T).2 ⟨hl.1, List.prefix_append _ _, hl.2⟩
  by_cases hab : (comp T (u ++ [true]) R).card ≤ (comp T (u ++ [false]) R).card
  · exact ⟨false, by omega, by omega, hmem false (by omega), by omega⟩
  · exact ⟨true, by omega, by omega, hmem true (by omega), by omega⟩

/-- **Balanced separator.** For a live `p` with `k = |comp p R| ≥ 2` there is a node `c ≠ p` of the
component with `k − 1 ≤ 3|comp c R| ≤ 2k + 1`. -/
lemma exists_separator {p R} (h : Live T p R) (hk : 2 ≤ (comp T p R).card) :
    ∃ c ∈ comp T p R, c ≠ p ∧ 3 * (comp T c R).card ≤ 2 * (comp T p R).card + 1 ∧
      (comp T p R).card ≤ 3 * (comp T c R).card + 1 := by
  set k := (comp T p R).card with hkdef
  set A := (comp T p R).filter fun c => c ≠ p ∧ k ≤ 3 * (comp T c R).card + 1
  have hA : A.Nonempty := by
    obtain ⟨b, h1, h2, h3, -⟩ := heavy_child T h hk
    refine ⟨p ++ [b], Finset.mem_filter.2 ⟨h3, ?_, by omega⟩⟩
    intro he; have := congrArg List.length he; simp at this
  obtain ⟨c, hcA, hmin⟩ := A.exists_min_image (fun c => (comp T c R).card) hA
  obtain ⟨hcC, hcp, hck⟩ := Finset.mem_filter.1 hcA
  refine ⟨c, hcC, hcp, ?_, hck⟩
  by_contra hcon
  push Not at hcon
  have hlc := live_of_mem_comp T hcC
  have hc2 : 2 ≤ (comp T c R).card := by omega
  obtain ⟨b, h1, h2, h3, h4⟩ := heavy_child T hlc hc2
  have hvA : c ++ [b] ∈ A := by
    refine Finset.mem_filter.2 ⟨comp_subset T hcC h3, ?_, by omega⟩
    intro he
    have hpc := ((mem_comp T).1 hcC).2.1
    have := hpc.length_le
    have := congrArg List.length he
    simp at this
    omega
  have := hmin _ hvA
  omega

/-- **The centroid.** For a live `p` with `k ≥ 2`, `centroid` returns a node `c ≠ p` of the
component whose two sides both have at most `(2k + 1)/3` nodes. -/
lemma centroid_spec {p R} (h : Live T p R) (hk : 2 ≤ (comp T p R).card) :
    ∃ c, centroid T p R = some c ∧ c ∈ comp T p R ∧ c ≠ p ∧
      3 * (comp T c R).card ≤ 2 * (comp T p R).card + 1 ∧
      3 * ((comp T p R).card - (comp T c R).card) ≤ 2 * (comp T p R).card + 1 := by
  obtain ⟨s, hsC, hsp, hs1, hs2⟩ := exists_separator T h hk
  have hsc : s ∈ (comp T p R).erase p := Finset.mem_erase.2 ⟨hsp, hsC⟩
  unfold centroid
  dsimp only
  split_ifs with hc hb
  · refine ⟨_, rfl, ?_⟩
    have hcmem := Finset.min'_mem _ hb
    obtain ⟨hce, hcs⟩ := Finset.mem_filter.1 hcmem
    obtain ⟨hcp, hcC⟩ := Finset.mem_erase.1 hce
    refine ⟨hcC, hcp, ?_⟩
    set c := Finset.min' _ hb
    have hle := Finset.inf'_le (fun c => max (comp T c R).card
      ((comp T p R).card - (comp T c R).card)) hsc
    rw [← hcs] at hle
    have h1 := le_max_left (comp T c R).card ((comp T p R).card - (comp T c R).card)
    have h2 := le_max_right (comp T c R).card ((comp T p R).card - (comp T c R).card)
    have h3 : 3 * max (comp T s R).card ((comp T p R).card - (comp T s R).card) ≤
        2 * (comp T p R).card + 1 := by
      rcases le_total (comp T s R).card ((comp T p R).card - (comp T s R).card) with hh | hh
      · rw [max_eq_right hh]; omega
      · rw [max_eq_left hh]; omega
    constructor <;> omega
  · exfalso
    obtain ⟨c, hc', hce⟩ := Finset.exists_mem_eq_inf' hc (fun c => max (comp T c R).card
      ((comp T p R).card - (comp T c R).card))
    exact hb ⟨c, Finset.mem_filter.2 ⟨hc', hce.symm⟩⟩
  · exact absurd ⟨s, hsc⟩ hc

end Separator


section Balance

variable (T : BSP m)

lemma nil_mem_paths : ([] : List Bool) ∈ T.paths :=
  (BSP.mem_paths_iff T []).2 ⟨T, by cases T <;> rfl⟩

lemma comp_nil_empty : comp T [] ∅ = T.paths := by
  ext x; simp [mem_comp, List.nil_prefix]

lemma card_ge_one {p R} (h : Live T p R) : 1 ≤ (comp T p R).card :=
  Finset.card_pos.2 ⟨p, self_mem_comp T h⟩

lemma live_root_of_mem {p c R} (hc : c ∈ comp T p R) : Live T p R :=
  ⟨BSP.mem_paths_of_prefix ((mem_comp T).1 hc).1 ((mem_comp T).1 hc).2.1,
    fun r hr hrp => ((mem_comp T).1 hc).2.2 r hr (hrp.trans ((mem_comp T).1 hc).2.1)⟩

lemma card_child_lt {p c R} (hc : c ∈ comp T p R) (hne : c ≠ p) :
    (comp T c R).card < (comp T p R).card :=
  Finset.card_lt_card ⟨comp_subset T hc, fun hsub =>
    not_mem_comp_of_ne T hc hne (hsub (self_mem_comp T (live_root_of_mem T hc)))⟩

/-- **M3 (correctness).** Under the invariant of the yes/no branches (`q` is in the box of `p` and
in none of the removed boxes), balancing answers with a leaf whose box contains `q`. -/
theorem balance_correct (hT : T.Covers) (q : Fin m → ℝ) :
    ∀ f p R, Live T p R → (comp T p R).card ≤ f →
      (∀ c ∈ R, ∀ tc, T.sub c = some tc → ¬ InBox tc.box.1 tc.box.2 q) →
      (∀ tp, T.sub p = some tp → InBox tp.box.1 tp.box.2 q) →
      ∃ p' lo hi a, T.sub p' = some (.leaf lo hi a) ∧ InBox lo hi q ∧
        (balance T f p R).eval q = a := by
  intro f
  induction f with
  | zero => intro p R hl hf; have := card_ge_one T hl; omega
  | succ f ih =>
    intro p R hl hf hR hp
    obtain ⟨tp, htp⟩ := (BSP.mem_paths_iff T p).1 hl.1
    have hqp := hp tp htp
    by_cases h1 : (comp T p R).card ≤ 1
    · simp only [balance, if_pos h1, htp, Option.bind_some, BoxTree.eval]
      cases tp with
      | leaf lo hi a => exact ⟨p, lo, hi, a, htp, hqp, rfl⟩
      | cut lo hi l r =>
        exfalso
        obtain ⟨hl0, hl1⟩ := BSP.sub_child htp
        have hcov := BSP.covers_sub T p hT htp
        have hblocked : ∀ b, ∀ t, T.sub (p ++ [b]) = some t → ¬ InBox t.box.1 t.box.2 q := by
          intro b t ht
          have hmem : p ++ [b] ∈ T.paths := (BSP.mem_paths_iff T _).2 ⟨t, ht⟩
          have hnot : p ++ [b] ∉ comp T p R := by
            intro hin
            have hpin := self_mem_comp T hl
            have : p ++ [b] = p := Finset.card_le_one.1 h1 _ hin _ hpin
            have := congrArg List.length this; simp at this
          obtain ⟨c, hcR, hcp⟩ : ∃ c ∈ R, c <+: p ++ [b] := by
            by_contra hcon
            push Not at hcon
            exact hnot ((mem_comp T).2 ⟨hmem, List.prefix_append _ _, hcon⟩)
          rcases List.prefix_concat_iff.1 hcp with he | he
          · exact hR c hcR t (he ▸ ht)
          · exact absurd he (hl.2 c hcR)
        rcases hcov.1 q hqp with h | h
        · exact hblocked false l hl0 h
        · exact hblocked true r hl1 h
    · push Not at h1
      obtain ⟨c, hcen, hcC, hcp, -, -⟩ := centroid_spec T hl h1
      obtain ⟨tc, htc⟩ := (BSP.mem_paths_iff T c).1 ((mem_comp T).1 hcC).1
      simp only [balance, if_neg (by omega : ¬ (comp T p R).card ≤ 1), hcen, htc, BoxTree.eval]
      split_ifs with hq
      · exact ih c R (live_of_mem_comp T hcC)
          (by have := card_child_lt T hcC hcp; omega) hR
          (fun t ht => by rw [htc] at ht; cases ht; exact hq)
      · refine ih p (insert c R) ⟨hl.1, ?_⟩ ?_ ?_ hp
        · intro r hr hrp
          rcases Finset.mem_insert.1 hr with rfl | hr
          · exact hcp (prefix_antisymm' hrp ((mem_comp T).1 hcC).2.1)
          · exact hl.2 r hr hrp
        · rw [card_comp_insert T hcC]
          have := card_ge_one T (live_of_mem_comp T hcC); omega
        · intro r hr t ht
          rcases Finset.mem_insert.1 hr with rfl | hr
          · rw [htc] at ht; cases ht; exact hq
          · exact hR r hr t ht

lemma log_step {k k' : ℕ} (hk : 2 ≤ k) (hk' : 1 ≤ k') (h3 : 3 * k' ≤ 2 * k + 1) :
    1 + 6 * Real.log k' ≤ 6 * Real.log k := by
  have h65 : (6 : ℝ) * k' ≤ 5 * k := by
    have : 6 * k' ≤ 5 * k := by omega
    exact_mod_cast this
  have hk'0 : (0 : ℝ) < k' := by exact_mod_cast hk'
  have hlog65 : (1 : ℝ) / 6 ≤ Real.log (6 / 5) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.abs_exp_sub_one_sub_id_le (x := (1 : ℝ) / 6) (by norm_num)
    have := le_abs_self (Real.exp (1 / 6) - 1 - 1 / 6)
    nlinarith
  have hmono : Real.log ((6 / 5) * k') ≤ Real.log k :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_mul (by norm_num) hk'0.ne'] at hmono
  linarith

/-- **M3 (depth).** The number of visited nodes is at most `1 + 6 ln |comp|`. -/
theorem balance_visits (q : Fin m → ℝ) :
    ∀ f p R, Live T p R → (comp T p R).card ≤ f →
      ((balance T f p R).visits q : ℝ) ≤ 1 + 6 * Real.log (comp T p R).card := by
  intro f
  induction f with
  | zero => intro p R hl hf; have := card_ge_one T hl; omega
  | succ f ih =>
    intro p R hl hf
    by_cases h1 : (comp T p R).card ≤ 1
    · simp only [balance, if_pos h1, BoxTree.visits]
      have : (comp T p R).card = 1 := le_antisymm h1 (card_ge_one T hl)
      rw [this]; simp
    · push Not at h1
      obtain ⟨c, hcen, hcC, hcp, hc1, hc2⟩ := centroid_spec T hl h1
      obtain ⟨tc, htc⟩ := (BSP.mem_paths_iff T c).1 ((mem_comp T).1 hcC).1
      simp only [balance, if_neg (by omega : ¬ (comp T p R).card ≤ 1), hcen, htc, BoxTree.visits]
      have hcge := card_ge_one T (live_of_mem_comp T hcC)
      split_ifs with hq
      · have := ih c R (live_of_mem_comp T hcC) (by have := card_child_lt T hcC hcp; omega)
        have hs := log_step h1 hcge hc1
        push_cast; linarith
      · have hl' : Live T p (insert c R) := ⟨hl.1, fun r hr hrp => by
          rcases Finset.mem_insert.1 hr with rfl | hr
          · exact hcp (prefix_antisymm' hrp ((mem_comp T).1 hcC).2.1)
          · exact hl.2 r hr hrp⟩
        have hcard := card_comp_insert T hcC
        have := ih p (insert c R) hl' (by rw [hcard]; omega)
        have hs := log_step h1 (card_ge_one T hl') (by rw [hcard]; exact hc2)
        push_cast; linarith

/-- **M3.** Centroid balancing of a covering BSP answers with a leaf whose box contains the query,
in at most `5 log₂ |T| + 6` visits. -/
theorem balance_spec' (hT : T.Covers) (q : Fin m → ℝ) :
    (InBox T.box.1 T.box.2 q → ∃ p lo hi a, T.sub p = some (.leaf lo hi a) ∧ InBox lo hi q ∧
      (balance T (T.paths.card + 1) [] ∅).eval q = a) ∧
    (balance T (T.paths.card + 1) [] ∅).visits q ≤ 5 * Nat.log 2 T.paths.card + 6 := by
  have hl : Live T [] ∅ := ⟨nil_mem_paths T, by simp⟩
  have hcard : (comp T [] ∅).card = T.paths.card := by rw [comp_nil_empty]
  refine ⟨fun hq => ?_, ?_⟩
  · refine balance_correct T hT q (T.paths.card + 1) [] ∅ hl (by rw [hcard]; omega) (by simp) ?_
    intro tp htp
    have : tp = T := by cases T <;> simp [BSP.sub] at htp <;> exact htp.symm
    rw [this]; exact hq
  · have hv := balance_visits T q (T.paths.card + 1) [] ∅ hl (by rw [hcard]; omega)
    rw [hcard] at hv
    set k := T.paths.card
    set L := Nat.log 2 k
    have hk1 : 1 ≤ k := by rw [← hcard]; exact card_ge_one T hl
    have hlt : (k : ℝ) < 2 ^ (L + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) k
    have hlog : Real.log k ≤ (L + 1) * Real.log 2 := by
      have := Real.log_le_log (by exact_mod_cast hk1) hlt.le
      rw [Real.log_pow] at this; push_cast at this; linarith
    have h2 := Real.log_two_lt_d9
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have : ((balance T (k + 1) [] ∅).visits q : ℝ) < 5 * L + 7 := by nlinarith
    have : ((balance T (k + 1) [] ∅).visits q : ℝ) < ((5 * L + 7 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega

end Balance

end DetANN.HPIM

open DetANN.HPIM in
theorem solution {m : ℕ} (T : BSP m) (hT : T.Covers) (q : Fin m → ℝ) :
    (InBox T.box.1 T.box.2 q → ∃ p lo hi a, T.sub p = some (.leaf lo hi a) ∧ InBox lo hi q ∧
      (balance T (T.paths.card + 1) [] ∅).eval q = a) ∧
    (balance T (T.paths.card + 1) [] ∅).visits q ≤ 5 * Nat.log 2 T.paths.card + 6 :=
  balance_spec' T hT q
