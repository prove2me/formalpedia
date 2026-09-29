-- Prove2me | solution 1 for Freiman.middleRepair_goodness_criterion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T09:57:38.60704+00:00
-- url     : https://prove2.me/submissions/66cab2e4-83fa-4570-96b9-654a64322dd1

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace M8Sep10GoodnessCriterion

private lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

private lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private lemma pe_order (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    (w.length % 2 = 0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y ≤ prefixEval w x) := by
  induction w with
  | nil => simp [prefixEval, hxy]
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hpx := pe_nonneg w x hx
    have hpy := pe_nonneg w y hy
    constructor
    · intro h
      have hw : w.length % 2 = 1 := by simp only [List.length_cons] at h; omega
      exact one_div_le_one_div_of_le (by linarith : 0 < ((a:ℕ):ℝ)+prefixEval w y)
        (by linarith only [ih.2 hw])
    · intro h
      have hw : w.length % 2 = 0 := by simp only [List.length_cons] at h; omega
      exact one_div_le_one_div_of_le (by linarith : 0 < ((a:ℕ):ℝ)+prefixEval w x)
        (by linarith only [ih.1 hw])

private lemma basic_bounds : 0 ≤ middleAlpha ∧ middleAlpha ≤ (1/2:ℝ) ∧
    (1/2:ℝ) ≤ middleBeta ∧ 0 ≤ middleRho := by
  have h4 : (4:ℝ) ≤ Real.sqrt 21 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 21 ≤ (5:ℝ) := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h1 : (1:ℝ) ≤ Real.sqrt 3 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  dsimp [middleAlpha, middleBeta, middleRho]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private lemma small_tails :
    middleAlpha ∈ Set.Icc (0:ℝ) (1/2) ∧
    prefixEval [3] middleRho ∈ Set.Icc (0:ℝ) (1/2) ∧
    prefixEval [2] middleBeta ∈ Set.Icc (0:ℝ) (1/2) := by
  obtain ⟨ha, ha', hb, hr⟩ := basic_bounds
  refine ⟨⟨ha, ha'⟩, ?_, ?_⟩
  · change 0 ≤ 1/(3+middleRho) ∧ 1/(3+middleRho) ≤ (1/2:ℝ)
    constructor
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < 3+middleRho)).2
      linarith
  · change 0 ≤ 1/(2+middleBeta) ∧ 1/(2+middleBeta) ≤ (1/2:ℝ)
    constructor
    · positivity
    · apply (div_le_iff₀ (by linarith : 0 < 2+middleBeta)).2
      linarith

private lemma big_tails :
    (1/2:ℝ) ≤ middleBeta ∧
    (1/2:ℝ) ≤ prefixEval [1,3] middleRho ∧
    (1/2:ℝ) ≤ prefixEval [1,2] middleBeta := by
  obtain ⟨_, hs3, hs2⟩ := small_tails
  refine ⟨basic_bounds.2.2.1, ?_, ?_⟩
  · simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
    change (1/2:ℝ) ≤ 1/(1+prefixEval [3] middleRho)
    apply (le_div_iff₀ (by linarith [hs3.1] : 0 < 1+prefixEval [3] middleRho)).2
    linarith [hs3.2]
  · simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
    change (1/2:ℝ) ≤ 1/(1+prefixEval [2] middleBeta)
    apply (le_div_iff₀ (by linarith [hs2.1] : 0 < 1+prefixEval [2] middleBeta)).2
    linarith [hs2.2]

private lemma e3_le (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.left x ≤ L)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.right x ≤ R) :
    middleE3 c ≤ 4+L+R := by
  obtain ⟨ha, h3, h2⟩ := small_tails
  unfold middleE3
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h3, hr _ h2]
  · rw [pe_append]
    linarith only [hl _ ha, hr _ h3]

private lemma e3_ge (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), L ≤ prefixEval c.left x)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), R ≤ prefixEval c.right x) :
    4+L+R ≤ middleE3 c := by
  obtain ⟨ha, h3, h2⟩ := small_tails
  unfold middleE3
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h3, hr _ h2]
  · rw [pe_append]
    linarith only [hl _ ha, hr _ h3]

private lemma e13_le (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval c.left x ≤ L)
    (hr : ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval c.right x ≤ R) :
    middleE13 c ≤ 4+L+R := by
  obtain ⟨hb, h13, h12⟩ := big_tails
  unfold middleE13
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h13, hr _ h12]
  · rw [pe_append]
    linarith only [hl _ hb, hr _ h13]

private lemma e13_ge (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x : ℝ, (1/2:ℝ) ≤ x → L ≤ prefixEval c.left x)
    (hr : ∀ x : ℝ, (1/2:ℝ) ≤ x → R ≤ prefixEval c.right x) :
    4+L+R ≤ middleE13 c := by
  obtain ⟨hb, h13, h12⟩ := big_tails
  unfold middleE13
  split_ifs
  · rw [pe_append, pe_append]
    linarith only [hl _ h13, hr _ h12]
  · rw [pe_append]
    linarith only [hl _ hb, hr _ h13]

private lemma even_small (w : List ℕ+) (hw : w.length % 2 = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval w x ≤ prefixEval w (1/2) := by
  intro x hx
  exact (pe_order w x (1/2) hx.1 (by norm_num) hx.2).1 hw

private lemma odd_small (w : List ℕ+) (hw : w.length % 2 = 1) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval w (1/2) ≤ prefixEval w x := by
  intro x hx
  exact (pe_order w x (1/2) hx.1 (by norm_num) hx.2).2 hw

private lemma even_big (w : List ℕ+) (hw : w.length % 2 = 0) :
    ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval w (1/2) ≤ prefixEval w x := by
  intro x hx
  exact (pe_order w (1/2) x (by norm_num) (by linarith) hx).1 hw

private lemma odd_big (w : List ℕ+) (hw : w.length % 2 = 1) :
    ∀ x : ℝ, (1/2:ℝ) ≤ x → prefixEval w x ≤ prefixEval w (1/2) := by
  intro x hx
  exact (pe_order w (1/2) x (by norm_num) (by linarith) hx).2 hw

private lemma even_append_one_small (w : List ℕ+) (hw : w.length % 2 = 0) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval w (1/2) ≤ prefixEval (w++[1]) x := by
  intro x hx
  rw [pe_append]
  apply even_big w hw
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  change (1/2:ℝ) ≤ 1/(1+x)
  apply (le_div_iff₀ (by linarith [hx.1] : 0 < 1+x)).2
  linarith [hx.2]

private lemma odd_append_one_small (w : List ℕ+) (hw : w.length % 2 = 1) :
    ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval (w++[1]) x ≤ prefixEval w (1/2) := by
  intro x hx
  rw [pe_append]
  apply odd_big w hw
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_ofNat, Nat.cast_one]
  change (1/2:ℝ) ≤ 1/(1+x)
  apply (le_div_iff₀ (by linarith [hx.1] : 0 < 1+x)).2
  linarith [hx.2]

private lemma normalized_parity (c : MiddleCore) (k : ℕ)
    (hl : c.left.length % 2 = k) (hr : c.right.length % 2 = k) :
    (middleNormalized c).left.length % 2 = k ∧ (middleNormalized c).right.length % 2 = k := by
  unfold middleNormalized
  split_ifs
  · exact ⟨hl, hr⟩
  · exact ⟨hr, hl⟩

private lemma equal_even (c : MiddleCore)
    (hl : c.left.length % 2 = 0) (hr : c.right.length % 2 = 0) :
    (middleEqualBounds c).1 = middleE3 (middleNormalized c) := by
  unfold middleEqualBounds
  simp only [(normalized_parity c 0 hl hr).1, ite_true]

private lemma equal_odd (c : MiddleCore)
    (hl : c.left.length % 2 = 1) (hr : c.right.length % 2 = 1) :
    (middleEqualBounds c).2 = middleE3 (middleNormalized c) := by
  unfold middleEqualBounds
  simp only [(normalized_parity c 1 hl hr).1, one_ne_zero, ite_false]

private lemma e3_normalized_le (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.left x ≤ L)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), prefixEval c.right x ≤ R) :
    middleE3 (middleNormalized c) ≤ 4+L+R := by
  unfold middleNormalized
  split_ifs
  · exact e3_le c L R hl hr
  · have h := e3_le ⟨c.right,c.left⟩ R L hr hl
    linarith only [h]

private lemma e3_normalized_ge (c : MiddleCore) (L R : ℝ)
    (hl : ∀ x ∈ Set.Icc (0:ℝ) (1/2), L ≤ prefixEval c.left x)
    (hr : ∀ x ∈ Set.Icc (0:ℝ) (1/2), R ≤ prefixEval c.right x) :
    4+L+R ≤ middleE3 (middleNormalized c) := by
  unfold middleNormalized
  split_ifs
  · exact e3_ge c L R hl hr
  · have h := e3_ge ⟨c.right,c.left⟩ R L hr hl
    linarith only [h]

private noncomputable def center (c : MiddleCore) : ℝ :=
  4 + prefixEval c.left (1/2) + prefixEval c.right (1/2)

private lemma center_normalized (c : MiddleCore) : center (middleNormalized c) = center c := by
  unfold middleNormalized
  split_ifs
  · rfl
  · dsimp only [center]
    ring

private lemma equal_center (c : MiddleCore) (hp : c.left.length % 2 = c.right.length % 2) :
    (middleEqualBounds c).1 ≤ center c ∧ center c ≤ (middleEqualBounds c).2 := by
  rw [← center_normalized c]
  let d := middleNormalized c
  have hd : d.left.length % 2 = d.right.length % 2 := by
    dsimp [d, middleNormalized]
    split_ifs
    · exact hp
    · exact hp.symm
  change (if d.left.length % 2 = 0 then (middleE3 d,middleE13 d)
    else (middleE13 d,middleE3 d)).1 ≤ center d ∧
    center d ≤ (if d.left.length % 2 = 0 then (middleE3 d,middleE13 d)
    else (middleE13 d,middleE3 d)).2
  by_cases he : d.left.length % 2 = 0
  · simp only [he, ite_true]
    have hr : d.right.length % 2 = 0 := hd.symm.trans he
    exact ⟨e3_le d _ _ (even_small _ he) (even_small _ hr),
      e13_ge d _ _ (even_big _ he) (even_big _ hr)⟩
  · simp only [he, ite_false]
    have ho : d.left.length % 2 = 1 := by omega
    have hr : d.right.length % 2 = 1 := hd.symm.trans ho
    exact ⟨e13_le d _ _ (odd_big _ ho) (odd_big _ hr),
      e3_ge d _ _ (odd_small _ ho) (odd_small _ hr)⟩

private lemma mixed_even_center (d : MiddleCore)
    (hl : d.left.length % 2 = 0) (hr : d.right.length % 2 = 1) :
    (middleEqualBounds ⟨d.left,d.right++[1]⟩).1 ≤ center d ∧
      center d ≤ (middleEqualBounds ⟨d.left++[1],d.right⟩).2 := by
  have hl1 : (d.left++[1]).length % 2 = 1 := by simp only [List.length_append, List.length_singleton]; omega
  have hr1 : (d.right++[1]).length % 2 = 0 := by simp only [List.length_append, List.length_singleton]; omega
  rw [equal_even ⟨d.left,d.right++[1]⟩ hl hr1, equal_odd ⟨d.left++[1],d.right⟩ hl1 hr]
  exact ⟨e3_normalized_le ⟨d.left,d.right++[1]⟩ _ _ (even_small _ hl) (odd_append_one_small _ hr),
    e3_normalized_ge ⟨d.left++[1],d.right⟩ _ _ (even_append_one_small _ hl) (odd_small _ hr)⟩

private lemma mixed_odd_center (d : MiddleCore)
    (hl : d.left.length % 2 = 1) (hr : d.right.length % 2 = 0) :
    (middleEqualBounds ⟨d.left++[1],d.right⟩).1 ≤ center d ∧
      center d ≤ (middleEqualBounds ⟨d.left,d.right++[1]⟩).2 := by
  have hl1 : (d.left++[1]).length % 2 = 0 := by simp only [List.length_append, List.length_singleton]; omega
  have hr1 : (d.right++[1]).length % 2 = 1 := by simp only [List.length_append, List.length_singleton]; omega
  rw [equal_even ⟨d.left++[1],d.right⟩ hl1 hr, equal_odd ⟨d.left,d.right++[1]⟩ hl hr1]
  exact ⟨e3_normalized_le ⟨d.left++[1],d.right⟩ _ _ (odd_append_one_small _ hl) (even_small _ hr),
    e3_normalized_ge ⟨d.left,d.right++[1]⟩ _ _ (odd_small _ hl) (even_append_one_small _ hr)⟩

private lemma bounds_center (c : MiddleCore) :
    (middleBounds c).1 ≤ center c ∧ center c ≤ (middleBounds c).2 := by
  have h : (middleBounds c).1 ≤ center (middleNormalized c) ∧
      center (middleNormalized c) ≤ (middleBounds c).2 := by
    unfold middleBounds
    dsimp only
    split_ifs with hsame he
    · exact equal_center _ hsame
    · exact mixed_even_center _ he (by omega)
    · exact mixed_odd_center _ (by omega) (by omega)
  simpa only [center_normalized] using h

private lemma child_center (c : MiddleCore) (u : List ℕ+) :
    center (middleRepairChild c u []) =
      4 + prefixEval (middleNormalized c).left (prefixEval u (1/2)) +
        prefixEval (middleNormalized c).right (1/2) := by
  unfold middleRepairChild
  rw [center_normalized]
  simp only [center, middleRepairRawChild, List.append_nil, pe_append]

private lemma child_center_order (c : MiddleCore) :
    if (middleNormalized c).left.length % 2 = 0 then
      center (middleRepairChild c [2] []) ≤ center (middleRepairChild c [1] [])
    else center (middleRepairChild c [1] []) ≤ center (middleRepairChild c [2] []) := by
  have h := pe_order (middleNormalized c).left (prefixEval [2] (1/2)) (prefixEval [1] (1/2))
    (by norm_num [prefixEval]) (by norm_num [prefixEval]) (by norm_num [prefixEval])
  by_cases he : (middleNormalized c).left.length % 2 = 0
  · rw [if_pos he, child_center, child_center]
    linarith only [h.1 he]
  · rw [if_neg he, child_center, child_center]
    have ho : (middleNormalized c).left.length % 2 = 1 := by omega
    linarith only [h.2 ho]

private lemma interval_inter_iff (l₁ u₁ l₂ u₂ : ℝ) (h₁ : l₁ ≤ u₁) (h₂ : l₂ ≤ u₂) :
    (Set.Icc l₁ u₁ ∩ Set.Icc l₂ u₂).Nonempty ↔ l₁ ≤ u₂ ∧ l₂ ≤ u₁ := by
  constructor
  · rintro ⟨x, hx₁, hx₂⟩
    exact ⟨hx₁.1.trans hx₂.2, hx₂.1.trans hx₁.2⟩
  · rintro ⟨h₁₂, h₂₁⟩
    exact ⟨max l₁ l₂, ⟨le_max_left _ _, max_le h₁ h₂₁⟩,
      ⟨le_max_right _ _, max_le h₁₂ h₂⟩⟩

end M8Sep10GoodnessCriterion

theorem solution :
    ∀ c : MiddleCore, middleRegular c → (middleRepairGood c ↔ (if (middleNormalized c).left.length%2=0 then (middleBounds (middleRepairChild c [1] [])).1 ≤ (middleBounds (middleRepairChild c [2] [])).2 else (middleBounds (middleRepairChild c [2] [])).1 ≤ (middleBounds (middleRepairChild c [1] [])).2)) := by
  intro c _
  have h₁ := M8Sep10GoodnessCriterion.bounds_center (middleRepairChild c [1] [])
  have h₂ := M8Sep10GoodnessCriterion.bounds_center (middleRepairChild c [2] [])
  rw [middleRepairGood, middleCover, middleCover,
    M8Sep10GoodnessCriterion.interval_inter_iff _ _ _ _ (h₁.1.trans h₁.2) (h₂.1.trans h₂.2)]
  have ho := M8Sep10GoodnessCriterion.child_center_order c
  by_cases he : (middleNormalized c).left.length % 2 = 0
  · rw [if_pos he] at ho ⊢
    constructor
    · exact And.left
    · intro h
      exact ⟨h, h₂.1.trans (ho.trans h₁.2)⟩
  · rw [if_neg he] at ho ⊢
    constructor
    · exact And.right
    · intro h
      exact ⟨h₁.1.trans (ho.trans h₂.2), h⟩

#print axioms solution
