-- Prove2me | solution 1 for ExtensionComplexity.TSP.razborov_distributional
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-06T10:38:11.257587+00:00
-- url     : https://prove2.me/submissions/3e0e3ed5-8b29-423f-ab37-fcb6a3d413ea

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_ExtensionComplexity_TSP_TSPPolytope


open Finset

namespace XCR

/-! ### Counting core of Claim 3 (replacing the entropy estimate) -/

section Counting
variable {α : Type*}

/-- Binomial tail: the subsets of `I` of size at most `j` number at most `2^j (3/2)^{|I|}`. -/
lemma card_small_subsets_le (I : Finset α) (j : ℕ) :
    ((I.powerset.filter (fun T => #T ≤ j)).card : ℝ) ≤ 2 ^ j * (3 / 2) ^ #I := by
  have hsum : (∑ T ∈ I.powerset, (1 / 2 : ℝ) ^ #T * 1 ^ (#I - #T)) = (3 / 2) ^ #I := by
    rw [sum_pow_mul_eq_add_pow]; norm_num
  rw [card_eq_sum_ones, Nat.cast_sum, ← hsum, mul_sum]
  calc (∑ x ∈ I.powerset.filter (fun T => #T ≤ j), ((1 : ℕ) : ℝ))
      ≤ ∑ T ∈ I.powerset.filter (fun T => #T ≤ j), (2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ #T * 1 ^ (#I - #T)) := by
        apply sum_le_sum
        intro T hT
        simp only [mem_filter] at hT
        rw [one_pow, mul_one, Nat.cast_one]
        have h1 : (2 : ℝ) ^ #T ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hT.2
        have h2 : (2 : ℝ) ^ #T * (1 / 2) ^ #T = 1 := by
          rw [← mul_pow]; norm_num
        nlinarith [pow_pos (show (0 : ℝ) < 1 / 2 by norm_num) #T]
    _ ≤ ∑ T ∈ I.powerset, (2 : ℝ) ^ j * ((1 / 2 : ℝ) ^ #T * 1 ^ (#I - #T)) := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro T _ _; positivity

/-- Markov step: if every `i ∈ I` lies in at most a quarter of the members of `S`, then at least
a third of the members of `S` meet `I` in at most `3|I|/8` points. -/
lemma card_le_three_mul_good [DecidableEq α] (S : Finset (Finset α)) (I : Finset α)
    (h : ∀ i ∈ I, 4 * #(S.filter (fun s => i ∈ s)) ≤ #S) :
    #S ≤ 3 * #(S.filter (fun s => 8 * #(I ∩ s) ≤ 3 * #I)) := by
  have hsum : 4 * (∑ s ∈ S, #(I ∩ s)) ≤ #I * #S := by
    have := sum_card_inter_le (s := I) (B := S) (n := #S / 4) (fun a ha => by
      have := h a ha
      omega)
    calc 4 * (∑ s ∈ S, #(I ∩ s)) ≤ 4 * (#I * (#S / 4)) := by omega
      _ ≤ #I * #S := by
        rw [← mul_assoc, mul_comm 4 #I, mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
  set G := S.filter (fun s => 8 * #(I ∩ s) ≤ 3 * #I)
  have hsplit := sum_filter_add_sum_filter_not S (fun s => 8 * #(I ∩ s) ≤ 3 * #I)
    (fun s => #(I ∩ s))
  have hbad : (3 * #I + 1) * #(S.filter (fun s => ¬ 8 * #(I ∩ s) ≤ 3 * #I)) ≤
      8 * ∑ s ∈ S.filter (fun s => ¬ 8 * #(I ∩ s) ≤ 3 * #I), #(I ∩ s) := by
    have := card_nsmul_le_sum (S.filter (fun s => ¬ 8 * #(I ∩ s) ≤ 3 * #I))
      (fun s => 8 * #(I ∩ s)) (3 * #I + 1) (by
        intro s hs; simp only [mem_filter] at hs; omega)
    rw [smul_eq_mul, ← mul_sum] at this
    linarith
  have hcard := card_filter_add_card_filter_not (s := S)
    (fun s => 8 * #(I ∩ s) ≤ 3 * #I)
  set B := S.filter (fun s => ¬ 8 * #(I ∩ s) ≤ 3 * #I)
  have h1 : (3 * #I + 1) * #B ≤ 2 * #I * (#G + #B) := by
    have e1 : ∑ s ∈ B, #(I ∩ s) ≤ ∑ s ∈ S, #(I ∩ s) := by omega
    have e2 : 2 * #I * (#G + #B) = 2 * (#I * #S) := by rw [hcard]; ring
    rw [e2]; omega
  have h2 : (#I + 1) * #B ≤ (#I + 1) * (2 * #G) := by nlinarith
  have h3 : #B ≤ 2 * #G := Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos _)
  have hc : #G + #B = #S := hcard
  omega

/-- Claim 3, counting form: if every `i ∈ I ⊆ W` lies in at most a quarter of the members of a
family `S` of subsets of `W`, then `|S| ≤ 3 · 2^{|W|-|I|} · 2^{⌊3|I|/8⌋} (3/2)^{|I|}`. -/
lemma card_family_le [DecidableEq α] (W I : Finset α) (hIW : I ⊆ W) (S : Finset (Finset α))
    (hSW : ∀ s ∈ S, s ⊆ W) (h : ∀ i ∈ I, 4 * #(S.filter (fun s => i ∈ s)) ≤ #S) :
    (#S : ℝ) ≤ 3 * (2 ^ (#W - #I) * (2 ^ (3 * #I / 8) * (3 / 2) ^ #I)) := by
  have h1 := card_le_three_mul_good S I h
  set G := S.filter (fun s => 8 * #(I ∩ s) ≤ 3 * #I)
  have h2 : #G ≤ #((I.powerset.filter (fun T => #T ≤ 3 * #I / 8)) ×ˢ (W \ I).powerset) := by
    apply card_le_card_of_injOn (fun s => (I ∩ s, s \ I))
    · intro s hs
      have hs' : s ∈ S ∧ 8 * #(I ∩ s) ≤ 3 * #I := by simpa [G] using hs
      simp only [mem_coe, mem_product, mem_filter, mem_powerset]
      refine ⟨⟨inter_subset_left, by omega⟩, ?_⟩
      exact sdiff_subset_sdiff (hSW s hs'.1) le_rfl
    · intro s _ t _ hst
      simp only [Prod.mk.injEq] at hst
      rw [← sdiff_union_inter s I, ← sdiff_union_inter t I, inter_comm s, inter_comm t,
        hst.1, hst.2]
  rw [card_product, card_powerset, card_sdiff_of_subset hIW] at h2
  have h3 := card_small_subsets_le I (3 * #I / 8)
  have h4 : (#G : ℝ) ≤ 2 ^ (#W - #I) * (2 ^ (3 * #I / 8) * (3 / 2) ^ #I) := by
    calc (#G : ℝ) ≤ ((#(I.powerset.filter (fun T => #T ≤ 3 * #I / 8)) * 2 ^ (#W - #I) : ℕ) : ℝ) := by
          exact_mod_cast h2
      _ ≤ _ := by
        push_cast
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : (#S : ℝ) ≤ 3 * #G := by exact_mod_cast h1
  linarith

end Counting

/-! ### One side of a partition -/

section Side
open Classical
variable {α : Type*} [DecidableEq α] (m : ℕ)

/-- `#{x ∈ [Z]^m : x ∈ X}`. -/
noncomputable def cnt0 (X : Finset α → Prop) (Z : Finset α) : ℕ :=
  #((powersetCard m Z).filter X)

/-- `#{x ∈ [Z]^{m-1} : x ∪ {i} ∈ X}`. -/
noncomputable def cnt1 (X : Finset α → Prop) (i : α) (Z : Finset α) : ℕ :=
  #((powersetCard (m - 1) Z).filter (fun x => X (insert i x)))

lemma cnt0_erase (X : Finset α → Prop) (W : Finset α) (i : α) :
    cnt0 m X (W.erase i) = #(((powersetCard m W).filter X).filter (fun s => i ∉ s)) := by
  unfold cnt0
  congr 1
  ext x
  simp only [mem_filter, mem_powersetCard, subset_erase]
  tauto

lemma cnt1_erase (hm : 1 ≤ m) (X : Finset α → Prop) (W : Finset α) (i : α) (hi : i ∈ W) :
    cnt1 m X i (W.erase i) = #(((powersetCard m W).filter X).filter (fun s => i ∈ s)) := by
  unfold cnt1
  apply card_bij' (fun x _ => insert i x) (fun s _ => s.erase i)
  · intro x hx
    simp only [mem_filter, mem_powersetCard, subset_erase] at hx
    exact erase_insert hx.1.1.2
  · intro s hs
    simp only [mem_filter] at hs
    exact insert_erase hs.2
  · intro x hx
    simp only [mem_filter, mem_powersetCard, subset_erase] at hx ⊢
    refine ⟨⟨⟨insert_subset hi hx.1.1.1, ?_⟩, hx.2⟩, mem_insert_self _ _⟩
    rw [card_insert_of_notMem hx.1.1.2, hx.1.2]; omega
  · intro s hs
    simp only [mem_filter, mem_powersetCard, subset_erase] at hs ⊢
    refine ⟨⟨⟨(erase_subset _ _).trans hs.1.1.1, notMem_erase _ _⟩, ?_⟩, ?_⟩
    · rw [card_erase_of_mem hs.2, hs.1.1.2]
    · rw [insert_erase hs.2]; exact hs.1.2

/-- Double counting: `∑_{i ∈ W} #{s ∈ S : i ∉ s} = m |S|` for `S ⊆ [W]^m`, `|W| = 2m`. -/
lemma sum_cnt0_erase (X : Finset α → Prop) (W : Finset α) (hW : #W = 2 * m) :
    ∑ i ∈ W, cnt0 m X (W.erase i) = m * #((powersetCard m W).filter X) := by
  simp_rw [cnt0_erase, card_filter]
  rw [sum_comm]
  have : ∀ s ∈ (powersetCard m W).filter X, (∑ i ∈ W, if i ∉ s then 1 else 0) = m := by
    intro s hs
    simp only [mem_filter, mem_powersetCard] at hs
    rw [← card_filter]
    have : W.filter (fun i => i ∉ s) = W \ s := by ext; simp [mem_sdiff]
    rw [this, card_sdiff_of_subset hs.1.1, hW, hs.1.2]; omega
  rw [sum_congr rfl this, sum_const, smul_eq_mul, mul_comm, card_filter]

/-- The normalizing binomial `C(2m-1, m)`. -/
noncomputable def cc : ℝ := ((2 * m - 1).choose m : ℝ)

/-- `P[x₀ ∈ X]` given the own part `Z` (`x₀` uniform in `[Z]^m`). -/
noncomputable def q0 (X : Finset α → Prop) (Z : Finset α) : ℝ := cnt0 m X Z / cc m

/-- `P[x₁ ∈ X]` given `i` and the own part `Z` (`x₁ = {i} ∪` uniform member of `[Z]^{m-1}`). -/
noncomputable def q1 (X : Finset α → Prop) (i : α) (Z : Finset α) : ℝ := cnt1 m X i Z / cc m

/-- Razborov's badness `p_{x,1} < p_{x,0}/3 − η`. -/
def bad (η : ℝ) (X : Finset α → Prop) (i : α) (Z : Finset α) : Prop :=
  q1 m X i Z < q0 m X Z / 3 - η

/-- The numerical inequality that makes Claim 3 work. -/
def NumOK (η : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ 2 * m → 2 * m ≤ 5 * k →
    (2 : ℝ) ^ (2 * m - k) * (2 ^ (3 * k / 8) * (3 / 2) ^ k) ≤ η * cc m

lemma cc_pos (hm : 1 ≤ m) : 0 < cc m := by
  unfold cc; exact_mod_cast Nat.choose_pos (by omega)

/-- Claim 3: for a fixed `W` (`= Z_x ∪ {i}`, `|W| = 2m`), fewer than `2m/5` choices of `i ∈ W`
are bad. -/
lemma few_bad (hm : 1 ≤ m) {η : ℝ} (hη : 0 ≤ η) (hnum : NumOK m η) (X : Finset α → Prop)
    (W : Finset α) (hW : #W = 2 * m) :
    5 * #(W.filter (fun i => bad m η X i (W.erase i))) < 2 * m := by
  by_contra hcon
  push Not at hcon
  set I := W.filter (fun i => bad m η X i (W.erase i))
  set S := (powersetCard m W).filter X
  have hc := cc_pos m hm
  have hIW : I ⊆ W := filter_subset _ _
  have hk : #I ≤ 2 * m := hW ▸ card_le_card hIW
  have hI : I.Nonempty := by
    rw [← card_pos]; omega
  -- each bad `i` gives `3·#S⁺ < #S⁻ − 3ηc`
  have key : ∀ i ∈ I, 3 * (#(S.filter (fun s => i ∈ s)) : ℝ) <
      #(S.filter (fun s => i ∉ s)) - 3 * η * cc m := by
    intro i hi
    have hb := (mem_filter.1 hi).2
    unfold bad q0 q1 at hb
    rw [cnt0_erase, cnt1_erase m hm X W i (mem_filter.1 hi).1] at hb
    have hb' := mul_lt_mul_of_pos_right hb (show 0 < 3 * cc m by positivity)
    have e1 : ((#(S.filter (fun s => i ∈ s)) : ℕ) : ℝ) / cc m * (3 * cc m) =
        3 * #(S.filter (fun s => i ∈ s)) := by field_simp
    have e2 : (((#(S.filter (fun s => i ∉ s)) : ℕ) : ℝ) / cc m / 3 - η) * (3 * cc m) =
        #(S.filter (fun s => i ∉ s)) - 3 * η * cc m := by field_simp
    linarith
  have hsplit : ∀ i, #(S.filter (fun s => i ∈ s)) + #(S.filter (fun s => i ∉ s)) = #S :=
    fun i => card_filter_add_card_filter_not _
  have hquarter : ∀ i ∈ I, 4 * #(S.filter (fun s => i ∈ s)) ≤ #S := by
    intro i hi
    have h1 := key i hi
    have h2 := hsplit i
    have h3 : (0 : ℝ) ≤ 3 * η * cc m := by positivity
    have h4 : 3 * (#(S.filter (fun s => i ∈ s)) : ℝ) < #(S.filter (fun s => i ∉ s)) := by linarith
    have h5 : 3 * #(S.filter (fun s => i ∈ s)) < #(S.filter (fun s => i ∉ s)) := by exact_mod_cast h4
    omega
  have hSW : ∀ s ∈ S, s ⊆ W := fun s hs => (mem_powersetCard.1 (mem_filter.1 hs).1).1
  have hbound := card_family_le W I hIW S hSW hquarter
  obtain ⟨i, hi⟩ := hI
  have h1 := key i hi
  have h2 : (#(S.filter (fun s => i ∉ s)) : ℝ) ≤ #S := by exact_mod_cast card_filter_le _ _
  have h3 := hnum #I hk hcon
  rw [hW] at hbound
  have h0 : (0 : ℝ) ≤ #(S.filter (fun s => i ∈ s)) := by positivity
  linarith

lemma q0_le_one (hm : 1 ≤ m) (X : Finset α → Prop) (Z : Finset α) (hZ : #Z = 2 * m - 1) :
    q0 m X Z ≤ 1 := by
  unfold q0
  rw [div_le_one (cc_pos m hm)]
  unfold cnt0 cc
  rw [← hZ, ← card_powersetCard]
  exact_mod_cast card_filter_le _ _

lemma q0_nonneg (X : Finset α → Prop) (Z : Finset α) : 0 ≤ q0 m X Z := by
  unfold q0 cc; positivity

lemma q1_nonneg (X : Finset α → Prop) (i : α) (Z : Finset α) : 0 ≤ q1 m X i Z := by
  unfold q1 cc; positivity

/-- Claim 4, per `W`: the bad `i` carry at most `2/5` of `∑_{i ∈ W} p_{x,0}`. -/
lemma sum_bad_le (hm : 1 ≤ m) {η : ℝ} (hη : 0 ≤ η) (hnum : NumOK m η) (X : Finset α → Prop)
    (W : Finset α) (hW : #W = 2 * m) :
    ∑ i ∈ W, (if bad m η X i (W.erase i) then q0 m X (W.erase i) else 0) ≤
      2 / 5 * ∑ i ∈ W, q0 m X (W.erase i) := by
  have hfew := few_bad m hm hη hnum X W hW
  set S := (powersetCard m W).filter X
  have hc := cc_pos m hm
  have htot : ∑ i ∈ W, q0 m X (W.erase i) = m * #S / cc m := by
    unfold q0
    rw [← sum_div, ← Nat.cast_sum, sum_cnt0_erase m X W hW]; push_cast; ring
  rw [htot, ← sum_filter]
  have hle : ∀ i ∈ W.filter (fun i => bad m η X i (W.erase i)), q0 m X (W.erase i) ≤ #S / cc m := by
    intro i _
    unfold q0
    apply div_le_div_of_nonneg_right _ hc.le
    rw [cnt0_erase]; exact_mod_cast card_filter_le _ _
  calc ∑ i ∈ W.filter (fun i => bad m η X i (W.erase i)), q0 m X (W.erase i)
      ≤ ∑ i ∈ W.filter (fun i => bad m η X i (W.erase i)), (#S : ℝ) / cc m := sum_le_sum hle
    _ = #(W.filter (fun i => bad m η X i (W.erase i))) * (#S / cc m) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (2 * m / 5) * (#S / cc m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have : (5 * #(W.filter (fun i => bad m η X i (W.erase i))) : ℝ) ≤ 2 * m := by
          exact_mod_cast hfew.le
        linarith
    _ = 2 / 5 * (m * #S / cc m) := by ring

end Side

/-! ### The random partition `(Z_x, Z_y, {i})` of `U` -/

section Partition
open Classical
variable {α : Type*} [DecidableEq α] (m : ℕ) (U : Finset α)

/-- Partitions `t = (i, Z_x)` of `U` into `Z_x`, `Z_y = U ∖ (Z_x ∪ {i})` and `{i}`, `|Z_x| = 2m-1`. -/
noncomputable def parts : Finset (α × Finset α) :=
  (U ×ˢ powersetCard (2 * m - 1) U).filter (fun t => t.1 ∉ t.2)

/-- `Z_y` of a partition. -/
noncomputable def zy (t : α × Finset α) : Finset α := U \ insert t.1 t.2

lemma mem_parts {t : α × Finset α} :
    t ∈ parts m U ↔ t.1 ∈ U ∧ t.2 ⊆ U ∧ #t.2 = 2 * m - 1 ∧ t.1 ∉ t.2 := by
  unfold parts; simp [mem_powersetCard, and_assoc]

variable {m U}

lemma card_zy (hm : 1 ≤ m) (hU : #U = 4 * m - 1) {t : α × Finset α} (ht : t ∈ parts m U) :
    #(zy U t) = 2 * m - 1 := by
  rw [mem_parts] at ht
  unfold zy
  rw [card_sdiff_of_subset (insert_subset ht.1 ht.2.1), card_insert_of_notMem ht.2.2.2, hU,
    ht.2.2.1]
  omega

lemma zy_zy {t : α × Finset α} (ht : t ∈ parts m U) : zy U (t.1, zy U t) = t.2 := by
  rw [mem_parts] at ht
  unfold zy
  ext a
  simp only [mem_sdiff, mem_insert]
  constructor
  · intro h; by_contra ha; exact h.2 (Or.inr ⟨h.1, fun h' => h'.elim (fun e => h.2 (Or.inl e)) ha⟩)
  · intro ha
    refine ⟨ht.2.1 ha, ?_⟩
    rintro (e | ⟨_, h⟩)
    · exact ht.2.2.2 (e ▸ ha)
    · exact h (Or.inr ha)

lemma swap_mem (hm : 1 ≤ m) (hU : #U = 4 * m - 1) {t : α × Finset α} (ht : t ∈ parts m U) :
    (t.1, zy U t) ∈ parts m U := by
  have hc := card_zy hm hU ht
  rw [mem_parts] at ht ⊢
  refine ⟨ht.1, sdiff_subset, hc, ?_⟩
  unfold zy; simp

/-- Symmetry `Z_x ↔ Z_y`. -/
lemma sum_swap (hm : 1 ≤ m) (hU : #U = 4 * m - 1) (f : α → Finset α → Finset α → ℝ) :
    ∑ t ∈ parts m U, f t.1 t.2 (zy U t) = ∑ t ∈ parts m U, f t.1 (zy U t) t.2 := by
  apply sum_nbij' (fun t => (t.1, zy U t)) (fun t => (t.1, zy U t))
  · intro t ht; exact swap_mem hm hU ht
  · intro t ht; exact swap_mem hm hU ht
  · intro t ht; simp [zy_zy ht]
  · intro t ht; simp [zy_zy ht]
  · intro t ht; simp [zy_zy ht]

/-- Regrouping by `W = Z_x ∪ {i}` (equivalently, conditioning on `Z_y = U ∖ W`). -/
lemma sum_regroup (hm : 1 ≤ m) (f : α → Finset α → Finset α → ℝ) :
    ∑ t ∈ parts m U, f t.1 t.2 (zy U t) =
      ∑ W ∈ powersetCard (2 * m) U, ∑ i ∈ W, f i (W.erase i) (U \ W) := by
  rw [sum_sigma']
  symm
  apply sum_nbij' (fun p => (p.2, p.1.erase p.2)) (fun t => ⟨insert t.1 t.2, t.1⟩)
  · intro p hp
    simp only [mem_sigma, mem_powersetCard] at hp
    rw [mem_parts]
    refine ⟨hp.1.1 hp.2, (erase_subset _ _).trans hp.1.1, ?_, notMem_erase _ _⟩
    rw [card_erase_of_mem hp.2, hp.1.2]
  · intro t ht
    rw [mem_parts] at ht
    simp only [mem_sigma, mem_powersetCard]
    refine ⟨⟨insert_subset ht.1 ht.2.1, ?_⟩, mem_insert_self _ _⟩
    rw [card_insert_of_notMem ht.2.2.2, ht.2.2.1]; omega
  · intro p hp
    simp only [mem_sigma] at hp
    simp [insert_erase hp.2]
  · intro t ht
    rw [mem_parts] at ht
    simp [erase_insert ht.2.2.2]
  · intro p hp
    simp only [mem_sigma] at hp
    simp only [zy, insert_erase hp.2]

/-- Claim 4 (the `x`-bad part). -/
lemma claim4_x (hm : 1 ≤ m) {η : ℝ} (hη : 0 ≤ η) (hnum : NumOK m η)
    (X Y : Finset α → Prop) :
    ∑ t ∈ parts m U, (if bad m η X t.1 t.2 then q0 m X t.2 else 0) * q0 m Y (zy U t) ≤
      2 / 5 * ∑ t ∈ parts m U, q0 m X t.2 * q0 m Y (zy U t) := by
  have h1 := sum_regroup (U := U) hm
    (fun i Zx Zy => (if bad m η X i Zx then q0 m X Zx else 0) * q0 m Y Zy)
  have h2 := sum_regroup (U := U) hm (fun i Zx Zy => q0 m X Zx * q0 m Y Zy)
  rw [h1, h2, mul_sum]
  apply sum_le_sum
  intro W hW
  rw [mem_powersetCard] at hW
  rw [← sum_mul, ← sum_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (sum_bad_le m hm hη hnum X W hW.2) (q0_nonneg m _ _)

/-- Claim 4. -/
lemma claim4 (hm : 1 ≤ m) (hU : #U = 4 * m - 1) {η : ℝ} (hη : 0 ≤ η) (hnum : NumOK m η)
    (X Y : Finset α → Prop) :
    ∑ t ∈ parts m U, ((if bad m η X t.1 t.2 then 1 else 0) +
        (if bad m η Y t.1 (zy U t) then 1 else 0)) * (q0 m X t.2 * q0 m Y (zy U t)) ≤
      4 / 5 * ∑ t ∈ parts m U, q0 m X t.2 * q0 m Y (zy U t) := by
  have hx := claim4_x (U := U) hm hη hnum X Y
  have hy := claim4_x (U := U) hm hη hnum Y X
  have s1 := sum_swap hm hU
    (fun i Zx Zy => (if bad m η Y i Zy then q0 m Y Zy else 0) * q0 m X Zx)
  have s2 := sum_swap hm hU (fun i Zx Zy => q0 m Y Zy * q0 m X Zx)
  rw [← s1, ← s2] at hy
  have e : ∀ t ∈ parts m U, ((if bad m η X t.1 t.2 then 1 else 0) +
        (if bad m η Y t.1 (zy U t) then 1 else 0)) * (q0 m X t.2 * q0 m Y (zy U t)) =
      (if bad m η X t.1 t.2 then q0 m X t.2 else 0) * q0 m Y (zy U t) +
        (if bad m η Y t.1 (zy U t) then q0 m Y (zy U t) else 0) * q0 m X t.2 := by
    intro t _; split_ifs <;> ring
  have e2 : ∀ t ∈ parts m U, q0 m Y (zy U t) * q0 m X t.2 = q0 m X t.2 * q0 m Y (zy U t) :=
    fun t _ => mul_comm _ _
  rw [sum_congr rfl e, sum_add_distrib]
  rw [sum_congr rfl e2] at hy
  linarith

/-- The pointwise estimate on a partition. -/
lemma pointwise (a b x y η : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hη : 0 ≤ η) (cx cy : ℝ) (hcx : cx = 0 ∨ cx = 1)
    (hcy : cy = 0 ∨ cy = 1) (gx : cx = 0 → a / 3 - η ≤ x) (gy : cy = 0 → b / 3 - η ≤ y) :
    a * b / 9 - (cx + cy) * (a * b) / 9 - 2 * η / 3 ≤ x * y := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  rcases hcx with rfl | rfl
  · rcases hcy with rfl | rfl
    · have gx := gx rfl; have gy := gy rfl
      by_cases h1 : 0 ≤ a / 3 - η
      · by_cases h2 : 0 ≤ b / 3 - η
        · nlinarith [mul_le_mul gx gy h2 hx]
        · nlinarith [mul_le_mul_of_nonneg_left hb1 ha]
      · nlinarith [mul_le_mul_of_nonneg_right ha1 hb]
    · nlinarith
  · rcases hcy with rfl | rfl <;> nlinarith

/-- Main estimate: `E[p_{x,1} p_{y,1}] ≥ E[p_{x,0} p_{y,0}]/45 − 2η/3`, as sums over partitions. -/
lemma main_est (hm : 1 ≤ m) (hU : #U = 4 * m - 1) {η : ℝ} (hη : 0 ≤ η) (hnum : NumOK m η)
    (X Y : Finset α → Prop) :
    (∑ t ∈ parts m U, q0 m X t.2 * q0 m Y (zy U t)) / 45 - 2 * η / 3 * #(parts m U) ≤
      ∑ t ∈ parts m U, q1 m X t.1 t.2 * q1 m Y t.1 (zy U t) := by
  have h4 := claim4 hm hU hη hnum X Y
  have hp : ∀ t ∈ parts m U,
      q0 m X t.2 * q0 m Y (zy U t) / 9 -
        ((if bad m η X t.1 t.2 then 1 else 0) + (if bad m η Y t.1 (zy U t) then 1 else 0)) *
          (q0 m X t.2 * q0 m Y (zy U t)) / 9 - 2 * η / 3 ≤
      q1 m X t.1 t.2 * q1 m Y t.1 (zy U t) := by
    intro t ht
    have hz := card_zy hm hU ht
    rw [mem_parts] at ht
    apply pointwise _ _ _ _ η (q0_nonneg m _ _) (q0_le_one m hm _ _ ht.2.2.1) (q0_nonneg m _ _)
      (q0_le_one m hm _ _ hz) (q1_nonneg m _ _ _) (q1_nonneg m _ _ _) hη
    · split_ifs <;> simp
    · split_ifs <;> simp
    · intro h; split_ifs at h with hb
      · norm_num at h
      · unfold bad at hb; linarith
    · intro h; split_ifs at h with hb
      · norm_num at h
      · unfold bad at hb; linarith
  have := sum_le_sum hp
  rw [sum_sub_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_div, ← sum_div] at this
  nlinarith

end Partition

/-! ### Numerics -/

section Numerics
variable {m : ℕ}

lemma two_mul_cc (hm : 1 ≤ m) : 2 * (2 * m - 1).choose m = (2 * m).choose m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h1 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have h2 : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
  rw [h1, h2, Nat.choose_succ_succ (2 * j + 1) j, Nat.choose_symm_half]
  ring

lemma cc_ge (hm : 1 ≤ m) : (4 : ℝ) ^ m / (2 * (2 * m + 1)) ≤ cc m := by
  have h := Nat.four_pow_le_two_mul_add_one_mul_central_binom m
  rw [← two_mul_cc hm] at h
  unfold cc
  rw [div_le_iff₀ (by positivity)]
  have : ((4 ^ m : ℕ) : ℝ) ≤ ((2 * m + 1) * (2 * (2 * m - 1).choose m) : ℕ) := by exact_mod_cast h
  push_cast at this
  linarith

lemma gamma_pow (k : ℕ) :
    ((2 : ℝ) ^ (3 * k / 8) * (3 / 4) ^ k) ^ 80 ≤ (81 / 100) ^ (10 * k) := by
  rw [mul_pow, ← pow_mul, ← pow_mul]
  have h1 : (2 : ℝ) ^ (3 * k / 8 * 80) ≤ 2 ^ (30 * k) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc (2 : ℝ) ^ (3 * k / 8 * 80) * (3 / 4) ^ (k * 80)
      ≤ 2 ^ (30 * k) * (3 / 4) ^ (k * 80) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (2 ^ 3 * (3 / 4) ^ 8) ^ (10 * k) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; ring_nf
    _ ≤ (81 / 100) ^ (10 * k) := pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Eventually (in `m`) `2 (2m+1)^{80}·r^m ≤ 1` with `r = 2·(81/100)^4 < 1`. -/
lemma eventually_small : ∃ M : ℕ, ∀ m ≥ M,
    2 * (2 * (2 * (m : ℝ) + 1)) ^ 80 * (2 * (81 / 100) ^ 4) ^ m ≤ 1 := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one 80
    (r := 2 * (81 / 100) ^ 4) (by rw [abs_of_pos (by norm_num)]; norm_num)
  have hev := (ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (2 * 6 ^ 80) by positivity)))
  rw [Filter.eventually_atTop] at hev
  obtain ⟨M, hM⟩ := hev
  refine ⟨max M 1, fun m hm => ?_⟩
  have h1 := hM m (le_of_max_le_left hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast le_of_max_le_right hm
  have h2 : (2 * (2 * (m : ℝ) + 1)) ^ 80 ≤ 6 ^ 80 * (m : ℝ) ^ 80 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hr : (0 : ℝ) ≤ (2 * (81 / 100) ^ 4) ^ m := by positivity
  have h3 : (m : ℝ) ^ 80 * (2 * (81 / 100) ^ 4) ^ m * (2 * 6 ^ 80) ≤ 1 := by
    rw [lt_div_iff₀ (by positivity)] at h1; linarith
  nlinarith [mul_le_mul_of_nonneg_right h2 hr]

/-- The numerical hypothesis of Claim 3 holds for `η = 2^{-n/320}`, `n ≤ 4m+2`, `m` large. -/
lemma numOK_eventually : ∃ M : ℕ, 1 ≤ M ∧ ∀ m ≥ M, ∀ n : ℕ, n ≤ 4 * m + 2 →
    NumOK m ((2 : ℝ) ^ (-(1 / 320 * (n : ℝ)))) := by
  obtain ⟨M, hM⟩ := eventually_small
  refine ⟨max M 1, le_max_right _ _, fun m hm n hn k hk1 hk2 => ?_⟩
  have hm1 : 1 ≤ m := le_of_max_le_right hm
  have hsm := hM m (le_of_max_le_left hm)
  set η := (2 : ℝ) ^ (-(1 / 320 * (n : ℝ)))
  have hη : 0 < η := by positivity
  -- `η^80 ≥ (1/2)^{m+1}`
  have hη80 : (1 / 2 : ℝ) ^ (m + 1) ≤ η ^ 80 := by
    have : η ^ 80 = (2 : ℝ) ^ (-(1 / 320 * (n : ℝ)) * 80) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this, one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (n : ℝ) ≤ 4 * m + 2 := by exact_mod_cast hn
    push_cast; nlinarith
  set γ := (2 : ℝ) ^ (3 * k / 8) * (3 / 4) ^ k
  have hγ : 0 ≤ γ := by positivity
  -- `A := 2(2m+1)γ ≤ η`
  have hA : 2 * (2 * (m : ℝ) + 1) * γ ≤ η := by
    apply le_of_pow_le_pow_left₀ (n := 80) (by norm_num) hη.le
    rw [mul_pow]
    have h1 := gamma_pow k
    have h2 : ((81 : ℝ) / 100) ^ (10 * k) ≤ (81 / 100) ^ (4 * m) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : ((81 : ℝ) / 100) ^ (4 * m) * 2 ^ (m + 1) = 2 * (2 * (81 / 100) ^ 4) ^ m := by
      have gen : ∀ r : ℝ, r ^ m * 2 ^ (m + 1) = 2 * (2 * r) ^ m := by
        intro r; rw [mul_pow, pow_succ]; ring
      rw [pow_mul (81 / 100 : ℝ) 4 m]
      exact gen _
    have h4 : (1 / 2 : ℝ) ^ (m + 1) * 2 ^ (m + 1) = 1 := by rw [← mul_pow]; norm_num
    have hP : (0 : ℝ) ≤ (2 * (2 * (m : ℝ) + 1)) ^ 80 := by positivity
    have h5 : (2 * (2 * (m : ℝ) + 1)) ^ 80 * γ ^ 80 ≤
        (2 * (2 * (m : ℝ) + 1)) ^ 80 * (81 / 100) ^ (4 * m) :=
      mul_le_mul_of_nonneg_left (h1.trans h2) hP
    have h6 : (2 * (2 * (m : ℝ) + 1)) ^ 80 * (81 / 100) ^ (4 * m) ≤ (1 / 2) ^ (m + 1) := by
      have hpos : (0 : ℝ) < 2 ^ (m + 1) := by positivity
      rw [← mul_le_mul_iff_of_pos_right hpos, h4, mul_assoc, h3]
      linarith
    linarith
  -- conclude
  have hc := cc_ge hm1
  have e : (2 : ℝ) ^ (2 * m - k) * (2 ^ (3 * k / 8) * (3 / 2) ^ k) = 4 ^ m * γ := by
    have : (2 : ℝ) ^ (2 * m - k) * 2 ^ k = 4 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hk1, pow_mul]; norm_num
    have h32 : (3 / 2 : ℝ) ^ k = 2 ^ k * (3 / 4) ^ k := by rw [← mul_pow]; norm_num
    rw [h32, ← this]; ring
  rw [e]
  have hq : (0 : ℝ) < 2 * (2 * m + 1) := by positivity
  calc (4 : ℝ) ^ m * γ = (4 ^ m / (2 * (2 * m + 1))) * (2 * (2 * m + 1) * γ) := by
        field_simp
    _ ≤ (4 ^ m / (2 * (2 * m + 1))) * η :=
        mul_le_mul_of_nonneg_left hA (by positivity)
    _ ≤ cc m * η := mul_le_mul_of_nonneg_right hc hη.le
    _ = η * cc m := mul_comm _ _

end Numerics

/-! ### The distribution `μ` on pairs of bit strings -/

section Measure
open Classical ExtensionComplexity.TSP
variable {n : ℕ}

/-- The characteristic bit string of a subset of `[n]`. -/
def toBits (s : Finset (Fin n)) : Fin n → Bool := fun j => decide (j ∈ s)

lemma toBits_inj : Function.Injective (toBits (n := n)) := by
  intro s t h; ext j; have := congrFun h j; simpa [toBits] using this

lemma bitDot_toBits (x y : Finset (Fin n)) : bitDot (toBits x) (toBits y) = #(x ∩ y) := by
  unfold bitDot toBits; congr 1; ext j; simp

variable (m : ℕ) (U : Finset (Fin n))

/-- Support of `(x₀, y₀)` given the partition `t`. -/
noncomputable def P0 (t : Fin n × Finset (Fin n)) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (powersetCard m t.2 ×ˢ powersetCard m (zy U t)).image (fun q => (toBits q.1, toBits q.2))

/-- Support of `(x₁, y₁)` given the partition `t`. -/
noncomputable def P1 (t : Fin n × Finset (Fin n)) : Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (powersetCard (m - 1) t.2 ×ˢ powersetCard (m - 1) (zy U t)).image
    (fun q => (toBits (insert t.1 q.1), toBits (insert t.1 q.2)))

/-- Razborov's distribution: average over partitions of `3/4·(x₀,y₀) + 1/4·(x₁,y₁)`. -/
noncomputable def mu (p : (Fin n → Bool) × (Fin n → Bool)) : ℝ :=
  (∑ t ∈ parts m U, (3 / 4 * (if p ∈ P0 m U t then 1 else 0) +
      1 / 4 * (if p ∈ P1 m U t then 1 else 0))) / (#(parts m U) * cc m ^ 2)

lemma sum_mu (F : (Fin n → Bool) × (Fin n → Bool) → Prop) [DecidablePred F] :
    ∑ p ∈ univ.filter F, mu m U p =
      (∑ t ∈ parts m U, (3 / 4 * (#((P0 m U t).filter F) : ℝ) +
        1 / 4 * #((P1 m U t).filter F))) / (#(parts m U) * cc m ^ 2) := by
  unfold mu
  rw [← sum_div, sum_comm]
  congr 1
  apply sum_congr rfl
  intro t _
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_boole, sum_boole]
  congr 4
  · ext p; simp only [mem_filter, mem_univ, true_and]; tauto
  · ext p; simp only [mem_filter, mem_univ, true_and]; tauto

variable {m U}

lemma disj_of_mem {t : Fin n × Finset (Fin n)} (ht : t ∈ parts m U) {x y : Finset (Fin n)}
    (hx : x ⊆ t.2) (hy : y ⊆ zy U t) : x ∩ y = ∅ ∧ t.1 ∉ x ∧ t.1 ∉ y := by
  rw [mem_parts] at ht
  refine ⟨?_, fun h => ht.2.2.2 (hx h), fun h => ?_⟩
  · ext a
    simp only [mem_inter, notMem_empty, iff_false, not_and]
    intro ha hb
    have := hy hb
    simp only [zy, mem_sdiff, mem_insert] at this
    exact this.2 (Or.inr (hx ha))
  · have := hy h
    simp [zy] at this

lemma card_P0_filter {t : Fin n × Finset (Fin n)} (ht : t ∈ parts m U) (G : ℕ → Prop)
    [DecidablePred G] (R₁ R₂ : Set (Fin n → Bool)) :
    #((P0 m U t).filter (fun p => G (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂)) =
      if G 0 then cnt0 m (fun x => toBits x ∈ R₁) t.2 * cnt0 m (fun y => toBits y ∈ R₂) (zy U t)
      else 0 := by
  unfold P0
  rw [filter_image, card_image_of_injOn]
  · split_ifs with hG
    · unfold cnt0
      rw [← card_product]
      congr 1
      ext q
      simp only [mem_filter, mem_product, mem_powersetCard, bitDot_toBits]
      constructor
      · rintro ⟨⟨h1, h2⟩, _, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
      · rintro ⟨⟨h1, h3⟩, h2, h4⟩
        refine ⟨⟨h1, h2⟩, ?_, h3, h4⟩
        rw [(disj_of_mem ht h1.1 h2.1).1, card_empty]; exact hG
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro q hq
      simp only [mem_product, mem_powersetCard] at hq
      rw [bitDot_toBits, (disj_of_mem ht hq.1.1 hq.2.1).1, card_empty]
      tauto
  · intro a _ b _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (toBits_inj h.1) (toBits_inj h.2)

lemma card_P1_filter {t : Fin n × Finset (Fin n)} (ht : t ∈ parts m U) (G : ℕ → Prop)
    [DecidablePred G] (R₁ R₂ : Set (Fin n → Bool)) :
    #((P1 m U t).filter (fun p => G (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂)) =
      if G 1 then cnt1 m (fun x => toBits x ∈ R₁) t.1 t.2 *
        cnt1 m (fun y => toBits y ∈ R₂) t.1 (zy U t) else 0 := by
  have hdot : ∀ q ∈ powersetCard (m - 1) t.2 ×ˢ powersetCard (m - 1) (zy U t),
      #(insert t.1 q.1 ∩ insert t.1 q.2) = 1 := by
    intro q hq
    simp only [mem_product, mem_powersetCard] at hq
    obtain ⟨hd, -, -⟩ := disj_of_mem ht hq.1.1 hq.2.1
    rw [← insert_inter_distrib, hd, card_insert_of_notMem (notMem_empty _), card_empty]
  unfold P1
  rw [filter_image, card_image_of_injOn]
  · split_ifs with hG
    · unfold cnt1
      rw [← card_product]
      congr 1
      ext q
      simp only [mem_filter, mem_product, bitDot_toBits]
      constructor
      · rintro ⟨⟨h1, h2⟩, _, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
      · rintro ⟨⟨h1, h3⟩, h2, h4⟩
        refine ⟨⟨h1, h2⟩, ?_, h3, h4⟩
        rw [hdot q (mem_product.2 ⟨h1, h2⟩)]; exact hG
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro q hq
      rw [bitDot_toBits, hdot q hq]
      tauto
  · intro a ha b hb h
    simp only [Prod.mk.injEq] at h
    rw [mem_coe, mem_filter, mem_product, mem_powersetCard, mem_powersetCard] at ha hb
    have e1 := toBits_inj h.1
    have e2 := toBits_inj h.2
    have i1 := (disj_of_mem ht ha.1.1.1 ha.1.2.1).2
    have i2 := (disj_of_mem ht hb.1.1.1 hb.1.2.1).2
    refine Prod.ext ?_ ?_
    · rw [← erase_insert i1.1, e1, erase_insert i2.1]
    · rw [← erase_insert i1.2, e2, erase_insert i2.2]

end Measure

/-! ### Assembly -/

section Final
open Classical ExtensionComplexity.TSP

lemma sum_mu_G {n m : ℕ} {U : Finset (Fin n)} (G : ℕ → Prop) [DecidablePred G]
    (R₁ R₂ : Set (Fin n → Bool)) :
    ∑ p ∈ univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) =>
        G (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂), mu m U p =
      (∑ t ∈ parts m U,
        (3 / 4 * (((if G 0 then cnt0 m (fun x => toBits x ∈ R₁) t.2 *
            cnt0 m (fun y => toBits y ∈ R₂) (zy U t) else 0 : ℕ)) : ℝ) +
          1 / 4 * (((if G 1 then cnt1 m (fun x => toBits x ∈ R₁) t.1 t.2 *
            cnt1 m (fun y => toBits y ∈ R₂) t.1 (zy U t) else 0 : ℕ)) : ℝ))) /
        (#(parts m U) * cc m ^ 2) := by
  rw [sum_mu]
  congr 1
  apply sum_congr rfl
  intro t ht
  rw [card_P0_filter ht, card_P1_filter ht]

lemma sum_mu_S {n m : ℕ} {U : Finset (Fin n)} (G : ℕ → Prop) [DecidablePred G]
    (R₁ R₂ : Set (Fin n → Bool)) (S : Finset ((Fin n → Bool) × (Fin n → Bool)))
    (hS : ∀ p, p ∈ S ↔ G (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂) :
    ∑ p ∈ S, mu m U p =
      (∑ t ∈ parts m U,
        (3 / 4 * (((if G 0 then cnt0 m (fun x => toBits x ∈ R₁) t.2 *
            cnt0 m (fun y => toBits y ∈ R₂) (zy U t) else 0 : ℕ)) : ℝ) +
          1 / 4 * (((if G 1 then cnt1 m (fun x => toBits x ∈ R₁) t.1 t.2 *
            cnt1 m (fun y => toBits y ∈ R₂) t.1 (zy U t) else 0 : ℕ)) : ℝ))) /
        (#(parts m U) * cc m ^ 2) := by
  have : S = univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) =>
      G (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂) := by
    ext p; simp [hS]
  rw [this]; exact sum_mu_G G R₁ R₂

theorem razborov :
    ∃ α δ : ℝ, 0 < α ∧ 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ (A B : Finset ((Fin n → Bool) × (Fin n → Bool))) (μ : (Fin n → Bool) × (Fin n → Bool) → ℝ),
        (∀ p, 0 ≤ μ p) ∧ (∑ p, μ p) = 1 ∧
        (∀ p ∈ A, bitDot p.1 p.2 = 0) ∧ (∀ p ∈ B, bitDot p.1 p.2 = 1) ∧
        (∑ p ∈ A, μ p) = 3 / 4 ∧
        ∀ R₁ R₂ : Set (Fin n → Bool),
          α * (∑ p ∈ A.filter (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂), μ p)
              - (2 : ℝ) ^ (-(δ * n)) ≤
            ∑ p ∈ B.filter (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂), μ p := by
  obtain ⟨M, hM1, hM⟩ := numOK_eventually
  refine ⟨1 / 135, 1 / 320, by norm_num, by norm_num, 4 * M + 3, fun n hn => ?_⟩
  obtain ⟨m, hmdef⟩ : ∃ m, m = (n + 1) / 4 := ⟨_, rfl⟩
  have hmM : M ≤ m := by omega
  have hm : 1 ≤ m := by omega
  have hL : 4 * m - 1 ≤ n := by omega
  have hn4 : n ≤ 4 * m + 2 := by omega
  set U : Finset (Fin n) := (univ : Finset (Fin (4 * m - 1))).map (Fin.castLEEmb hL) with hUdef
  have hU : #U = 4 * m - 1 := by simp [U]
  have hnum := hM m hmM n hn4
  set η : ℝ := (2 : ℝ) ^ (-(1 / 320 * (n : ℝ))) with hηdef
  have hη : 0 ≤ η := by positivity
  have hc := cc_pos m hm
  have hT : 0 < #(parts m U) := by
    obtain ⟨i, hi⟩ : U.Nonempty := by rw [← card_pos, hU]; omega
    obtain ⟨Z, hZ, hZc⟩ := exists_subset_card_eq (s := U.erase i) (n := 2 * m - 1)
      (by rw [card_erase_of_mem hi, hU]; omega)
    apply card_pos.2 ⟨(i, Z), ?_⟩
    rw [mem_parts]
    exact ⟨hi, hZ.trans (erase_subset _ _), hZc, fun h => (notMem_erase i U) (hZ h)⟩
  have hTr : (0 : ℝ) < #(parts m U) := by exact_mod_cast hT
  -- full counts
  have hfull0 : ∀ Z : Finset (Fin n), #Z = 2 * m - 1 →
      cnt0 m (fun x => toBits x ∈ (Set.univ : Set (Fin n → Bool))) Z = (2 * m - 1).choose m := by
    intro Z hZ
    simp only [cnt0, Set.mem_univ]
    rw [filter_true_of_mem (fun _ _ => trivial), card_powersetCard, hZ]
  have hfull1 : ∀ (i : Fin n) (Z : Finset (Fin n)), #Z = 2 * m - 1 →
      cnt1 m (fun x => toBits x ∈ (Set.univ : Set (Fin n → Bool))) i Z = (2 * m - 1).choose m := by
    intro i Z hZ
    simp only [cnt1, Set.mem_univ]
    rw [filter_true_of_mem (fun _ _ => trivial), card_powersetCard, hZ, ← Nat.choose_symm (by omega)]
    congr 1; omega
  have hcc : cc m = ((2 * m - 1).choose m : ℝ) := rfl
  refine ⟨univ.filter (fun p => bitDot p.1 p.2 = 0), univ.filter (fun p => bitDot p.1 p.2 = 1),
    mu m U, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p; unfold mu; apply div_nonneg _ (by positivity)
    apply sum_nonneg; intro t _; split_ifs <;> norm_num
  · rw [sum_mu_S (fun _ : ℕ => True) Set.univ Set.univ univ (by simp)]
    rw [div_eq_one_iff_eq (by positivity)]
    rw [sum_congr rfl (g := fun _ => cc m ^ 2)]
    · rw [sum_const, nsmul_eq_mul]
    · intro t ht
      have hz := card_zy hm hU ht
      rw [mem_parts] at ht
      simp only [if_true]
      rw [hfull0 _ ht.2.2.1, hfull0 _ hz, hfull1 _ _ ht.2.2.1, hfull1 _ _ hz, hcc]
      push_cast; ring
  · intro p hp; simpa using hp
  · intro p hp; simpa using hp
  · rw [sum_mu_S (fun k : ℕ => k = 0) Set.univ Set.univ _ (by simp)]
    rw [sum_congr rfl (g := fun _ => 3 / 4 * cc m ^ 2)]
    · rw [sum_const, nsmul_eq_mul]; field_simp
    · intro t ht
      have hz := card_zy hm hU ht
      rw [mem_parts] at ht
      simp only [if_true, show ¬ ((1 : ℕ) = 0) from one_ne_zero, if_false]
      rw [hfull0 _ ht.2.2.1, hfull0 _ hz, hcc]
      push_cast; ring
  · intro R₁ R₂
    have eA : (univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) => bitDot p.1 p.2 = 0)).filter
        (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂) =
        univ.filter (fun p => (fun k : ℕ => k = 0) (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂) := by
      ext; simp
    have eB : (univ.filter (fun p : (Fin n → Bool) × (Fin n → Bool) => bitDot p.1 p.2 = 1)).filter
        (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂) =
        univ.filter (fun p => (fun k : ℕ => k = 1) (bitDot p.1 p.2) ∧ p.1 ∈ R₁ ∧ p.2 ∈ R₂) := by
      ext; simp
    rw [sum_mu_S (fun k : ℕ => k = 0) R₁ R₂ _ (by simp), sum_mu_S (fun k : ℕ => k = 1) R₁ R₂ _ (by simp)]
    simp only [if_true, show ¬ ((1 : ℕ) = 0) from one_ne_zero, if_false,
      show ¬ ((0 : ℕ) = 1) from zero_ne_one, Nat.cast_zero, mul_zero, add_zero, zero_add,
      Nat.cast_mul]
    set X : Finset (Fin n) → Prop := fun x => toBits x ∈ R₁
    set Y : Finset (Fin n) → Prop := fun y => toBits y ∈ R₂
    have hmain := main_est hm hU hη hnum X Y
    have e0 : ∑ t ∈ parts m U, q0 m X t.2 * q0 m Y (zy U t) =
        (∑ t ∈ parts m U, ((cnt0 m X t.2 : ℝ) * cnt0 m Y (zy U t))) / cc m ^ 2 := by
      rw [sum_div]; apply sum_congr rfl; intro t _; unfold q0; field_simp
    have e1 : ∑ t ∈ parts m U, q1 m X t.1 t.2 * q1 m Y t.1 (zy U t) =
        (∑ t ∈ parts m U, ((cnt1 m X t.1 t.2 : ℝ) * cnt1 m Y t.1 (zy U t))) / cc m ^ 2 := by
      rw [sum_div]; apply sum_congr rfl; intro t _; unfold q1; field_simp
    rw [e0, e1] at hmain
    rw [← mul_sum, ← mul_sum]
    set S0 := ∑ t ∈ parts m U, ((cnt0 m X t.2 : ℝ) * cnt0 m Y (zy U t))
    set S1 := ∑ t ∈ parts m U, ((cnt1 m X t.1 t.2 : ℝ) * cnt1 m Y t.1 (zy U t))
    set D := (#(parts m U) : ℝ) * cc m ^ 2
    have hD : 0 < D := by positivity
    have hc2 : 0 < cc m ^ 2 := by positivity
    -- divide the main estimate by `|T|`
    have hmain' : S0 / D / 45 - 2 * η / 3 ≤ S1 / D := by
      have : S0 / D = S0 / cc m ^ 2 / #(parts m U) := by
        rw [div_div, mul_comm]
      have : S1 / D = S1 / cc m ^ 2 / #(parts m U) := by
        rw [div_div, mul_comm]
      rw [‹S0 / D = _›, this]
      have e : S0 / cc m ^ 2 / #(parts m U) / 45 - 2 * η / 3 =
          (S0 / cc m ^ 2 / 45 - 2 * η / 3 * #(parts m U)) / #(parts m U) := by
        field_simp
      rw [e]
      exact div_le_div_of_nonneg_right hmain hTr.le
    have q1 : 3 / 4 * S0 / D = 3 / 4 * (S0 / D) := by ring
    have q2 : 1 / 4 * S1 / D = 1 / 4 * (S1 / D) := by ring
    rw [q1, q2]
    nlinarith

end Final

end XCR

open Matrix ExtensionComplexity.TSP

open Classical

theorem solution :
    ∃ α δ : ℝ, 0 < α ∧ 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ (A B : Finset ((Fin n → Bool) × (Fin n → Bool))) (μ : (Fin n → Bool) × (Fin n → Bool) → ℝ),
        (∀ p, 0 ≤ μ p) ∧ (∑ p, μ p) = 1 ∧
        (∀ p ∈ A, bitDot p.1 p.2 = 0) ∧ (∀ p ∈ B, bitDot p.1 p.2 = 1) ∧
        (∑ p ∈ A, μ p) = 3 / 4 ∧
        ∀ R₁ R₂ : Set (Fin n → Bool),
          α * (∑ p ∈ A.filter (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂), μ p)
              - (2 : ℝ) ^ (-(δ * n)) ≤
            ∑ p ∈ B.filter (fun p => p.1 ∈ R₁ ∧ p.2 ∈ R₂), μ p :=
  XCR.razborov
