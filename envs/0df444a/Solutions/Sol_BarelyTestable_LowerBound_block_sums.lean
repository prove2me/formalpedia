-- Prove2me | solution 1 for BarelyTestable.LowerBound.block_sums
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:39:12.171186+00:00
-- url     : https://prove2.me/submissions/b6d7889f-4997-49fe-8a56-2a365954ed78

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Loads

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_block

open Finset

lemma xorSet_singleton {ι : Type} [DecidableEq ι] (Y : Finset ι) (a : ι) :
    xorSet Y {a} = if a ∈ Y then Y.erase a else insert a Y := by
  ext x; unfold xorSet; split_ifs with h <;> simp <;> by_cases hx : x = a <;> simp_all

lemma xorSet_invol {ι : Type} [DecidableEq ι] (Y : Finset ι) (a : ι) :
    xorSet (xorSet Y {a}) {a} = Y := by
  ext x; unfold xorSet; by_cases hx : x = a <;> simp_all

lemma union_single_iff {ι : Type} [DecidableEq ι] (X U : Finset ι) (a : ι) :
    X ∪ {a} = U ↔ a ∈ U ∧ (X = U ∨ X = U.erase a) := by
  constructor
  · rintro rfl
    refine ⟨by simp, ?_⟩
    by_cases ha : a ∈ X
    · left; ext x; by_cases hx : x = a <;> simp_all
    · right; ext x; by_cases hx : x = a <;> simp_all
  · rintro ⟨ha, rfl | rfl⟩
    · ext x; by_cases hx : x = a <;> simp_all
    · ext x; by_cases hx : x = a <;> simp_all

lemma sdiff_single_iff {ι : Type} [DecidableEq ι] (X U : Finset ι) (a : ι) :
    X \ {a} = U ↔ a ∉ U ∧ (X = U ∨ X = insert a U) := by
  constructor
  · rintro rfl
    refine ⟨by simp, ?_⟩
    by_cases ha : a ∈ X
    · right; ext x; by_cases hx : x = a <;> simp_all
    · left; ext x; by_cases hx : x = a <;> simp_all
  · rintro ⟨ha, rfl | rfl⟩
    · ext x; by_cases hx : x = a <;> simp_all
    · ext x; by_cases hx : x = a <;> simp_all

lemma xor_union_iff {ι : Type} [DecidableEq ι] (X U : Finset ι) (a b : ι) :
    xorSet X {a} ∪ {b} = U ↔ b ∈ U ∧ (X = xorSet (U.erase b) {a} ∨ X = xorSet U {a}) := by
  rw [union_single_iff]
  have key : ∀ W : Finset ι, xorSet X {a} = W ↔ X = xorSet W {a} := by
    intro W; constructor
    · rintro rfl; rw [xorSet_invol]
    · rintro rfl; rw [xorSet_invol]
  rw [key, key]; tauto

lemma pick {ι : Type} (X Y1 Y2 : Finset ι) (π s : Bool) (c R : Prop)
    (hR : R ↔ c ∧ (X = Y1 ∨ X = Y2))
    (h1 : c → decide (Y1.card % 2 = 1) = s) (h2 : c → decide (Y2.card % 2 = 1) = !s) :
    (decide (X.card % 2 = 1) = π ∧ R) ↔ c ∧ X = if s = π then Y1 else Y2 := by
  rw [hR]
  constructor
  · rintro ⟨hp, hc, rfl | rfl⟩
    · refine ⟨hc, ?_⟩; rw [h1 hc] at hp; simp [hp]
    · refine ⟨hc, ?_⟩; rw [h2 hc] at hp; subst hp; cases s <;> simp
  · rintro ⟨hc, rfl⟩
    split_ifs with h
    · exact ⟨by rw [h1 hc, h], hc, Or.inl rfl⟩
    · refine ⟨?_, hc, Or.inr rfl⟩; rw [h2 hc]; cases s <;> cases π <;> simp_all


lemma reform {m : ℕ} (j : Fin 3) (π : Bool) (U : Cube (Fin m)) (c : Fin m × Fin m → Prop)
    [DecidablePred c] (sel : Fin m × Fin m → Cube (Fin m))
    (h : ∀ X p, (decide (X.card % 2 = 1) = π ∧ result j X {p.1} {p.2} = U) ↔ (c p ∧ X = sel p)) :
    blockS j π U = ∑ p : Fin m × Fin m, (if c p then 1 else 0) ∧
    blockT j π U = ∑ p : Fin m × Fin m, ∑ q : Fin m × Fin m,
      (if c p ∧ c q ∧ sel p = sel q then 1 else 0) := by
  classical
  constructor
  · unfold blockS blockGamma
    have : ∀ X : Cube (Fin m), (if decide (X.card % 2 = 1) = π then
        (Finset.univ.filter (fun p : Fin m × Fin m => result j X {p.1} {p.2} = U)).card else 0)
        = ∑ p : Fin m × Fin m, if c p ∧ X = sel p then 1 else 0 := by
      intro X
      rw [Finset.card_filter]
      split_ifs with hp
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        exact if_congr (by rw [← h]; simp [hp]) rfl rfl
      · refine (Finset.sum_eq_zero (fun p _ => ?_)).symm
        rw [if_neg]; rw [← h]; simp [hp]
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hc : c p <;> simp [hc]
  · unfold blockT blockGamma
    have : ∀ X : Cube (Fin m), (if decide (X.card % 2 = 1) = π then
        (Finset.univ.filter (fun p : Fin m × Fin m => result j X {p.1} {p.2} = U)).card ^ 2 else 0)
        = ∑ p : Fin m × Fin m, ∑ q : Fin m × Fin m,
          if (c p ∧ X = sel p) ∧ (c q ∧ X = sel q) then 1 else 0 := by
      intro X
      rw [Finset.card_filter, sq, Finset.sum_mul_sum]
      split_ifs with hp
      · refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        rw [ite_zero_mul_ite_zero, one_mul]
        exact if_congr (by rw [← h, ← h]; simp [hp]) rfl rfl
      · refine (Finset.sum_eq_zero (fun p _ => Finset.sum_eq_zero (fun q _ => ?_))).symm
        rw [if_neg]; rw [← h]; simp [hp]
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    by_cases hc : c p ∧ c q ∧ sel p = sel q
    · obtain ⟨h1, h2, h3⟩ := hc
      simp [h1, h2, h3]
    · rw [if_neg hc]
      refine Finset.sum_eq_zero (fun X _ => ?_)
      rw [if_neg]; rintro ⟨⟨h1, rfl⟩, h2, h3⟩; exact hc ⟨h1, h2, h3⟩


lemma reform2 {m : ℕ} (j : Fin 3) (π : Bool) (U : Cube (Fin m)) (c : Fin m → Fin m → Prop)
    [∀ a b, Decidable (c a b)] (sel : Fin m → Fin m → Cube (Fin m))
    (h : ∀ X a b, (decide (X.card % 2 = 1) = π ∧ result j X {a} {b} = U) ↔ (c a b ∧ X = sel a b)) :
    blockS j π U = ∑ a : Fin m, ∑ b : Fin m, (if c a b then 1 else 0) ∧
    blockT j π U = ∑ a : Fin m, ∑ b : Fin m, ∑ a' : Fin m, ∑ b' : Fin m,
      (if c a b ∧ c a' b' ∧ sel a b = sel a' b' then 1 else 0) := by
  obtain ⟨h1, h2⟩ := reform j π U (fun p => c p.1 p.2) (fun p => sel p.1 p.2) (fun X p => h X p.1 p.2)
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · rw [Fintype.sum_prod_type]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [Fintype.sum_prod_type]

lemma par_flip {k n : ℕ} (h : k + 1 = n ∨ n + 1 = k) :
    decide (k % 2 = 1) = !decide (n % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h' | h' <;> simp [h'] <;> omega

lemma par_same {k n : ℕ} (h : k + 2 = n ∨ k = n) :
    decide (k % 2 = 1) = decide (n % 2 = 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h' | h' <;> simp [h'] <;> omega

lemma card_xor_single {ι : Type} [DecidableEq ι] (Y : Finset ι) (a : ι) :
    (xorSet Y {a}).card + 1 = Y.card ∨ Y.card + 1 = (xorSet Y {a}).card := by
  rw [xorSet_singleton]
  split_ifs with h
  · left; rw [card_erase_of_mem h]; have := card_pos.mpr ⟨a, h⟩; omega
  · right; rw [card_insert_of_notMem h]

lemma mem_xor_single {ι : Type} [DecidableEq ι] (Y : Finset ι) (a x : ι) :
    x ∈ xorSet Y {a} ↔ (x ∈ Y ∧ x ≠ a) ∨ (x = a ∧ a ∉ Y) := by
  unfold xorSet; by_cases hx : x = a <;> simp_all

lemma xor_erase_eq_iff {ι : Type} [DecidableEq ι] (U : Finset ι) (a b a' b' : ι)
    (hb : b ∈ U) (hb' : b' ∈ U) :
    xorSet (U.erase b) {a} = xorSet (U.erase b') {a'} ↔
      (a = a' ∧ b = b') ∨ (a = b ∧ a' = b' ∧ b ≠ b') ∨ (a = b' ∧ a' = b ∧ b ≠ b') := by
  constructor
  · intro h
    have hm : ∀ x, x ∈ xorSet (U.erase b) {a} ↔ x ∈ xorSet (U.erase b') {a'} := by
      intro x; rw [h]
    have h1 := hm a
    have h2 := hm a'
    have h3 := hm b
    have h4 := hm b'
    simp only [mem_xor_single, mem_erase] at h1 h2 h3 h4
    by_cases e1 : a = a' <;> by_cases e2 : b = b' <;> by_cases e3 : a = b <;> by_cases e4 : a' = b' <;>
      by_cases e5 : a = b' <;> by_cases e6 : a' = b <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl, hne⟩ | ⟨rfl, rfl, hne⟩)
    · rfl
    · ext x; simp only [mem_xor_single, mem_erase]; by_cases hx : x = a <;> by_cases hx' : x = a' <;> simp_all
    · ext x; simp only [mem_xor_single, mem_erase]; by_cases hx : x = a <;> by_cases hx' : x = a' <;> simp_all

lemma erase_cond {ι : Type} [DecidableEq ι] (U : Finset ι) (a a' : ι) :
    (a ∈ U ∧ a' ∈ U ∧ U.erase a = U.erase a') ↔ (a ∈ U ∧ a' = a) := by
  constructor
  · rintro ⟨ha, ha', h⟩
    refine ⟨ha, ?_⟩
    by_contra hne
    have : a ∈ U.erase a' := mem_erase.mpr ⟨fun e => hne e.symm, ha⟩
    rw [← h] at this; simp at this
  · rintro ⟨ha, rfl⟩; exact ⟨ha, ha, rfl⟩

lemma insert_cond {ι : Type} [DecidableEq ι] (U : Finset ι) (a a' : ι) :
    (a ∉ U ∧ a' ∉ U ∧ insert a U = insert a' U) ↔ (a ∉ U ∧ a' = a) := by
  constructor
  · rintro ⟨ha, ha', h⟩
    refine ⟨ha, ?_⟩
    have : a ∈ insert a' U := by rw [← h]; exact mem_insert_self a U
    rcases mem_insert.mp this with e | e
    · exact e.symm
    · exact absurd e ha
  · rintro ⟨ha, rfl⟩; exact ⟨ha, ha, rfl⟩

lemma xor_cond {ι : Type} [DecidableEq ι] (U : Finset ι) (a b a' b' : ι) :
    (b ∈ U ∧ b' ∈ U ∧ xorSet U {a} = xorSet U {a'}) ↔ (b ∈ U ∧ b' ∈ U ∧ a' = a) := by
  constructor
  · rintro ⟨hb, hb', h⟩
    refine ⟨hb, hb', ?_⟩
    by_contra hne
    have h1 : a ∈ xorSet U {a} ↔ a ∈ xorSet U {a'} := by rw [h]
    simp only [mem_xor_single] at h1
    by_cases ha : a ∈ U <;> simp_all [eq_comm]
  · rintro ⟨hb, hb', rfl⟩; exact ⟨hb, hb', rfl⟩

lemma sum_mem_const {m : ℕ} (U : Finset (Fin m)) (c : ℕ) :
    ∑ a : Fin m, (if a ∈ U then c else 0) = U.card * c := by
  rw [Finset.sum_ite_mem, univ_inter, sum_const, smul_eq_mul]

lemma sum_nmem_const {m : ℕ} (U : Finset (Fin m)) (c : ℕ) :
    ∑ a : Fin m, (if a ∉ U then c else 0) = (m - U.card) * c := by
  simp_rw [← Finset.mem_compl]
  rw [Finset.sum_ite_mem, univ_inter, sum_const, smul_eq_mul, card_compl, Fintype.card_fin]

lemma offdiag_count {m : ℕ} (U : Finset (Fin m)) :
    (∑ x : Fin m, if x ∈ U then ∑ y : Fin m, (if y ∈ U then (if x ≠ y then 1 else 0) else 0) else 0)
      = U.card * (U.card - 1) := by
  have inner : ∀ x ∈ U, (∑ y : Fin m, (if y ∈ U then (if x ≠ y then 1 else 0) else 0)) = U.card - 1 := by
    intro x hx
    rw [Finset.sum_ite_mem, univ_inter, Finset.sum_boole, Finset.filter_ne, card_erase_of_mem hx]
    simp
  rw [Finset.sum_ite_mem, univ_inter, Finset.sum_congr rfl inner, sum_const, smul_eq_mul]

lemma split3 {ι : Type} [DecidableEq ι] (U : Finset ι) (a b a' b' : ι) :
    (if b ∈ U ∧ b' ∈ U ∧ xorSet (U.erase b) {a} = xorSet (U.erase b') {a'} then 1 else 0) =
      (if b ∈ U ∧ a' = a ∧ b' = b then 1 else 0) +
      (if a = b ∧ b ∈ U ∧ a' = b' ∧ b' ∈ U ∧ a ≠ a' then 1 else 0) +
      (if a ∈ U ∧ b ∈ U ∧ a' = b ∧ b' = a ∧ a ≠ b then 1 else 0) := by
  by_cases hb : b ∈ U
  · by_cases hb' : b' ∈ U
    · rw [if_congr (and_congr_right (fun _ => and_congr_right (fun _ =>
        xor_erase_eq_iff U a b a' b' hb hb'))) rfl rfl]
      split_ifs <;> grind
    · split_ifs <;> grind
  · split_ifs <;> grind

theorem block_id {m : ℕ} (hm : 1 ≤ m) (π : Bool) (U : Cube (Fin m)) :
    let w := U.card
    let same := decide (w % 2 = 1) = π
    blockS 0 π U = m * w ∧
    blockT 0 π U = (if same then m^2 * w^2 else m^2 * w) ∧
    blockS 1 π U = m * (m - w) ∧
    blockT 1 π U = (if same then m^2 * (m-w)^2 else m^2 * (m-w)) ∧
    blockS 2 π U = m * w ∧
    blockT 2 π U = (if same then w * (m + 2*w - 2) else m * w^2) := by
  dsimp only
  obtain ⟨hS0, hT0⟩ := reform2 0 π U (fun a _ => a ∈ U)
    (fun a _ => if decide (U.card % 2 = 1) = π then U else U.erase a) (fun X a b => by
      have hr : result 0 X {a} {b} = X ∪ {a} := rfl
      rw [hr]
      exact pick X U (U.erase a) π (decide (U.card % 2 = 1)) (a ∈ U) _ (union_single_iff X U a)
        (fun _ => rfl) (fun ha => par_flip (Or.inl (by
          rw [card_erase_of_mem ha]; have := card_pos.mpr ⟨a, ha⟩; omega))))
  obtain ⟨hS1, hT1⟩ := reform2 1 π U (fun a _ => a ∉ U)
    (fun a _ => if decide (U.card % 2 = 1) = π then U else insert a U) (fun X a b => by
      have hr : result 1 X {a} {b} = X \ {a} := rfl
      rw [hr]
      exact pick X U (insert a U) π (decide (U.card % 2 = 1)) (a ∉ U) _ (sdiff_single_iff X U a)
        (fun _ => rfl) (fun ha => par_flip (Or.inr (by rw [card_insert_of_notMem ha]))))
  obtain ⟨hS2, hT2⟩ := reform2 2 π U (fun _ b => b ∈ U)
    (fun a b => if decide (U.card % 2 = 1) = π then xorSet (U.erase b) {a} else xorSet U {a})
    (fun X a b => by
      have hr : result 2 X {a} {b} = xorSet X {a} ∪ {b} := rfl
      rw [hr]
      refine pick X _ _ π (decide (U.card % 2 = 1)) (b ∈ U) _ (xor_union_iff X U a b) ?_ ?_
      · intro hb
        apply par_same
        have h1 := card_erase_of_mem hb
        have h2 := card_pos.mpr ⟨b, hb⟩
        rcases card_xor_single (U.erase b) a with h | h
        · left; omega
        · right; omega
      · intro _
        rw [par_flip (card_xor_single U a)])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS0]
    simp only [ite_and, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_mem_const,
      ← Finset.mul_sum]
    ring
  · rw [hT0]
    split_ifs with hs
    · simp only [hs, if_true, and_true, ite_and, Finset.sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, sum_mem_const, ← Finset.mul_sum, Finset.sum_ite_irrel, mul_ite, mul_one, mul_zero]
      ring
    · simp only [hs, if_false, erase_cond, ite_and, Finset.sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, sum_mem_const, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, Finset.sum_ite_irrel, mul_ite, mul_one, mul_zero]
      ring
  · rw [hS1]
    simp only [ite_and, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_nmem_const,
      ← Finset.mul_sum]
    ring
  · rw [hT1]
    split_ifs with hs
    · simp only [hs, if_true, and_true, ite_and, Finset.sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, sum_nmem_const, ← Finset.mul_sum, Finset.sum_ite_irrel, mul_ite, mul_one, mul_zero]
      ring
    · simp only [hs, if_false, insert_cond, ite_and, Finset.sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, sum_nmem_const, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, Finset.sum_ite_irrel, mul_ite, mul_one, mul_zero]
      ring
  · rw [hS2]
    simp only [ite_and, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, sum_mem_const,
      ← Finset.mul_sum]
    ring
  · rw [hT2]
    split_ifs with hs
    · have hsplit : ∀ a b a' b' : Fin m,
          (if b ∈ U ∧ b' ∈ U ∧ xorSet (U.erase b) {a} = xorSet (U.erase b') {a'} then 1 else 0) =
          (if b ∈ U ∧ a' = a ∧ b' = b then 1 else 0) +
          (if a = b ∧ b ∈ U ∧ a' = b' ∧ b' ∈ U ∧ a ≠ a' then 1 else 0) +
          (if a ∈ U ∧ b ∈ U ∧ a' = b ∧ b' = a ∧ a ≠ b then 1 else 0) :=
        fun a b a' b' => split3 U a b a' b'
      simp only [hsplit, Finset.sum_add_distrib]
      simp only [ite_and, Finset.sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, sum_mem_const, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, Finset.sum_ite_irrel, mul_ite, mul_one, mul_zero]
      rw [offdiag_count]
      generalize U.card = w
      rcases w with _ | k
      · simp
      · have h2 : m + 2 * (k + 1) - 2 = m + 2 * k := by omega
        rw [h2, Nat.add_sub_cancel]; ring
    · simp only [hs, if_false, xor_cond, ite_and, Finset.sum_const, card_univ, Fintype.card_fin,
        smul_eq_mul, sum_mem_const, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, Finset.sum_ite_irrel, mul_ite, mul_one, mul_zero]
      ring

end BTHelper_block

namespace BTHelper_sums

open Finset

set_option linter.unusedSectionVars false
variable {α : Type} [DecidableEq α]

lemma T1 (S : Finset α) : 2 * ∑ V ∈ S.powerset, V.card = S.card * 2 ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_powerset_insert ha, card_insert_of_notMem ha]
    have h1 : ∑ V ∈ S.powerset, (insert a V).card = ∑ V ∈ S.powerset, (V.card + 1) := by
      refine Finset.sum_congr rfl (fun V hV => ?_)
      rw [card_insert_of_notMem (fun h => ha (mem_powerset.mp hV h))]
    rw [h1, Finset.sum_add_distrib, sum_const, card_powerset, smul_eq_mul]
    calc 2 * (∑ V ∈ S.powerset, V.card + (∑ V ∈ S.powerset, V.card + 2 ^ S.card * 1))
        = 2 * (2 * ∑ V ∈ S.powerset, V.card) + 2 * 2 ^ S.card := by ring
      _ = _ := by rw [ih]; ring

lemma T2 (S : Finset α) : 4 * ∑ V ∈ S.powerset, V.card ^ 2 = S.card * (S.card + 1) * 2 ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_powerset_insert ha, card_insert_of_notMem ha]
    have h1 : ∑ V ∈ S.powerset, (insert a V).card ^ 2 =
        ∑ V ∈ S.powerset, (V.card ^ 2 + 2 * V.card + 1) := by
      refine Finset.sum_congr rfl (fun V hV => ?_)
      rw [card_insert_of_notMem (fun h => ha (mem_powerset.mp hV h))]; ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, sum_const,
      card_powerset, smul_eq_mul]
    have h2 := T1 S
    calc 4 * (∑ V ∈ S.powerset, V.card ^ 2 + (∑ V ∈ S.powerset, V.card ^ 2 +
          2 * ∑ V ∈ S.powerset, V.card + 2 ^ S.card * 1))
        = 2 * (4 * ∑ V ∈ S.powerset, V.card ^ 2) + 4 * (2 * ∑ V ∈ S.powerset, V.card)
          + 4 * 2 ^ S.card := by ring
      _ = _ := by rw [ih, h2]; ring

lemma split_insert (S : Finset α) (a : α) (ha : a ∉ S) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) (f : ℕ → ℕ) :
    ∑ V ∈ (insert a S).powerset, (if Q V.card then f V.card else 0) =
      ∑ V ∈ S.powerset, (if Q V.card then f V.card else 0) +
      ∑ V ∈ S.powerset, (if ¬ Q V.card then f (V.card + 1) else 0) := by
  rw [Finset.sum_powerset_insert ha]
  congr 1
  refine Finset.sum_congr rfl (fun V hV => ?_)
  rw [card_insert_of_notMem (fun h => ha (mem_powerset.mp hV h))]
  exact if_congr (hQ _) rfl rfl

lemma ite_split (S : Finset α) (Q : ℕ → Prop) [DecidablePred Q] (f : ℕ → ℕ) :
    ∑ V ∈ S.powerset, (if Q V.card then f V.card else 0) +
      ∑ V ∈ S.powerset, (if ¬ Q V.card then f V.card else 0) = ∑ V ∈ S.powerset, f V.card := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun V _ => ?_)
  split_ifs <;> simp_all

lemma exists_insert (S : Finset α) (h : 1 ≤ S.card) :
    ∃ a S', a ∉ S' ∧ S = insert a S' ∧ S'.card + 1 = S.card := by
  obtain ⟨a, ha⟩ := card_pos.mp h
  exact ⟨a, S.erase a, notMem_erase a S, (insert_erase ha).symm, card_erase_add_one ha⟩

lemma F (S : Finset α) (hS : 1 ≤ S.card) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) :
    2 * ∑ V ∈ S.powerset, (if Q V.card then 1 else 0) = 2 ^ S.card := by
  obtain ⟨a, S', ha, rfl, hc⟩ := exists_insert S hS
  rw [split_insert S' a ha Q hQ (fun _ => 1), ite_split S' Q (fun _ => 1), ← hc]
  simp [pow_succ]; ring

lemma G (S : Finset α) (hS : 2 ≤ S.card) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) :
    4 * ∑ V ∈ S.powerset, (if Q V.card then V.card else 0) = S.card * 2 ^ S.card := by
  obtain ⟨a, S', ha, rfl, hc⟩ := exists_insert S (by omega)
  have hQ' : ∀ k, ¬ Q (k + 1) ↔ ¬ ¬ Q k := fun k => not_congr (hQ k)
  rw [split_insert S' a ha Q hQ (fun k => k)]
  have e : ∀ V ∈ S'.powerset, (if ¬ Q V.card then V.card + 1 else 0) =
      (if ¬ Q V.card then V.card else 0) + (if ¬ Q V.card then 1 else 0) := by
    intro V _; split_ifs <;> simp
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← add_assoc, ite_split S' Q (fun k => k)]
  have h1 := T1 S'
  have h2 := F S' (by omega) (fun k => ¬ Q k) hQ'
  rw [← hc]
  calc 4 * (∑ V ∈ S'.powerset, V.card + ∑ V ∈ S'.powerset, if ¬Q V.card then 1 else 0)
      = 2 * (2 * ∑ V ∈ S'.powerset, V.card) + 2 * (2 * ∑ V ∈ S'.powerset, if ¬Q V.card then 1 else 0) := by ring
    _ = _ := by rw [h1, h2]; ring

lemma H (S : Finset α) (hS : 3 ≤ S.card) (Q : ℕ → Prop) [DecidablePred Q]
    (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) :
    8 * ∑ V ∈ S.powerset, (if Q V.card then V.card ^ 2 else 0) = S.card * (S.card + 1) * 2 ^ S.card := by
  obtain ⟨a, S', ha, rfl, hc⟩ := exists_insert S (by omega)
  have hQ' : ∀ k, ¬ Q (k + 1) ↔ ¬ ¬ Q k := fun k => not_congr (hQ k)
  rw [split_insert S' a ha Q hQ (fun k => k ^ 2)]
  have e : ∀ V ∈ S'.powerset, (if ¬ Q V.card then (V.card + 1) ^ 2 else 0) =
      (if ¬ Q V.card then V.card ^ 2 else 0) + 2 * (if ¬ Q V.card then V.card else 0)
        + (if ¬ Q V.card then 1 else 0) := by
    intro V _; split_ifs <;> ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← add_assoc, ← add_assoc, ite_split S' Q (fun k => k ^ 2)]
  have h1 := T2 S'
  have h2 := G S' (by omega) (fun k => ¬ Q k) hQ'
  have h3 := F S' (by omega) (fun k => ¬ Q k) hQ'
  rw [← hc]
  calc 8 * (∑ V ∈ S'.powerset, V.card ^ 2 + 2 * (∑ V ∈ S'.powerset, if ¬Q V.card then V.card else 0)
        + ∑ V ∈ S'.powerset, if ¬Q V.card then 1 else 0)
      = 2 * (4 * ∑ V ∈ S'.powerset, V.card ^ 2)
        + 4 * (4 * ∑ V ∈ S'.powerset, if ¬Q V.card then V.card else 0)
        + 4 * (2 * ∑ V ∈ S'.powerset, if ¬Q V.card then 1 else 0) := by ring
    _ = _ := by rw [h1, h2, h3]; ring


section real
variable {m : ℕ}

lemma univ_sum (f : Finset (Fin m) → ℝ) :
    ∑ U : Finset (Fin m), f U = ∑ U ∈ (univ : Finset (Fin m)).powerset, f U := by
  rw [powerset_univ]

lemma rT0 : ∑ _U : Finset (Fin m), (1 : ℝ) = 2 ^ m := by
  simp

lemma rT1 : ∑ U : Finset (Fin m), (U.card : ℝ) = m * 2 ^ m / 2 := by
  have h := T1 (univ : Finset (Fin m))
  rw [card_univ, Fintype.card_fin] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  rw [univ_sum]; linarith

lemma rT2 : ∑ U : Finset (Fin m), (U.card : ℝ) ^ 2 = m * (m + 1) * 2 ^ m / 4 := by
  have h := T2 (univ : Finset (Fin m))
  rw [card_univ, Fintype.card_fin] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  rw [univ_sum]; linarith

lemma rF (hm : 1 ≤ m) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) :
    ∑ U : Finset (Fin m), (if Q U.card then (1 : ℝ) else 0) = 2 ^ m / 2 := by
  have h := F (univ : Finset (Fin m)) (by simp; omega) Q hQ
  rw [card_univ, Fintype.card_fin] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  rw [univ_sum]; linarith

lemma rG (hm : 2 ≤ m) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) :
    ∑ U : Finset (Fin m), (if Q U.card then (U.card : ℝ) else 0) = m * 2 ^ m / 4 := by
  have h := G (univ : Finset (Fin m)) (by simp; omega) Q hQ
  rw [card_univ, Fintype.card_fin] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  rw [univ_sum]; linarith

lemma rH (hm : 3 ≤ m) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ k, Q (k + 1) ↔ ¬ Q k) :
    ∑ U : Finset (Fin m), (if Q U.card then (U.card : ℝ) ^ 2 else 0) = m * (m + 1) * 2 ^ m / 8 := by
  have h := H (univ : Finset (Fin m)) (by simp; omega) Q hQ
  rw [card_univ, Fintype.card_fin] at h
  have h' := congrArg (Nat.cast : ℕ → ℝ) h
  push_cast at h'
  rw [univ_sum]; linarith

end real

end BTHelper_sums

open BTHelper_block BTHelper_sums Finset

theorem solution {m : ℕ} (hm : 4 ≤ m) (π : Bool) (j : Fin 3) :
    (∑ U : Cube (Fin m), (blockS j π U : ℝ)^2) =
      (1 + 1/(m : ℝ)) * (m : ℝ)^4 * 2^(m-2) ∧
    (∑ U : Cube (Fin m), (blockT j π U : ℝ)) ≤
      (1 + 3/(m : ℝ)) * (m : ℝ)^4 * 2^(m-3) := by
  have hm1 : 1 ≤ m := by omega
  have hQ : ∀ k, (decide ((k + 1) % 2 = 1) = π) ↔ ¬ (decide (k % 2 = 1) = π) := by
    intro k; cases π <;> simp <;> omega
  have hQ' : ∀ k, ¬ (decide ((k + 1) % 2 = 1) = π) ↔ ¬ ¬ (decide (k % 2 = 1) = π) :=
    fun k => not_congr (hQ k)
  have hG := rG (m := m) (by omega) (fun k => decide (k % 2 = 1) = π) hQ
  have hG' := rG (m := m) (by omega) (fun k => ¬ (decide (k % 2 = 1) = π)) hQ'
  have hH := rH (m := m) (by omega) (fun k => decide (k % 2 = 1) = π) hQ
  have hH' := rH (m := m) (by omega) (fun k => ¬ (decide (k % 2 = 1) = π)) hQ'
  have hF := rF (m := m) (by omega) (fun k => decide (k % 2 = 1) = π) hQ
  have hF' := rF (m := m) (by omega) (fun k => ¬ (decide (k % 2 = 1) = π)) hQ'
  beta_reduce at hG hG' hH hH' hF hF'
  have h0 := rT0 (m := m)
  have h1 := rT1 (m := m)
  have h2 := rT2 (m := m)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp8 : (2 : ℝ) ^ m = 2 ^ (m - 3) * 8 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, ← pow_add]; congr 1; omega
  have hp4 : (2 : ℝ) ^ (m - 2) = 2 ^ (m - 3) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have hpos : (0 : ℝ) < 2 ^ (m - 3) := by positivity
  have eS : (1 + 1 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 2) = ((m : ℝ) + 1) * m ^ 3 * 2 ^ (m - 2) := by
    field_simp
  have eT : (1 + 3 / (m : ℝ)) * (m : ℝ) ^ 4 * 2 ^ (m - 3) = ((m : ℝ) + 3) * m ^ 3 * 2 ^ (m - 3) := by
    field_simp
  rw [eS, eT, hp4]
  have hcard : ∀ U : Cube (Fin m), U.card ≤ m := fun U => by
    simpa using card_le_univ U
  fin_cases j
  · constructor
    · have e : ∀ U : Cube (Fin m), ((blockS 0 π U : ℕ) : ℝ) ^ 2 = (m : ℝ) ^ 2 * (U.card : ℝ) ^ 2 := by
        intro U; rw [(block_id hm1 π U).1]; push_cast; ring
      simp only [Fin.zero_eta]
      rw [Finset.sum_congr rfl (fun U _ => e U), ← Finset.mul_sum, h2, hp8]; ring
    · have e : ∀ U : Cube (Fin m), ((blockT 0 π U : ℕ) : ℝ) =
          (m : ℝ) ^ 2 * (if decide (U.card % 2 = 1) = π then (U.card : ℝ) ^ 2 else 0) +
          (m : ℝ) ^ 2 * (if ¬ (decide (U.card % 2 = 1) = π) then (U.card : ℝ) else 0) := by
        intro U; rw [(block_id hm1 π U).2.1]; split_ifs <;> push_cast <;> ring
      simp only [Fin.zero_eta]
      rw [Finset.sum_congr rfl (fun U _ => e U), Finset.sum_add_distrib, ← Finset.mul_sum,
        ← Finset.mul_sum, hH, hG', hp8]
      apply le_of_eq; ring
  · constructor
    · have e : ∀ U : Cube (Fin m), ((blockS 1 π U : ℕ) : ℝ) ^ 2 =
          (m : ℝ) ^ 4 * 1 - 2 * (m : ℝ) ^ 3 * (U.card : ℝ) + (m : ℝ) ^ 2 * (U.card : ℝ) ^ 2 := by
        intro U; rw [(block_id hm1 π U).2.2.1]; push_cast [hcard U]; ring
      simp only [Fin.mk_one]
      rw [Finset.sum_congr rfl (fun U _ => e U), Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h0, h1, h2, hp8]; ring
    · have e : ∀ U : Cube (Fin m), ((blockT 1 π U : ℕ) : ℝ) =
          (m : ℝ) ^ 4 * (if decide (U.card % 2 = 1) = π then (1 : ℝ) else 0)
          - 2 * (m : ℝ) ^ 3 * (if decide (U.card % 2 = 1) = π then (U.card : ℝ) else 0)
          + (m : ℝ) ^ 2 * (if decide (U.card % 2 = 1) = π then (U.card : ℝ) ^ 2 else 0)
          + (m : ℝ) ^ 3 * (if ¬ (decide (U.card % 2 = 1) = π) then (1 : ℝ) else 0)
          - (m : ℝ) ^ 2 * (if ¬ (decide (U.card % 2 = 1) = π) then (U.card : ℝ) else 0) := by
        intro U; rw [(block_id hm1 π U).2.2.2.1]; split_ifs <;> push_cast [hcard U] <;> ring
      simp only [Fin.mk_one]
      rw [Finset.sum_congr rfl (fun U _ => e U), Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]
      rw [hF, hG, hH, hF', hG', hp8]
      apply le_of_eq; ring
  · constructor
    · have e : ∀ U : Cube (Fin m), ((blockS 2 π U : ℕ) : ℝ) ^ 2 = (m : ℝ) ^ 2 * (U.card : ℝ) ^ 2 := by
        intro U; rw [(block_id hm1 π U).2.2.2.2.1]; push_cast; ring
      simp only [Fin.reduceFinMk]
      rw [Finset.sum_congr rfl (fun U _ => e U), ← Finset.mul_sum, h2, hp8]; ring
    · have e : ∀ U : Cube (Fin m), ((blockT 2 π U : ℕ) : ℝ) =
          ((m : ℝ) - 2) * (if decide (U.card % 2 = 1) = π then (U.card : ℝ) else 0)
          + 2 * (if decide (U.card % 2 = 1) = π then (U.card : ℝ) ^ 2 else 0)
          + (m : ℝ) * (if ¬ (decide (U.card % 2 = 1) = π) then (U.card : ℝ) ^ 2 else 0) := by
        intro U; rw [(block_id hm1 π U).2.2.2.2.2]
        have : 2 ≤ m + 2 * U.card := by omega
        split_ifs <;> push_cast [this] <;> ring
      simp only [Fin.reduceFinMk]
      rw [Finset.sum_congr rfl (fun U _ => e U), Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]
      rw [hG, hH, hH', hp8]
      have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
      have key : 0 ≤ (m : ℝ) ^ 4 + 2 * (m : ℝ) ^ 3 - 5 * (m : ℝ) ^ 2 + 2 * (m : ℝ) := by
        have h5 : 0 ≤ (m : ℝ) ^ 2 + 2 * (m : ℝ) - 5 := by nlinarith
        have : (m : ℝ) ^ 4 + 2 * (m : ℝ) ^ 3 - 5 * (m : ℝ) ^ 2 + 2 * (m : ℝ)
            = (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 + 2 * (m : ℝ) - 5) + 2 * (m : ℝ) := by ring
        rw [this]; positivity
      nlinarith [mul_nonneg hpos.le key]
