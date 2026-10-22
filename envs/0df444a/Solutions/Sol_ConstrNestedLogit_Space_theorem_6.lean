-- Prove2me | solution 1 for ConstrNestedLogit.Space.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T08:24:54.856664+00:00
-- url     : https://prove2.me/submissions/52fb456d-888b-4efc-81d9-1135082afd90

import Mathlib
import Definitions.Def_ConstrNestedLogit_Space_Model

set_option autoImplicit false

namespace PriorGreedy

namespace FractionalKnapsack

structure Certificate {α : Type*} (S : Finset α) (w a : α → ℝ) (c R : ℝ) where
  x : α → ℝ
  lam : ℝ
  lam_nonneg : 0 ≤ lam
  lam_le : lam ≤ R
  outside : ∀ j, j ∉ S → x j = 0
  box : ∀ j, 0 ≤ x j ∧ x j ≤ 1
  feasible : (∑ j ∈ S, w j * x j) ≤ c
  complement : lam = 0 ∨ (∑ j ∈ S, w j * x j) = c
  positive : ∀ j, 0 < x j → 0 < a j
  lower : ∀ j ∈ S, 0 < x j → lam ≤ a j / w j
  upper : ∀ j ∈ S, x j < 1 → a j / w j ≤ lam
  fractional : ∀ j k, 0 < x j → x j < 1 → 0 < x k → x k < 1 → j = k

theorem update_sum {α : Type*} [DecidableEq α] (S : Finset α) (p : α)
    (hp : p ∈ S) (w y : α → ℝ) (t : ℝ) :
    (∑ j ∈ S, w j * Function.update y p t j) =
      (∑ j ∈ S.erase p, w j * y j) + w p * t := by
  rw [← Finset.sum_erase_add _ _ hp]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update, (Finset.mem_erase.mp hj).1]
  · simp

theorem build {α : Type*} [DecidableEq α] (S : Finset α) (w a : α → ℝ)
    (hw : ∀ j, 0 < w j) (c R : ℝ) (hc : 0 ≤ c) (hR : 0 ≤ R)
    (hbound : ∀ j ∈ S, a j / w j ≤ R) : Nonempty (Certificate S w a c R) := by
  classical
  induction S using Finset.strongInductionOn generalizing c R with
  | _ S ih =>
    by_cases hpos : ∃ z ∈ S, 0 < a z
    · obtain ⟨z, hz, haz⟩ := hpos
      obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun j => a j / w j) ⟨z, hz⟩
      have hratio : 0 < a p / w p := (div_pos haz (hw z)).trans_le (hmax z hz)
      have hap : 0 < a p := by simpa using (lt_div_iff₀ (hw p)).mp hratio
      by_cases hcap : w p ≤ c
      · obtain ⟨T⟩ := ih (S.erase p) (Finset.erase_ssubset hp) (c - w p) (a p / w p)
          (sub_nonneg.mpr hcap) hratio.le (fun j hj => hmax j (Finset.mem_erase.mp hj).2)
        let x := Function.update T.x p 1
        have hsum : (∑ j ∈ S, w j * x j) = (∑ j ∈ S.erase p, w j * T.x j) + w p := by
          simpa [x] using update_sum S p hp w T.x 1
        refine ⟨{
          x := x, lam := T.lam, lam_nonneg := T.lam_nonneg,
          lam_le := T.lam_le.trans (hbound p hp), outside := ?_, box := ?_,
          feasible := ?_, complement := ?_, positive := ?_, lower := ?_, upper := ?_,
          fractional := ?_ }⟩
        · intro j hj
          have hjp : j ≠ p := fun e => hj (e ▸ hp)
          simp only [x, Function.update_of_ne hjp]
          exact T.outside j (fun h => hj (Finset.mem_erase.mp h).2)
        · intro j
          by_cases hj : j = p
          · subst j; simp [x]
          · simpa [x, hj] using T.box j
        · rw [hsum]; linarith [T.feasible]
        · rcases T.complement with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hsum]; linarith)
        · intro j hj
          by_cases hjp : j = p
          · subst j; exact hap
          · apply T.positive j
            simpa [x, hjp] using hj
        · intro j hj hjx
          by_cases hjp : j = p
          · subst j; exact T.lam_le
          · exact T.lower j (Finset.mem_erase.mpr ⟨hjp, hj⟩) (by simpa [x, hjp] using hjx)
        · intro j hj hjx
          by_cases hjp : j = p
          · subst j; simp [x] at hjx
          · exact T.upper j (Finset.mem_erase.mpr ⟨hjp, hj⟩) (by simpa [x, hjp] using hjx)
        · intro j k hj0 hj1 hk0 hk1
          have hjp : j ≠ p := by intro e; subst j; simp [x] at hj1
          have hkp : k ≠ p := by intro e; subst k; simp [x] at hk1
          exact T.fractional j k (by simpa [x, hjp] using hj0)
            (by simpa [x, hjp] using hj1) (by simpa [x, hkp] using hk0)
            (by simpa [x, hkp] using hk1)
      · let x : α → ℝ := Function.update (fun _ => 0) p (c / w p)
        have hsum : (∑ j ∈ S, w j * x j) = c := by
          rw [show x = Function.update (fun _ => 0) p (c / w p) from rfl,
            update_sum S p hp]
          simp [mul_div_cancel₀, ne_of_gt (hw p)]
        refine ⟨{
          x := x, lam := a p / w p, lam_nonneg := hratio.le,
          lam_le := hbound p hp, outside := ?_, box := ?_, feasible := hsum.le,
          complement := Or.inr hsum, positive := ?_, lower := ?_, upper := ?_,
          fractional := ?_ }⟩
        · intro j hj
          have hjp : j ≠ p := fun e => hj (e ▸ hp)
          simp [x, hjp]
        · intro j
          by_cases hj : j = p
          · subst j
            simpa [x] using And.intro (div_nonneg hc (hw p).le)
              ((div_le_one (hw p)).2 (le_of_not_ge hcap))
          · simp [x, hj]
        · intro j hj
          by_cases hjp : j = p
          · subst j; exact hap
          · simp [x, hjp] at hj
        · intro j hj hjx
          by_cases hjp : j = p
          · subst j; rfl
          · simp [x, hjp] at hjx
        · intro j hj _
          exact hmax j hj
        · intro j k hj0 _ hk0 _
          have hjp : j = p := by by_contra h; simp [x, h] at hj0
          have hkp : k = p := by by_contra h; simp [x, h] at hk0
          exact hjp.trans hkp.symm
    · refine ⟨{
        x := fun _ => 0, lam := 0, lam_nonneg := le_rfl,
        lam_le := hR, outside := by simp, box := by simp,
        feasible := by simpa using hc, complement := Or.inl rfl,
        positive := by simp, lower := by simp, upper := ?_, fractional := by simp }⟩
      intro j hj _
      exact div_nonpos_of_nonpos_of_nonneg (le_of_not_gt (fun h => hpos ⟨j, hj, h⟩)) (hw j).le

theorem certificate_optimal {α : Type*} [Fintype α] (w a : α → ℝ)
    (hw : ∀ j, 0 < w j) (c R : ℝ) (T : Certificate Finset.univ w a c R)
    (y : α → ℝ) (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) (hycap : (∑ j, w j * y j) ≤ c) :
    (∑ j, a j * y j) ≤ ∑ j, a j * T.x j := by
  have hpoint (j : α) : (a j - T.lam * w j) * y j ≤ (a j - T.lam * w j) * T.x j := by
    by_cases hz : T.x j = 0
    · have hratio := T.upper j (Finset.mem_univ _) (by rw [hz]; norm_num)
      have hcoeff : a j - T.lam * w j ≤ 0 := by
        have := (div_le_iff₀ (hw j)).mp hratio
        linarith
      rw [hz, mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hcoeff (hy j).1
    · have hxpos : 0 < T.x j := lt_of_le_of_ne (T.box j).1 (Ne.symm hz)
      have hl := (le_div_iff₀ (hw j)).mp (T.lower j (Finset.mem_univ _) hxpos)
      have hc0 : 0 ≤ a j - T.lam * w j := by linarith
      by_cases h1 : T.x j = 1
      · rw [h1]
        exact mul_le_mul_of_nonneg_left (hy j).2 hc0
      · have hxlt : T.x j < 1 := lt_of_le_of_ne (T.box j).2 h1
        have hu := (div_le_iff₀ (hw j)).mp (T.upper j (Finset.mem_univ _) hxlt)
        have heq : a j - T.lam * w j = 0 := by linarith
        simp [heq]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset α)) => hpoint j)
  simp_rw [sub_mul, mul_assoc] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at hs
  rcases T.complement with h | h
  · simpa [h] using hs
  · have hcap := mul_le_mul_of_nonneg_left hycap T.lam_nonneg
    rw [h] at hs
    linarith

end FractionalKnapsack

open ConstrNestedLogit.Space

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hn : 0 < n)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) :
    ∃ x : Fin n → ℝ, spaceLPOptimal I w c i u x ∧ atMostOneFractional x ∧
      (∀ j, 0 < x j → 0 < utility I i u j) ∧
      (∀ j k, 0 < x j → x k < 1 →
        utilityRatio I w i u k ≤ utilityRatio I w i u j) := by
  classical
  let a := utility I i u
  let R : ℝ := ∑ j, max (a j / w i j) 0
  have hR : 0 ≤ R := Finset.sum_nonneg (fun j _ => le_max_right _ _)
  have hbound : ∀ j ∈ (Finset.univ : Finset (Fin n)), a j / w i j ≤ R := by
    intro j _
    exact (le_max_left _ _).trans (Finset.single_le_sum (fun k _ => le_max_right (a k / w i k) 0)
      (Finset.mem_univ j))
  have hc : 0 ≤ c i := (hw ⟨0, hn⟩).le.trans (hwc ⟨0, hn⟩)
  obtain ⟨T⟩ := FractionalKnapsack.build Finset.univ (w i) a hw (c i) R hc hR hbound
  refine ⟨T.x, ⟨⟨T.box, T.feasible⟩, ?_⟩, T.fractional, T.positive, ?_⟩
  · intro y hy
    exact FractionalKnapsack.certificate_optimal (w i) a hw (c i) R T y hy.1 hy.2
  · intro j k hj hk
    exact (T.upper k (Finset.mem_univ _) hk).trans (T.lower j (Finset.mem_univ _) hj)

#print axioms solution

end PriorGreedy

open ConstrNestedLogit.Space
open PriorGreedy.FractionalKnapsack
namespace KnapsackStability

theorem certificate_transport {n : ℕ} (w a b : Fin n → ℝ)
    (hw : ∀ j, 0 < w j) (c R : ℝ) (T : Certificate Finset.univ w a c R)
    (hpos : ∀ j, 0 < a j ↔ 0 < b j)
    (horder : ∀ j k, a j / w j ≤ a k / w k ↔ b j / w j ≤ b k / w k) :
    knapsackLPOptimal w b c T.x := by
  classical
  let U := (Finset.univ : Finset (Fin n)).filter (fun j => T.x j < 1)
  let B := insert (0 : ℝ) (U.image (fun j => b j / w j))
  have hB : B.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let L := B.max' hB
  have hL0 : 0 ≤ L := Finset.le_max' B 0 (Finset.mem_insert_self _ _)
  have hu (j : Fin n) (hj : T.x j < 1) : b j / w j ≤ L := by
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hj⟩, rfl⟩)
  have hl (j : Fin n) (hj : 0 < T.x j) : L ≤ b j / w j := by
    apply Finset.max'_le
    intro z hz
    rcases Finset.mem_insert.mp hz with hz | hz
    · subst z
      exact (div_pos ((hpos j).mp (T.positive j hj)) (hw j)).le
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
      apply (horder k j).mp
      exact (T.upper k (Finset.mem_univ _) (Finset.mem_filter.mp hk).2).trans
        (T.lower j (Finset.mem_univ _) hj)
  have hcomp : L = 0 ∨ (∑ j, w j * T.x j) = c := by
    rcases T.complement with h | h
    · left
      apply le_antisymm ?_ hL0
      apply Finset.max'_le
      intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · simpa [hz]
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
        have ha := T.upper k (Finset.mem_univ _) (Finset.mem_filter.mp hk).2
        rw [h] at ha
        have ha0 : a k ≤ 0 := by have hh := (div_le_iff₀ (hw k)).mp ha; simpa using hh
        have hb0 : b k ≤ 0 := le_of_not_gt (fun h => (not_lt_of_ge ha0) ((hpos k).mpr h))
        exact div_nonpos_of_nonpos_of_nonneg hb0 (hw k).le
    · exact Or.inr h
  let T' : Certificate Finset.univ w b c L := {
    x := T.x, lam := L, lam_nonneg := hL0, lam_le := le_rfl,
    outside := T.outside, box := T.box, feasible := T.feasible,
    complement := hcomp, positive := fun j hj => (hpos j).mp (T.positive j hj),
    lower := fun j _ hj => hl j hj, upper := fun j _ hj => hu j hj,
    fractional := T.fractional }
  refine ⟨⟨T.box, T.feasible⟩, ?_⟩
  intro y hy
  exact certificate_optimal w b hw c L T' y hy.1 hy.2

end KnapsackStability

namespace RealBreakpointCells
noncomputable def code (B : Finset ℝ) (u : ℝ) : ℕ :=
  (B.filter (fun b => b ≤ u)).card + (B.filter (fun b => b < u)).card

def SameCell (B : Finset ℝ) (u v : ℝ) : Prop :=
  ∀ b ∈ B, (u ≤ b ↔ v ≤ b) ∧ (u < b ↔ v < b)

lemma code_le (B : Finset ℝ) (u : ℝ) : code B u ≤ 2 * B.card := by
  classical
  have h1 := Finset.card_filter_le (s := B) (p := fun b => b ≤ u)
  have h2 := Finset.card_filter_le (s := B) (p := fun b => b < u)
  unfold code
  omega

lemma same_cell_ordered (B : Finset ℝ) (u v : ℝ) (huv : u ≤ v)
    (he : code B u = code B v) : SameCell B u v := by
  classical
  have hle : B.filter (fun b => b ≤ u) ⊆ B.filter (fun b => b ≤ v) := by
    intro b hb
    simp only [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1,hb.2.trans huv⟩
  have hlt : B.filter (fun b => b < u) ⊆ B.filter (fun b => b < v) := by
    intro b hb
    simp only [Finset.mem_filter] at hb ⊢
    exact ⟨hb.1,hb.2.trans_le huv⟩
  have hcl := Finset.card_le_card hle
  have hct := Finset.card_le_card hlt
  have hel : B.filter (fun b => b ≤ u) = B.filter (fun b => b ≤ v) := by
    apply Finset.eq_of_subset_of_card_le hle
    unfold code at he
    omega
  have het : B.filter (fun b => b < u) = B.filter (fun b => b < v) := by
    apply Finset.eq_of_subset_of_card_le hlt
    unfold code at he
    omega
  intro b hb
  have hble : (b ≤ u ↔ b ≤ v) := by
    have hh := Finset.ext_iff.mp hel b
    simpa [hb] using hh
  have hblt : (b < u ↔ b < v) := by
    have hh := Finset.ext_iff.mp het b
    simpa [hb] using hh
  constructor
  · simpa only [not_lt] using not_congr hblt
  · simpa only [not_le] using not_congr hble

lemma same_cell_of_code (B : Finset ℝ) (u v : ℝ) (he : code B u = code B v) :
    SameCell B u v := by
  rcases le_total u v with h | h
  · exact same_cell_ordered B u v h he
  · intro b hb
    have hh := same_cell_ordered B v u h he.symm b hb
    exact ⟨hh.1.symm,hh.2.symm⟩

theorem representatives (B : Finset ℝ) :
    ∃ V : Finset ℝ, V.card ≤ 2 * B.card + 1 ∧
      (∀ v ∈ V, 0 ≤ v) ∧ ∀ u : ℝ, 0 ≤ u → ∃ v ∈ V, SameCell B u v := by
  classical
  let rep : Fin (2 * B.card + 1) → ℝ := fun k =>
    if h : ∃ u : ℝ, 0 ≤ u ∧ code B u = k.val then Classical.choose h else 0
  have hnonneg (k : Fin (2*B.card+1)) : 0 ≤ rep k := by
    dsimp [rep]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · rfl
  refine ⟨Finset.univ.image rep, ?_, ?_, ?_⟩
  · exact (Finset.card_image_le).trans (by simp)
  · intro v hv
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hv
    exact hnonneg k
  · intro u hu
    let k : Fin (2*B.card+1) := ⟨code B u, by have := code_le B u; omega⟩
    have h : ∃ z : ℝ, 0 ≤ z ∧ code B z = k.val := ⟨u,hu,rfl⟩
    refine ⟨rep k, Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
    apply same_cell_of_code
    simpa [rep, h, k] using (Classical.choose_spec h).2.symm

end RealBreakpointCells

#print axioms KnapsackStability.certificate_transport
#print axioms RealBreakpointCells.representatives

namespace AffineOrderCells
open RealBreakpointCells

lemma linear_sign (a b u v : ℝ) (ha : a ≠ 0)
    (hc : (u ≤ -b/a ↔ v ≤ -b/a) ∧ (u < -b/a ↔ v < -b/a)) :
    (0 ≤ a*u+b ↔ 0 ≤ a*v+b) ∧ (0 < a*u+b ↔ 0 < a*v+b) := by
  rcases lt_or_gt_of_ne ha with ha | ha
  · have hle (z : ℝ) : 0 ≤ a*z+b ↔ z ≤ -b/a := by
      rw [le_div_iff_of_neg ha]
      constructor <;> intro h <;> nlinarith
    have hlt (z : ℝ) : 0 < a*z+b ↔ z < -b/a := by
      rw [lt_div_iff_of_neg ha]
      constructor <;> intro h <;> nlinarith
    simpa only [hle, hlt] using hc
  · have hle (z : ℝ) : 0 ≤ a*z+b ↔ -b/a ≤ z := by
      rw [div_le_iff₀ ha]
      constructor <;> intro h <;> nlinarith
    have hlt (z : ℝ) : 0 < a*z+b ↔ -b/a < z := by
      rw [div_lt_iff₀ ha]
      constructor <;> intro h <;> nlinarith
    rw [hle, hle, hlt, hlt]
    exact ⟨by simpa only [not_lt] using not_congr hc.2,
      by simpa only [not_le] using not_congr hc.1⟩

abbrev PairIdx (n : ℕ) := Σ i : Fin (n+1), Fin i.val

def lower {n : ℕ} (p : PairIdx n) : Fin (n+1) := ⟨p.2.val, p.2.isLt.trans p.1.isLt⟩

noncomputable def crossings {n : ℕ} (a b : Fin (n+1) → ℝ) : Finset ℝ :=
  ((Finset.univ : Finset (PairIdx n)).filter (fun p => a p.1 ≠ a (lower p))).image
    (fun p => (b p.1 - b (lower p))/(a (lower p)-a p.1))

lemma pair_card (n : ℕ) : 2 * Fintype.card (PairIdx n) = n*(n+1) := by
  have h := Finset.sum_range_id_mul_two (n+1)
  simp only [PairIdx, Fintype.card_sigma, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i)]
  simpa [Nat.mul_comm] using h

lemma crossing_card {n : ℕ} (a b : Fin (n+1) → ℝ) :
    2 * (crossings a b).card ≤ n*(n+1) := by
  have h : (crossings a b).card ≤ Fintype.card (PairIdx n) :=
    Finset.card_image_le.trans ((Finset.card_filter_le (s := Finset.univ)
      (p := fun p : PairIdx n => a p.1 ≠ a (lower p))).trans (by simp))
  exact (Nat.mul_le_mul_left 2 h).trans_eq (pair_card n)

lemma ordered_stable {n : ℕ} (a b : Fin (n+1) → ℝ) (u v : ℝ)
    (hc : SameCell (crossings a b) u v) (i j : Fin (n+1)) (hji : j.val < i.val) :
    (a i*u+b i ≤ a j*u+b j ↔ a i*v+b i ≤ a j*v+b j) ∧
      (a i*u+b i < a j*u+b j ↔ a i*v+b i < a j*v+b j) := by
  classical
  by_cases he : a i = a j
  · rw [he]
    constructor <;> constructor <;> intro h <;> linarith
  · let p : PairIdx n := ⟨i,⟨j.val,hji⟩⟩
    have hl : lower p = j := Fin.ext rfl
    have hr : (b i-b j)/(a j-a i) ∈ crossings a b := by
      apply Finset.mem_image.mpr
      refine ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · simpa only [p, hl] using he
      · simp only [p, hl]
    have h := linear_sign (a j-a i) (b j-b i) u v (sub_ne_zero.mpr (Ne.symm he))
      (by simpa only [neg_sub] using hc _ hr)
    constructor
    · constructor <;> intro hh
      · have hh' := h.1.mp (show 0 ≤ (a j-a i)*u+(b j-b i) by nlinarith)
        nlinarith
      · have hh' := h.1.mpr (show 0 ≤ (a j-a i)*v+(b j-b i) by nlinarith)
        nlinarith
    · constructor <;> intro hh
      · have hh' := h.2.mp (show 0 < (a j-a i)*u+(b j-b i) by nlinarith)
        nlinarith
      · have hh' := h.2.mpr (show 0 < (a j-a i)*v+(b j-b i) by nlinarith)
        nlinarith

lemma all_stable {n : ℕ} (a b : Fin (n+1) → ℝ) (u v : ℝ)
    (hc : SameCell (crossings a b) u v) (i j : Fin (n+1)) :
    (a i*u+b i ≤ a j*u+b j ↔ a i*v+b i ≤ a j*v+b j) ∧
      (a i*u+b i < a j*u+b j ↔ a i*v+b i < a j*v+b j) := by
  rcases lt_trichotomy j.val i.val with h | h | h
  · exact ordered_stable a b u v hc i j h
  · have he : j = i := Fin.ext h
    subst j
    simp
  · have hh := ordered_stable a b u v hc j i h
    exact ⟨by simpa only [not_lt] using not_congr hh.2,
      by simpa only [not_le] using not_congr hh.1⟩

theorem representatives {n : ℕ} (a b : Fin (n+1) → ℝ) :
    ∃ V : Finset ℝ, V.card ≤ n*(n+1)+1 ∧ (∀ v ∈ V, 0 ≤ v) ∧
      ∀ u : ℝ, 0 ≤ u → ∃ v ∈ V, ∀ i j : Fin (n+1),
        (a i*u+b i ≤ a j*u+b j ↔ a i*v+b i ≤ a j*v+b j) ∧
        (a i*u+b i < a j*u+b j ↔ a i*v+b i < a j*v+b j) := by
  obtain ⟨V,hV,hpos,hcover⟩ := RealBreakpointCells.representatives (crossings a b)
  refine ⟨V,hV.trans (Nat.add_le_add_right (crossing_card a b) 1),hpos,?_⟩
  intro u hu
  obtain ⟨v,hv,hc⟩ := hcover u hu
  exact ⟨v,hv,all_stable a b u v hc⟩

end AffineOrderCells

#print axioms AffineOrderCells.representatives

namespace UniformKnapsack
open PriorGreedy.FractionalKnapsack
open ConstrNestedLogit.Space

theorem uniform_points {ι : Type*} {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n) (w : ι → Fin n → ℝ)
    (c : ι → ℝ) (i : ι) (hw : ∀ j, 0 < w i j) (hc : 0 ≤ c i) :
    ∃ V : Finset ℝ, ∃ X : ℝ → Fin n → ℝ,
      V.card ≤ n*(n+1)+1 ∧
      (∀ v ∈ V, 0 ≤ v ∧ spaceLPOptimal I w c i v (X v) ∧ atMostOneFractional (X v)) ∧
      ∀ u : ℝ, 0 ≤ u → ∃ v ∈ V,
        spaceLPOptimal I w c i u (X v) ∧ (∀ j, 0 < X v j → 0 < utility I i u j) := by
  classical
  let a : Fin (n+1) → ℝ := Fin.lastCases 0 (fun j => -I.v i j / w i j)
  let b : Fin (n+1) → ℝ := Fin.lastCases 0 (fun j => I.v i j * I.r i j / w i j)
  have he (j : Fin n) (u : ℝ) : a j.castSucc*u+b j.castSucc = utilityRatio I w i u j := by
    simp only [a, b, Fin.lastCases_castSucc, utilityRatio, utility]
    ring
  have hz (u : ℝ) : a (Fin.last n)*u+b (Fin.last n) = 0 := by simp [a,b]
  obtain ⟨V,hcard,hV,hcover⟩ := AffineOrderCells.representatives a b
  let R (u : ℝ) : ℝ := ∑ j, max (utilityRatio I w i u j) 0
  have hcert (u : ℝ) : Nonempty (Certificate Finset.univ (w i) (utility I i u) (c i) (R u)) := by
    apply build _ _ _ hw _ _ hc
    · exact Finset.sum_nonneg (fun j _ => le_max_right _ _)
    · intro j _
      exact (le_max_left _ _).trans (Finset.single_le_sum
        (fun k _ => le_max_right (utilityRatio I w i u k) 0) (Finset.mem_univ j))
  let T (u : ℝ) := Classical.choice (hcert u)
  have hop (u : ℝ) : spaceLPOptimal I w c i u (T u).x := by
    refine ⟨⟨(T u).box,(T u).feasible⟩,?_⟩
    intro y hy
    exact certificate_optimal (w i) (utility I i u) hw (c i) (R u) (T u) y hy.1 hy.2
  refine ⟨V,fun u => (T u).x,hcard,?_,?_⟩
  · intro v hv
    exact ⟨hV v hv,hop v,(T v).fractional⟩
  · intro u hu
    obtain ⟨v,hv,horder⟩ := hcover u hu
    have hp (j : Fin n) : 0 < utility I i v j ↔ 0 < utility I i u j := by
      have h := (horder (Fin.last n) j.castSucc).2
      rw [hz, hz, he, he] at h
      simpa only [utilityRatio, lt_div_iff₀ (hw j), zero_mul] using h.symm
    have ho (j k : Fin n) : utility I i v j / w i j ≤ utility I i v k / w i k ↔
        utility I i u j / w i j ≤ utility I i u k / w i k := by
      have h := (horder j.castSucc k.castSucc).1
      simpa only [he, utilityRatio] using h.symm
    exact ⟨v,hv,KnapsackStability.certificate_transport (w i) (utility I i v)
      (utility I i u) hw (c i) (R v) (T v) hp ho,fun j hj => (hp j).mp ((T v).positive j hj)⟩

end UniformKnapsack

#print axioms UniformKnapsack.uniform_points

namespace PriorRounding

open scoped BigOperators
open ConstrNestedLogit.Space

namespace KnapsackRounding

lemma support_nonneg {n : ℕ} (w a x : Fin n → ℝ) (c : ℝ)
    (hw : ∀ k, 0 ≤ w k) (hx : knapsackLPOptimal w a c x)
    (k : Fin n) (hk : 0 < x k) : 0 ≤ a k := by
  classical
  by_contra ha
  have ha : a k < 0 := lt_of_not_ge ha
  let y : Fin n → ℝ := fun l => if l = k then 0 else x l
  have hy : knapsackLPFeasible w c y := by
    constructor
    · intro l
      by_cases hl : l = k
      · simp [y, hl]
      · simpa [y, hl] using hx.1.1 l
    · apply le_trans _ hx.1.2
      apply Finset.sum_le_sum
      intro l hl
      by_cases hlk : l = k
      · subst l
        simpa [y] using mul_nonneg (hw k) (hx.1.1 k).1
      · simp [y, hlk]
  have hs : knapsackLPObjective a x < knapsackLPObjective a y := by
    apply Finset.sum_lt_sum
    · intro l hl
      by_cases hlk : l = k
      · subst l
        simp only [y, if_pos rfl, mul_zero]
        exact le_of_lt (mul_neg_of_neg_of_pos ha hk)
      · simp [y, hlk]
    · exact ⟨k, Finset.mem_univ k, by simpa [y] using mul_neg_of_neg_of_pos ha hk⟩
  exact (not_lt_of_ge (hx.2 y hy)) hs

lemma objective_split {n : ℕ} (a x : Fin n → ℝ)
    (hx : ∀ k, 0 ≤ x k ∧ x k ≤ 1) (j : Option (Fin n))
    (hj : ∀ k, (0 < x k ∧ x k < 1) ↔ j = some k) :
    knapsackLPObjective a x =
      (∑ k ∈ rounded x, a k) +
        (match j with | none => 0 | some k => a k * x k) := by
  classical
  have hbin (k : Fin n) (hk : j ≠ some k) : x k = 0 ∨ x k = 1 := by
    by_contra h
    have h0 : x k ≠ 0 := fun h0 => h (Or.inl h0)
    have h1 : x k ≠ 1 := fun h1 => h (Or.inr h1)
    exact hk ((hj k).mp ⟨lt_of_le_of_ne (hx k).1 (Ne.symm h0),
      lt_of_le_of_ne (hx k).2 h1⟩)
  cases j with
  | none =>
    simp only [add_zero, knapsackLPObjective, rounded, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    rcases hbin k (by simp) with h | h <;> simp [h]
  | some k =>
    have hk := (hj k).mpr rfl
    have heq (l : Fin n) :
        a l * x l = (if x l = 1 then a l else 0) +
          (if l = k then a k * x k else 0) := by
      by_cases hl : l = k
      · subst l
        simp [ne_of_lt hk.2]
      · rcases hbin l (by simpa using Ne.symm hl) with h | h <;> simp [h, hl]
    simp only [knapsackLPObjective, rounded, Finset.sum_filter]
    calc
      _ = ∑ l, ((if x l = 1 then a l else 0) +
          (if l = k then a k * x k else 0)) := Finset.sum_congr rfl (fun l _ => heq l)
      _ = _ := by rw [Finset.sum_add_distrib]; simp

lemma integer_le_lp {n : ℕ} (w a x : Fin n → ℝ) (c : ℝ)
    (hx : knapsackLPOptimal w a c x)
    (T : Finset (Fin n)) (hT : ∑ k ∈ T, w k ≤ c) :
    (∑ k ∈ T, a k) ≤ knapsackLPObjective a x := by
  classical
  let y : Fin n → ℝ := fun k => if k ∈ T then 1 else 0
  have hy : knapsackLPFeasible w c y := by
    constructor
    · intro k
      by_cases hk : k ∈ T <;> simp [y, hk]
    · simpa [y, mul_ite] using hT
  simpa [knapsackLPObjective, y, mul_ite] using hx.2 y hy

end KnapsackRounding

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hvnp : ∀ i, I.vnp i = 0) (hv : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i)
    (u : ℝ) (hu : 0 ≤ u) (x : Fin n → ℝ)
    (hx : spaceLPOptimal I w c i u x) (j : Option (Fin n))
    (hj : ∀ k, (0 < x k ∧ x k < 1) ↔ j = some k) :
    ∀ T : Finset (Fin n), spaceFeasible w c i T →
      assortmentUtility I i u T ≤
        2 * max (assortmentUtility I i u (rounded x))
          (match j with | none => 0 | some k => utility I i u k) := by
  intro T hT
  have hbound := KnapsackRounding.integer_le_lp (w i) (utility I i u) x (c i) hx T hT
  have hsplit := KnapsackRounding.objective_split (utility I i u) x hx.1.1 j hj
  change assortmentUtility I i u T ≤ _ at hbound
  change knapsackLPObjective (utility I i u) x =
    assortmentUtility I i u (rounded x) + _ at hsplit
  cases j with
  | none =>
    simp only [add_zero] at hsplit
    have hmax := le_max_left (assortmentUtility I i u (rounded x)) (0 : ℝ)
    have hnonneg := le_max_right (assortmentUtility I i u (rounded x)) (0 : ℝ)
    dsimp
    linarith
  | some k =>
    have hk := (hj k).mpr rfl
    have ha := KnapsackRounding.support_nonneg (w i) (utility I i u) x (c i)
      (fun l => (hw l).le) hx k hk.1
    have hprod : utility I i u k * x k ≤ utility I i u k :=
      mul_le_of_le_one_right ha (hx.1.1 k).2
    have hmax₁ := le_max_left (assortmentUtility I i u (rounded x)) (utility I i u k)
    have hmax₂ := le_max_right (assortmentUtility I i u (rounded x)) (utility I i u k)
    dsimp at hsplit ⊢
    linarith

#print axioms solution

end PriorRounding

namespace RoundedUniformFamily
open ConstrNestedLogit.Space

lemma rounded_feasible {n : ℕ} (w x : Fin n → ℝ) (c : ℝ)
    (hw : ∀ j, 0 ≤ w j) (hx : knapsackLPFeasible w c x) :
    (∑ j ∈ rounded x, w j) ≤ c := by
  classical
  have h (j : Fin n) : (if x j = 1 then w j else 0) ≤ w j * x j := by
    by_cases hj : x j = 1
    · simp [hj]
    · simpa [hj] using mul_nonneg (hw j) (hx.1 j).1
  calc
    _ = ∑ j, if x j = 1 then w j else 0 := by simp [rounded, Finset.sum_filter]
    _ ≤ ∑ j, w j * x j := Finset.sum_le_sum (fun j _ => h j)
    _ ≤ c := hx.2

lemma value_identity {ι : Type*} {n : ℕ} (I : NestedLogitVariants.LP.Instance ι n)
    (i : ι) (hvnp : I.vnp i = 0) (hvpref : ∀ j, 0 < I.v i j) (u : ℝ)
    (S : Finset (Fin n)) :
    NestedLogitVariants.LP.V I i S * (NestedLogitVariants.LP.R I i S - u) =
      assortmentUtility I i u S := by
  classical
  by_cases hS : S = ∅
  · simp [hS, NestedLogitVariants.LP.V, NestedLogitVariants.LP.R, hvnp, assortmentUtility]
  · have hV : 0 < NestedLogitVariants.LP.V I i S := by
      simpa [NestedLogitVariants.LP.V, hvnp] using
        Finset.sum_pos (fun j (_ : j ∈ S) => hvpref j) (Finset.nonempty_iff_ne_empty.mpr hS)
    rw [NestedLogitVariants.LP.R, mul_sub]
    rw [mul_div_cancel₀ _ (ne_of_gt hV)]
    simp only [NestedLogitVariants.LP.V, hvnp, zero_add, assortmentUtility, utility,
      mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

lemma fractional_option {n : ℕ} (x : Fin n → ℝ) (hf : atMostOneFractional x) :
    ∃ j : Option (Fin n), ∀ k, (0 < x k ∧ x k < 1) ↔ j = some k := by
  classical
  by_cases h : ∃ j, 0 < x j ∧ x j < 1
  · obtain ⟨j,hj⟩ := h
    refine ⟨some j,?_⟩
    intro k
    constructor
    · intro hk
      have he := hf k j hk.1 hk.2 hj.1 hj.2
      simp [he]
    · intro he
      have he' := Option.some.inj he
      simpa [← he'] using hj
  · refine ⟨none,?_⟩
    intro k
    constructor
    · intro hk
      exact (h ⟨k,hk⟩).elim
    · intro hk
      cases hk

end RoundedUniformFamily

open ConstrNestedLogit.Space

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (w : ι → Fin n → ℝ) (c : ι → ℝ) (i : ι)
    (hn : 0 < n)
    (hvnp : ∀ i, I.vnp i = 0) (hvpref : ∀ j, 0 < I.v i j)
    (hw : ∀ j, 0 < w i j) (hwc : ∀ j, w i j ≤ c i) :
    ∃ A : Finset (Finset (Fin n)),
      isRoundedCandidateFamily I w c i A ∧
      (∀ S ∈ A, spaceFeasible w c i S) ∧
      A.card ≤ (n + 1) ^ 2 ∧
      ∀ u : ℝ, 0 ≤ u → ∃ S ∈ A, isApproximateAt I w c i u 2 S := by
  classical
  have hc : 0 ≤ c i := (hw ⟨0,hn⟩).le.trans (hwc ⟨0,hn⟩)
  obtain ⟨V,X,hcard,hV,hcover⟩ := UniformKnapsack.uniform_points I w c i hw hc
  let A := V.image (fun v => rounded (X v)) ∪
    (Finset.univ : Finset (Fin n)).image (fun j => ({j} : Finset (Fin n)))
  have hround (v : ℝ) (hv : v ∈ V) : rounded (X v) ∈ A :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  have hsingle (j : Fin n) : ({j} : Finset (Fin n)) ∈ A :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  have hfeas : ∀ S ∈ A, spaceFeasible w c i S := by
    intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hS
      exact RoundedUniformFamily.rounded_feasible (w i) (X v) (c i)
        (fun j => (hw j).le) (hV v hv).2.1.1
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hS
      simpa [spaceFeasible] using hwc j
  have hempty : (∅ : Finset (Fin n)) ∈ A := by
    let u : ℝ := ∑ j, max (I.r i j) 0
    have hu : 0 ≤ u := Finset.sum_nonneg (fun j _ => le_max_right _ _)
    obtain ⟨v,hv,hopt,hpos⟩ := hcover u hu
    have he : rounded (X v) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj1 := (Finset.mem_filter.mp hj).2
      have hp := hpos j (by rw [hj1]; norm_num)
      have hr : I.r i j ≤ u := (le_max_left _ _).trans
        (Finset.single_le_sum (fun k _ => le_max_right (I.r i k) 0) (Finset.mem_univ j))
      have hn : utility I i u j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hvpref j).le (sub_nonpos.mpr hr)
      exact not_lt_of_ge hn hp
    rw [← he]
    exact hround v hv
  refine ⟨A,⟨hempty,hsingle,?_⟩,hfeas,?_,?_⟩
  · intro S hS
    rcases Finset.mem_union.mp hS with hS | hS
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hS
      exact Or.inr ⟨v,(hV v hv).1,X v,(hV v hv).2.1,(hV v hv).2.2,rfl⟩
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hS
      exact Or.inl ⟨j,rfl⟩
  · have ha := Finset.card_union_le (V.image (fun v => rounded (X v)))
        ((Finset.univ : Finset (Fin n)).image (fun j => ({j} : Finset (Fin n))))
    have hvcard : (V.image (fun v => rounded (X v))).card ≤ V.card := Finset.card_image_le
    have hjcard : ((Finset.univ : Finset (Fin n)).image (fun j => ({j} : Finset (Fin n)))).card ≤ n :=
      Finset.card_image_le.trans (by simp)
    dsimp [A]
    nlinarith
  · intro u hu
    obtain ⟨v,hv,hopt,hpos⟩ := hcover u hu
    obtain ⟨j,hj⟩ := RoundedUniformFamily.fractional_option (X v) (hV v hv).2.2
    let E : Finset (Fin n) := match j with | none => ∅ | some k => {k}
    have hE : E ∈ A := by cases j with
      | none => exact hempty
      | some k => exact hsingle k
    have hEU : (match j with | none => 0 | some k => utility I i u k) =
        assortmentUtility I i u E := by cases j <;> simp [E,assortmentUtility]
    have hb (T : Finset (Fin n)) (hT : spaceFeasible w c i T) :
        assortmentUtility I i u T ≤ 2 * max (assortmentUtility I i u (rounded (X v)))
          (assortmentUtility I i u E) := by
      have h := PriorRounding.solution I w c i hvnp hvpref hw hwc u hu (X v) hopt j hj T hT
      cases j <;> simpa [E, assortmentUtility] using h
    have he (S : Finset (Fin n)) := RoundedUniformFamily.value_identity I i (hvnp i) hvpref u S
    by_cases hh : assortmentUtility I i u E ≤ assortmentUtility I i u (rounded (X v))
    · refine ⟨rounded (X v),hround v hv,hfeas _ (hround v hv),?_⟩
      intro T hT
      rw [he T, he (rounded (X v))]
      simpa only [max_eq_left hh] using hb T hT
    · refine ⟨E,hE,hfeas _ hE,?_⟩
      intro T hT
      rw [he T,he E]
      simpa only [max_eq_right (le_of_not_ge hh)] using hb T hT

#print axioms solution
