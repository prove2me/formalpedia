-- Prove2me | solution 2 for DeletionHash.MixedEdit.nonseparated_thin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:09:45.530357+00:00
-- url     : https://prove2.me/submissions/c0086cde-7b86-4554-bea0-c62f0a1adca5

import Definitions.Def_DeletionHash_MixedEdit_ConflictGraph
import Definitions.Def_DeletionHash_MixedEdit_Labels
import Definitions.Def_DeletionHash_MixedEdit_UniqueWords
import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Dist
import Theorems.Thm_DeletionHash_MixedEdit_independent_differences
import Theorems.Thm_DeletionHash_MixedEdit_parity_distinguishes

namespace DeletionGraph.HashUniform
open DeletionHash.MixedEdit
universe u
theorem joint {α : Type u} [Fintype α] [DecidableEq α] {L r R : ℕ}
    (w : Fin R → Spectrum α L)
    (hw : LinearIndependent (ZMod 2) (fun i => parity (w i))) (a : Fin R → Label r) :
    uniformProbability (fun ξ : HashSample α L r => ∀ i, hash ξ (w i) = a i) =
      1 / ((2 : ℝ)^r)^R := by
  by_cases hr : 1≤r
  · exact (DeletionHash.MixedEdit.independent_differences L r R 0 0 0 hr w hw).1 a
  · have hr0 : r=0 := by omega
    subst r
    have he : (fun ξ : HashSample α L 0 => ∀ i, hash ξ (w i) = a i) = (fun _ => True) := by
      funext ξ
      apply propext
      exact ⟨fun _ => trivial, fun _ _ => Subsingleton.elim _ _⟩
    rw [he]
    simp [uniformProbability,Nat.card_eq_fintype_card]
theorem single {α : Type u} [Fintype α] [DecidableEq α] {L r : ℕ}
    (v : Spectrum α L) (hv : parity v ≠ 0) :
    uniformProbability (fun ξ : HashSample α L r => hash ξ v = 0) = 1 / (2:ℝ)^r := by
  have hi : LinearIndependent (ZMod 2) (fun _ : Fin 1 => parity v) := by
    rw [linearIndependent_unique_iff]
    exact hv
  simpa using joint (r:=r) (fun _ : Fin 1 => v) hi (fun _ => 0)
end DeletionGraph.HashUniform
/- Adapted from Eyal En Gad, deletion-codes-lean, commit 24d093a4 (Apache-2.0). Alphabet generalization preserves the original reconstruction proof. -/
namespace DeletionGraph.OverlapCollision
variable (α : Type*) [Fintype α]
abbrev Bits (n : ℕ) := Fin n → α
def padBits {n : ℕ} (x : Bits α n) (i : ℕ) : Option α :=
  if hi : i < n then some (x ⟨i, hi⟩) else none
def Agree (p : ℕ → Option α) (a : ℕ) (q : ℕ → Option α) (b k : ℕ) : Prop :=
  ∀ i, i < k → p (a+i) = q (b+i)

end DeletionGraph.OverlapCollision
namespace DeletionGraph.UniqueWordCount
open OverlapCollision
variable (α : Type*) [Fintype α] [DecidableEq α] [Nonempty α]
attribute [local instance] Classical.propDecidable

def KUnique (p : ℕ → Option α) (n k : ℕ) : Prop :=
  ∀ a b, a+k ≤ n → b+k ≤ n → Agree α p a p b k → a=b
noncomputable def uniqueWords (n k : ℕ) : Finset (Bits α n) := by
  classical
  exact Finset.univ.filter (fun x => KUnique α (padBits α x) n k)


end DeletionGraph.UniqueWordCount
namespace DeletionGraph.UniqueBridge
open DeletionHash.MixedEdit
universe u
variable {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]

theorem window_as_ofFn {n k a : ℕ} (x : Word α n) (ha : a+k ≤ n) :
    window k (letters x) a = List.ofFn (fun i : Fin k => x ⟨a+i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [window, letters, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [window, letters, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem window_eq_iff {n k a b : ℕ} (x : Word α n)
    (ha : a+k ≤ n) (hb : b+k ≤ n) :
    window k (letters x) a = window k (letters x) b ↔
      OverlapCollision.Agree α (OverlapCollision.padBits α x) a
        (OverlapCollision.padBits α x) b k := by
  rw [window_as_ofFn x ha, window_as_ofFn x hb, List.ofFn_inj]
  constructor
  · intro h i hi
    have he := congrFun h (⟨i, hi⟩ : Fin k)
    simpa only [OverlapCollision.padBits, dif_pos (show a+i<n by omega),
      dif_pos (show b+i<n by omega), Option.some.injEq] using he
  · intro h
    funext i
    have he := h i.val i.isLt
    simpa only [OverlapCollision.padBits, dif_pos (show a+i.val<n by omega),
      dif_pos (show b+i.val<n by omega), Option.some.injEq] using he

theorem unique_iff {n k : ℕ} (x : Word α n) :
    IsUnique k (letters x) ↔ UniqueWordCount.KUnique α (OverlapCollision.padBits α x) n k := by
  unfold IsUnique windows starts
  rw [List.nodup_map_iff_inj_on List.nodup_range]
  simp only [List.mem_range, letters, List.length_ofFn]
  constructor
  · intro h a b ha hb hab
    have hkn : k ≤ n := by omega
    apply h a (by simp only [if_pos hkn]; omega) b (by simp only [if_pos hkn]; omega)
    exact (window_eq_iff x ha hb).mpr hab
  · intro h a ha b hb hab
    by_cases hkn : k ≤ n
    · simp only [if_pos hkn] at ha hb
      exact h a b (by omega) (by omega) ((window_eq_iff x (by omega) (by omega)).mp hab)
    · simp only [if_neg hkn] at ha
      omega

theorem family_eq (n k : ℕ) : uniqueFamily α n k = UniqueWordCount.uniqueWords α n k := by
  classical
  ext x
  simp only [uniqueFamily, UniqueWordCount.uniqueWords, Finset.mem_filter,
    Finset.mem_univ, true_and, unique_iff]

end DeletionGraph.UniqueBridge

/-!
Counting tuples with an anchor near an endpoint or another anchor. The count
removes one coordinate, records the remaining tuple, and reconstructs the
omitted entry. Each distance constraint allows at most `2 * B` entries.
The right endpoint test is distance to `m`, so no bound on the anchors by `m`
is required. All cardinalities count actual tuples, including repeated anchors.
-/

namespace DeletionGraph.ClosePositions

open Finset

noncomputable section

attribute [local instance] Classical.propDecidable

/-- An endpoint-near or mutually close tuple of anchors. -/
def Bad {r n : ℕ} (m B : ℕ) (a : Fin r → Fin n) : Prop :=
  (∃ i, (a i).val < B) ∨
  (∃ i, Nat.dist (a i).val m < B) ∨
  (∃ i j, i ≠ j ∧ Nat.dist (a i).val (a j).val < B)

/-- A natural-number ball, intersected with `Fin n`, contains at most `2 * B` points. -/
theorem near_card_le (n c B : ℕ) :
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤ 2 * B := by
  calc
    (univ.filter (fun x : Fin n => Nat.dist x.val c < B)).card ≤
        (range (2 * B)).card := by
      apply Finset.card_le_card_of_injOn (fun x : Fin n => x.val + B - c)
      · intro x hx
        have hd := (mem_filter.mp hx).2
        change x.val + B - c ∈ range (2 * B)
        rw [mem_range]
        unfold Nat.dist at hd
        omega
      · intro x hx y hy heq
        have hx' := (mem_filter.mp hx).2
        have hy' := (mem_filter.mp hy).2
        change x.val + B - c = y.val + B - c at heq
        unfold Nat.dist at hx' hy'
        apply Fin.ext
        omega
    _ = 2 * B := card_range _

/-- Omitting one coordinate leaves exactly `n^r` possible records; each record
admits at most `M` values of the omitted coordinate. -/
theorem coordinate_constraint_card_le {r n : ℕ} (i : Fin (r + 1))
    (P : (Fin r → Fin n) → Fin n → Prop) (M : ℕ)
    (hM : ∀ b, (univ.filter (P b)).card ≤ M) :
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
      M * n ^ r := by
  let fibers : (Fin r → Fin n) → Finset (Fin (r + 1) → Fin n) :=
    fun b => (univ.filter (P b)).image (fun x => i.insertNth x b)
  have hcover :
      univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i)) ⊆
        (univ : Finset (Fin r → Fin n)).biUnion fibers := by
    intro a ha
    apply mem_biUnion.mpr
    refine ⟨i.removeNth a, mem_univ _, ?_⟩
    apply mem_image.mpr
    refine ⟨a i, mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ha).2⟩, ?_⟩
    exact Fin.insertNth_self_removeNth i a
  calc
    (univ.filter (fun a : Fin (r + 1) → Fin n => P (i.removeNth a) (a i))).card ≤
        ((univ : Finset (Fin r → Fin n)).biUnion fibers).card := card_le_card hcover
    _ ≤ (univ : Finset (Fin r → Fin n)).card * M :=
      card_biUnion_le_card_mul _ fibers M (fun b _ => (card_image_le).trans (hM b))
    _ = M * n ^ r := by simp [Nat.mul_comm]

/-- The reference point may depend on every coordinate except the constrained one. -/
theorem coordinate_near_card_le {r n : ℕ} (i : Fin (r + 1))
    (c : (Fin r → Fin n) → ℕ) (B : ℕ) :
    (univ.filter (fun a : Fin (r + 1) → Fin n =>
      Nat.dist (a i).val (c (i.removeNth a)) < B)).card ≤ (2 * B) * n ^ r := by
  have h := coordinate_constraint_card_le i (fun b x => Nat.dist x.val (c b) < B) (2 * B)
    (fun b => by
      apply le_of_eq_of_le ?_ (near_card_le n (c b) B)
      apply congrArg Finset.card
      ext x
      simp only [mem_filter, mem_univ, true_and])
  apply le_of_eq_of_le ?_ h
  apply congrArg Finset.card
  ext a
  simp only [mem_filter, mem_univ, true_and]

private abbrev EventIndex (r : ℕ) := Fin r × (Fin r ⊕ Bool)

private def Event {r n : ℕ} (m B : ℕ) (q : EventIndex r) (a : Fin r → Fin n) : Prop :=
  match q.2 with
  | .inl j => q.1 ≠ j ∧ Nat.dist (a q.1).val (a j).val < B
  | .inr false => (a q.1).val < B
  | .inr true => Nat.dist (a q.1).val m < B

private theorem event_card_le {r n : ℕ} (m B : ℕ) (q : EventIndex (r + 1)) :
    (univ.filter (Event (n := n) m B q)).card ≤ (2 * B) * n ^ r := by
  rcases q with ⟨i, s⟩
  cases s with
  | inl j =>
      by_cases hij : i = j
      · have hempty : univ.filter (Event (n := n) m B (i, .inl j)) = ∅ := by
          ext a
          simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty]
          change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔ False
          simp [hij]
        rw [hempty, card_empty]
        exact Nat.zero_le _
      · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (Ne.symm hij)
        apply le_of_eq_of_le ?_
          (coordinate_near_card_le (n := n) i (fun b => (b j').val) B)
        apply congrArg Finset.card
        ext a
        simp only [mem_filter, mem_univ, true_and]
        change (i ≠ j ∧ Nat.dist (a i).val (a j).val < B) ↔
          Nat.dist (a i).val (a (i.succAbove j')).val < B
        rw [hj']
        exact ⟨And.right, fun h => ⟨hij, h⟩⟩
  | inr b =>
      cases b with
      | false =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => 0) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          change (a i).val < B ↔ Nat.dist (a i).val 0 < B
          rw [Nat.dist_zero_right]
      | true =>
          apply le_of_eq_of_le ?_ (coordinate_near_card_le (n := n) i (fun _ => m) B)
          apply congrArg Finset.card
          ext a
          simp only [mem_filter, mem_univ, true_and]
          rfl

/-- A union bound over all actual endpoint and pair constraints. The exponent
is `r - 1`, and the theorem also covers `r = 0`, `n = 0`, and `B = 0`. -/
theorem bad_card_le (r n m B : ℕ) :
    (univ.filter (Bad (r := r) (n := n) m B)).card ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) := by
  cases r with
  | zero => simp [Bad]
  | succ r =>
      let events : EventIndex (r + 1) → Finset (Fin (r + 1) → Fin n) :=
        fun q => univ.filter (Event m B q)
      have hcover : univ.filter (Bad (r := r + 1) (n := n) m B) =
          (univ : Finset (EventIndex (r + 1))).biUnion events := by
        ext a
        simp only [mem_filter, mem_univ, true_and, mem_biUnion, events]
        constructor
        · rintro (⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, j, hij, hd⟩)
          · exact ⟨(i, .inr false), hi⟩
          · exact ⟨(i, .inr true), hi⟩
          · exact ⟨(i, .inl j), hij, hd⟩
        · rintro ⟨⟨i, s⟩, h⟩
          cases s with
          | inl j => exact Or.inr (Or.inr ⟨i, j, h⟩)
          | inr b =>
              cases b with
              | false => exact Or.inl ⟨i, h⟩
              | true => exact Or.inr (Or.inl ⟨i, h⟩)
      rw [hcover]
      calc
        ((univ : Finset (EventIndex (r + 1))).biUnion events).card ≤
            (univ : Finset (EventIndex (r + 1))).card * ((2 * B) * n ^ r) :=
          card_biUnion_le_card_mul _ events _ (fun q _ => event_card_le m B q)
        _ = (r + 1) * (r + 1 + 2) * (2 * B) * n ^ (r + 1 - 1) := by
          simp [EventIndex, Fintype.card_prod, Fintype.card_sum, Nat.mul_assoc]


end

end DeletionGraph.ClosePositions
namespace DeletionGraph.RecordCount
open DeletionHash.MixedEdit
universe u
variable (α : Type u) [Fintype α] [DecidableEq α]

abbrev Tag (b : ℕ) := Fin (b+1) × (Σ l : Fin (b+1), Fin l.val → α)
abbrev Record (b N r : ℕ) := (Fin r → Fin N) × (Fin r → Tag α b)

def decode {b N r : ℕ} (rec : Record α b N r) : List (Edit α) :=
  List.ofFn fun i => ⟨(rec.1 i).val, (rec.2 i).1.val, List.ofFn (rec.2 i).2.2⟩

theorem tag_card_le (b : ℕ) (hq : 1 ≤ Fintype.card α) :
    Fintype.card (Tag α b) ≤ (b+1)^2 * (Fintype.card α)^b := by
  classical
  simp only [Tag, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma, Fintype.card_fun]
  calc
    (b+1) * (∑ l : Fin (b+1), (Fintype.card α)^l.val) ≤
      (b+1) * (∑ _l : Fin (b+1), (Fintype.card α)^b) := by
        gcongr with l
        omega
    _ = (b+1)^2 * (Fintype.card α)^b := by simp; ring

theorem record_card (b N r : ℕ) :
    Fintype.card (Record α b N r) = N^r * (Fintype.card (Tag α b))^r := by
  simp [Record, Fintype.card_fun]

theorem bad_record_card_le (b N r n B : ℕ) :
    Nat.card {rec : Record α b N r // ClosePositions.Bad n B rec.1} ≤
      r*(r+2)*(2*B)*N^(r-1)*(Fintype.card (Tag α b))^r := by
  classical
  let e : {rec : Record α b N r // ClosePositions.Bad n B rec.1} ≃
      {a : Fin r → Fin N // ClosePositions.Bad n B a} × (Fin r → Tag α b) :=
    { toFun := fun rec => (⟨rec.val.1,rec.property⟩,rec.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin]
  apply Nat.mul_le_mul_right
  simpa only [Fintype.card_subtype] using ClosePositions.bad_card_le r N n B

theorem edited_length_le (b : ℕ) (x : List α) (e : Edit α) (he : ValidEdit b x e) :
    (applyEdit e x).length ≤ x.length+b := by
  have h1 := he.1
  have h2 := he.2.2.1
  simp only [applyEdit, List.length_append, List.length_take, List.length_drop]
  omega

theorem record_bounds (b : ℕ) (x : List α) (es : List (Edit α)) (he : ValidRecord b x es) :
    ∀ e ∈ es, e.position ≤ x.length+es.length*b ∧
      e.removed ≤ b ∧ e.replacement.length ≤ b := by
  induction es generalizing x with
  | nil => simp
  | cons e es ih =>
    obtain ⟨he,hes⟩ := he
    have hlen := edited_length_le α b x e he
    have hpos := he.1
    have htail := ih (applyEdit e x) hes
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨by simp only [List.length_cons]; omega, he.2.1, he.2.2.1⟩
    · obtain ⟨hp,hr,hl⟩ := htail f hf
      refine ⟨?_,hr,hl⟩
      simp only [List.length_cons]
      nlinarith

theorem encode_exists (b N : ℕ) (es : List (Edit α))
    (he : ∀ e ∈ es, e.position < N ∧ e.removed ≤ b ∧ e.replacement.length ≤ b) :
    ∃ rec : Record α b N es.length, decode α rec = es := by
  let positions : Fin es.length → Fin N := fun i =>
    ⟨(es.get i).position, (he (es.get i) (List.get_mem es i)).1⟩
  let tags : Fin es.length → Tag α b := fun i =>
    (⟨(es.get i).removed, by have h := (he (es.get i) (List.get_mem es i)).2.1; omega⟩,
     ⟨⟨(es.get i).replacement.length, by have h := (he (es.get i) (List.get_mem es i)).2.2; omega⟩,
      fun j => (es.get i).replacement.get j⟩)
  refine ⟨(positions,tags), ?_⟩
  unfold decode
  conv_rhs => rw [← List.ofFn_get es]
  congr 1
  funext i
  simp [positions, tags]


theorem not_separated_bad (n t b L r : ℕ)
    (rec : Record α b (n+2*t*b+1) r) (hnot : ¬ Separated n t b L (decode α rec)) :
    ClosePositions.Bad n (8*(L+t*b)+2*t*b+1) rec.1 := by
  by_contra hbad
  apply hnot
  simp only [ClosePositions.Bad, not_or, not_exists, not_and, not_lt] at hbad
  constructor
  · intro e he
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
    change 8*(L+t*b) ≤ (rec.1 i).val ∧ (rec.1 i).val+8*(L+t*b) ≤ n
    have hl := hbad.1 i
    have hr := hbad.2.1 i
    have hb := (rec.1 i).isLt
    unfold Nat.dist at hr
    constructor <;> omega
  · intro i j hij
    let i' : Fin r := ⟨i.val, by simpa [decode] using i.isLt⟩
    let j' : Fin r := ⟨j.val, by simpa [decode] using j.isLt⟩
    have hne : i' ≠ j' := by
      intro h
      apply hij
      apply Fin.ext
      simpa only [i', j'] using congrArg (fun z : Fin r => z.val) h
    have h := hbad.2.2 i' j' hne
    have hh : 8*(L+t*b) ≤ Nat.dist (rec.1 i').val (rec.1 j').val := by omega
    change 8*(L+t*b) ≤ Nat.dist ((decode α rec).get i).position ((decode α rec).get j).position
    dsimp only [decode]
    erw [List.get_ofFn, List.get_ofFn]
    exact hh

def decodeWord {b N r n : ℕ} (x : Word α n) (rec : Record α b N r) : Word α n :=
  fun i => (target (letters x) (decode α rec)).getD i.val (x i)

theorem decodeWord_eq {b N r n : ℕ} (x z : Word α n) (rec : Record α b N r)
    (he : target (letters x) (decode α rec) = letters z) : decodeWord α x rec = z := by
  funext i
  change (target (letters x) (decode α rec)).getD i.val (x i) = z i
  rw [he]
  simp [letters, List.getD, i.isLt]

noncomputable def shortPartners {n : ℕ} (t b : ℕ) (x : Word α n) : Finset (Word α n) := by
  classical
  exact (Finset.range (2*t)).biUnion fun r =>
    (Finset.univ : Finset (Record α b (n+2*t*b+1) r)).image (decodeWord α x)

noncomputable def fullPartners {n : ℕ} (t b L : ℕ) (x : Word α n) : Finset (Word α n) := by
  classical
  exact ((Finset.univ : Finset (Record α b (n+2*t*b+1) (2*t))).filter
    (fun rec => ClosePositions.Bad n (8*(L+t*b)+2*t*b+1) rec.1)).image (decodeWord α x)

theorem shortPartners_card_le {n : ℕ} (t b : ℕ) (x : Word α n) :
    (shortPartners α t b x).card ≤
      ∑ r ∈ Finset.range (2*t), (n+2*t*b+1)^r * (Fintype.card (Tag α b))^r := by
  classical
  unfold shortPartners
  apply le_trans Finset.card_biUnion_le
  apply Finset.sum_le_sum
  intro r hr
  exact Finset.card_image_le.trans (by simp [record_card])

theorem fullPartners_card_le {n : ℕ} (t b L : ℕ) (x : Word α n) :
    (fullPartners α t b L x).card ≤
      (2*t)*(2*t+2)*(2*(8*(L+t*b)+2*t*b+1))*(n+2*t*b+1)^(2*t-1)*
        (Fintype.card (Tag α b))^(2*t) := by
  classical
  unfold fullPartners
  apply Finset.card_image_le.trans
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    bad_record_card_le α b (n+2*t*b+1) (2*t) n (8*(L+t*b)+2*t*b+1)

theorem partners_cover {n : ℕ} (t b L : ℕ) (x z : Word α n) (es : List (Edit α))
    (hlen : es.length ≤ 2*t) (he : ValidRecord b (letters x) es)
    (hz : target (letters x) es = letters z)
    (hbad : es.length < 2*t ∨ ¬ Separated n t b L es) :
    z ∈ shortPartners α t b x ∪ fullPartners α t b L x := by
  classical
  have hb := record_bounds α b (letters x) es he
  obtain ⟨rec, hrec⟩ := encode_exists α b (n+2*t*b+1) es (by
    intro e he
    obtain ⟨hp,hr,hl⟩ := hb e he
    simp only [letters, List.length_ofFn] at hp
    have hmul := Nat.mul_le_mul_right b hlen
    exact ⟨by omega,hr,hl⟩)
  have hd := decodeWord_eq α x z rec (by rwa [hrec])
  by_cases hshort : es.length < 2*t
  · apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨es.length, Finset.mem_range.mpr hshort, Finset.mem_image.mpr ⟨rec, Finset.mem_univ _, hd⟩⟩
  · have heq : es.length = 2*t := by omega
    obtain ⟨rec', hrec'⟩ : ∃ rec' : Record α b (n+2*t*b+1) (2*t), decode α rec'=es := by
      have aux : ∀ (r : ℕ), es.length=r → ∃ rec' : Record α b (n+2*t*b+1) r, decode α rec'=es := by
        intro r h
        subst r
        exact ⟨rec,hrec⟩
      exact aux (2*t) heq
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨rec', Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, decodeWord_eq α x z rec' (by rwa [hrec'])⟩
    apply not_separated_bad α n t b L (2*t) rec'
    simpa only [hrec'] using hbad.resolve_left hshort


end DeletionGraph.RecordCount

namespace DeletionGraph.RecordArithmetic
open DeletionHash.MixedEdit RecordCount
universe u

def countConstant (t b : ℕ) : ℕ :=
  (2*t+(2*t)*(2*t+2)*(2*(9+10*t*b))) * (2*t*b+2)^(2*t-1) * (b+1)^(4*t)

theorem countConstant_pos (t b : ℕ) (ht : 1 ≤ t) : 0 < countConstant t b := by
  unfold countConstant
  positivity

theorem short_bound (N T R : ℕ) (hN : 1 ≤ N) (hT : 1 ≤ T) :
    (∑ r ∈ Finset.range R, N^r*T^r) ≤ R*T^R*N^(R-1) := by
  calc
    _ ≤ ∑ _r ∈ Finset.range R, T^R*N^(R-1) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr := Finset.mem_range.mp hr
      calc
        N^r*T^r ≤ N^(R-1)*T^R := by gcongr <;> omega
        _ = T^R*N^(R-1) := Nat.mul_comm _ _
    _ = R*T^R*N^(R-1) := by simp [Nat.mul_assoc]

theorem combined_bound (n t b L T q : ℕ) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hT : 1 ≤ T) (htag : T ≤ (b+1)^2*q^b) :
    (∑ r ∈ Finset.range (2*t), (n+2*t*b+1)^r*T^r) +
      (2*t)*(2*t+2)*(2*(8*(L+t*b)+2*t*b+1))*(n+2*t*b+1)^(2*t-1)*T^(2*t) ≤
      countConstant t b * L * n^(2*t-1) * q^(2*b*t) := by
  let N := n+2*t*b+1
  let B := 8*(L+t*b)+2*t*b+1
  let K := 9+10*t*b
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hB : B ≤ K*L := by
    dsimp [B,K]
    have h := Nat.mul_le_mul_left (10*t*b) hL
    nlinarith
  have hN' : N ≤ (2*t*b+2)*n := by
    dsimp [N]
    have h := Nat.mul_le_mul_left (2*t*b+1) hn
    nlinarith
  have htag' : T^(2*t) ≤ (b+1)^(4*t)*q^(2*b*t) := by
    calc
      T^(2*t) ≤ ((b+1)^2*q^b)^(2*t) := Nat.pow_le_pow_left htag _
      _ = (b+1)^(4*t)*q^(2*b*t) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> ring
  have hs := short_bound N T (2*t) hN hT
  change (∑ r ∈ Finset.range (2*t), N^r*T^r) +
    (2*t)*(2*t+2)*(2*B)*N^(2*t-1)*T^(2*t) ≤ _
  calc
    _ ≤ (2*t)*T^(2*t)*N^(2*t-1) +
      (2*t)*(2*t+2)*(2*B)*N^(2*t-1)*T^(2*t) := Nat.add_le_add_right hs _
    _ ≤ (2*t)*L*T^(2*t)*N^(2*t-1) +
      (2*t)*(2*t+2)*(2*(K*L))*N^(2*t-1)*T^(2*t) := by
        apply Nat.add_le_add
        · have hR : 2*t ≤ 2*t*L := by simpa using Nat.mul_le_mul_left (2*t) hL
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hR)
        · exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
            (Nat.mul_le_mul_left ((2*t)*(2*t+2)) (Nat.mul_le_mul_left 2 hB)))
    _ = (2*t+(2*t)*(2*t+2)*(2*K))*L*N^(2*t-1)*T^(2*t) := by ring
    _ ≤ (2*t+(2*t)*(2*t+2)*(2*K))*L*((2*t*b+2)*n)^(2*t-1)*
      ((b+1)^(4*t)*q^(2*b*t)) := by gcongr
    _ = countConstant t b * L * n^(2*t-1) * q^(2*b*t) := by
      rw [mul_pow]
      unfold countConstant K
      ring

theorem partners_card_le {α : Type u} [Fintype α] [DecidableEq α]
    {n : ℕ} (t b L : ℕ) (x : Word α n) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hq : 1 ≤ Fintype.card α) :
    (shortPartners α t b x ∪ fullPartners α t b L x).card ≤
      countConstant t b * L * n^(2*t-1) * (Fintype.card α)^(2*b*t) := by
  classical
  have ht : 1 ≤ Fintype.card (Tag α b) := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨(0, ⟨0, Fin.elim0⟩)⟩
  calc
    _ ≤ (shortPartners α t b x).card + (fullPartners α t b L x).card := Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add (shortPartners_card_le α t b x) (fullPartners_card_le α t b L x)
    _ ≤ _ := combined_bound n t b L (Fintype.card (Tag α b)) (Fintype.card α)
      hn hL ht (tag_card_le α b hq)

end DeletionGraph.RecordArithmetic
namespace DeletionGraph.ExceptionalProbability
open DeletionHash.MixedEdit
universe u v

theorem probability_mono {Ω : Type u} [Fintype Ω] {P Q : Ω → Prop}
    (h : ∀ x, P x → Q x) : uniformProbability P ≤ uniformProbability Q := by
  classical
  unfold uniformProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact_mod_cast Fintype.card_le_of_injective
    (fun x : {x // P x} => (⟨x.val,h x.val x.property⟩ : {x // Q x}))
    (fun x y he => Subtype.ext (congrArg (fun z : {x // Q x} => z.val) he))

theorem probability_union {Ω : Type u} [Fintype Ω] {β : Type v}
    (S : Finset β) (P : β → Ω → Prop) :
    uniformProbability (fun x => ∃ z ∈ S, P z x) ≤ ∑ z ∈ S, uniformProbability (P z) := by
  classical
  let E : β → Finset Ω := fun z => Finset.univ.filter (P z)
  have he : Finset.univ.filter (fun x => ∃ z ∈ S, P z x) = S.biUnion E := by
    ext x
    simp [E]
  simp only [uniformProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [he]
  have hc : (S.biUnion E).card ≤ ∑ z ∈ S, (E z).card := Finset.card_biUnion_le
  calc
    ((S.biUnion E).card : ℝ) / Fintype.card Ω ≤
        ((∑ z ∈ S, (E z).card : ℕ) : ℝ) / Fintype.card Ω := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hc
    _ = _ := by simp only [Nat.cast_sum, Finset.sum_div, E]

theorem hash_sub {α : Type u} [Fintype α] {L r : ℕ}
    (ξ : HashSample α L r) (p q : Spectrum α L) :
    DeletionHash.MixedEdit.hash ξ (p-q) =
      DeletionHash.MixedEdit.hash ξ p - DeletionHash.MixedEdit.hash ξ q := by
  simp [DeletionHash.MixedEdit.hash, parity, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem unique_mono {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {n k m : ℕ} (x : Word α n) (hk : k ≤ m) (hx : IsUnique k (letters x)) :
    IsUnique m (letters x) := by
  apply (UniqueBridge.unique_iff x).mpr
  intro a b ha hb hab
  apply (UniqueBridge.unique_iff x).mp hx a b (by omega) (by omega)
  intro i hi
  exact hab i (by omega)

theorem collision_bound {α : Type u} [Fintype α] [DecidableEq α] [Nonempty α]
    {n L r : ℕ} (x z : Word α n) (hL : 1 ≤ L) (hn : L ≤ n)
    (hx : IsUnique (L-1) (letters x))
    (hneq : z ≠ x → parity (spectrum L (letters z)-spectrum L (letters x)) ≠ 0) :
    uniformProbability (fun ξ : HashSample α L r =>
      z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) ≤
      1 / (2 : ℝ)^r := by
  classical
  by_cases hne : z=x
  · subst z
    simp [uniformProbability]
  · have hp := hneq hne
    have h := HashUniform.single (r := r) (spectrum L (letters z)-spectrum L (letters x)) hp
    simp only [hash_sub, sub_eq_zero] at h
    simpa [hne] using h.le


theorem exceptional_bound {α : Type u} [Fintype α] [DecidableEq α]
    (n t b k L r : ℕ) (hreg : Regime (Fintype.card α) n t b k L)
    (x : Word α n) (hx : IsUnique k (letters x)) :
    uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
      (RecordArithmetic.countConstant t b : ℝ) * (Fintype.card α : ℝ)^(2*b*t) *
        (L : ℝ) * (n : ℝ)^(2*t-1) / (2 : ℝ)^r := by
  classical
  obtain ⟨hq, ht, hb, hk, hL, hbk, hn⟩ := hreg
  letI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hLpos : 1 ≤ L := by omega
  have hnx : 1 ≤ n := by omega
  have hxm : IsUnique (L-1) (letters x) := unique_mono x (by omega) hx
  let S := RecordCount.shortPartners α t b x ∪ RecordCount.fullPartners α t b L x
  have hcover : ∀ ξ : HashSample α L r, Exceptional n k t b ξ x →
      ∃ z ∈ S, z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x)) := by
    intro ξ hex
    obtain ⟨_, es, hlen, hvalid, hword, hne, hhash, hbad⟩ := hex
    let y := target (letters x) es
    let z : Word α n := fun i => y.getD i.val (x i)
    have hz : letters z = y := by
      apply List.ext_getElem
      · simp only [letters, List.length_ofFn]
        exact hword.symm
      · intro i hi hj
        simp only [letters, List.getElem_ofFn, z, List.getD,
          List.getElem?_eq_getElem hj, Option.getD_some]
    have hz' : target (letters x) es = letters z := hz.symm
    refine ⟨z, RecordCount.partners_cover α t b L x z es hlen hvalid hz' hbad, ?_, ?_⟩
    · intro heq
      apply hne
      rw [hz', heq]
    · simpa only [hz] using hhash
  have hcard : (S.card : ℝ) ≤
      (RecordArithmetic.countConstant t b : ℝ) * L * (n : ℝ)^(2*t-1) *
        (Fintype.card α : ℝ)^(2*b*t) := by
    exact_mod_cast RecordArithmetic.partners_card_le t b L x hnx hLpos (by omega)
  calc
    _ ≤ uniformProbability (fun ξ : HashSample α L r =>
      ∃ z ∈ S, z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) :=
        probability_mono hcover
    _ ≤ ∑ z ∈ S, uniformProbability (fun ξ : HashSample α L r =>
      z ≠ x ∧ hash ξ (spectrum L (letters z)) = hash ξ (spectrum L (letters x))) := probability_union _ _
    _ ≤ ∑ _z ∈ S, 1 / (2 : ℝ)^r := by
      apply Finset.sum_le_sum
      intro z hz
      exact collision_bound x z hLpos hn hxm
        (DeletionHash.MixedEdit.parity_distinguishes n t b k L ⟨hq,ht,hb,hk,hL,hbk,hn⟩ x hxm z)
    _ = (S.card : ℝ) / (2 : ℝ)^r := by simp [div_eq_mul_inv]
    _ ≤ ((RecordArithmetic.countConstant t b : ℝ) * L * (n : ℝ)^(2*t-1) *
        (Fintype.card α : ℝ)^(2*b*t)) / (2 : ℝ)^r :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = _ := by ring


end DeletionGraph.ExceptionalProbability
open DeletionHash.MixedEdit

universe u

/-- Lemma 3.4: c precedes every alphabet, length and label dimension. -/
theorem solution (t b : ℕ) (ht : 2 ≤ t) (hb : 1 ≤ b) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (α : Type u) [Fintype α] [DecidableEq α],
      Fintype.card α = q → ∀ n k L r : ℕ, Regime q n t b k L → 1 ≤ r →
      ∀ x : Word α n, IsUnique k (letters x) →
      uniformProbability (fun ξ : HashSample α L r => Exceptional n k t b ξ x) ≤
        c * (q : ℝ)^(2*b*t) * (L : ℝ) * (n : ℝ)^(2*t-1) / (2 : ℝ)^r := by
  refine ⟨(DeletionGraph.RecordArithmetic.countConstant t b : ℝ), ?_, ?_⟩
  · exact_mod_cast DeletionGraph.RecordArithmetic.countConstant_pos t b (by omega)
  · intro q α instF instD hc n k L r hreg hr x hx
    subst q
    exact DeletionGraph.ExceptionalProbability.exceptional_bound n t b k L r hreg x hx



#print axioms solution
