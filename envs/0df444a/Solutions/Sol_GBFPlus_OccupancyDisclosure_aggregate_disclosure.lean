-- Prove2me | solution 1 for GBFPlus.OccupancyDisclosure.aggregate_disclosure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:56:29.704506+00:00
-- url     : https://prove2.me/submissions/0408ee17-7e28-41a0-910a-a376612dce1a

import Mathlib
import Definitions.Def_GBFPlus_OccupancyDisclosure

namespace GBFPlus.OccupancyDisclosure

theorem x5gb_two {C : Config} (w : Word C) : w + w = 0 := by
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  ext i <;> simp [h]

theorem x5gb_mem_occ {C : Config} (A : Snapshot C) (i : Fin C.cells) :
    i ∈ occupied A ↔ (A i).isSome := by
  simp [occupied]

theorem x5gb_ins_old {C : Config} (A : Snapshot C) (r : Row C) (p : Fin C.cells)
    (free : Fin C.cells → Word C) (hp : A p = none) (i : Fin C.cells) (hi : (A i).isSome) :
    insert A r p free i = A i := by
  have hip : i ≠ p := by rintro rfl; simp [hp] at hi
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hi
  unfold insert
  split_ifs <;> simp_all [fillWord]

theorem x5gb_ins_occ {C : Config} (A : Snapshot C) (r : Row C) (p : Fin C.cells)
    (free : Fin C.cells → Word C) :
    occupied (insert A r p free) = occupied A ∪ r.support := by
  ext i
  simp only [x5gb_mem_occ, Finset.mem_union, insert]
  split_ifs with h <;> simp [h]

theorem x5gb_ins_new {C : Config} (A : Snapshot C) (r : Row C) (p : Fin C.cells)
    (free : Fin C.cells → Word C) (hp : p ∈ r.support) :
    rowXor (insert A r p free) r = r.target := by
  unfold rowXor
  rw [← Finset.add_sum_erase _ _ hp]
  have h1 : ∀ i ∈ r.support.erase p, payload (insert A r p free) i = fillWord A free i := by
    intro i hi
    have := Finset.mem_erase.mp hi
    simp [payload, insert, this.1, this.2]
  rw [Finset.sum_congr rfl h1]
  simp only [payload, insert, hp, if_true, Option.getD_some]
  rw [add_assoc, x5gb_two, add_zero]

def x5gb_inv {C : Config} (A : Snapshot C) (L : List (Row C)) : Prop :=
  ∀ r ∈ L, r.support ⊆ occupied A ∧ rowXor A r = r.target

theorem x5gb_step_inv {C : Config} (A : Snapshot C) (r : Row C) (p : Fin C.cells)
    (free : Fin C.cells → Word C) (hp : A p = none) (hpr : p ∈ r.support)
    (L : List (Row C)) (hL : x5gb_inv A L) :
    x5gb_inv (insert A r p free) (L ++ [r]) := by
  intro s hs
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨h1, h2⟩ := hL s hs
    refine ⟨?_, ?_⟩
    · rw [x5gb_ins_occ]; exact h1.trans Finset.subset_union_left
    · rw [← h2]; unfold rowXor
      refine Finset.sum_congr rfl fun i hi => ?_
      have := (x5gb_mem_occ A i).mp (h1 hi)
      simp [payload, x5gb_ins_old A r p free hp i this]
  · simp only [List.mem_singleton] at hs
    subst hs
    refine ⟨?_, x5gb_ins_new A s p free hpr⟩
    rw [x5gb_ins_occ]; exact Finset.subset_union_right

theorem x5gb_gen {C : Config} : ∀ (es : List (Attempt C)) (A : Snapshot C) (L : List (Row C)),
    Honest A es → x5gb_inv A L →
    occupied (run A es) = (successful es).foldl (fun U r => U ∪ r.support) (occupied A) ∧
    x5gb_inv (run A es) (L ++ successful es)
  | [], A, L, _, hL => by simpa [run, successful] using hL
  | e :: es, A, L, h, hL => by
    obtain ⟨ha, h⟩ := h
    rcases e with ⟨r, _ | p, free⟩
    · have hs : step A ⟨r, none, free⟩ = A := rfl
      rw [hs] at h
      have := x5gb_gen es A L h hL
      simpa [run, successful, hs] using this
    · have hs : step A ⟨r, some p, free⟩ = insert A r p free := rfl
      rw [hs] at h
      simp only [admissible] at ha
      have := x5gb_gen es _ _ h (x5gb_step_inv A r p free ha.2 ha.1 L hL)
      have hsucc : successful (⟨r, some p, free⟩ :: es) = r :: successful es := rfl
      rw [hsucc]
      refine ⟨?_, ?_⟩
      · simp only [run, hs, this.1, x5gb_ins_occ, List.foldl_cons]
      · simpa [run, hs, List.append_assoc] using this.2

theorem x5gb_main {C : Config} (es : List (Attempt C)) (h : Honest (empty C) es) :
    occupied (finalSnapshot es) = supportUnion (successful es) ∧
    ∀ r ∈ successful es, r.support ⊆ occupied (finalSnapshot es) ∧
      rowXor (finalSnapshot es) r = r.target := by
  have h0 : occupied (empty C) = ∅ := by ext i; simp [occupied, empty]
  have := x5gb_gen es (empty C) [] h (by intro r hr; simp at hr)
  refine ⟨?_, ?_⟩
  · rw [finalSnapshot, this.1, h0]; rfl
  · intro r hr; exact this.2 r (by simpa using hr)

theorem x5gb_card {C : Config} : ∀ (rs : List (Row C)) (U : Finset (Fin C.cells)),
    (rs.foldl (fun U r => U ∪ r.support) U).card ≤ U.card + rs.length * C.shares ∧
    ((rs.foldl (fun U r => U ∪ r.support) U).card = U.card + rs.length * C.shares →
      rs.Pairwise (fun r s => Disjoint r.support s.support) ∧ ∀ r ∈ rs, Disjoint U r.support)
  | [], U => by simp
  | r :: rs, U => by
    obtain ⟨h1, h2⟩ := x5gb_card rs (U ∪ r.support)
    have hu : (U ∪ r.support).card ≤ U.card + C.shares := by
      rw [← r.support_card]; exact Finset.card_union_le _ _
    simp only [List.foldl_cons, List.length_cons] at h1 h2 ⊢
    refine ⟨by nlinarith, fun heq => ?_⟩
    have hU : (U ∪ r.support).card = U.card + C.shares := by nlinarith
    obtain ⟨hp, hd⟩ := h2 (by nlinarith)
    have hdisj : Disjoint U r.support := by
      rw [← Finset.card_union_eq_card_add_card, hU, r.support_card]
    refine ⟨List.pairwise_cons.mpr ⟨fun s hs => ?_, hp⟩, ?_⟩
    · exact (hd s hs).mono_left Finset.subset_union_right
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact hdisj
      · exact (hd s hs).mono_left Finset.subset_union_left

theorem x5gb_sum {C : Config} {M : Type*} [AddCommMonoid M] (g : Fin C.cells → M) :
    ∀ (rs : List (Row C)) (U : Finset (Fin C.cells)),
    rs.Pairwise (fun r s => Disjoint r.support s.support) → (∀ r ∈ rs, Disjoint U r.support) →
    ∑ i ∈ rs.foldl (fun U r => U ∪ r.support) U, g i =
      ∑ i ∈ U, g i + (rs.map fun r => ∑ i ∈ r.support, g i).sum
  | [], U, _, _ => by simp
  | r :: rs, U, hp, hd => by
    obtain ⟨hr, hp⟩ := List.pairwise_cons.mp hp
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [x5gb_sum g rs (U ∪ r.support) hp ?_, Finset.sum_union (hd r (by simp)), add_assoc]
    intro s hs
    exact Finset.disjoint_union_left.mpr ⟨hd s (by simp [hs]), hr s hs⟩

end GBFPlus.OccupancyDisclosure

namespace GBFPlus.OccupancyDisclosure

theorem x5gb_ident {C : Config} : ∀ rs : List (Row C),
    ((rs.map Row.target).sum).2 = identifierXor rs
  | [] => by simp [identifierXor]
  | r :: rs => by
    have := x5gb_ident rs
    simp only [identifierXor] at this ⊢
    simp [List.sum_cons, Prod.snd_add, this, Row.target]

theorem x5gb_disj {C : Config} (es : List (Attempt C)) (h : Honest (empty C) es)
    (hcount : (occupied (finalSnapshot es)).card = (successful es).length * C.shares) :
    (successful es).Pairwise (fun r s => Disjoint r.support s.support) := by
  have h1 := (x5gb_main es h).1
  rw [h1, supportUnion] at hcount
  exact ((x5gb_card (successful es) ∅).2 (by simpa using hcount)).1

theorem x5gb_agg {C : Config} (es : List (Attempt C)) (h : Honest (empty C) es)
    (hcount : (occupied (finalSnapshot es)).card = (successful es).length * C.shares) :
    recover (finalSnapshot es) = identifierXor (successful es) := by
  obtain ⟨h1, h2⟩ := x5gb_main es h
  have hp := x5gb_disj es h hcount
  rw [recover, h1, supportUnion, x5gb_sum _ _ ∅ hp (by simp), Finset.sum_empty, zero_add,
    ← x5gb_ident]
  congr 2
  refine List.map_congr_left fun r hr => ?_
  exact (h2 r hr).2

end GBFPlus.OccupancyDisclosure

open GBFPlus.OccupancyDisclosure in
theorem solution (C : Config) (es : List (Attempt C))
    (h : Honest (empty C) es) (hpositive : 1 ≤ (successful es).length)
    (hcount : (occupied (finalSnapshot es)).card = (successful es).length * C.shares) :
    recover (finalSnapshot es) = identifierXor (successful es) :=
  x5gb_agg es h hcount
