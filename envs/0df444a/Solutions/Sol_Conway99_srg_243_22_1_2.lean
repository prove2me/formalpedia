-- Prove2me | solution 1 for Conway99.srg_243_22_1_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-06T17:18:49.545242+00:00
-- url     : https://prove2.me/submissions/a80c935a-3c43-4c48-803d-634ae2e7650b

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel

open SimpleGraph Finset

set_option maxRecDepth 40000

/-! ### Cayley graphs of finite abelian groups -/

/-- The Cayley graph of an abelian group with respect to a symmetric connection
set avoiding `0`. -/
private def cayley {G : Type} [AddCommGroup G] [DecidableEq G] (S : Finset G)
    (hS0 : (0 : G) ∉ S) (hSneg : ∀ s ∈ S, -s ∈ S) : SimpleGraph G where
  Adj x y := y - x ∈ S
  symm := ⟨fun x y h => by simpa using hSneg _ h⟩
  loopless := ⟨fun x h => hS0 (by simpa using h)⟩

private instance cayleyDec {G : Type} [AddCommGroup G] [DecidableEq G] (S : Finset G)
    (hS0 : (0 : G) ∉ S) (hSneg : ∀ s ∈ S, -s ∈ S) :
    DecidableRel (cayley S hS0 hSneg).Adj :=
  fun x y => decidable_of_iff (y - x ∈ S) Iff.rfl

/-- A Cayley graph is strongly regular as soon as the number of ways of writing a
nonzero group element as a difference of two connection-set elements depends only
on whether that element is itself in the connection set. -/
private theorem cayley_isSRG {G : Type} [Fintype G] [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (hS0 : (0 : G) ∉ S) (hSneg : ∀ s ∈ S, -s ∈ S)
    (n k l m : ℕ) (hn : Fintype.card G = n) (hk : S.card = k)
    (hcount : ∀ d : G, d ≠ 0 →
      (S.filter fun w => w - d ∈ S).card = if d ∈ S then l else m) :
    (cayley S hS0 hSneg).IsSRGWith n k l m := by
  classical
  set g := cayley S hS0 hSneg with hg
  have hinj : ∀ x : G, Function.Injective (fun s : G => x + s) := by
    intro x a b hab
    simpa using hab
  have hdeg : ∀ x : G, g.degree x = S.card := by
    intro x
    have hset : g.neighborFinset x = S.image (fun s => x + s) := by
      ext y
      simp only [mem_neighborFinset, Finset.mem_image]
      constructor
      · intro h
        exact ⟨y - x, h, by abel⟩
      · rintro ⟨s, hs, rfl⟩
        have : x + s - x = s := by abel
        show x + s - x ∈ S
        rw [this]; exact hs
    show (g.neighborFinset x).card = S.card
    rw [hset, Finset.card_image_of_injective _ (hinj x)]
  have hcn : ∀ x y : G, Fintype.card (g.commonNeighbors x y)
      = (S.filter fun w => w - (y - x) ∈ S).card := by
    intro x y
    rw [← Set.toFinset_card]
    have hset : (g.commonNeighbors x y).toFinset
        = (S.filter fun w => w - (y - x) ∈ S).image (fun w => x + w) := by
      ext u
      simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, Finset.mem_image,
        Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨u - x, ⟨h1, ?_⟩, by abel⟩
        have he : u - x - (y - x) = u - y := by abel
        rw [he]; exact h2
      · rintro ⟨w, ⟨hw, hw2⟩, rfl⟩
        constructor
        · show x + w - x ∈ S
          have : x + w - x = w := by abel
          rw [this]; exact hw
        · show x + w - y ∈ S
          have : x + w - y = w - (y - x) := by abel
          rw [this]; exact hw2
    rw [hset, Finset.card_image_of_injective _ (hinj x)]
  refine ⟨hn, ?_, ?_, ?_⟩
  · intro x
    rw [hdeg x, hk]
  · intro x y hxy
    have hd : y - x ∈ S := hxy
    have hdne : y - x ≠ 0 := by
      intro hz
      exact hS0 (hz ▸ hd)
    rw [hcn x y, hcount _ hdne, if_pos hd]
  · intro x y hne hnadj
    have hd : y - x ∉ S := hnadj
    have hdne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [hcn x y, hcount _ hdne, if_neg hd]

/-! ### The Berlekamp–van Lint–Seidel graph -/

/-- The syndrome space `GF(3)^5` of the perfect ternary Golay code. -/
private abbrev G5 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

/-- The `22` syndromes of the weight-one vectors of `GF(3)^11`, i.e. `±` the
eleven columns of a parity check matrix of the perfect ternary Golay code. -/
private def Sgolay : Finset G5 :=
  {(0,0,0,0,1), (0,0,0,0,2), (0,0,0,1,0), (0,0,0,2,0), (0,0,1,0,0), (0,0,2,0,0),
   (0,1,0,0,0), (0,1,1,1,1), (0,2,0,0,0), (0,2,2,2,2), (1,0,0,0,0), (1,0,1,1,2),
   (1,1,0,2,1), (1,1,2,0,2), (1,2,1,2,0), (1,2,2,1,1), (2,0,0,0,0), (2,0,2,2,1),
   (2,1,1,2,2), (2,1,2,1,0), (2,2,0,1,2), (2,2,1,0,1)}

private theorem hS0 : (0 : G5) ∉ Sgolay := by decide

private theorem hSneg : ∀ s ∈ Sgolay, -s ∈ Sgolay := by decide

theorem solution : ∃ (α : Type) (_ : Fintype α) (g : SimpleGraph α)
    (_ : DecidableRel g.Adj), IsSRGWith g 243 22 1 2 := by
  refine ⟨G5, inferInstance, cayley Sgolay hS0 hSneg, cayleyDec _ _ _, ?_⟩
  refine cayley_isSRG Sgolay hS0 hSneg 243 22 1 2 (by decide) (by decide) ?_
  decide +kernel
