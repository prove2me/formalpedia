-- Prove2me | solution 1 for CumulativeBlockCode.capacity_and_fidelity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T22:31:42.642792+00:00
-- url     : https://prove2.me/submissions/296ca3f0-9f49-40ce-897a-d85af96eaa1b

import Definitions.Def_CumulativeCrossingBlocks

open CumulativeBlockCode

variable {Header Cell : Type}

private def readBlocks (reversePrefix : List Cell) : List (Option Cell) → List (List Cell)
  | [] => []
  | none :: tail => reversePrefix.reverse :: readBlocks [] tail
  | some x :: tail => readBlocks (x :: reversePrefix) tail

private theorem read_prefix (xs acc : List Cell) (tail : List (Option Cell)) :
    readBlocks acc (xs.map some ++ none :: tail) =
      (acc.reverse ++ xs) :: readBlocks [] tail := by
  induction xs generalizing acc with
  | nil => simp [readBlocks]
  | cons x xs ih =>
    simp only [List.map_cons,List.cons_append,readBlocks,ih,List.reverse_cons,List.append_assoc,
      List.nil_append]

private theorem read_markBlocks (xs : List (List Cell)) :
    readBlocks [] (markBlocks xs) = xs := by
  induction xs with
  | nil => rfl
  | cons cells rest ih =>
    simp only [markBlocks,read_prefix,List.reverse_nil,List.nil_append,ih]

private theorem markBlocks_length (cells : List (List Cell)) :
    (markBlocks cells).length = cells.length+(cells.map List.length).sum := by
  induction cells with
  | nil => rfl
  | cons head rest ih =>
    simp only [markBlocks,List.length_append,List.length_map,List.length_cons,ih,List.map_cons,List.sum_cons]
    omega

private theorem pad_faithful {A : Type} {bound : ℕ} {xs ys : List A}
    (fitsX : xs.length ≤ bound) (fitsY : ys.length ≤ bound)
    (eq : pad bound xs = pad bound ys) : xs = ys := by
  apply List.ext_getElem?
  intro i
  by_cases within : i < bound
  · exact congrFun eq ⟨i,within⟩
  · have after := Nat.le_of_not_gt within
    rw [List.getElem?_eq_none_iff.mpr (fitsX.trans after),
      List.getElem?_eq_none_iff.mpr (fitsY.trans after)]

theorem capacity [Fintype Header] [Fintype Cell] (r s : ℕ) :
    Fintype.card (Code Header Cell r s) =
      (Fintype.card Header+1)^r * (Fintype.card Cell+2)^(r+s) := by
  simp only [Code,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_option]

private theorem zip_projections (trace : List (Header × List Cell)) :
    List.zip (trace.map Prod.fst) (trace.map Prod.snd) = trace := by
  induction trace with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨header,cells⟩
    simp only [List.map_cons,List.zip_cons_cons,ih]

/-- A total bound over all blocks suffices even if the individual lengths
differ. Sentinel padding is distinguishable from each live delimiter. -/
theorem faithful {r s : ℕ} {x y : List (Header × List Cell)}
    (xBlocks : x.length ≤ r) (xCells : totalCells x ≤ s)
    (yBlocks : y.length ≤ r) (yCells : totalCells y ≤ s)
    (equal : encode r s x = encode r s y) : x = y := by
  have markFits (z : List (Header × List Cell)) (blocks : z.length ≤ r)
      (cells : totalCells z ≤ s) : (markBlocks (z.map Prod.snd)).length ≤ r+s := by
    rw [markBlocks_length,List.length_map,List.map_map]
    exact Nat.add_le_add blocks cells
  have headers : x.map Prod.fst = y.map Prod.fst :=
    pad_faithful (by simpa only [List.length_map] using xBlocks)
      (by simpa only [List.length_map] using yBlocks) (congrArg Prod.fst equal)
  have marked : markBlocks (x.map Prod.snd) = markBlocks (y.map Prod.snd) :=
    pad_faithful (markFits x xBlocks xCells) (markFits y yBlocks yCells) (congrArg Prod.snd equal)
  have bodies : x.map Prod.snd = y.map Prod.snd := by
    simpa only [read_markBlocks] using congrArg (readBlocks []) marked
  calc
    x = List.zip (x.map Prod.fst) (x.map Prod.snd) := (zip_projections x).symm
    _ = List.zip (y.map Prod.fst) (y.map Prod.snd) := by rw [headers,bodies]
    _ = y := zip_projections y

theorem solution {Header Cell : Type} [Fintype Header] [Fintype Cell] (blocks cells : ℕ) :
    Fintype.card (Code Header Cell blocks cells) =
      (Fintype.card Header+1)^blocks * (Fintype.card Cell+2)^(blocks+cells) ∧
    (∀ (x y : List (Header × List Cell)),
      x.length ≤ blocks → totalCells x ≤ cells → y.length ≤ blocks → totalCells y ≤ cells →
      encode blocks cells x = encode blocks cells y → x = y) := by
  refine ⟨capacity blocks cells,?_⟩
  intro x y xBlocks xCells yBlocks yCells eq
  exact faithful xBlocks xCells yBlocks yCells eq

#print axioms solution
