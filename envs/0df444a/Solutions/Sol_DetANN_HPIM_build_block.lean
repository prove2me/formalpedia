-- Prove2me | solution 1 for DetANN.HPIM.build_block
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T21:44:37.256761+00:00
-- url     : https://prove2.me/submissions/94ded686-681f-42c3-b9f9-5aa591c49800

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_HPIMBuildProg
import Definitions.Def_DetANN_HPIMBuild
import Theorems.Thm_DetANN_HPIM_BD_scan_steps
import Theorems.Thm_DetANN_HPIM_BD_split_steps
import Theorems.Thm_DetANN_HPIM_BD_carve_steps
import Theorems.Thm_DetANN_HPIM_BD_loop_specs
import Theorems.Thm_DetANN_HPIM_BD_peel_specs

set_option Elab.async false

namespace DetANN.HPIM.QP
end DetANN.HPIM.QP
namespace DetANN.HPIM
end DetANN.HPIM
namespace DetANN.HPIM.PP
end DetANN.HPIM.PP
namespace DetANN.HPIM.SegStep
end DetANN.HPIM.SegStep
namespace DetANN.HPIM.BS
end DetANN.HPIM.BS

-- ===== QP_Work =====
open PNormReg PNormRegLib SmaleNinth

namespace DetANN.HPIM.QP

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

end DetANN.HPIM.QP

-- ===== PP_Prog =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

/-- The child blocks and their lengths. -/
structure Blocks where
  med : ℕ → Program
  comps : ℕ → Program
  build : ℕ → Program
  bal : ℕ → Program
  Lm : ℕ
  Lc : ℕ
  Lb : ℕ
  Lbal : ℕ

namespace Blocks

/-- Offset of piece 1. -/
def o1 (B : Blocks) : ℕ := 39

/-- Offset of piece 2. -/
def o2 (B : Blocks) : ℕ := 39 + 14

/-- Offset of piece 13. -/
def o13 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc + 29

/-- Offset of piece 14. -/
def o14 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc + 29 + B.Lc

end Blocks

end DetANN.HPIM.PP

-- ===== PP_Basic =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN

/-- `cellsWritten` over consecutive run segments. -/
lemma cellsWritten_add (P : Program) (s : State) (a b : ℕ) :
    cellsWritten P s (a + b) = cellsWritten P s a ∪ cellsWritten P (run P s detTape a) b := by
  ext c
  simp only [cellsWritten, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hc⟩
    by_cases hia : i < a
    · exact Or.inl ⟨i, hia, hc⟩
    · refine Or.inr ⟨i - a, by omega, ?_⟩
      rw [← run_add, Nat.add_sub_cancel' (by omega)]; exact hc
  · rintro (⟨i, hi, hc⟩ | ⟨i, hi, hc⟩)
    · exact ⟨i, by omega, hc⟩
    · exact ⟨a + i, by omega, by rw [run_add]; exact hc⟩

variable (B : Blocks)

end DetANN.HPIM.PP

-- ===== PP_Det =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN DetANN.HPIM

/-- One admissible deterministic instruction. -/
def Good (op : Instr) : Prop :=
  (match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True) ∧ (∀ r, op ≠ .coin r) ∧ (∀ r a e, op ≠ .rpow r a e)

lemma det_of_good {P : Program} (h : ∀ op ∈ P, Good op) : DetProgram P :=
  ⟨fun op hop => (h op hop).1, fun op hop => (h op hop).2⟩

lemma det_append {A B : Program} (hA : DetProgram A) (hB : DetProgram B) : DetProgram (A ++ B) := by
  refine ⟨fun op hop => ?_, fun op hop => ?_⟩
  · rcases List.mem_append.1 hop with h | h
    · exact hA.1 op h
    · exact hB.1 op h
  · rcases List.mem_append.1 hop with h | h
    · exact hA.2 op h
    · exact hB.2 op h

end DetANN.HPIM.PP

-- ===== BB_Pre =====
namespace DetANN.HPIM.BB

open DetANN.HPIM

variable {m : ℕ}

/-- The number of nodes. -/
def size : BSP m → ℕ
  | .leaf .. => 1
  | .cut _ _ l r => 1 + size l + size r

/-- The nodes in preorder: (path, subtree). -/
def pl : BSP m → List (List Bool × BSP m)
  | .leaf lo hi a => [([], .leaf lo hi a)]
  | .cut lo hi l r => ([], .cut lo hi l r) ::
      ((pl l).map (fun e => (false :: e.1, e.2)) ++ (pl r).map (fun e => (true :: e.1, e.2)))

lemma size_pos (T : BSP m) : 1 ≤ size T := by
  cases T <;> simp only [size] <;> omega

lemma pl_length (T : BSP m) : (pl T).length = size T := by
  induction T with
  | leaf => rfl
  | cut lo hi l r ihl ihr =>
    simp only [pl, List.length_cons, List.length_append, List.length_map, ihl, ihr, size]; omega

/-- The node at preorder index `i`. -/
def nd (T : BSP m) (i : ℕ) : List Bool × BSP m := ((pl T)[i]?).getD ([], T)

/-- Its path. -/
def P (T : BSP m) (i : ℕ) : List Bool := (nd T i).1

lemma nd_some (T : BSP m) (i : ℕ) (h : i < size T) : (pl T)[i]? = some (nd T i) := by
  unfold nd
  rw [List.getElem?_eq_getElem (by rw [pl_length]; exact h)]
  rfl

lemma nd_zero (T : BSP m) : nd T 0 = ([], T) := by
  cases T <;> rfl

lemma nd_left (lo hi : Fin m → ℝ) (l r : BSP m) (i : ℕ) (h : i < size l) :
    nd (.cut lo hi l r) (1 + i) = (false :: (nd l i).1, (nd l i).2) := by
  unfold nd
  rw [show 1 + i = i + 1 by omega]
  simp only [pl, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [List.length_map, pl_length]; exact h), List.getElem?_map,
    nd_some l i h]
  rfl

lemma nd_right (lo hi : Fin m → ℝ) (l r : BSP m) (i : ℕ) (h : i < size r) :
    nd (.cut lo hi l r) (1 + size l + i) = (true :: (nd r i).1, (nd r i).2) := by
  unfold nd
  rw [show 1 + size l + i = (size l + i) + 1 by omega]
  simp only [pl, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [List.length_map, pl_length]; omega), List.length_map,
    pl_length, show size l + i - size l = i by omega, List.getElem?_map, nd_some r i h]
  rfl

lemma cut_cases (a b i : ℕ) (h : i < 1 + a + b) :
    i = 0 ∨ (∃ i', i' < a ∧ i = 1 + i') ∨ (∃ i', i' < b ∧ i = 1 + a + i') := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  · by_cases h1 : i < 1 + a
    · exact Or.inr (Or.inl ⟨i - 1, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨i - 1 - a, by omega, by omega⟩)

lemma P_zero (T : BSP m) : P T 0 = [] := by unfold P; rw [nd_zero]

/-- **Preorder is the path order.** -/
lemma P_lt (T : BSP m) : ∀ i k, i < k → k < size T → P T i < P T k := by
  induction T with
  | leaf lo hi a => intro i k hik hk; simp only [size] at hk; omega
  | cut lo hi l r ihl ihr =>
    intro i k hik hk'
    have hs : size (BSP.cut lo hi l r) = 1 + size l + size r := rfl
    rcases cut_cases (size l) (size r) k (by omega) with h | ⟨k', h2, rfl⟩ | ⟨k', h2, rfl⟩
    · omega
    · rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; rw [P_zero]; unfold P; rw [nd_left lo hi l r k' h2]; exact List.nil_lt_cons _ _
      · have := ihl i' k' (by omega) h2
        unfold P at this ⊢; rw [nd_left lo hi l r i' h1, nd_left lo hi l r k' h2]
        exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, this⟩)
      · omega
    · rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; rw [P_zero]; unfold P; rw [nd_right lo hi l r k' h2]; exact List.nil_lt_cons _ _
      · unfold P; rw [nd_left lo hi l r i' h1, nd_right lo hi l r k' h2]
        exact List.cons_lt_cons_iff.2 (Or.inl (by decide))
      · have := ihr i' k' (by omega) h2
        unfold P at this ⊢; rw [nd_right lo hi l r i' h1, nd_right lo hi l r k' h2]
        exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, this⟩)

lemma P_inj (T : BSP m) (i k : ℕ) (hi : i < size T) (hk : k < size T) (h : P T i = P T k) : i = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (P_lt T i k h' hk).ne
  · exact absurd h.symm (P_lt T k i h' hi).ne

lemma mem_paths (T : BSP m) : ∀ x, x ∈ T.paths ↔ ∃ i < size T, P T i = x := by
  induction T with
  | leaf lo hi a =>
    intro x; simp only [BSP.paths, Finset.mem_singleton, size]
    constructor
    · rintro rfl; exact ⟨0, by omega, P_zero _⟩
    · rintro ⟨i, hi, rfl⟩; rw [show i = 0 by omega, P_zero]
  | cut lo hi l r ihl ihr =>
    intro x
    have hs : size (BSP.cut lo hi l r) = 1 + size l + size r := rfl
    simp only [BSP.paths, Finset.mem_insert, Finset.mem_union, Finset.mem_image, ihl, ihr]
    constructor
    · rintro (rfl | ⟨y, ⟨i, hi2, rfl⟩, rfl⟩ | ⟨y, ⟨i, hi2, rfl⟩, rfl⟩)
      · exact ⟨0, by omega, P_zero _⟩
      · refine ⟨1 + i, by omega, ?_⟩; unfold P; rw [nd_left lo hi l r i hi2]
      · refine ⟨1 + size l + i, by omega, ?_⟩; unfold P; rw [nd_right lo hi l r i hi2]
    · rintro ⟨i, hi', rfl⟩
      rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; exact Or.inl (P_zero _)
      · refine Or.inr (Or.inl ⟨P l i', ⟨i', h1, rfl⟩, ?_⟩); unfold P; rw [nd_left lo hi l r i' h1]
      · refine Or.inr (Or.inr ⟨P r i', ⟨i', h1, rfl⟩, ?_⟩); unfold P; rw [nd_right lo hi l r i' h1]

lemma paths_card (T : BSP m) : T.paths.card = size T := by
  have : T.paths = (Finset.range (size T)).image (P T) := by
    ext x; simp only [mem_paths, Finset.mem_image, Finset.mem_range]
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi k hk h
  exact P_inj T i k (Finset.mem_range.1 hi) (Finset.mem_range.1 hk) h

end DetANN.HPIM.BB

-- ===== BB_Lay =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- The output tree `B` is stored at `u` with all its cells in `[u, u')` (integer) and `[v, v')`
(real), stably under any change outside these ranges. -/
def Good (s : State) (u v u' v' : ℤ) (B : BoxTree m) : Prop :=
  ∀ s'' : State, (∀ z, u ≤ z → z < u' → s''.integerMemory z = s.integerMemory z) →
    (∀ z, v ≤ z → z < v' → s''.core.mem z = s.core.mem z) → BoxTreeAt m s'' u B

end DetANN.HPIM.BB

-- ===== BD_Prog =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep

lemma len_init (off : ℕ) : (bd_init off).length = 34 := rfl

lemma len_disp (off : ℕ) : (bd_disp off).length = 19 := rfl

lemma len_dl (off : ℕ) : (bd_dl off).length = 33 := rfl

lemma len_near (off : ℕ) : (bd_near off).length = 30 := rfl

lemma len_fi (off : ℕ) : (bd_fi off).length = 18 := rfl

lemma len_tb (off : ℕ) : (bd_tb off).length = 27 := rfl

lemma len_sg0 (off : ℕ) : (bd_sg0 off).length = 11 := rfl

lemma len_sg (off : ℕ) : (bd_sg off).length = 25 := rfl

lemma len_split (off : ℕ) : (bd_split off).length = 29 := rfl

lemma len_split2 (off : ℕ) : (bd_split2 off).length = 32 := rfl

lemma len_cs (off : ℕ) : (bd_cs off).length = 22 := rfl

lemma len_cv (off : ℕ) : (bd_cv off).length = 24 := rfl

lemma len_cv2 (off : ℕ) : (bd_cv2 off).length = 22 := rfl

lemma len_cv3 (off : ℕ) : (bd_cv3 off).length = 22 := rfl

lemma len_cv4 (off : ℕ) : (bd_cv4 off).length = 24 := rfl

lemma len_ce (off : ℕ) : (bd_ce off).length = 11 := rfl

lemma len_leaf (off : ℕ) : (bd_leaf off).length = 13 := rfl

lemma bd_len (off : ℕ) : (bd off).length = 396 := by
  simp only [bd, List.length_append, len_init, len_disp, len_dl, len_near, len_fi, len_tb, len_sg0, len_sg, len_split, len_split2, len_cs, len_cv, len_cv2, len_cv3, len_cv4, len_ce, len_leaf]

lemma det_init (off : ℕ) : DetProgram (bd_init off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_init at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_disp (off : ℕ) : DetProgram (bd_disp off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_disp at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_dl (off : ℕ) : DetProgram (bd_dl off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_dl at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_near (off : ℕ) : DetProgram (bd_near off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_near at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_fi (off : ℕ) : DetProgram (bd_fi off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_fi at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_tb (off : ℕ) : DetProgram (bd_tb off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_tb at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_sg0 (off : ℕ) : DetProgram (bd_sg0 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_sg0 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_sg (off : ℕ) : DetProgram (bd_sg off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_sg at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_split (off : ℕ) : DetProgram (bd_split off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_split at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_split2 (off : ℕ) : DetProgram (bd_split2 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_split2 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_cs (off : ℕ) : DetProgram (bd_cs off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_cs at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_cv (off : ℕ) : DetProgram (bd_cv off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_cv at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_cv2 (off : ℕ) : DetProgram (bd_cv2 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_cv2 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_cv3 (off : ℕ) : DetProgram (bd_cv3 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_cv3 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_cv4 (off : ℕ) : DetProgram (bd_cv4 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_cv4 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_ce (off : ℕ) : DetProgram (bd_ce off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_ce at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma det_leaf (off : ℕ) : DetProgram (bd_leaf off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bd_leaf at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done)

lemma bd_det (off : ℕ) : DetProgram (bd off) := by
  unfold bd
  exact DetANN.HPIM.PP.det_append (det_init off) (DetANN.HPIM.PP.det_append (det_disp off) (DetANN.HPIM.PP.det_append (det_dl off) (DetANN.HPIM.PP.det_append (det_near off) (DetANN.HPIM.PP.det_append (det_fi off) (DetANN.HPIM.PP.det_append (det_tb off) (DetANN.HPIM.PP.det_append (det_sg0 off) (DetANN.HPIM.PP.det_append (det_sg off) (DetANN.HPIM.PP.det_append (det_split off) (DetANN.HPIM.PP.det_append (det_split2 off) (DetANN.HPIM.PP.det_append (det_cs off) (DetANN.HPIM.PP.det_append (det_cv off) (DetANN.HPIM.PP.det_append (det_cv2 off) (DetANN.HPIM.PP.det_append (det_cv3 off) (DetANN.HPIM.PP.det_append (det_cv4 off) (DetANN.HPIM.PP.det_append (det_ce off) (det_leaf off))))))))))))))))

lemma bd_block : IsBlock bd 396 := fun off => ⟨bd_len off, bd_det off⟩

end DetANN.HPIM.BD

-- ===== BD_SegA =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

/-- Constants, the root box allocation. -/
lemma seg_init (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 0) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 13).core.pc = off + 13 ∧
      (run Q s detTape 13).halted = false ∧
      (run Q s detTape 13).core.ptrs 14 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧
      (run Q s detTape 13).core.ptrs 40 = s.core.ptrs 13 ∧
      (run Q s detTape 13).core.ptrs 43 = s.core.ptrs 14 - 2 * s.core.ptrs 1 ∧
      (run Q s detTape 13).core.ptrs 46 = 0 ∧
      (run Q s detTape 13).core.ptrs 60 = 2 * s.core.ptrs 1 ∧
      (run Q s detTape 13).core.ptrs 68 = 1 ∧
      (run Q s detTape 13).core.ptrs 69 = 0 ∧
      (∀ x, x ≠ 14 → x ≠ 40 → x ≠ 43 → x ≠ 46 → x ≠ 60 → x ≠ 68 → x ≠ 69 → (run Q s detTape 13).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 13).core.regs 40 = (s.core.regs 11 * s.core.regs 11) ∧
      (run Q s detTape 13).core.regs 41 = ((s.core.regs 12 * s.core.regs 11) * (s.core.regs 12 * s.core.regs 11)) ∧
      (run Q s detTape 13).core.regs 47 = (s.core.regs 12 * s.core.regs 11) ∧
      (run Q s detTape 13).core.regs 49 = (s.core.regs 11 + s.core.regs 11) ∧
      (run Q s detTape 13).core.regs 50 = (0 : ℝ) ∧
      (run Q s detTape 13).core.regs 53 = (2 : ℝ) ∧
      (∀ x, x ≠ 40 → x ≠ 41 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 53 → (run Q s detTape 13).core.regs x = s.core.regs x) ∧
      (run Q s detTape 13).core.mem = s.core.mem ∧
      (run Q s detTape 13).integerMemory = s.integerMemory ∧
      (run Q s detTape 13).work = s.work + 13 ∧
      cellsWritten Q s 13 = ∅ :=
  scan_steps.1 Q off hE s hpc hh hm1

/-- Root slot and the first task. -/
lemma seg_icd (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 20) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 14).core.pc = off + 34 ∧
      (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 13 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 14).core.ptrs 42 = s.core.ptrs 13 - 4 ∧
      (run Q s detTape 14).core.ptrs 44 = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 14).core.ptrs 57 = s.core.ptrs 13 - 2 ∧
      (run Q s detTape 14).core.ptrs 59 = s.core.ptrs 13 - 1 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 44 → x ≠ 57 → x ≠ 59 → (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs = s.core.regs ∧
      (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 4) = s.core.ptrs 43 ∧
      (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 13 - 1 ∧
      (run Q s detTape 14).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 40 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 4 → z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 14).work = s.work + 14 ∧
      ∀ c ∈ cellsWritten Q s 14, c = (false, s.core.ptrs 13 - 4) ∨ c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) :=
  scan_steps.2.2.2.1 Q off hE s hpc hh hm1

lemma disp_end (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false)
    (hb0 : s.core.ptrs 40 ≤ s.core.ptrs 42)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 395 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  scan_steps.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

lemma seg_end (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (rt : ℤ) (s : State)
    (hpc : s.core.pc = off + 395) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 59) = rt)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 396 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 17 = rt ∧
      (∀ x, x ≠ 17 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  scan_steps.2.2.2.2.2.1 Q off hE rt s hpc hh fi0 hm1

/-- Pop a task and allocate the near box. -/
lemma seg_pop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ep esl elink : ℤ) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 42) = ep)
    (fi1 : s.integerMemory (s.core.ptrs 42 + 1) = esl)
    (fi2 : s.integerMemory (s.core.ptrs 42 + 2) = elink)
    (hb0 : s.core.ptrs 42 < s.core.ptrs 40)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 45 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 14 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (run Q s detTape 11).core.ptrs 42 = elink ∧
      (run Q s detTape 11).core.ptrs 43 = ep ∧
      (run Q s detTape 11).core.ptrs 44 = esl ∧
      (run Q s detTape 11).core.ptrs 45 = 0 ∧
      (run Q s detTape 11).core.ptrs 48 = s.core.ptrs 14 - s.core.ptrs 60 ∧
      (run Q s detTape 11).core.ptrs 49 = 0 ∧
      (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 42 + 2 ∧
      (∀ x, x ≠ 14 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 48 → x ≠ 49 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ :=
  scan_steps.2.2.2.2.2.2.1 Q off hE ep esl elink s hpc hh fi0 fi1 fi2 hb0 hm1

lemma scan_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 45) (hh : s.halted = false)
    (hb0 : s.core.ptrs 11 ≤ s.core.ptrs 45)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 131 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

/-- Address of point `i`; zero both sums. -/
lemma scan_head (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (ki pa : ℤ) (s : State)
    (hpc : s.core.pc = off + 45) (hh : s.halted = false)
    (fi0 : s.integerMemory (s.core.ptrs 10 + s.core.ptrs 45) = ki)
    (fi1 : s.integerMemory (s.core.ptrs 12 + ki) = pa)
    (hb0 : s.core.ptrs 45 < s.core.ptrs 11)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 8).core.pc = off + 53 ∧
      (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 46 = 0 ∧
      (run Q s detTape 8).core.ptrs 47 = pa ∧
      (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 12 + ki ∧
      (∀ x, x ≠ 46 → x ≠ 47 → x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs 42 = (0 : ℝ) ∧
      (run Q s detTape 8).core.regs 43 = (0 : ℝ) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      cellsWritten Q s 8 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.1 Q off hE ki pa s hpc hh fi0 fi1 hb0 hm1

lemma dd_far (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : ¬ (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 126 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 3).core.regs 54 = (s.core.regs 42 - s.core.regs 40) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

lemma dd_good (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hb1 : (s.core.regs 43 - s.core.regs 41) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 4).core.pc = off + 128 ∧
      (run Q s detTape 4).halted = false ∧
      (run Q s detTape 4).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 4).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 4).core.regs x = s.core.regs x) ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧
      (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).work = s.work + 4 ∧
      cellsWritten Q s 4 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hm1

lemma dd_up (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0)
    (hb2 : s.core.ptrs 69 < s.core.ptrs 49)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 6).core.pc = off + 93 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 46 = 0 ∧
      (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hb2 hm1

lemma dd_fi (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 86) (hh : s.halted = false)
    (hb0 : (s.core.regs 42 - s.core.regs 40) ≤ 0)
    (hb1 : ¬ (s.core.regs 43 - s.core.regs 41) ≤ 0)
    (hb2 : s.core.ptrs 49 ≤ s.core.ptrs 69)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 6).core.pc = off + 116 ∧
      (run Q s detTape 6).halted = false ∧
      (run Q s detTape 6).core.ptrs 46 = 0 ∧
      (∀ x, x ≠ 46 → (run Q s detTape 6).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 6).core.regs 54 = (s.core.regs 43 - s.core.regs 41) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 6).core.regs x = s.core.regs x) ∧
      (run Q s detTape 6).core.mem = s.core.mem ∧
      (run Q s detTape 6).integerMemory = s.integerMemory ∧
      (run Q s detTape 6).work = s.work + 6 ∧
      cellsWritten Q s 6 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hb1 hb2 hm1

lemma seg_next (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 126) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 45 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 45 = s.core.ptrs 45 + 1 ∧
      (∀ x, x ≠ 45 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma seg_good (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 128) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 383 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 61 = s.core.ptrs 45 + 1 ∧
      (∀ x, x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma scd_out (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 131) (hh : s.halted = false)
    (hb0 : s.core.ptrs 49 ≤ s.core.ptrs 69)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 383 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 61 = 0 ∧
      (∀ x, x ≠ 61 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

lemma scd_tb (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 131) (hh : s.halted = false)
    (hb0 : s.core.ptrs 69 < s.core.ptrs 49)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 134 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 46 = 0 ∧
      (run Q s detTape 3).core.ptrs 61 = 0 ∧
      (∀ x, x ≠ 46 → x ≠ 61 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ :=
  scan_steps.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 Q off hE s hpc hh hb0 hm1

end DetANN.HPIM.BD

-- ===== BD_SegB =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma seg_sg0 (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (a0 b0 c0 d0 : ℝ) (s : State)
    (hpc : s.core.pc = off + 161) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48) = a0)
    (fr1 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 1) = b0)
    (fr2 : s.core.mem (s.core.ptrs 43) = c0)
    (fr3 : s.core.mem (s.core.ptrs 43 + s.core.ptrs 1) = d0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 172 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 46 = 1 ∧
      (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 43 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs 44 = c0 ∧
      (run Q s detTape 11).core.regs 45 = d0 ∧
      (run Q s detTape 11).core.regs 51 = (b0 - a0) ∧
      (run Q s detTape 11).core.regs 52 = (d0 - c0) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 51 → x ≠ 52 → (run Q s detTape 11).core.regs x = s.core.regs x) ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory = s.integerMemory ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      cellsWritten Q s 11 = ∅ :=
  split_steps.2.2.1 Q off hE a0 b0 c0 d0 s hpc hh fr0 fr1 fr2 fr3 hm1

lemma sgd_carve (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 197) (hh : s.halted = false)
    (hb0 : ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 280 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 3).core.regs 54 = ((s.core.regs 51 + s.core.regs 51) - s.core.regs 52) ∧
      (∀ x, x ≠ 54 → (run Q s detTape 3).core.regs x = s.core.regs x) ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ :=
  split_steps.2.2.2.2.2.1 Q off hE s hpc hh hb0 hm1

end DetANN.HPIM.BD

-- ===== BD_SegC =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP

lemma seg_carve (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 280) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 3).core.pc = off + 283 ∧
      (run Q s detTape 3).halted = false ∧
      (run Q s detTape 3).core.ptrs 53 = 0 ∧
      (run Q s detTape 3).core.ptrs 54 = s.core.ptrs 43 ∧
      (run Q s detTape 3).core.ptrs 55 = s.core.ptrs 44 ∧
      (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → (run Q s detTape 3).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 3).core.regs = s.core.regs ∧
      (run Q s detTape 3).core.mem = s.core.mem ∧
      (run Q s detTape 3).integerMemory = s.integerMemory ∧
      (run Q s detTape 3).work = s.work + 3 ∧
      cellsWritten Q s 3 = ∅ :=
  carve_steps.1 Q off hE s hpc hh hm1

lemma ck_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (hb0 : s.core.ptrs 1 ≤ s.core.ptrs 53)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 1).core.pc = off + 372 ∧
      (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs = s.core.ptrs ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧
      (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧
      cellsWritten Q s 1 = ∅ :=
  carve_steps.2.1 Q off hE s hpc hh hb0 hm1

lemma ck_nolow (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tl lo : ℝ) (s : State)
    (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53) = tl)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53) = lo)
    (hb0 : s.core.ptrs 53 < s.core.ptrs 1)
    (hb1 : (tl - lo) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 7).core.pc = off + 326 ∧
      (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs 44 = tl ∧
      (run Q s detTape 7).core.regs 45 = lo ∧
      (run Q s detTape 7).core.regs 54 = (tl - lo) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 54 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      cellsWritten Q s 7 = ∅ :=
  carve_steps.2.2.1 Q off hE tl lo s hpc hh fr0 fr1 hb0 hb1 hm1

lemma ch_nohigh (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (th hi : ℝ) (s : State)
    (hpc : s.core.pc = off + 326) (hh : s.halted = false)
    (fr0 : s.core.mem (s.core.ptrs 48 + s.core.ptrs 53 + s.core.ptrs 1) = th)
    (fr1 : s.core.mem (s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1) = hi)
    (hb0 : (hi - th) ≤ 0)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 8).core.pc = off + 370 ∧
      (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 57 = s.core.ptrs 54 + s.core.ptrs 53 + s.core.ptrs 1 ∧
      (∀ x, x ≠ 57 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs 44 = th ∧
      (run Q s detTape 8).core.regs 46 = hi ∧
      (run Q s detTape 8).core.regs 54 = (hi - th) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → (run Q s detTape 8).core.regs x = s.core.regs x) ∧
      (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      cellsWritten Q s 8 = ∅ :=
  carve_steps.2.2.2.2.2.2.1 Q off hE th hi s hpc hh fr0 fr1 hb0 hm1

lemma seg_cn (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 370) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 2).core.pc = off + 283 ∧
      (run Q s detTape 2).halted = false ∧
      (run Q s detTape 2).core.ptrs 53 = s.core.ptrs 53 + 1 ∧
      (∀ x, x ≠ 53 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧
      (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧
      cellsWritten Q s 2 = ∅ :=
  carve_steps.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma seg_ce (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 372) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1) :
    (run Q s detTape 11).core.pc = off + 34 ∧
      (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 11).core.ptrs 42 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 11).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧
      (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 55 ∧
      (run Q s detTape 11).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 42 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      ∀ c ∈ cellsWritten Q s 11, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) :=
  carve_steps.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh hm1

lemma seg_leaf (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (s : State)
    (hpc : s.core.pc = off + 383) (hh : s.halted = false)
    (hm1 : 1 ≤ s.core.ptrs 1)
    (hx0 : s.core.ptrs 13 ≤ s.core.ptrs 44) :
    (run Q s detTape 12).core.pc = off + 34 ∧
      (run Q s detTape 12).halted = false ∧
      (run Q s detTape 12).core.ptrs 13 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 12).core.ptrs 52 = s.core.ptrs 13 - 3 ∧
      (run Q s detTape 12).core.ptrs 57 = s.core.ptrs 13 - 1 ∧
      (∀ x, x ≠ 13 → x ≠ 52 → x ≠ 57 → (run Q s detTape 12).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 12).core.regs = s.core.regs ∧
      (run Q s detTape 12).core.mem = s.core.mem ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 69 ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 2) = s.core.ptrs 43 ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 13 - 1) = s.core.ptrs 61 ∧
      (run Q s detTape 12).integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 3 ∧
      (∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → z ≠ s.core.ptrs 44 → (run Q s detTape 12).integerMemory z = s.integerMemory z) ∧
      (run Q s detTape 12).work = s.work + 12 ∧
      ∀ c ∈ cellsWritten Q s 12, c = (false, s.core.ptrs 13 - 3) ∨ c = (false, s.core.ptrs 13 - 2) ∨ c = (false, s.core.ptrs 13 - 1) ∨ c = (false, s.core.ptrs 44) :=
  carve_steps.2.2.2.2.2.2.2.2.2.2.2.2 Q off hE s hpc hh hm1 hx0

end DetANN.HPIM.BD

-- ===== BS_Geo =====
namespace DetANN.HPIM.BS

open DetANN.HPIM

variable {m n : ℕ} (pts : Fin n → Fin m → ℝ) (r c : ℝ)

/-- The near set of a box. -/
noncomputable def nearS (lo hi : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => boxDist2 lo hi (pts i) ≤ r ^ 2

/-- The good (IN-certificate) set. -/
noncomputable def goodS (lo hi : Fin m → ℝ) : Finset (Fin n) :=
  (nearS pts r lo hi).filter fun i => boxMaxDist2 lo hi (pts i) ≤ (c * r) ^ 2

def IsLive (lo hi : Fin m → ℝ) : Prop :=
  (nearS pts r lo hi).Nonempty ∧ ¬ (goodS pts r c lo hi).Nonempty

/-- Coordinatewise min / max of a point set (0 if empty). -/
noncomputable def aLo (N : Finset (Fin n)) (j : Fin m) : ℝ :=
  if h : N.Nonempty then N.inf' h (fun i => pts i j) else 0

noncomputable def bHi (N : Finset (Fin n)) (j : Fin m) : ℝ :=
  if h : N.Nonempty then N.sup' h (fun i => pts i j) else 0

noncomputable def coreLo (lo hi : Fin m → ℝ) : Fin m → ℝ :=
  fun j => max (aLo pts (nearS pts r lo hi) j - 2 * r) (lo j)

noncomputable def coreHi (lo hi : Fin m → ℝ) : Fin m → ℝ :=
  fun j => min (bHi pts (nearS pts r lo hi) j + 2 * r) (hi j)

/-- Does the live box carve? -/
def Carves (lo hi : Fin m → ℝ) : Prop :=
  2 * sigma (coreLo pts r lo hi) (coreHi pts r lo hi) ≤ sigma lo hi

lemma build_succ_carve (f : ℕ) (lo hi : Fin m → ℝ) (h : IsLive pts r c lo hi)
    (hc : Carves pts r lo hi) :
    build pts r c (f + 1) lo hi =
      carve (coreLo pts r lo hi) (coreHi pts r lo hi) (build pts r c f) m 0 lo hi := by
  obtain ⟨h1, h2⟩ := h
  unfold Carves coreLo coreHi aLo bHi at hc
  unfold coreLo coreHi aLo bHi
  unfold goodS at h2
  simp only [build]
  unfold nearS at h1 h2 hc ⊢
  rw [dif_pos h1, dif_neg h2]
  simp only [dif_pos h1] at hc ⊢
  rw [if_pos hc]

lemma build_succ_split (f : ℕ) (lo hi : Fin m → ℝ) (h : IsLive pts r c lo hi)
    (hc : ¬ Carves pts r lo hi) (k : Fin m) (hk : longestAxis lo hi = some k) :
    build pts r c (f + 1) lo hi =
      .cut lo hi (build pts r c f lo (setCoord hi k ((lo k + hi k) / 2)))
        (build pts r c f (setCoord lo k ((lo k + hi k) / 2)) hi) := by
  obtain ⟨h1, h2⟩ := h
  unfold Carves coreLo coreHi aLo bHi at hc
  unfold goodS at h2
  simp only [build]
  unfold nearS at h1 h2 hc
  rw [dif_pos h1, dif_neg h2]
  simp only [dif_pos h1] at hc ⊢
  rw [if_neg hc, hk]

lemma le_sigma (lo hi : Fin m → ℝ) (j : Fin m) : hi j - lo j ≤ sigma lo hi :=
  le_ciSup (f := fun j => hi j - lo j) (Finite.bddAbove_range _) j

lemma sigma_le (hm : 0 < m) {lo hi : Fin m → ℝ} {x : ℝ} (h : ∀ j, hi j - lo j ≤ x) :
    sigma lo hi ≤ x := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  exact ciSup_le h

/-- Number of leaves. -/
def leaves : BSP m → ℕ
  | .leaf .. => 1
  | .cut _ _ l t => leaves l + leaves t

lemma paths_card (T : BSP m) : T.paths.card + 1 = 2 * leaves T := by
  induction T with
  | leaf => simp [BSP.paths, leaves]
  | cut lo hi l t ihl iht =>
    simp only [BSP.paths, leaves]
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ (List.cons_injective),
          Finset.card_image_of_injective _ (List.cons_injective)]
        omega
      · rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨b, -, hb⟩ := Finset.mem_image.1 hx'
        simp at hb
    · intro hx
      rcases Finset.mem_union.1 hx with hx | hx <;>
        · obtain ⟨a, -, ha⟩ := Finset.mem_image.1 hx
          simp at ha

end DetANN.HPIM.BS

-- ===== BD_Math =====
namespace DetANN.HPIM.BD

open DetANN.HPIM DetANN.HPIM.BS

variable {m n : ℕ}

lemma psum_zero (g : Fin m → ℝ) : psum g 0 = 0 := by simp [psum]

/-- The near points with index `< i`. -/
noncomputable def nearP (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) (i : ℕ) :
    Finset (Fin n) :=
  (nearS pts r lo hi).filter fun i' => (i' : ℕ) < i

lemma nearP_zero (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) : nearP pts r lo hi 0 = ∅ := by
  ext x; simp [nearP]

lemma nearP_all (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) :
    nearP pts r lo hi n = nearS pts r lo hi := by
  ext x; simp [nearP, x.isLt]

lemma nearP_succ_near (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) {i : ℕ} (hi' : i < n)
    (h : boxDist2 lo hi (pts ⟨i, hi'⟩) ≤ r ^ 2) :
    nearP pts r lo hi (i + 1) = insert ⟨i, hi'⟩ (nearP pts r lo hi i) := by
  ext x
  simp only [nearP, nearS, Finset.mem_filter, Finset.mem_insert, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases hx : (x : ℕ) = i
    · left; exact Fin.ext hx
    · right; exact ⟨h1, by omega⟩
  · rintro (rfl | ⟨h1, h2⟩)
    · exact ⟨h, by simp⟩
    · exact ⟨h1, by omega⟩

lemma nearP_succ_far (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) {i : ℕ} (hi' : i < n)
    (h : ¬ boxDist2 lo hi (pts ⟨i, hi'⟩) ≤ r ^ 2) :
    nearP pts r lo hi (i + 1) = nearP pts r lo hi i := by
  ext x
  simp only [nearP, nearS, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra hx
    have : x = ⟨i, hi'⟩ := Fin.ext (show (x : ℕ) = i by omega)
    subst this; exact h h1
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

lemma build_succ_none (pts : Fin n → Fin m → ℝ) (r c : ℝ) (f : ℕ) (lo hi : Fin m → ℝ)
    (h : ¬ (nearS pts r lo hi).Nonempty) : build pts r c (f + 1) lo hi = .leaf lo hi none := by
  simp only [build]
  unfold nearS at h
  rw [dif_neg h]

lemma build_succ_good (pts : Fin n → Fin m → ℝ) (r c : ℝ) (f : ℕ) (lo hi : Fin m → ℝ)
    (h1 : (nearS pts r lo hi).Nonempty) (h2 : (goodS pts r c lo hi).Nonempty) :
    build pts r c (f + 1) lo hi = .leaf lo hi (some ((goodS pts r c lo hi).min' h2 : ℕ)) := by
  simp only [build]
  unfold goodS nearS at h2
  unfold nearS at h1
  rw [dif_pos h1, dif_pos h2]
  rfl

lemma goodS_min' (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) {i : Fin n}
    (hi' : i ∈ goodS pts r c lo hi) (hlt : ∀ i' : Fin n, (i' : ℕ) < i → i' ∉ goodS pts r c lo hi) :
    (goodS pts r c lo hi).min' ⟨i, hi'⟩ = i := by
  apply le_antisymm (Finset.min'_le _ _ hi')
  apply Finset.le_min'
  intro y hy
  by_contra hlt'
  exact hlt y (not_le.1 hlt') hy

lemma mem_goodS (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) {i : Fin n} :
    i ∈ goodS pts r c lo hi ↔
      boxDist2 lo hi (pts i) ≤ r ^ 2 ∧ boxMaxDist2 lo hi (pts i) ≤ (c * r) ^ 2 := by
  simp [goodS, nearS]

lemma le_rmax (g : ℕ → ℝ) : ∀ k j, j ≤ k → g j ≤ rmax g k := by
  intro k
  induction k with
  | zero => intro j hj; rw [Nat.le_zero.1 hj]; exact le_rfl
  | succ k ih =>
    intro j hj
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (ih j (by omega)).trans (le_max_left _ _)
    · rw [show j = k + 1 by omega]; exact le_max_right _ _

lemma rmax_mem (g : ℕ → ℝ) : ∀ k, ∃ j ≤ k, rmax g k = g j := by
  intro k
  induction k with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ k ih =>
    obtain ⟨j, hj, e⟩ := ih
    simp only [rmax]
    rcases le_total (rmax g k) (g (k + 1)) with h | h
    · exact ⟨k + 1, le_rfl, max_eq_right h⟩
    · exact ⟨j, by omega, (max_eq_left h).trans e⟩

lemma rmax_sigma (hm : 0 < m) (lo hi : Fin m → ℝ) : rmax (side lo hi) (m - 1) = sigma lo hi := by
  apply le_antisymm
  · obtain ⟨j, hj, e⟩ := rmax_mem (side lo hi) (m - 1)
    rw [e]; unfold side; rw [dif_pos (by omega)]; exact le_sigma _ _ _
  · apply sigma_le hm
    intro j
    have := le_rmax (side lo hi) (m - 1) j (by have := j.isLt; omega)
    unfold side at this; rw [dif_pos j.isLt] at this; exact this

variable (pts : Fin n → Fin m → ℝ) (r c : ℝ)

lemma starves_carve {f : ℕ} {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi) (hc : Carves pts r lo hi) :
    Starves pts r c (f + 1) lo hi ↔
      ∃ B ∈ carveBoxes (coreLo pts r lo hi) (coreHi pts r lo hi) m 0 lo hi, Starves pts r c f B.1 B.2 := by
  obtain ⟨h1, h2⟩ := hl
  unfold goodS at h2
  have hc' := hc
  unfold Carves coreLo coreHi aLo bHi at hc'
  unfold coreLo coreHi aLo bHi
  simp only [Starves]
  unfold nearS at h1 h2 hc' ⊢
  rw [dif_pos h1, if_neg h2]
  simp only [dif_pos h1] at hc' ⊢
  rw [if_pos hc']

lemma starves_split {f : ℕ} {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi) (hc : ¬ Carves pts r lo hi)
    {k : Fin m} (hk : longestAxis lo hi = some k) :
    Starves pts r c (f + 1) lo hi ↔
      Starves pts r c f lo (setCoord hi k ((lo k + hi k) / 2)) ∨
        Starves pts r c f (setCoord lo k ((lo k + hi k) / 2)) hi := by
  obtain ⟨h1, h2⟩ := hl
  unfold goodS at h2
  have hc' := hc
  unfold Carves coreLo coreHi aLo bHi at hc'
  simp only [Starves]
  unfold nearS at h1 h2 hc'
  rw [dif_pos h1, if_neg h2]
  simp only [dif_pos h1] at hc' ⊢
  rw [if_neg hc', hk]

section Carve

variable (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m)

lemma carveBoxes_zero (k : ℕ) (lo hi : Fin m → ℝ) : carveBoxes tlo thi 0 k lo hi = [(lo, hi)] := rfl

/-- One axis of the carve, in the order of the machine: first the low peel, then the high peel. -/
lemma carve_succ (d k : ℕ) (hk : k < m) (lo hi : Fin m → ℝ) :
    carve tlo thi bld (d + 1) k lo hi =
      let lo' := if lo ⟨k, hk⟩ < tlo ⟨k, hk⟩ then setCoord lo k (tlo ⟨k, hk⟩) else lo
      let rest : BSP m :=
        if hi ⟨k, hk⟩ > thi ⟨k, hk⟩ then
          .cut lo' hi (carve tlo thi bld d (k + 1) lo' (setCoord hi k (thi ⟨k, hk⟩)))
            (bld (setCoord lo' k (thi ⟨k, hk⟩)) hi)
        else carve tlo thi bld d (k + 1) lo' hi
      if lo ⟨k, hk⟩ < tlo ⟨k, hk⟩ then .cut lo hi (bld lo (setCoord hi k (tlo ⟨k, hk⟩))) rest
      else rest := by
  simp only [carve, dif_pos hk]

lemma carveBoxes_succ (d k : ℕ) (hk : k < m) (lo hi : Fin m → ℝ) :
    carveBoxes tlo thi (d + 1) k lo hi =
      let lo' := if lo ⟨k, hk⟩ < tlo ⟨k, hk⟩ then setCoord lo k (tlo ⟨k, hk⟩) else lo
      let rest :=
        if hi ⟨k, hk⟩ > thi ⟨k, hk⟩ then
          carveBoxes tlo thi d (k + 1) lo' (setCoord hi k (thi ⟨k, hk⟩)) ++
            [(setCoord lo' k (thi ⟨k, hk⟩), hi)]
        else carveBoxes tlo thi d (k + 1) lo' hi
      if lo ⟨k, hk⟩ < tlo ⟨k, hk⟩ then (lo, setCoord hi k (tlo ⟨k, hk⟩)) :: rest else rest := by
  simp only [carveBoxes, dif_pos hk]

/-- With no peel left, the carve hands the box itself to its builder. -/
lemma carveBoxes_nopeel : ∀ d k (lo hi : Fin m → ℝ), k + d = m →
    (∀ k' (hk' : k' < m), k ≤ k' → ¬ lo ⟨k', hk'⟩ < tlo ⟨k', hk'⟩ ∧ ¬ hi ⟨k', hk'⟩ > thi ⟨k', hk'⟩) →
    carveBoxes tlo thi d k lo hi = [(lo, hi)] := by
  intro d
  induction d with
  | zero => intro k lo hi _ _; rfl
  | succ d ih =>
    intro k lo hi hkd h
    have hk : k < m := by omega
    rw [carveBoxes_succ tlo thi d k hk]
    obtain ⟨h1, h2⟩ := h k hk le_rfl
    simp only [if_neg h1, if_neg h2]
    exact ih (k + 1) lo hi (by omega) fun k' hk' hkk => h k' hk' (by omega)

end Carve

/-- A live, carving box with no peel starves at every fuel. -/
lemma nopeel_starves {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi) (hc : Carves pts r lo hi)
    (hnp : ∀ k (hk : k < m), ¬ lo ⟨k, hk⟩ < coreLo pts r lo hi ⟨k, hk⟩ ∧
      ¬ hi ⟨k, hk⟩ > coreHi pts r lo hi ⟨k, hk⟩) :
    ∀ f, Starves pts r c f lo hi := by
  have hB := carveBoxes_nopeel (coreLo pts r lo hi) (coreHi pts r lo hi) m 0 lo hi (by omega)
    (fun k' hk' _ => hnp k' hk')
  intro f
  induction f with
  | zero => simp [Starves]
  | succ f ih =>
    rw [starves_carve pts r c hl hc, hB]
    exact ⟨(lo, hi), List.mem_singleton_self _, ih⟩

/-- Under `¬ Starves`, a carve peels on some axis. -/
lemma carve_peels {f : ℕ} {lo hi : Fin m → ℝ} (hl : IsLive pts r c lo hi) (hc : Carves pts r lo hi)
    (hns : ¬ Starves pts r c (f + 1) lo hi) :
    ∃ k, ∃ hk : k < m, lo ⟨k, hk⟩ < coreLo pts r lo hi ⟨k, hk⟩ ∨ hi ⟨k, hk⟩ > coreHi pts r lo hi ⟨k, hk⟩ := by
  by_contra hne
  push Not at hne
  exact hns (nopeel_starves pts r c hl hc (fun k hk => ⟨not_lt.2 (hne k hk).1, not_lt.2 (hne k hk).2⟩) _)

lemma size_pos (T : BSP m) : 1 ≤ BB.size T := by
  cases T <;> simp [BB.size] <;> omega

end DetANN.HPIM.BD

-- ===== BD_Loops =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma dl_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (lo hi pt : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 53 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 →
      (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) → BoxAt s (s.core.ptrs 43) lo hi →
      s.core.regs 42 = psum (t1 lo hi pt) j → s.core.regs 43 = psum (t2 lo hi pt) j →
      ∃ t, t ≤ 33 * k + 1 ∧ (run Q s detTape t).core.pc = off + 86 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.regs 42 = boxDist2 lo hi pt ∧
        (run Q s detTape t).core.regs 43 = boxMaxDist2 lo hi pt ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 47 → x ≠ 48 → x ≠ 54 →
          (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ :=
  loop_specs.1 Q off hE lo hi pt

/-- The near box `[mn, mx]` is stored at `q` in the layout of `BoxAt`. -/
lemma up_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt mn0 mx0 : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 93 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 →
      s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 →
      (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) →
      (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = min (mn0 jj) (pt jj) ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = max (mx0 jj) (pt jj)) →
      (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) →
      ∃ t, t ≤ 23 * k + 1 ∧ (run Q s detTape t).core.pc = off + 126 ∧
        (run Q s detTape t).halted = false ∧
        BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => min (mn0 jj) (pt jj))
          (fun jj => max (mx0 jj) (pt jj)) ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m :=
  loop_specs.2.1 Q off hE pt mn0 mx0

lemma fi_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pt : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 116 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j →
      s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 47 →
      (∀ jj : Fin m, s.core.mem (s.core.ptrs 47 + jj) = pt jj) →
      (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = pt jj ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = pt jj) →
      ∃ t, t ≤ 9 * k + 2 ∧ (run Q s detTape t).core.pc = off + 126 ∧
        (run Q s detTape t).halted = false ∧
        BoxAt (run Q s detTape t) (s.core.ptrs 48) pt pt ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (run Q s detTape t).core.ptrs 49 = 1 ∧
        (∀ x, x ≠ 46 → x ≠ 49 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m :=
  loop_specs.2.2.1 Q off hE pt

lemma tb_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (mn0 mx0 lo hi : Fin m → ℝ) (r2 : ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → s.core.pc = off + 134 → s.halted = false →
      s.core.ptrs 1 = m → 1 ≤ m → s.core.ptrs 46 = j → s.core.regs 53 = 2 → s.core.regs 49 = r2 →
      s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 43 → BoxAt s (s.core.ptrs 43) lo hi →
      (∀ jj : Fin m, (jj : ℕ) < j → s.core.mem (s.core.ptrs 48 + jj) = max (mn0 jj - r2) (lo jj) ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = min (mx0 jj + r2) (hi jj)) →
      (∀ jj : Fin m, j ≤ (jj : ℕ) → s.core.mem (s.core.ptrs 48 + jj) = mn0 jj ∧
        s.core.mem (s.core.ptrs 48 + jj + m) = mx0 jj) →
      ∃ t, t ≤ 27 * k + 1 ∧ (run Q s detTape t).core.pc = off + 161 ∧
        (run Q s detTape t).halted = false ∧
        BoxAt (run Q s detTape t) (s.core.ptrs 48) (fun jj => max (mn0 jj - r2) (lo jj))
          (fun jj => min (mx0 jj + r2) (hi jj)) ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 54 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 48 ≤ c.2 ∧ c.2 < s.core.ptrs 48 + 2 * m :=
  loop_specs.2.2.2.1 Q off hE mn0 mx0 lo hi r2

lemma sg_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (tlo thi lo hi : Fin m → ℝ) :
    ∀ (k j : ℕ) (s : State), j + k = m → 1 ≤ j → s.core.pc = off + 172 → s.halted = false →
      s.core.ptrs 1 = m → s.core.ptrs 46 = j → s.core.regs 53 = 2 →
      BoxAt s (s.core.ptrs 48) tlo thi → BoxAt s (s.core.ptrs 43) lo hi →
      s.core.regs 51 = rmax (side tlo thi) (j - 1) → s.core.regs 52 = rmax (side lo hi) (j - 1) →
      ∃ t, t ≤ 25 * k + 1 ∧ (run Q s detTape t).core.pc = off + 197 ∧
        (run Q s detTape t).halted = false ∧
        (run Q s detTape t).core.regs 51 = rmax (side tlo thi) (m - 1) ∧
        (run Q s detTape t).core.regs 52 = rmax (side lo hi) (m - 1) ∧
        (∀ x, x ≠ 46 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 47 → x ≠ 51 → x ≠ 52 → x ≠ 54 →
          (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ :=
  loop_specs.2.2.2.2.1 Q off hE tlo thi lo hi

lemma icp_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (src : ℕ → ℝ) (L : ℕ) :
    ∀ (k j : ℕ) (s : State), j + k = L → s.core.pc = off + 13 → s.halted = false → 1 ≤ s.core.ptrs 1 →
      s.core.ptrs 60 = L → s.core.ptrs 46 = j → s.core.ptrs 43 + L ≤ s.core.ptrs 17 →
      (∀ z, z < L → s.core.mem (s.core.ptrs 17 + z) = src z) →
      (∀ z, z < j → s.core.mem (s.core.ptrs 43 + z) = src z) →
      ∃ t, t ≤ 7 * k + 1 ∧ (run Q s detTape t).core.pc = off + 20 ∧
        (run Q s detTape t).halted = false ∧
        (∀ z, z < L → (run Q s detTape t).core.mem (s.core.ptrs 43 + z) = src z) ∧
        (∀ z, (z < s.core.ptrs 43 ∨ s.core.ptrs 43 + L ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (∀ x, x ≠ 46 → x ≠ 50 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 55 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = true ∧ s.core.ptrs 43 ≤ c.2 ∧ c.2 < s.core.ptrs 43 + L :=
  loop_specs.2.2.2.2.2.2.2 Q off hE src L

end DetANN.HPIM.BD

-- ===== BD_Scan =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma aLo_insert (pts : Fin n → Fin m → ℝ) {N : Finset (Fin n)} (hN : N.Nonempty) (a : Fin n) (j : Fin m) :
    aLo pts (insert a N) j = min (aLo pts N j) (pts a j) := by
  unfold aLo
  rw [dif_pos (Finset.insert_nonempty a N), dif_pos hN, Finset.inf'_insert, min_comm]

lemma bHi_insert (pts : Fin n → Fin m → ℝ) {N : Finset (Fin n)} (hN : N.Nonempty) (a : Fin n) (j : Fin m) :
    bHi pts (insert a N) j = max (bHi pts N j) (pts a j) := by
  unfold bHi
  rw [dif_pos (Finset.insert_nonempty a N), dif_pos hN, Finset.sup'_insert, max_comm]

lemma aLo_single (pts : Fin n → Fin m → ℝ) (a : Fin n) (j : Fin m) : aLo pts {a} j = pts a j := by
  unfold aLo; rw [dif_pos (Finset.singleton_nonempty a)]; simp

lemma bHi_single (pts : Fin n → Fin m → ℝ) (a : Fin n) (j : Fin m) : bHi pts {a} j = pts a j := by
  unfold bHi; rw [dif_pos (Finset.singleton_nonempty a)]; simp

lemma localPts_of {s s' : State} {pts : Fin n → Fin m → ℝ} (h : LocalPts s pts)
    (h1 : s'.core.ptrs 1 = s.core.ptrs 1) (h10 : s'.core.ptrs 10 = s.core.ptrs 10)
    (h11 : s'.core.ptrs 11 = s.core.ptrs 11) (h12 : s'.core.ptrs 12 = s.core.ptrs 12)
    (hI : ∀ z, 0 ≤ z → s'.integerMemory z = s.integerMemory z)
    (hM : ∀ z, 0 ≤ z → s'.core.mem z = s.core.mem z) : LocalPts s' pts := by
  obtain ⟨a1, a11, a10, a12, hp⟩ := h
  refine ⟨by rw [h1, a1], by rw [h11, a11], by rw [h10]; exact a10, by rw [h12]; exact a12, fun i => ?_⟩
  obtain ⟨b1, b2, b3⟩ := hp i
  have e1 : s'.integerMemory (s'.core.ptrs 10 + i) = s.integerMemory (s.core.ptrs 10 + i) := by
    rw [h10]; exact hI _ (by positivity)
  have e2 : s'.integerMemory (s'.core.ptrs 12 + s'.integerMemory (s'.core.ptrs 10 + i)) =
      s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i)) := by
    rw [e1, h12]; exact hI _ (by omega)
  refine ⟨by rw [e1]; exact b1, by rw [e2]; exact b2, fun j => ?_⟩
  rw [e2, hM _ (by positivity)]; exact b3 j

/-- The near box of the points with index `< i` is stored at `q` (if there is one). -/
def NearInv (s : State) (pts : Fin n → Fin m → ℝ) (r : ℝ) (lo hi : Fin m → ℝ) (i : ℕ) : Prop :=
  (s.core.ptrs 49 = 0 ∧ nearP pts r lo hi i = ∅) ∨
    (s.core.ptrs 49 = 1 ∧ (nearP pts r lo hi i).Nonempty ∧
      BoxAt s (s.core.ptrs 48) (aLo pts (nearP pts r lo hi i)) (bHi pts (nearP pts r lo hi i)))

lemma near_iff (d r : ℝ) : d ≤ r ^ 2 ↔ d - r * r ≤ 0 := by rw [sq, sub_nonpos]

lemma scan_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (lo hi : Fin m → ℝ) (hm : 1 ≤ m) :
    ∀ (d i : ℕ) (s : State), i + d = n → s.core.pc = off + 45 → s.halted = false →
      LocalPts s pts → s.core.ptrs 45 = i →
      s.core.regs 40 = r * r → s.core.regs 41 = (c * r) * (c * r) → s.core.regs 53 = 2 →
      s.core.ptrs 69 = 0 →
      BoxAt s (s.core.ptrs 43) lo hi → s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 43 →
      s.core.ptrs 43 + 2 * m ≤ 0 →
      (∀ i' : Fin n, (i' : ℕ) < i → i' ∉ goodS pts r c lo hi) →
      NearInv s pts r lo hi i →
      ∃ t, t ≤ (60 * m + 30) * d + 1 ∧ (run Q s detTape t).halted = false ∧
        ((∃ i0 : Fin n, i0 ∈ goodS pts r c lo hi ∧ (∀ i' : Fin n, i' < i0 → i' ∉ goodS pts r c lo hi) ∧
            (run Q s detTape t).core.pc = off + 128 ∧ (run Q s detTape t).core.ptrs 45 = i0) ∨
          ((∀ i' : Fin n, i' ∉ goodS pts r c lo hi) ∧ (run Q s detTape t).core.pc = off + 131 ∧
            NearInv (run Q s detTape t) pts r lo hi n)) ∧
        (∀ x, (x < 45 ∨ x = 48 ∨ 58 ≤ x) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
          (run Q s detTape t).core.mem z = s.core.mem z) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ w ∈ cellsWritten Q s t, w.1 = true ∧ s.core.ptrs 48 ≤ w.2 ∧ w.2 < s.core.ptrs 48 + 2 * m := by
  intro d
  induction d with
  | zero =>
    intro i s hid hpc hh hL h45 _ _ _ _ _ _ _ hng hN
    obtain ⟨a1, a11, -, -, -⟩ := hL
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      scan_exit Q off hE s hpc hh (by rw [a11, h45]; omega) (by rw [a1]; exact_mod_cast hm)
    refine ⟨1, by omega, g2, Or.inr ⟨fun i' => hng i' (by omega), g1, ?_⟩, fun x _ => by rw [g3],
      fun x _ => by rw [g4], fun z _ => by rw [g5], g6, g7, by rw [g8]; simp⟩
    obtain rfl : i = n := by omega
    unfold NearInv; rw [g3]; unfold BoxAt; rw [g5]; exact hN
  | succ d ih =>
    intro i s hid hpc hh hL h45 h40 h41 h53 h69 hB hq hp hng hN
    have hin : i < n := by omega
    have hL' := hL
    obtain ⟨a1, a11, a10, a12, hpt⟩ := hL'
    obtain ⟨b1, b2, b3⟩ := hpt ⟨i, hin⟩
    simp only at b1 b2 b3
    -- head: address of point i
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13⟩ :=
      scan_head Q off hE (s.integerMemory (s.core.ptrs 10 + i))
        (s.integerMemory (s.core.ptrs 12 + s.integerMemory (s.core.ptrs 10 + i))) s hpc hh (by rw [h45]) rfl (by rw [a11, h45]; exact_mod_cast hin)
        (by rw [a1]; exact_mod_cast hm)
    set s1 := run Q s detTape 8 with hs1
    have P1 : ∀ x, x ≠ 46 → x ≠ 47 → x ≠ 57 → s1.core.ptrs x = s.core.ptrs x := g6
    -- distances
    obtain ⟨u1, hu1, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ :=
      dl_loop Q off hE lo hi (pts ⟨i, hin⟩) m 0 s1 (by omega) g1 g2 (by rw [P1 1 (by decide) (by decide) (by decide), a1])
        hm g3 (by rw [g9 53 (by decide) (by decide), h53])
        (by intro jj; rw [g4, g10]; exact b3 jj)
        (by rw [P1 43 (by decide) (by decide) (by decide)]; unfold BoxAt; rw [g10]; exact hB)
        (by rw [g7, psum_zero]) (by rw [g8, psum_zero])
    set s2 := run Q s1 detTape u1 with hs2
    have Q1 : ∀ x, (x < 45 ∨ x = 48 ∨ 58 ≤ x) → s2.core.ptrs x = s.core.ptrs x := fun x hx => by
      rw [k5 x (by omega) (by omega), P1 x (by omega) (by omega) (by omega)]
    have Q0 : ∀ x, x ≠ 46 → x ≠ 47 → x ≠ 57 → s2.core.ptrs x = s.core.ptrs x := fun x h1 h2 h3 => by
      rw [k5 x h1 h3, P1 x h1 h2 h3]
    have R1 : ∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → s2.core.regs x = s.core.regs x := fun x hx => by
      rw [k6 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        g9 x (by omega) (by omega)]
    have M2 : s2.core.mem = s.core.mem := by rw [k7, g10]
    have I2 : s2.integerMemory = s.integerMemory := by rw [k8, g11]
    have W2 : s2.work = s.work + (8 + u1) := by rw [k9, g12]; ring
    have C2 : cellsWritten Q s (8 + u1) = ∅ := by rw [cellsWritten_add, ← hs1, g13, k10]; simp
    have r40 : s2.core.regs 40 = r * r := by rw [R1 40 (by decide), h40]
    have r41 : s2.core.regs 41 = (c * r) * (c * r) := by rw [R1 41 (by decide), h41]
    have hrun2 : run Q s detTape (8 + u1) = s2 := by rw [run_add, ← hs1]
    -- the remaining scan, after the point
    have tail : ∀ (u : ℕ) (s3 : State), u ≤ 23 * m + 12 → run Q s2 detTape u = s3 →
        s3.core.pc = off + 45 → s3.halted = false →
        s3.core.ptrs 45 = (i + 1 : ℕ) →
        (∀ x, (x < 45 ∨ x = 48 ∨ 58 ≤ x) → s3.core.ptrs x = s2.core.ptrs x) →
        (∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → s3.core.regs x = s2.core.regs x) →
        (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → s3.core.mem z = s.core.mem z) →
        s3.integerMemory = s.integerMemory → s3.work = s2.work + u →
        (∀ w ∈ cellsWritten Q s2 u, w.1 = true ∧ s.core.ptrs 48 ≤ w.2 ∧ w.2 < s.core.ptrs 48 + 2 * m) →
        (∀ i' : Fin n, (i' : ℕ) < i + 1 → i' ∉ goodS pts r c lo hi) →
        NearInv s3 pts r lo hi (i + 1) →
        ∃ t, t ≤ (60 * m + 30) * (d + 1) + 1 ∧ (run Q s detTape t).halted = false ∧
          ((∃ i0 : Fin n, i0 ∈ goodS pts r c lo hi ∧ (∀ i' : Fin n, i' < i0 → i' ∉ goodS pts r c lo hi) ∧
              (run Q s detTape t).core.pc = off + 128 ∧ (run Q s detTape t).core.ptrs 45 = i0) ∨
            ((∀ i' : Fin n, i' ∉ goodS pts r c lo hi) ∧ (run Q s detTape t).core.pc = off + 131 ∧
              NearInv (run Q s detTape t) pts r lo hi n)) ∧
          (∀ x, (x < 45 ∨ x = 48 ∨ 58 ≤ x) → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
          (∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → (run Q s detTape t).core.regs x = s.core.regs x) ∧
          (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) →
            (run Q s detTape t).core.mem z = s.core.mem z) ∧
          (run Q s detTape t).integerMemory = s.integerMemory ∧
          (run Q s detTape t).work = s.work + t ∧
          ∀ w ∈ cellsWritten Q s t, w.1 = true ∧ s.core.ptrs 48 ≤ w.2 ∧ w.2 < s.core.ptrs 48 + 2 * m := by
      intro u s3 hu hs3 c1 c2 c3 c4 c5 c6 c7 c8 c9 hng' hN'
      have S4 : ∀ x, (x < 45 ∨ x = 48 ∨ 58 ≤ x) → s3.core.ptrs x = s.core.ptrs x := fun x hx => by
        rw [c4 x hx, Q1 x hx]
      have T4 : ∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → s3.core.regs x = s.core.regs x := fun x hx => by
        rw [c5 x hx, R1 x hx]
      obtain ⟨t3, ht3, q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
        ih (i + 1) s3 (by omega) c1 c2
          (localPts_of hL (S4 1 (by decide)) (S4 10 (by decide)) (S4 11 (by decide)) (S4 12 (by decide))
            (fun z _ => by rw [c7]) (fun z hz => c6 z (Or.inr (by omega))))
          c3 (by rw [T4 40 (by decide), h40]) (by rw [T4 41 (by decide), h41]) (by rw [T4 53 (by decide), h53])
          (by rw [S4 69 (by decide), h69])
          (by rw [S4 43 (by decide)]; intro jj; have := jj.isLt
              rw [c6 _ (Or.inr (by omega)), c6 _ (Or.inr (by omega))]; exact hB jj)
          (by rw [S4 43 (by decide), S4 48 (by decide)]; exact hq) (by rw [S4 43 (by decide)]; exact hp)
          hng' hN'
      refine ⟨(8 + u1 + u) + t3, ?_, ?_⟩
      · rw [show (60 * m + 30) * (d + 1) + 1 = (60 * m + 30) * d + 1 + (60 * m + 30) by ring]
        generalize (60 * m + 30) * d = X at ht3 ⊢
        omega
      have hrun3 : run Q s detTape (8 + u1 + u) = s3 := by rw [run_add Q s detTape (8 + u1) u, hrun2, hs3]
      rw [cellsWritten_add Q s (8 + u1 + u) t3, cellsWritten_add Q s (8 + u1) u, C2, hrun2, hrun3,
        run_add Q s detTape (8 + u1 + u) t3, hrun3]
      refine ⟨q1, q2, fun x hx => by rw [q3 x hx, S4 x hx], fun x hx => by rw [q4 x hx, T4 x hx], ?_,
        by rw [q6, c7], by rw [q7, c8, W2]; ring, ?_⟩
      · intro z hz
        rw [q5 z (by rw [S4 48 (by decide)]; exact hz), c6 z hz]
      · intro w hw
        simp only [Finset.empty_union, Finset.mem_union] at hw
        rcases hw with hw | hw
        · exact c9 w hw
        · obtain ⟨e1, e2, e3⟩ := q8 w hw; rw [S4 48 (by decide)] at e2 e3; exact ⟨e1, e2, e3⟩
    -- the decision
    have hd2 : boxDist2 lo hi (pts ⟨i, hin⟩) ≤ r ^ 2 ↔ s2.core.regs 42 - s2.core.regs 40 ≤ 0 := by
      rw [k3, r40, near_iff]
    have hD2 : boxMaxDist2 lo hi (pts ⟨i, hin⟩) ≤ (c * r) ^ 2 ↔ s2.core.regs 43 - s2.core.regs 41 ≤ 0 := by
      rw [k4, r41, near_iff]
    have h45' : s2.core.ptrs 45 = (i : ℤ) := by rw [Q0 45 (by decide) (by decide) (by decide), h45]
    by_cases hnear : boxDist2 lo hi (pts ⟨i, hin⟩) ≤ r ^ 2
    · by_cases hgood : boxMaxDist2 lo hi (pts ⟨i, hin⟩) ≤ (c * r) ^ 2
      · -- an IN certificate at `i`
        obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
          dd_good Q off hE s2 k1 k2 (hd2.1 hnear) (hD2.1 hgood)
            (by rw [Q1 1 (by decide), a1]; exact_mod_cast hm)
        refine ⟨(8 + u1) + 4, ?_, ?_⟩
        · rw [show (60 * m + 30) * (d + 1) + 1 = (60 * m + 30) * d + 1 + (60 * m + 30) by ring]
          generalize (60 * m + 30) * d = X
          omega
        rw [run_add, hrun2, cellsWritten_add, C2, hrun2, f9]
        refine ⟨f2, Or.inl ⟨⟨i, hin⟩, (mem_goodS pts r c lo hi).2 ⟨hnear, hgood⟩,
          fun i' hi' => hng i' hi', f1, by rw [f3, h45']⟩, fun x hx => by rw [f3, Q1 x hx],
          fun x hx => by rw [f5 x (by omega), R1 x hx], fun z _ => by rw [f6, M2], by rw [f7, I2],
          by rw [f8, W2]; ring, by simp⟩
      · have hng' : ∀ i' : Fin n, (i' : ℕ) < i + 1 → i' ∉ goodS pts r c lo hi := by
          intro i' hi'
          rcases Nat.lt_or_ge (i' : ℕ) i with h | h
          · exact hng i' h
          · have : i' = ⟨i, hin⟩ := Fin.ext (show (i' : ℕ) = i by omega)
            subst this; rw [mem_goodS]; exact fun h => hgood h.2
        have hNP := nearP_succ_near pts r lo hi hin hnear
        rcases hN with ⟨h49, hN0⟩ | ⟨h49, hNne, hNB⟩
        · -- the first near point: initialise the near box
          obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ :=
            dd_fi Q off hE s2 k1 k2 (hd2.1 hnear) (fun h => hgood (hD2.2 h))
              (by rw [Q0 49 (by decide) (by decide) (by decide), Q1 69 (by decide), h49, h69])
              (by rw [Q1 1 (by decide), a1]; exact_mod_cast hm)
          set s3 := run Q s2 detTape 6 with hs3
          obtain ⟨v1, hv1, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ :=
            fi_loop Q off hE (pts ⟨i, hin⟩) m 0 s3 (by omega) f1 f2
              (by rw [f4 1 (by decide), Q1 1 (by decide), a1]) hm f3
              (by rw [f4 48 (by decide), f4 47 (by decide), k5 47 (by decide) (by decide), g4,
                Q1 48 (by decide)]; have := b2; omega)
              (by intro jj; rw [f4 47 (by decide), k5 47 (by decide) (by decide), g4, f7, M2]; exact b3 jj)
              (fun jj h => absurd h (by omega))
          set s4 := run Q s3 detTape v1 with hs4
          obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ :=
            seg_next Q off hE s4 l1 l2
              (by rw [l6 1 (by decide) (by decide) (by decide), f4 1 (by decide), Q1 1 (by decide), a1]; exact_mod_cast hm)
          have p48 : s3.core.ptrs 48 = s.core.ptrs 48 := by rw [f4 48 (by decide), Q1 48 (by decide)]
          apply tail (6 + v1 + 2) (run Q s4 detTape 2) (by omega)
            (by rw [run_add, run_add, ← hs3, ← hs4]) n1 n2
            (by rw [n3, l6 45 (by decide) (by decide) (by decide), f4 45 (by decide), h45']; push_cast; ring)
            (fun x hx => by rw [n4 x (by omega), l6 x (by omega) (by omega) (by omega), f4 x (by omega)])
            (fun x hx => by rw [n5, l7 x (by omega), f6 x (by omega)])
            (fun z hz => by rw [n6, l4 z (by rw [p48]; exact hz), f7, M2])
            (by rw [n7, l8, f8, I2]) (by rw [n8, l9, f9]; ring)
            (by
              intro w hw
              rw [cellsWritten_add Q s2 (6 + v1) 2, cellsWritten_add Q s2 6 v1, run_add Q s2 detTape 6 v1, ← hs3, ← hs4, f10, n9] at hw
              simp only [Finset.empty_union, Finset.union_empty] at hw
              obtain ⟨e1, e2, e3⟩ := l10 w hw; rw [p48] at e2 e3; exact ⟨e1, e2, e3⟩)
            hng'
          right
          refine ⟨by rw [n4 49 (by decide), l5], by rw [hNP]; exact Finset.insert_nonempty _ _, ?_⟩
          rw [n4 48 (by decide), l6 48 (by decide) (by decide) (by decide), hNP, hN0, Finset.insert_empty]
          intro jj
          rw [n6, aLo_single, bHi_single]
          exact l3 jj
        · -- a later near point: update the near box
          obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ :=
            dd_up Q off hE s2 k1 k2 (hd2.1 hnear) (fun h => hgood (hD2.2 h))
              (by rw [Q0 49 (by decide) (by decide) (by decide), Q1 69 (by decide), h49, h69]; norm_num)
              (by rw [Q1 1 (by decide), a1]; exact_mod_cast hm)
          set s3 := run Q s2 detTape 6 with hs3
          have p48 : s3.core.ptrs 48 = s.core.ptrs 48 := by rw [f4 48 (by decide), Q1 48 (by decide)]
          obtain ⟨v1, hv1, l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ :=
            up_loop Q off hE (pts ⟨i, hin⟩) (aLo pts (nearP pts r lo hi i)) (bHi pts (nearP pts r lo hi i))
              m 0 s3 (by omega) f1 f2 (by rw [f4 1 (by decide), Q1 1 (by decide), a1]) hm f3
              (by rw [f6 53 (by decide), R1 53 (by decide), h53])
              (by rw [p48, f4 47 (by decide), k5 47 (by decide) (by decide), g4]; have := b2; omega)
              (by intro jj; rw [f4 47 (by decide), k5 47 (by decide) (by decide), g4, f7, M2]; exact b3 jj)
              (fun jj h => absurd h (by omega))
              (by intro jj _; rw [p48, f7, M2]; exact hNB jj)
          set s4 := run Q s3 detTape v1 with hs4
          obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ :=
            seg_next Q off hE s4 l1 l2
              (by rw [l5 1 (by decide) (by decide), f4 1 (by decide), Q1 1 (by decide), a1]; exact_mod_cast hm)
          apply tail (6 + v1 + 2) (run Q s4 detTape 2) (by omega)
            (by rw [run_add, run_add, ← hs3, ← hs4]) n1 n2
            (by rw [n3, l5 45 (by decide) (by decide), f4 45 (by decide), h45']; push_cast; ring)
            (fun x hx => by rw [n4 x (by omega), l5 x (by omega) (by omega), f4 x (by omega)])
            (fun x hx => by rw [n5, l6 x (by omega) (by omega) (by omega) (by omega), f6 x (by omega)])
            (fun z hz => by rw [n6, l4 z (by rw [p48]; exact hz), f7, M2])
            (by rw [n7, l7, f8, I2]) (by rw [n8, l8, f9]; ring)
            (by
              intro w hw
              rw [cellsWritten_add Q s2 (6 + v1) 2, cellsWritten_add Q s2 6 v1, run_add Q s2 detTape 6 v1, ← hs3, ← hs4, f10, n9] at hw
              simp only [Finset.empty_union, Finset.union_empty] at hw
              obtain ⟨e1, e2, e3⟩ := l9 w hw; rw [p48] at e2 e3; exact ⟨e1, e2, e3⟩)
            hng'
          right
          refine ⟨by rw [n4 49 (by decide), l5 49 (by decide) (by decide), f4 49 (by decide), Q0 49 (by decide) (by decide) (by decide), h49],
            by rw [hNP]; exact Finset.insert_nonempty _ _, ?_⟩
          rw [n4 48 (by decide), l5 48 (by decide) (by decide), hNP]
          intro jj
          rw [n6, aLo_insert pts hNne, bHi_insert pts hNne]
          exact l3 jj
    · -- far: skip the point
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ :=
        dd_far Q off hE s2 k1 k2 (fun h => hnear (hd2.2 h)) (by rw [Q1 1 (by decide), a1]; exact_mod_cast hm)
      set s3 := run Q s2 detTape 3 with hs3
      obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ :=
        seg_next Q off hE s3 f1 f2 (by rw [f3, Q1 1 (by decide), a1]; exact_mod_cast hm)
      apply tail (3 + 2) (run Q s3 detTape 2) (by omega) (by rw [run_add, ← hs3]) n1 n2
        (by rw [n3, f3, h45']; push_cast; ring)
        (fun x hx => by rw [n4 x (by omega), f3])
        (fun x hx => by rw [n5, f5 x (by omega)])
        (fun z _ => by rw [n6, f6, M2]) (by rw [n7, f7, I2]) (by rw [n8, f8])
        (by
          intro w hw
          rw [cellsWritten_add, ← hs3, f9, n9] at hw
          simp at hw)
        (by
          intro i' hi'
          rcases Nat.lt_or_ge (i' : ℕ) i with h | h
          · exact hng i' h
          · have : i' = ⟨i, hin⟩ := Fin.ext (show (i' : ℕ) = i by omega)
            subst this; rw [mem_goodS]; exact fun h => hnear h.1)
      unfold NearInv
      rw [n4 49 (by decide), f3, n4 48 (by decide), f3, Q1 48 (by decide), nearP_succ_far pts r lo hi hin hnear]
      rcases hN with ⟨h49, hN0⟩ | ⟨h49, hNne, hNB⟩
      · left; exact ⟨by rw [Q0 49 (by decide) (by decide) (by decide)]; exact h49, hN0⟩
      · right
        refine ⟨by rw [Q0 49 (by decide) (by decide) (by decide)]; exact h49, hNne, ?_⟩
        intro jj; rw [n6, f6, M2]; exact hNB jj

end DetANN.HPIM.BD

-- ===== BD_Inv =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma env_of {s s' : State} {pts : Fin n → Fin m → ℝ} {r c : ℝ} {Z0 : ℤ} (h : Env s pts r c Z0)
    (hP : ∀ x, (x < 40 ∨ x = 40 ∨ x = 60 ∨ x = 68 ∨ x = 69) → x ≠ 13 → x ≠ 14 → x ≠ 17 →
      s'.core.ptrs x = s.core.ptrs x)
    (hR : ∀ x, (x < 42 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x)
    (hI : ∀ z, 0 ≤ z → s'.integerMemory z = s.integerMemory z)
    (hM : ∀ z, 0 ≤ z → s'.core.mem z = s.core.mem z) : Env s' pts r c Z0 := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := h
  refine ⟨localPts_of a0 (hP 1 (by decide) (by decide) (by decide) (by decide))
      (hP 10 (by decide) (by decide) (by decide) (by decide)) (hP 11 (by decide) (by decide) (by decide) (by decide))
      (hP 12 (by decide) (by decide) (by decide) (by decide)) hI hM,
    by rw [hR 11 (by decide), a1], by rw [hR 12 (by decide), a2],
    by rw [hP 40 (by decide) (by decide) (by decide) (by decide), a3],
    by rw [hP 60 (by decide) (by decide) (by decide) (by decide), a4],
    by rw [hP 68 (by decide) (by decide) (by decide) (by decide), a5],
    by rw [hP 69 (by decide) (by decide) (by decide) (by decide), a6],
    by rw [hR 40 (by decide), a7], by rw [hR 41 (by decide), a8], by rw [hR 49 (by decide), a9],
    by rw [hR 50 (by decide), a10], by rw [hR 53 (by decide), a11]⟩

/-- The task stack from `sp`: entries `(e, p, sl)` at `e` = `[p, sl, link]`, ending at `Z0`. -/
def StkAt (s : State) (Z0 : ℤ) : ℤ → List (ℤ × ℤ × ℤ) → Prop
  | sp, [] => sp = Z0
  | sp, (e, p, sl) :: S => sp = e ∧ e + 3 ≤ Z0 ∧ s.integerMemory e = p ∧ s.integerMemory (e + 1) = sl ∧
      StkAt s Z0 (s.integerMemory (e + 2)) S

lemma stkAt_of {s s' : State} {Z0 : ℤ} :
    ∀ (S : List (ℤ × ℤ × ℤ)) (sp : ℤ), StkAt s Z0 sp S →
      (∀ x ∈ S, ∀ z, x.1 ≤ z → z < x.1 + 3 → s'.integerMemory z = s.integerMemory z) →
      StkAt s' Z0 sp S := by
  intro S
  induction S with
  | nil => intro sp h _; exact h
  | cons x S ih =>
    obtain ⟨e, p, sl⟩ := x
    intro sp h hf
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have he := hf (e, p, sl) List.mem_cons_self
    refine ⟨h1, h2, by rw [he e le_rfl (by omega), h3], by rw [he (e + 1) (by omega) (by omega), h4], ?_⟩
    rw [he (e + 2) (by omega) (by omega)]
    exact ih _ h5 fun x hx => hf x (List.mem_cons_of_mem _ hx)

/-- A stored subtree: `T` is at `u` in every state that agrees on its integer cells `[Zl, Zh)` and its
real cells `[Rl, Rh)` and `[p, p + 2m)` (the root box). The windows run up to `Z0`, `R0`. -/
def GoodT (s : State) (Z0 R0 Zl Zh Rl Rh p u : ℤ) (T : BSP m) : Prop :=
  ∀ s'' : State, (∀ z, Zl ≤ z → z < Zh → s''.integerMemory z = s.integerMemory z) →
    (∀ z, (Rl ≤ z ∧ z < Rh) ∨ (p ≤ z ∧ z < p + 2 * m) → s''.core.mem z = s.core.mem z) →
    BSPAt m s'' Zl Z0 Rl R0 u T

lemma bspat_mono {s : State} {ilo ihi rlo rhi ilo' rlo' u : ℤ} {T : BSP m}
    (h : BSPAt m s ilo ihi rlo rhi u T) (h1 : ilo' ≤ ilo) (h2 : rlo' ≤ rlo) :
    BSPAt m s ilo' ihi rlo' rhi u T := by
  induction h with
  | leaf u lo hi a a1 a2 a3 a4 a5 a6 a7 a8 =>
    exact BSPAt.leaf u lo hi a (by omega) a2 a3 (by omega) a5 a6 a7 a8
  | cut u lo hi l r a1 a2 a3 a4 a5 a6 a7 _ _ ihl ihr =>
    exact BSPAt.cut u lo hi l r (by omega) a2 a3 (by omega) a5 a6 a7 ihl ihr

lemma goodT_mono {s s2 : State} {Z0 R0 Zl Zh Rl Rh p u : ℤ} {T : BSP m}
    (h : GoodT s Z0 R0 Zl Zh Rl Rh p u T)
    (hI : ∀ z, Zl ≤ z → z < Zh → s2.integerMemory z = s.integerMemory z)
    (hM : ∀ z, (Rl ≤ z ∧ z < Rh) ∨ (p ≤ z ∧ z < p + 2 * m) → s2.core.mem z = s.core.mem z) :
    GoodT s2 Z0 R0 Zl Zh Rl Rh p u T :=
  fun s'' h1 h2 => h s'' (fun z a b => (h1 z a b).trans (hI z a b)) (fun z a => (h2 z a).trans (hM z a))

/-- Widen the windows of a stored subtree. -/
lemma goodT_widen {s : State} {Z0 R0 Zl Zh Rl Rh p u Zl' Zh' Rl' Rh' : ℤ} {T : BSP m}
    (h : GoodT s Z0 R0 Zl Zh Rl Rh p u T) (h1 : Zl' ≤ Zl) (h2 : Zh ≤ Zh') (h3 : Rl' ≤ Rl) (h4 : Rh ≤ Rh') :
    ∀ s'' : State, (∀ z, Zl' ≤ z → z < Zh' → s''.integerMemory z = s.integerMemory z) →
      (∀ z, (Rl' ≤ z ∧ z < Rh') ∨ (p ≤ z ∧ z < p + 2 * m) → s''.core.mem z = s.core.mem z) →
      BSPAt m s'' Zl' Z0 Rl' R0 u T :=
  fun s'' hI hM => bspat_mono (h s'' (fun z a b => hI z (by omega) (by omega))
    (fun z hz => hM z (hz.imp (fun ⟨a, b⟩ => ⟨by omega, by omega⟩) id))) h1 h3

lemma fr_comp {Q : Program} {s1 s2 s3 : State} {t1 t2 : ℕ} {A B : ℤ → Prop}
    (h1 : Fr Q s1 s2 t1 A) (h2 : Fr Q s2 s3 t2 B) : Fr Q s1 s3 (t1 + t2) (fun z => A z ∨ B z) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h1
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := h2
  refine ⟨by rw [run_add, a0, b0], by rw [b1, a1]; ring, by omega, by omega,
    fun x h c d => by rw [b4 x h c d, a4 x h c d], by rw [b5, a5], fun x h => by rw [b6 x h, a6 x h],
    fun z hz hA => by rw [b7 z (by omega) (fun h => hA (Or.inr h)), a7 z (by omega) (fun h => hA (Or.inl h))],
    fun z hz => by rw [b8 z (by omega), a8 z (by omega)], ?_⟩
  intro w hw
  rw [cellsWritten_add, a0] at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · rcases a9 w hw with ⟨e1, ⟨c1, c2⟩ | e2⟩ | ⟨e1, c1, c2⟩
    · exact Or.inl ⟨e1, Or.inl ⟨by omega, c2⟩⟩
    · exact Or.inl ⟨e1, Or.inr (Or.inl e2)⟩
    · exact Or.inr ⟨e1, by omega, c2⟩
  · rcases b9 w hw with ⟨e1, ⟨c1, c2⟩ | e2⟩ | ⟨e1, c1, c2⟩
    · exact Or.inl ⟨e1, Or.inl ⟨c1, by omega⟩⟩
    · exact Or.inl ⟨e1, Or.inr (Or.inr e2)⟩
    · exact Or.inr ⟨e1, c1, by omega⟩

lemma fr_mono {Q : Program} {s s' : State} {t : ℕ} {A B : ℤ → Prop} (h : Fr Q s s' t A)
    (hAB : ∀ z, A z → (s'.core.ptrs 13 ≤ z ∧ z < s.core.ptrs 13) ∨ B z) : Fr Q s s' t B := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨a0, a1, a2, a3, a4, a5, a6, fun z hz hb => a7 z hz (fun ha => ?_), a8, ?_⟩
  · rcases hAB z ha with h | h
    · omega
    · exact hb h
  intro w hw
  rcases a9 w hw with ⟨e1, e2 | e2⟩ | e
  · exact Or.inl ⟨e1, Or.inl e2⟩
  · rcases hAB _ e2 with h | h
    · exact Or.inl ⟨e1, Or.inl h⟩
    · exact Or.inl ⟨e1, Or.inr h⟩
  · exact Or.inr e

/-- A stored subtree survives a run that writes neither its windows nor its root box. -/
lemma goodT_fr {Q : Program} {s s' : State} {t : ℕ} {A : ℤ → Prop} {Z0 R0 Zl Zh Rl Rh p u : ℤ}
    {T : BSP m} (hG : GoodT s Z0 R0 Zl Zh Rl Rh p u T) (h : Fr Q s s' t A)
    (hZ : s.core.ptrs 13 ≤ Zl) (hR : s.core.ptrs 14 ≤ Rl) (hp : s.core.ptrs 14 ≤ p)
    (hA : ∀ z, A z → z < Zl ∨ Zh ≤ z) : GoodT s' Z0 R0 Zl Zh Rl Rh p u T := by
  obtain ⟨-, -, -, -, -, -, -, a7, a8, -⟩ := h
  refine goodT_mono hG (fun z h1 h2 => a7 z (Or.inr (by omega)) (fun ha => by have := hA z ha; omega))
    (fun z hz => a8 z (Or.inr (by rcases hz with ⟨c, d⟩ | ⟨c, d⟩ <;> omega)))

/-- A cut node over two stored children. -/
lemma goodT_cut {s : State} {Z0 R0 Zl Zh Rl Rh p u : ℤ} {lo hi : Fin m → ℝ} {L R : BSP m}
    {ZlL ZhL RlL RhL pL uL ZlR ZhR RlR RhR pR uR : ℤ}
    (hu : Zl ≤ u) (hu4 : u + 4 ≤ Zh) (hZ : Zh ≤ Z0) (hp1 : Rl ≤ p) (hp2 : p + 2 * m ≤ R0)
    (h0 : s.integerMemory u = 1) (h1 : s.integerMemory (u + 1) = p)
    (hB : ∀ j : Fin m, s.core.mem (p + j) = lo j ∧ s.core.mem (p + j + m) = hi j)
    (h2 : s.integerMemory (u + 2) = uL) (h3 : s.integerMemory (u + 3) = uR)
    (hL : GoodT s Z0 R0 ZlL ZhL RlL RhL pL uL L) (hR : GoodT s Z0 R0 ZlR ZhR RlR RhR pR uR R)
    (l1 : Zl ≤ ZlL) (l2 : ZhL ≤ Zh) (l3 : Rl ≤ RlL) (l4 : RhL ≤ Rh) (l5 : Rl ≤ pL) (l6 : pL + 2 * m ≤ Rh)
    (r1 : Zl ≤ ZlR) (r2 : ZhR ≤ Zh) (r3 : Rl ≤ RlR) (r4 : RhR ≤ Rh) (r5 : Rl ≤ pR) (r6 : pR + 2 * m ≤ Rh) :
    GoodT s Z0 R0 Zl Zh Rl Rh p u (.cut lo hi L R) := by
  intro s'' hI hM
  have i0 : s''.integerMemory (u + 1) = p := by rw [hI _ (by omega) (by omega), h1]
  refine BSPAt.cut u lo hi L R hu (by omega) (by rw [hI _ hu (by omega), h0]) (by rw [i0]; exact hp1)
    (by rw [i0]; exact hp2) ?_ ?_ ?_ ?_
  · intro j; have := j.isLt; rw [i0, hM _ (Or.inr ⟨by omega, by omega⟩)]; exact (hB j).1
  · intro j; have := j.isLt; rw [i0, hM _ (Or.inr ⟨by omega, by omega⟩), add_right_comm]; exact (hB j).2
  · rw [hI _ (by omega) (by omega), h2]
    refine bspat_mono (hL s'' (fun z a b => hI z (by omega) (by omega)) (fun z hz => hM z (Or.inl ?_))) l1 l3
    rcases hz with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> omega
  · rw [hI _ (by omega) (by omega), h3]
    refine bspat_mono (hR s'' (fun z a b => hI z (by omega) (by omega)) (fun z hz => hM z (Or.inl ?_))) r1 r3
    rcases hz with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> omega

end DetANN.HPIM.BD

-- ===== BD_Task =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- The work per node. -/
def W0 (n m : ℕ) : ℕ := 400 * (n + 1) * (m + 1) ^ 2

/-- The state after a task: back at `DISPATCH` with the task popped, `T` stored through the slot, and
bounded fresh scratch. -/
def TPost (Q : Program) (off : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 R0 : ℤ) (s : State) (p sl : ℤ)
    (S : List (ℤ × ℤ × ℤ)) (T : BSP m) (t : ℕ) (s' : State) (u : ℤ) : Prop :=
  s'.core.pc = off + 34 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ StkAt s' Z0 (s'.core.ptrs 42) S ∧
    s'.integerMemory sl = u ∧
    GoodT s' Z0 R0 (s'.core.ptrs 13) (s.core.ptrs 13) (s'.core.ptrs 14) (s.core.ptrs 14) p u T ∧
    s.core.ptrs 13 ≤ s'.core.ptrs 13 + 10 * BB.size T ∧
    s.core.ptrs 14 ≤ s'.core.ptrs 14 + 6 * m * BB.size T ∧
    t ≤ W0 n m * BB.size T ∧ Fr Q s s' t (fun z => z = sl)

/-- The contract of a task with fuel `f`: from `DISPATCH` with the task `(p, sl)` on top of the
stack, the run reaches `TPost` for `build f lo hi`. -/
def TaskOK (Q : Program) (off : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 R0 : ℤ) (f : ℕ) : Prop :=
  ∀ (s : State) (e p sl : ℤ) (S : List (ℤ × ℤ × ℤ)) (lo hi : Fin m → ℝ),
    s.core.pc = off + 34 → s.halted = false → Env s pts r c Z0 →
    StkAt s Z0 (s.core.ptrs 42) ((e, p, sl) :: S) →
    (∀ x ∈ (e, p, sl) :: S, s.core.ptrs 13 ≤ x.1) →
    s.core.ptrs 13 ≤ sl → sl < Z0 → (∀ x ∈ S, sl < x.1 ∨ x.1 + 3 ≤ sl) →
    BoxAt s p lo hi → s.core.ptrs 14 ≤ p → p + 2 * m ≤ R0 → s.core.ptrs 13 ≤ Z0 →
    ¬ Starves pts r c f lo hi →
    ∃ (t : ℕ) (s' : State) (u : ℤ), TPost Q off pts r c Z0 R0 s p sl S (build pts r c f lo hi) t s' u

/-- The head of a task: pop it, allocate the near box `q = R − 2m`, and scan the points. -/
lemma task_head (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m)
    (s : State) (e p sl : ℤ) (S : List (ℤ × ℤ × ℤ)) (lo hi : Fin m → ℝ)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hEnv : Env s pts r c Z0)
    (hS : StkAt s Z0 (s.core.ptrs 42) ((e, p, sl) :: S))
    (hB : BoxAt s p lo hi) (hRp : s.core.ptrs 14 ≤ p) (hpR : p + 2 * m ≤ R0) (hR0 : R0 ≤ 0) :
    ∃ t s2, run Q s detTape t = s2 ∧ t ≤ (60 * m + 30) * n + 12 ∧ s2.halted = false ∧
      s2.core.ptrs 43 = p ∧ s2.core.ptrs 44 = sl ∧ s2.core.ptrs 42 = s.integerMemory (e + 2) ∧
      s2.core.ptrs 48 = s.core.ptrs 14 - 2 * m ∧ s2.core.ptrs 14 = s.core.ptrs 14 - 2 * m ∧
      (∀ x, (x < 42 ∨ x = 59 ∨ 60 ≤ x ∨ x = 40) → x ≠ 14 → s2.core.ptrs x = s.core.ptrs x) ∧
      (∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → s2.core.regs x = s.core.regs x) ∧
      (∀ z, (z < s.core.ptrs 14 - 2 * m ∨ s.core.ptrs 14 ≤ z) → s2.core.mem z = s.core.mem z) ∧
      s2.integerMemory = s.integerMemory ∧ s2.work = s.work + t ∧
      (∀ w ∈ cellsWritten Q s t, w.1 = true ∧ s.core.ptrs 14 - 2 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14) ∧
      Env s2 pts r c Z0 ∧ BoxAt s2 p lo hi ∧
      ((∃ i0 : Fin n, i0 ∈ goodS pts r c lo hi ∧ (∀ i' : Fin n, i' < i0 → i' ∉ goodS pts r c lo hi) ∧
          s2.core.pc = off + 128 ∧ s2.core.ptrs 45 = i0) ∨
        ((∀ i' : Fin n, i' ∉ goodS pts r c lo hi) ∧ s2.core.pc = off + 131 ∧
          NearInv s2 pts r lo hi n)) := by
  obtain ⟨hL, e11, e12, e40, e60, e68, e69, e40', e41, e49, e50, e53⟩ := hEnv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS
  obtain ⟨a1, a11, a10, a12, hpt⟩ := hL
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩ :=
    seg_pop Q off hE p sl (s.integerMemory (e + 2)) s hpc hh (by rw [h1]; exact h3) (by rw [h1]; exact h4)
      (by rw [h1]) (by rw [h1, e40]; omega) hm1
  set s1 := run Q s detTape 11 with hs1
  have P1 : ∀ x, x ≠ 14 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 48 → x ≠ 49 → x ≠ 57 →
      s1.core.ptrs x = s.core.ptrs x := g11
  rw [e60] at g3 g8
  obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    scan_loop Q off hE pts r c lo hi hm n 0 s1 (by omega) g1 g2
      (localPts_of ⟨a1, a11, a10, a12, hpt⟩ (P1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) (P1 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)) (P1 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (P1 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun z _ => by rw [g14]) (fun z _ => by rw [g13]))
      (by rw [g7]; rfl) (by rw [g12, e40']) (by rw [g12, e41]) (by rw [g12, e53])
      (by rw [P1 69 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e69])
      (by rw [g5]; unfold BoxAt; rw [g13]; exact hB) (by rw [g5, g8]; omega) (by rw [g5]; omega)
      (fun i' h => absurd h (by omega))
      (Or.inl ⟨g9, by rw [nearP_zero]⟩)
  set s2 := run Q s1 detTape t2 with hs2
  have hrun : run Q s detTape (11 + t2) = s2 := by rw [run_add, ← hs1]
  have P2 : ∀ x, (x < 42 ∨ x = 59 ∨ 60 ≤ x ∨ x = 40) → x ≠ 14 → s2.core.ptrs x = s.core.ptrs x := by
    intro x hx h14
    rw [q3 x (by omega), P1 x h14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have R2 : ∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → s2.core.regs x = s.core.regs x := fun x hx => by
    rw [q4 x hx, g12]
  have M2 : ∀ z, (z < s.core.ptrs 14 - 2 * m ∨ s.core.ptrs 14 ≤ z) → s2.core.mem z = s.core.mem z := by
    intro z hz; rw [q5 z (by rw [g8]; omega), g13]
  refine ⟨11 + t2, s2, hrun, by clear * - ht2; generalize (60 * m + 30) * n = X at *; omega, q1, by rw [q3 43 (by decide), g5], by rw [q3 44 (by decide), g6],
    by rw [q3 42 (by decide), g4], by rw [q3 48 (by decide), g8], by rw [q3 14 (by decide), g3],
    P2, R2, M2, by rw [q6, g14], by rw [q7, g15]; ring, ?_, ?_, ?_, ?_⟩
  · intro w hw
    rw [cellsWritten_add, ← hs1, g16, Finset.empty_union] at hw
    obtain ⟨e1, e2, e3⟩ := q8 w hw; rw [g8] at e2 e3; exact ⟨e1, e2, by omega⟩
  · exact env_of ⟨⟨a1, a11, a10, a12, hpt⟩, e11, e12, e40, e60, e68, e69, e40', e41, e49, e50, e53⟩
      (fun x hx a b c => P2 x (by omega) b) (fun x hx => R2 x (by omega)) (fun z _ => by rw [q6, g14])
      (fun z hz => M2 z (Or.inr (by omega)))
  · intro jj; have := jj.isLt
    rw [M2 _ (Or.inr (by omega)), M2 _ (Or.inr (by omega))]; exact hB jj
  · rcases q2 with ⟨i0, a, b, c, d⟩ | ⟨a, b, d⟩
    · left; exact ⟨i0, a, b, c, d⟩
    · right; exact ⟨a, b, d⟩

/-- The integer code of a leaf answer. -/
def encA : Option ℕ → ℤ
  | none => 0
  | some i => (i : ℤ) + 1

/-- Finish a task at a leaf: from `LEAF` with the answer in pointer `61`, write the leaf node and
return to `DISPATCH`. -/
lemma leaf_finish (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (T : BSP m) (a : Option ℕ)
    (s : State) (e p sl : ℤ) (S : List (ℤ × ℤ × ℤ)) (lo hi : Fin m → ℝ) (hT : T = .leaf lo hi a)
    (hS : StkAt s Z0 (s.core.ptrs 42) ((e, p, sl) :: S))
    (hge : ∀ x ∈ (e, p, sl) :: S, s.core.ptrs 13 ≤ x.1)
    (hsl : s.core.ptrs 13 ≤ sl) (hsl0 : sl < Z0) (hav : ∀ x ∈ S, sl < x.1 ∨ x.1 + 3 ≤ sl)
    (hRp : s.core.ptrs 14 ≤ p) (hpR : p + 2 * m ≤ R0) (hZ : s.core.ptrs 13 ≤ Z0) (hZ0 : Z0 ≤ 0)
    (tL : ℕ) (sL : State) (hL : run Q s detTape tL = sL) (htL : tL + 12 ≤ W0 n m)
    (l1 : sL.core.pc = off + 383) (l2 : sL.halted = false) (l3 : sL.core.ptrs 43 = p)
    (l4 : sL.core.ptrs 44 = sl) (l5 : sL.core.ptrs 42 = s.integerMemory (e + 2))
    (l6 : sL.core.ptrs 61 = encA a) (l7 : sL.core.ptrs 14 = s.core.ptrs 14 - 2 * m)
    (l8 : ∀ x, (x < 42 ∨ x = 59 ∨ 60 ≤ x ∨ x = 40) → x ≠ 14 → x ≠ 61 → sL.core.ptrs x = s.core.ptrs x)
    (l9 : ∀ x, (x < 42 ∨ (49 ≤ x ∧ x ≠ 54)) → sL.core.regs x = s.core.regs x)
    (l10 : ∀ z, (z < s.core.ptrs 14 - 2 * m ∨ s.core.ptrs 14 ≤ z) → sL.core.mem z = s.core.mem z)
    (l11 : sL.integerMemory = s.integerMemory) (l12 : sL.work = s.work + tL)
    (l13 : ∀ w ∈ cellsWritten Q s tL, w.1 = true ∧ s.core.ptrs 14 - 2 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14)
    (l14 : Env sL pts r c Z0) (l15 : BoxAt sL p lo hi) :
    ∃ (t : ℕ) (s' : State) (u : ℤ), TPost Q off pts r c Z0 R0 s p sl S T t s' u := by
  have p13 : sL.core.ptrs 13 = s.core.ptrs 13 := l8 13 (by decide) (by decide) (by decide)
  have hm1 : 1 ≤ sL.core.ptrs 1 := by rw [l14.1.1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15⟩ :=
    seg_leaf Q off hE sL l1 l2 hm1 (by rw [p13, l4]; exact hsl)
  set s4 := run Q sL detTape 12 with hs4
  have p14 : s4.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by rw [g6 14 (by decide) (by decide) (by decide), l7]
  have hrun : run Q s detTape (tL + 12) = s4 := by rw [run_add, hL]
  have h69 : sL.core.ptrs 69 = 0 := l14.2.2.2.2.2.2.1
  simp only [p13, l4, l3, l6, h69] at g3 g9 g10 g11 g12 g13 g15
  obtain ⟨_, _, h3, h4, h5⟩ := hS
  have hBS : BB.size T = 1 := by rw [hT]; rfl
  have P4 : ∀ x, (x < 42 ∨ x = 59 ∨ 60 ≤ x ∨ x = 40) → x ≠ 13 → x ≠ 14 → x ≠ 52 → x ≠ 57 → x ≠ 61 →
      s4.core.ptrs x = s.core.ptrs x := fun x hx a b c d f => by rw [g6 x a c d, l8 x hx b f]
  have I4 : ∀ z, z ≠ s.core.ptrs 13 - 3 → z ≠ s.core.ptrs 13 - 2 → z ≠ s.core.ptrs 13 - 1 → z ≠ sl →
      s4.integerMemory z = s.integerMemory z := fun z a b c d => by rw [g13 z a b c d, l11]
  refine ⟨tL + 12, s4, s.core.ptrs 13 - 3, g1, g2, ?_, ?_, g12, ?_, by rw [g3, hBS]; omega,
    by rw [p14, hBS]; push_cast; omega, by rw [hBS]; omega, hrun, by rw [g14, l12]; ring,
    by rw [g3]; omega, by rw [p14]; omega,
    fun x hx a b => P4 x (by omega) a b (by omega) (by omega) (by omega),
    P4 59 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    fun x hx => by rw [congrFun g7 x, l9 x (by omega)], ?_, ?_, ?_⟩
  · exact env_of l14 (fun x hx a b c => by rw [g6 x a (by omega) (by omega)]) (fun x _ => by rw [g7])
      (fun z hz => by rw [g13 z (by omega) (by omega) (by omega) (by omega)]) (fun z _ => by rw [g8])
  · rw [g6 42 (by decide) (by decide) (by decide), l5]
    exact stkAt_of S _ h5 (fun x hx z z1 z2 => by
      have := hge x (List.mem_cons_of_mem _ hx)
      rcases hav x hx with h | h <;> exact I4 z (by omega) (by omega) (by omega) (by omega))
  · intro s'' hI hM
    rw [g3] at hI; rw [p14] at hM
    rw [g3, p14, hT]
    have hu : s''.integerMemory (s.core.ptrs 13 - 3) = 0 := by
      rw [hI _ (by omega) (by omega)]; exact g9
    have hu1 : s''.integerMemory (s.core.ptrs 13 - 3 + 1) = p := by
      rw [hI _ (by omega) (by omega), show s.core.ptrs 13 - 3 + 1 = s.core.ptrs 13 - 2 by ring]; exact g10
    have hu2 : s''.integerMemory (s.core.ptrs 13 - 3 + 2) = encA a := by
      rw [hI _ (by omega) (by omega), show s.core.ptrs 13 - 3 + 2 = s.core.ptrs 13 - 1 by ring]; exact g11
    refine BSPAt.leaf _ lo hi a le_rfl (by omega) hu (by rw [hu1]; omega) (by rw [hu1]; exact hpR) ?_ ?_ ?_
    · intro j; have := j.isLt
      rw [hu1, hM _ (Or.inr ⟨by omega, by omega⟩), g8]; exact (l15 j).1
    · intro j; have := j.isLt
      rw [hu1, hM _ (Or.inr ⟨by omega, by omega⟩), g8, add_right_comm]; exact (l15 j).2
    · rw [hu2]; cases a <;> rfl
  · intro z hz hne
    rw [g3] at hz
    by_cases h1 : z = s.core.ptrs 13 - 3
    · omega
    · by_cases h2 : z = s.core.ptrs 13 - 2
      · omega
      · by_cases h3' : z = s.core.ptrs 13 - 1
        · omega
        · exact I4 z h1 h2 h3' hne
  · intro z hz; rw [p14] at hz; rw [g8, l10 z hz]
  · intro w hw
    rw [cellsWritten_add, hL] at hw
    rcases Finset.mem_union.1 hw with hw | hw
    · right; obtain ⟨a1, a2, a3⟩ := l13 w hw; rw [p14]; exact ⟨a1, a2, a3⟩
    · left
      rcases g15 w hw with rfl | rfl | rfl | rfl
      · exact ⟨rfl, Or.inl ⟨by rw [g3], by omega⟩⟩
      · exact ⟨rfl, Or.inl ⟨by rw [g3]; omega, by omega⟩⟩
      · exact ⟨rfl, Or.inl ⟨by rw [g3]; omega, by omega⟩⟩
      · exact ⟨rfl, Or.inr rfl⟩

end DetANN.HPIM.BD

-- ===== BD_Mid =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma boxAt_zero {s : State} {p : ℤ} {lo hi : Fin m → ℝ} (hm : 0 < m) (h : BoxAt s p lo hi) :
    s.core.mem p = lo ⟨0, hm⟩ ∧ s.core.mem (p + m) = hi ⟨0, hm⟩ := by
  have := h ⟨0, hm⟩; simpa using this

lemma rmax_zero_side (hm : 0 < m) (lo hi : Fin m → ℝ) :
    rmax (side lo hi) 0 = hi ⟨0, hm⟩ - lo ⟨0, hm⟩ := by
  simp only [rmax, side, dif_pos hm]

/-- From `SCD` with a near point: the tight box at `q`, then `σ` of it (real `51`) and of the box
(real `52`), at `SGD`. -/
lemma task_mid (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (lo hi : Fin m → ℝ) (s : State)
    (hpc : s.core.pc = off + 131) (hh : s.halted = false) (hEnv : Env s pts r c Z0)
    (h49 : s.core.ptrs 49 = 1) (hN : (nearS pts r lo hi).Nonempty)
    (hNB : BoxAt s (s.core.ptrs 48) (aLo pts (nearS pts r lo hi)) (bHi pts (nearS pts r lo hi)))
    (hB : BoxAt s (s.core.ptrs 43) lo hi) (hq : s.core.ptrs 48 + 2 * m ≤ s.core.ptrs 43) :
    ∃ t s3, run Q s detTape t = s3 ∧ t ≤ 52 * m + 16 ∧ s3.core.pc = off + 197 ∧ s3.halted = false ∧
      BoxAt s3 (s.core.ptrs 48) (coreLo pts r lo hi) (coreHi pts r lo hi) ∧
      s3.core.regs 51 = sigma (coreLo pts r lo hi) (coreHi pts r lo hi) ∧
      s3.core.regs 52 = sigma lo hi ∧
      (∀ x, x ≠ 46 → x ≠ 50 → x ≠ 57 → x ≠ 61 → s3.core.ptrs x = s.core.ptrs x) ∧
      (∀ x, (x < 44 ∨ (48 ≤ x ∧ x ≠ 51 ∧ x ≠ 52 ∧ x ≠ 54)) → s3.core.regs x = s.core.regs x) ∧
      (∀ z, (z < s.core.ptrs 48 ∨ s.core.ptrs 48 + 2 * m ≤ z) → s3.core.mem z = s.core.mem z) ∧
      s3.integerMemory = s.integerMemory ∧ s3.work = s.work + t ∧
      (∀ w ∈ cellsWritten Q s t, w.1 = true ∧ s.core.ptrs 48 ≤ w.2 ∧ w.2 < s.core.ptrs 48 + 2 * m) := by
  obtain ⟨hL, e11, e12, e40, e60, e68, e69, e40', e41, e49, e50, e53⟩ := hEnv
  have a1 := hL.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
    scd_tb Q off hE s hpc hh (by rw [h49, e69]; norm_num) hm1
  set s1 := run Q s detTape 3 with hs1
  obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    tb_loop Q off hE (aLo pts (nearS pts r lo hi)) (bHi pts (nearS pts r lo hi)) lo hi (r + r) m 0 s1
      (by omega) g1 g2 (by rw [g5 1 (by decide) (by decide), a1]) hm g3 (by rw [g6, e53]) (by rw [g6, e49])
      (by rw [g5 48 (by decide) (by decide), g5 43 (by decide) (by decide)]; exact hq)
      (by rw [g5 43 (by decide) (by decide)]; unfold BoxAt; rw [g7]; exact hB)
      (fun jj h => absurd h (by omega))
      (by intro jj _; rw [g5 48 (by decide) (by decide), g7]; exact hNB jj)
  set s2 := run Q s1 detTape t2 with hs2
  have p48 : s1.core.ptrs 48 = s.core.ptrs 48 := g5 48 (by decide) (by decide)
  have p43 : s2.core.ptrs 43 = s.core.ptrs 43 := by
    rw [q5 43 (by decide) (by decide) (by decide), g5 43 (by decide) (by decide)]
  have p48' : s2.core.ptrs 48 = s.core.ptrs 48 := by rw [q5 48 (by decide) (by decide) (by decide), p48]
  have hcore : BoxAt s2 (s.core.ptrs 48) (coreLo pts r lo hi) (coreHi pts r lo hi) := by
    rw [← p48]
    have e2 : r + r = 2 * r := by ring
    unfold coreLo coreHi; rw [← e2]; exact q3
  have hB2 : BoxAt s2 (s.core.ptrs 43) lo hi := by
    intro jj; have := jj.isLt
    rw [q4 _ (by rw [p48]; omega), q4 _ (by rw [p48]; omega), g7]; exact hB jj
  have hm0 : 0 < m := by omega
  obtain ⟨c0, d0⟩ := boxAt_zero hm0 hcore
  obtain ⟨c1, d1⟩ := boxAt_zero hm0 hB2
  have hm2 : 1 ≤ s2.core.ptrs 1 := by
    rw [q5 1 (by decide) (by decide) (by decide), g5 1 (by decide) (by decide)]; exact hm1
  have a1' : s2.core.ptrs 1 = m := by rw [q5 1 (by decide) (by decide) (by decide), g5 1 (by decide) (by decide), a1]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ :=
    seg_sg0 Q off hE (coreLo pts r lo hi ⟨0, hm0⟩) (coreHi pts r lo hi ⟨0, hm0⟩) (lo ⟨0, hm0⟩) (hi ⟨0, hm0⟩) s2 q1 q2 (by rw [p48']; exact c0) (by rw [p48', a1']; exact d0)
      (by rw [p43]; exact c1) (by rw [p43, a1']; exact d1) hm2
  set s3 := run Q s2 detTape 11 with hs3
  have r53 : s3.core.regs 53 = 2 := by
    rw [k10 53 (by decide) (by decide) (by decide) (by decide), q6 53 (by decide) (by decide) (by decide) (by decide),
      g6, e53]
  obtain ⟨t4, ht4, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ :=
    sg_loop Q off hE (coreLo pts r lo hi) (coreHi pts r lo hi) lo hi (m - 1) 1 s3 (by omega) le_rfl k1 k2
      (by rw [k5 1 (by decide) (by decide), a1']) k3 r53
      (by rw [k5 48 (by decide) (by decide), p48']; unfold BoxAt; rw [k11]; exact hcore)
      (by rw [k5 43 (by decide) (by decide), p43]; unfold BoxAt; rw [k11]; exact hB2)
      (by rw [k8, rmax_zero_side hm0])
      (by rw [k9, rmax_zero_side hm0])
  refine ⟨3 + t2 + 11 + t4, run Q s3 detTape t4, by rw [run_add, run_add, run_add, ← hs1, ← hs2, ← hs3],
    by omega, l1, l2, ?_, by rw [l3, rmax_sigma hm0], by rw [l4, rmax_sigma hm0], ?_, ?_, ?_,
    by rw [l8, k12, q7, g8], by rw [l9, k13, q8, g9]; ring, ?_⟩
  · unfold BoxAt; rw [l7, k11]; exact hcore
  · intro x a b c d
    rw [l5 x (by omega) (by omega), k5 x (by omega) (by omega), q5 x (by omega) b (by omega), g5 x (by omega) d]
  · intro x hx
    rw [l6 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      k10 x (by omega) (by omega) (by omega) (by omega),
      q6 x (by omega) (by omega) (by omega) (by omega), g6]
  · intro z hz
    rw [l7, k11, q4 z (by rw [p48]; exact hz), g7]
  · intro w hw
    have hr2 : run Q s detTape (3 + t2) = s2 := by rw [run_add, ← hs1]
    have hr3 : run Q s detTape (3 + t2 + 11) = s3 := by rw [run_add, hr2]
    rw [cellsWritten_add Q s (3 + t2 + 11) t4, hr3, cellsWritten_add Q s (3 + t2) 11, hr2,
      cellsWritten_add Q s 3 t2, ← hs1, g10, k14, l10] at hw
    simp only [Finset.empty_union, Finset.union_empty] at hw
    obtain ⟨a, b, c⟩ := q9 w hw; rw [p48] at b c; exact ⟨a, b, c⟩

end DetANN.HPIM.BD

-- ===== BD_Live =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- Half the work per node. -/
def W1 (n m : ℕ) : ℕ := 200 * (n + 1) * (m + 1) ^ 2

lemma w0_eq (n m : ℕ) : W0 n m = 2 * W1 n m := by unfold W0 W1; ring

lemma w1_ge (n m : ℕ) : (60 * m + 30) * n + 200 * m + 200 ≤ W1 n m := by
  unfold W1; nlinarith [Nat.zero_le (n * m), Nat.zero_le (n * m * m), Nat.zero_le (m * m)]

/-- A task either ends in a leaf, or its box is live and the run reaches `SGD` with the tight box
and both longest sides. -/
lemma task_cases (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (f : ℕ)
    (s : State) (e p sl : ℤ) (S : List (ℤ × ℤ × ℤ)) (lo hi : Fin m → ℝ)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hEnv : Env s pts r c Z0)
    (hS : StkAt s Z0 (s.core.ptrs 42) ((e, p, sl) :: S))
    (hge : ∀ x ∈ (e, p, sl) :: S, s.core.ptrs 13 ≤ x.1)
    (hsl : s.core.ptrs 13 ≤ sl) (hsl0 : sl < Z0) (hav : ∀ x ∈ S, sl < x.1 ∨ x.1 + 3 ≤ sl)
    (hB : BoxAt s p lo hi) (hRp : s.core.ptrs 14 ≤ p) (hpR : p + 2 * m ≤ R0) (hZ : s.core.ptrs 13 ≤ Z0)
    (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) :
    (∃ (t : ℕ) (s' : State) (u : ℤ), TPost Q off pts r c Z0 R0 s p sl S (build pts r c (f + 1) lo hi) t s' u) ∨
    (IsLive pts r c lo hi ∧ ∃ (t : ℕ) (s3 : State), Fr Q s s3 t (fun _ => False) ∧
      t ≤ (60 * m + 30) * n + 52 * m + 28 ∧ s3.core.pc = off + 197 ∧ s3.halted = false ∧
      Env s3 pts r c Z0 ∧ s3.core.ptrs 43 = p ∧ s3.core.ptrs 44 = sl ∧
      s3.core.ptrs 42 = s.integerMemory (e + 2) ∧ s3.core.ptrs 48 = s.core.ptrs 14 - 2 * m ∧
      s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m ∧ s3.core.ptrs 13 = s.core.ptrs 13 ∧
      BoxAt s3 p lo hi ∧ BoxAt s3 (s.core.ptrs 14 - 2 * m) (coreLo pts r lo hi) (coreHi pts r lo hi) ∧
      s3.core.regs 51 = sigma (coreLo pts r lo hi) (coreHi pts r lo hi) ∧ s3.core.regs 52 = sigma lo hi ∧
      s3.integerMemory = s.integerMemory) := by
  obtain ⟨t2, s2, hr2, ht2, h2, a43, a44, a42, a48, a14, P2, R2, M2, I2, W2, C2, E2, B2, br⟩ :=
    task_head Q off hE pts r c Z0 R0 hm s e p sl S lo hi hpc hh hEnv hS hB hRp hpR hR0
  have hw1 := w1_ge n m
  have hw0 := w0_eq n m
  have s2p1 : 1 ≤ s2.core.ptrs 1 := by rw [E2.1.1]; exact_mod_cast hm
  -- the leaf finish from a state at `LEAF` reached in `3` or `2` more steps
  have fin : ∀ (k : ℕ) (a : Option ℕ), k ≤ 3 → build pts r c (f + 1) lo hi = .leaf lo hi a →
      (run Q s2 detTape k).core.pc = off + 383 → (run Q s2 detTape k).halted = false →
      (run Q s2 detTape k).core.ptrs 61 = encA a →
      (∀ x, x ≠ 61 → (run Q s2 detTape k).core.ptrs x = s2.core.ptrs x) →
      (run Q s2 detTape k).core.regs = s2.core.regs → (run Q s2 detTape k).core.mem = s2.core.mem →
      (run Q s2 detTape k).integerMemory = s2.integerMemory → (run Q s2 detTape k).work = s2.work + k →
      cellsWritten Q s2 k = ∅ →
      ∃ (t : ℕ) (s' : State) (u : ℤ), TPost Q off pts r c Z0 R0 s p sl S (build pts r c (f + 1) lo hi) t s' u := by
    intro k a hk hT g1 g2 g3 g4 g5 g6 g7 g8 g9
    have hrun : run Q s detTape (t2 + k) = run Q s2 detTape k := by rw [run_add, hr2]
    exact leaf_finish Q off hE pts r c Z0 R0 hm _ a s e p sl S lo hi hT hS hge hsl hsl0 hav hRp hpR hZ hZ0
      (t2 + k) _ hrun (by rw [hw0]; clear * - ht2 hk hw1; generalize (60 * m + 30) * n = X at *; generalize W1 n m = Y at *; omega) g1 g2 (by rw [g4 43 (by decide), a43]) (by rw [g4 44 (by decide), a44])
      (by rw [g4 42 (by decide), a42]) g3 (by rw [g4 14 (by decide), a14])
      (fun x hx a b => by rw [g4 x b, P2 x hx a]) (fun x hx => by rw [g5, R2 x hx])
      (fun z hz => by rw [g6, M2 z hz]) (by rw [g7, I2]) (by rw [g8, W2]; ring)
      (fun w hw => by
        rw [cellsWritten_add, hr2, g9, Finset.union_empty] at hw; exact C2 w hw)
      (env_of E2 (fun x hx a b c => g4 x (by omega)) (fun x _ => by rw [g5]) (fun z _ => by rw [g7])
        (fun z _ => by rw [g6]))
      (by unfold BoxAt; rw [g6]; exact B2)
  rcases br with ⟨i0, hg, hlt, hpc2, h45⟩ | ⟨hng, hpc2, hN⟩
  · -- a good point: a certified leaf
    left
    have hn : (nearS pts r lo hi).Nonempty := ⟨i0, (Finset.mem_filter.1 hg).1⟩
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := seg_good Q off hE s2 hpc2 h2 s2p1
    refine fin 3 (some (i0 : ℕ)) le_rfl ?_ g1 g2 (by rw [g3, h45]; rfl) g4 g5 g6 g7 g8 g9
    rw [build_succ_good pts r c f lo hi hn ⟨i0, hg⟩, goodS_min' pts r c lo hi hg (fun i' h => hlt i' h)]
  · unfold NearInv at hN; rw [nearP_all] at hN
    rcases hN with ⟨h49, hne⟩ | ⟨h49, hne, hNB⟩
    · -- no near point: an empty leaf
      left
      have hn : ¬ (nearS pts r lo hi).Nonempty := by rw [hne]; exact Finset.not_nonempty_empty
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
        scd_out Q off hE s2 hpc2 h2 (by rw [h49, E2.2.2.2.2.2.2.1]) s2p1
      refine fin 2 none (by omega) (build_succ_none pts r c f lo hi hn) g1 g2 (by rw [g3]; rfl) g4 g5 g6 g7 g8 g9
    · -- a live box
      right
      refine ⟨⟨hne, fun h => by obtain ⟨i, hi'⟩ := h; exact hng i hi'⟩, ?_⟩
      obtain ⟨t3, s3, hr3, ht3, q1, q2, q3, q4, q5, Q3, R3, M3, I3, W3, C3⟩ :=
        task_mid Q off hE pts r c Z0 hm lo hi s2 hpc2 h2 E2 h49 hne hNB (by rw [a43]; exact B2)
          (by rw [a48, a43]; omega)
      rw [a48] at q3 M3 C3
      have p13 : s3.core.ptrs 13 = s.core.ptrs 13 := by
        rw [Q3 13 (by decide) (by decide) (by decide) (by decide), P2 13 (by decide) (by decide)]
      have p14 : s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by
        rw [Q3 14 (by decide) (by decide) (by decide) (by decide), a14]
      have hM : ∀ z, (z < s.core.ptrs 14 - 2 * m ∨ s.core.ptrs 14 ≤ z) → s3.core.mem z = s.core.mem z := by
        intro z hz; rw [M3 z (by omega), M2 z hz]
      refine ⟨t2 + t3, s3, ⟨by rw [run_add, hr2, hr3], by rw [W3, W2]; ring, by rw [p13], by rw [p14]; omega,
        fun x hx a b => by rw [Q3 x (by omega) (by omega) (by omega) (by omega), P2 x (by omega) b],
        by rw [Q3 59 (by decide) (by decide) (by decide) (by decide), P2 59 (by decide) (by decide)],
        fun x hx => by rw [R3 x (by omega), R2 x (by omega)], fun z _ _ => by rw [I3, I2],
        fun z hz => hM z (by rw [p14] at hz; exact hz), ?_⟩, by omega, q1, q2, ?_,
        by rw [Q3 43 (by decide) (by decide) (by decide) (by decide), a43],
        by rw [Q3 44 (by decide) (by decide) (by decide) (by decide), a44],
        by rw [Q3 42 (by decide) (by decide) (by decide) (by decide), a42],
        by rw [Q3 48 (by decide) (by decide) (by decide) (by decide), a48], p14, p13,
        fun jj => by have := jj.isLt; rw [hM _ (Or.inr (by omega)), hM _ (Or.inr (by omega))]; exact hB jj,
        q3, q4, q5, by rw [I3, I2]⟩
      · intro w hw
        rw [cellsWritten_add, hr2] at hw
        rcases Finset.mem_union.1 hw with hw | hw
        · obtain ⟨a, b, c⟩ := C2 w hw; exact Or.inr ⟨a, by rw [p14]; exact b, c⟩
        · obtain ⟨a, b, c⟩ := C3 w hw; exact Or.inr ⟨a, by rw [p14]; exact b, by omega⟩
      · exact env_of E2 (fun x hx a b c => Q3 x (by omega) (by omega) (by omega) (by omega))
          (fun x hx => R3 x (by omega)) (fun z _ => by rw [I3])
          (fun z hz => M3 z (Or.inr (by omega)))

end DetANN.HPIM.BD

-- ===== BD_Split =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- From `SGD` without carving: the split node, both halves, and two pushed tasks. -/
lemma split_pre (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (lo hi : Fin m → ℝ) (s : State)
    (hpc : s.core.pc = off + 197) (hh : s.halted = false) (hEnv : Env s pts r c Z0)
    (h52 : s.core.regs 52 = sigma lo hi) (hc : ¬ (s.core.regs 51 + s.core.regs 51 - s.core.regs 52 ≤ 0))
    (hB : BoxAt s (s.core.ptrs 43) lo hi) (hsl : s.core.ptrs 13 ≤ s.core.ptrs 44)
    (hp : s.core.ptrs 14 ≤ s.core.ptrs 43) :
    ∃ (t : ℕ) (s' : State) (k : Fin m), run Q s detTape t = s' ∧ t ≤ 37 * m + 91 ∧ longestAxis lo hi = some k ∧
      s'.core.pc = off + 34 ∧ s'.halted = false ∧
      s'.core.ptrs 13 = s.core.ptrs 13 - 10 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧
      s'.core.ptrs 42 = s.core.ptrs 13 - 10 ∧
      s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 43 ∧
      s'.integerMemory (s.core.ptrs 44) = s.core.ptrs 13 - 4 ∧
      s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧
      s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧
      s'.integerMemory (s.core.ptrs 13 - 10) = s.core.ptrs 14 - 4 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 9) = s.core.ptrs 13 - 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 8) = s.core.ptrs 13 - 7 ∧
      BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k ((lo k + hi k) / 2)) ∧
      BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k ((lo k + hi k) / 2)) hi ∧
      (∀ x, (x < 13 ∨ (14 < x ∧ x < 42) ∨ x = 40 ∨ x = 59 ∨ x = 60 ∨ x = 68 ∨ x = 69) →
        s'.core.ptrs x = s.core.ptrs x) ∧
      (∀ x, (x < 44 ∨ x = 49 ∨ x = 50 ∨ x = 53) → s'.core.regs x = s.core.regs x) ∧
      (∀ z, (z < s.core.ptrs 14 - 4 * m ∨ s.core.ptrs 14 ≤ z) → s'.core.mem z = s.core.mem z) ∧
      (∀ z, (z < s.core.ptrs 13 - 10 ∨ s.core.ptrs 13 ≤ z) → z ≠ s.core.ptrs 44 →
        s'.integerMemory z = s.integerMemory z) ∧
      s'.work = s.work + t ∧
      (∀ w ∈ cellsWritten Q s t,
        (w.1 = false ∧ ((s.core.ptrs 13 - 10 ≤ w.2 ∧ w.2 < s.core.ptrs 13) ∨ w.2 = s.core.ptrs 44)) ∨
        (w.1 = true ∧ s.core.ptrs 14 - 4 * m ≤ w.2 ∧ w.2 < s.core.ptrs 14)) :=
  peel_specs.1 Q off hE pts r c Z0 hm lo hi s hpc hh hEnv h52 hc hB hsl hp

end DetANN.HPIM.BD

-- ===== BD_Split2 =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

lemma size_cut (lo hi : Fin m → ℝ) (L R : BSP m) : BB.size (.cut lo hi L R) = 1 + BB.size L + BB.size R := rfl

set_option maxHeartbeats 1000000 in
lemma split_task (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (f : ℕ) (hT : TaskOK Q off pts r c Z0 R0 f)
    (s : State) (e p sl : ℤ) (S : List (ℤ × ℤ × ℤ)) (lo hi : Fin m → ℝ)
    (hS : StkAt s Z0 (s.core.ptrs 42) ((e, p, sl) :: S))
    (hge : ∀ x ∈ (e, p, sl) :: S, s.core.ptrs 13 ≤ x.1)
    (hsl : s.core.ptrs 13 ≤ sl) (hsl0 : sl < Z0) (hav : ∀ x ∈ S, sl < x.1 ∨ x.1 + 3 ≤ sl)
    (hRp : s.core.ptrs 14 ≤ p) (hpR : p + 2 * m ≤ R0) (hZ : s.core.ptrs 13 ≤ Z0)
    (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0)
    (hl : IsLive pts r c lo hi) (hc : ¬ Carves pts r lo hi) (hns : ¬ Starves pts r c (f + 1) lo hi)
    (t0 : ℕ) (s3 : State) (hF0 : Fr Q s s3 t0 (fun _ => False))
    (ht0 : t0 ≤ (60 * m + 30) * n + 52 * m + 28) (c1 : s3.core.pc = off + 197) (c2 : s3.halted = false)
    (E3 : Env s3 pts r c Z0) (a43 : s3.core.ptrs 43 = p) (a44 : s3.core.ptrs 44 = sl)
    (a42 : s3.core.ptrs 42 = s.integerMemory (e + 2))
    (a14 : s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m) (a13 : s3.core.ptrs 13 = s.core.ptrs 13)
    (B3 : BoxAt s3 p lo hi) (h51 : s3.core.regs 51 = sigma (coreLo pts r lo hi) (coreHi pts r lo hi))
    (h52 : s3.core.regs 52 = sigma lo hi) (I3 : s3.integerMemory = s.integerMemory) :
    ∃ (t : ℕ) (s' : State) (u : ℤ), TPost Q off pts r c Z0 R0 s p sl S (build pts r c (f + 1) lo hi) t s' u := by
  have hc' : ¬ (s3.core.regs 51 + s3.core.regs 51 - s3.core.regs 52 ≤ 0) := by
    intro h; apply hc; unfold Carves; rw [h51, h52] at h; linarith
  obtain ⟨t4, s4, k, hr4, ht4, hLA, o1, o2, o13, o14, o42, i1, i2, i3, i4, i5, i6, i7, i8, i9, BL, BR,
      PF, RF, MF, IF, WF, CF⟩ :=
    split_pre Q off hE pts r c Z0 hm lo hi s3 c1 c2 E3 h52 hc' (by rw [a43]; exact B3)
      (by rw [a13, a44]; exact hsl) (by rw [a14, a43]; omega)
  simp only [a13, a14, a43, a44, a42] at o13 o14 o42 i1 i2 i3 i4 i5 i6 i7 i8 i9 BL BR MF IF CF
  obtain ⟨hns1, hns2⟩ := not_or.1 ((starves_split pts r c hl hc hLA).not.1 hns)
  have hS' := hS.2.2.2.2
  -- the frame of the split node
  have F4 : Fr Q s3 s4 t4 (fun z => z = sl) := by
    refine ⟨hr4, WF, by rw [o13, a13]; omega, by rw [o14, a14]; omega,
      fun x hx a b => PF x (by omega), PF 59 (by decide), fun x hx => RF x (by omega),
      fun z hz hne => IF z (by rw [o13, a13] at hz; omega) hne, fun z hz => MF z (by rw [o14, a14] at hz; omega), ?_⟩
    intro w hw
    rcases CF w hw with ⟨a, b | b⟩ | ⟨a, b, c⟩
    · exact Or.inl ⟨a, Or.inl ⟨by rw [o13]; omega, by rw [a13]; omega⟩⟩
    · exact Or.inl ⟨a, Or.inr b⟩
    · exact Or.inr ⟨a, by rw [o14]; omega, by rw [a14]; omega⟩
  have E4 : Env s4 pts r c Z0 :=
    env_of E3 (fun x hx a b c => PF x (by omega)) (fun x hx => RF x (by omega))
      (fun z hz => IF z (by omega) (by omega)) (fun z hz => MF z (by omega))
  -- the stack after the split node
  have hStk : StkAt s4 Z0 (s4.core.ptrs 42) ((s.core.ptrs 13 - 10, s.core.ptrs 14 - 2 * m - 4 * m, s.core.ptrs 13 - 1) ::
      (s.core.ptrs 13 - 7, s.core.ptrs 14 - 2 * m - 2 * m, s.core.ptrs 13 - 2) :: S) := by
    refine ⟨o42, by omega, i7, by rw [show s.core.ptrs 13 - 10 + 1 = s.core.ptrs 13 - 9 by ring, i8],
      ?_⟩
    rw [show s.core.ptrs 13 - 10 + 2 = s.core.ptrs 13 - 8 by ring, i9]
    refine ⟨rfl, by omega, i4, by rw [show s.core.ptrs 13 - 7 + 1 = s.core.ptrs 13 - 6 by ring, i5],
      ?_⟩
    rw [show s.core.ptrs 13 - 7 + 2 = s.core.ptrs 13 - 5 by ring, i6]
    refine stkAt_of S _ hS' (fun x hx z z1 z2 => ?_)
    have := hge x (List.mem_cons_of_mem _ hx)
    rw [IF z (by omega) (by rcases hav x hx with h | h <;> omega), I3]
  -- the right child (top of the stack)
  obtain ⟨t5, s5, uR, q1, q2, E5, S5, U5, G5, B5, C5, T5, F5⟩ :=
    hT s4 _ _ _ _ _ _ o1 o2 E4 hStk
      (by intro x hx; rw [o13]; simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | hx
          · exact le_rfl
          · simp only; omega
          · have := hge x (List.mem_cons_of_mem _ hx); omega)
      (by rw [o13]; omega) (by omega)
      (by intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · right; simp only; omega
          · left; have := hge x (List.mem_cons_of_mem _ hx); omega)
      BR (by rw [o14]) (by omega) (by rw [o13]; omega) hns2
  obtain ⟨-, -, f13, f14, -, -, -, fI5, fM5, -⟩ := id F5
  -- the left child
  obtain ⟨t6, s6, uL, w1, w2, E6, S6, U6, G6, B6, C6, T6, F6⟩ :=
    hT s5 _ _ _ _ _ _ q1 q2 E5 S5
      (by intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp only; rw [o13] at f13; omega
          · have := hge x (List.mem_cons_of_mem _ hx); rw [o13] at f13; omega)
      (by rw [o13] at f13; omega) (by omega)
      (fun x hx => Or.inl (by have := hge x (List.mem_cons_of_mem _ hx); omega))
      (fun jj => by
        have := jj.isLt
        rw [fM5 _ (Or.inr (by rw [o14]; omega)), fM5 _ (Or.inr (by rw [o14]; omega))]; exact BL jj)
      (by rw [o14] at f14; omega) (by omega) (by rw [o13] at f13; omega) hns1
  obtain ⟨-, -, g13, g14, -, -, -, fI6, fM6, -⟩ := id F6
  rw [o13] at f13 B5; rw [o14] at f14 C5
  have hI : ∀ z, s.core.ptrs 13 - 10 ≤ z → z ≠ s.core.ptrs 13 - 1 → z ≠ s.core.ptrs 13 - 2 →
      s6.integerMemory z = s4.integerMemory z := fun z h1 h2 h3 => by
    rw [fI6 z (Or.inr (by omega)) h3, fI5 z (Or.inr (by omega)) h2]
  have hw1 := w1_ge n m
  have hw0 := w0_eq n m
  refine ⟨t0 + t4 + t5 + t6, s6, s.core.ptrs 13 - 4, w1, w2, E6, S6,
    by rw [hI sl (by omega) (by omega) (by omega)]; exact i3, ?_, ?_, ?_, ?_, ?_⟩
  · rw [build_succ_split pts r c f lo hi hl hc k hLA]
    refine goodT_cut (pL := s.core.ptrs 14 - 2 * m - 2 * m) (pR := s.core.ptrs 14 - 2 * m - 4 * m)
      (by omega) (by omega) hZ (by omega) hpR
      (by rw [hI _ (by omega) (by omega) (by omega)]; exact i1)
      (by rw [show s.core.ptrs 13 - 4 + 1 = s.core.ptrs 13 - 3 by ring, hI _ (by omega) (by omega) (by omega)]
          exact i2)
      (fun j => by
        have := j.isLt
        rw [fM6 _ (Or.inr (by omega)), fM5 _ (Or.inr (by omega)), MF _ (Or.inr (by omega)),
          fM6 _ (Or.inr (by omega)), fM5 _ (Or.inr (by omega)), MF _ (Or.inr (by omega))]
        exact B3 j)
      (by rw [show s.core.ptrs 13 - 4 + 2 = s.core.ptrs 13 - 2 by ring]; exact U6)
      (by rw [show s.core.ptrs 13 - 4 + 3 = s.core.ptrs 13 - 1 by ring,
            fI6 _ (Or.inr (by omega)) (by omega)]; exact U5)
      G6 (goodT_fr G5 F6 le_rfl le_rfl (by omega) (fun z hz => Or.inr (by rw [o13]; omega)))
      le_rfl (by omega) le_rfl (by omega) (by omega) (by omega)
      g13 (by rw [o13]; omega) g14 (by rw [o14]; omega) (by omega) (by omega)
  · rw [build_succ_split pts r c f lo hi hl hc k hLA, size_cut]; push_cast; linarith
  · rw [build_succ_split pts r c f lo hi hl hc k hLA, size_cut]; push_cast; linarith
  · rw [build_succ_split pts r c f lo hi hl hc k hLA, size_cut]; linarith
  · refine fr_mono (fr_comp (fr_comp (fr_comp hF0 F4) F5) F6) (fun z hz => ?_)
    rcases hz with ((h | h) | h) | h
    · exact h.elim
    · exact Or.inr h
    · left; omega
    · left; omega

end DetANN.HPIM.BD

-- ===== BD_CarveSeg =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- The low peel on axis `k`: a cut node at the current slot, the low slab pushed into its left slot,
and the rest (in the new current box) continuing in its right slot; from `CK` to `CH`. -/
lemma axis_low (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 283) (hh : s.halted = false)
    (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k)
    (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi)
    (hlow : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55)
    (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48)
    (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0) :
    ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧
      s'.core.pc = off + 326 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧
      s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧
      s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k ∧
      s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 2 ∧
      s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧
      BoxAt s' (s.core.ptrs 14 - 2 * m) lo (setCoord hi k (tlo ⟨k, hk⟩)) ∧
      BoxAt s' (s.core.ptrs 14 - 4 * m) (setCoord lo k (tlo ⟨k, hk⟩)) hi :=
  peel_specs.2.1 Q off hE pts r c Z0 hm s hpc hh hEnv k hk h53 tlo thi lo hi hQ hB hlow hcsl hcb hq hZ hcsl0 hR

/-- The high peel on axis `k`: a cut node at the current slot, the high slab pushed into its right
slot, and the rest (in the new current box) continuing in its left slot; from `CH` to `CK`. -/
lemma axis_high (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 : ℤ) (hm : 1 ≤ m) (s : State) (hpc : s.core.pc = off + 326) (hh : s.halted = false)
    (hEnv : Env s pts r c Z0) (k : ℕ) (hk : k < m) (h53 : s.core.ptrs 53 = k)
    (tlo thi lo hi : Fin m → ℝ) (hQ : BoxAt s (s.core.ptrs 48) tlo thi) (hB : BoxAt s (s.core.ptrs 54) lo hi)
    (hhigh : hi ⟨k, hk⟩ > thi ⟨k, hk⟩) (hcsl : s.core.ptrs 13 ≤ s.core.ptrs 55)
    (hcb : s.core.ptrs 14 ≤ s.core.ptrs 54) (hq : s.core.ptrs 14 ≤ s.core.ptrs 48)
    (hZ : s.core.ptrs 13 ≤ 0) (hcsl0 : s.core.ptrs 55 < 0) (hR : s.core.ptrs 14 ≤ 0) :
    ∃ (t : ℕ) (s' : State), Fr Q s s' t (fun z => z = s.core.ptrs 55) ∧ t ≤ 28 * m + 80 ∧
      s'.core.pc = off + 283 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧
      s'.core.ptrs 13 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 14 = s.core.ptrs 14 - 4 * m ∧
      s'.core.ptrs 42 = s.core.ptrs 13 - 7 ∧ s'.core.ptrs 48 = s.core.ptrs 48 ∧ s'.core.ptrs 53 = k + 1 ∧
      s'.core.ptrs 54 = s.core.ptrs 14 - 4 * m ∧ s'.core.ptrs 55 = s.core.ptrs 13 - 2 ∧
      s'.integerMemory (s.core.ptrs 13 - 4) = 1 ∧ s'.integerMemory (s.core.ptrs 13 - 3) = s.core.ptrs 54 ∧
      s'.integerMemory (s.core.ptrs 55) = s.core.ptrs 13 - 4 ∧
      s'.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m ∧
      s'.integerMemory (s.core.ptrs 13 - 6) = s.core.ptrs 13 - 1 ∧
      s'.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42 ∧
      BoxAt s' (s.core.ptrs 14 - 2 * m) (setCoord lo k (thi ⟨k, hk⟩)) hi ∧
      BoxAt s' (s.core.ptrs 14 - 4 * m) lo (setCoord hi k (thi ⟨k, hk⟩)) :=
  peel_specs.2.2 Q off hE pts r c Z0 hm s hpc hh hEnv k hk h53 tlo thi lo hi hQ hB hhigh hcsl hcb hq hZ hcsl0 hR

end DetANN.HPIM.BD

-- ===== BD_Carve =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

section Defs

variable (tlo thi : Fin m → ℝ) (bld : (Fin m → ℝ) → (Fin m → ℝ) → BSP m)

/-- The carve from the high check of axis `k` on. -/
noncomputable def chT (d k : ℕ) (lo hi : Fin m → ℝ) : BSP m :=
  if hk : k < m then
    if hi ⟨k, hk⟩ > thi ⟨k, hk⟩ then
      .cut lo hi (carve tlo thi bld d (k + 1) lo (setCoord hi k (thi ⟨k, hk⟩))) (bld (setCoord lo k (thi ⟨k, hk⟩)) hi)
    else carve tlo thi bld d (k + 1) lo hi
  else bld lo hi

/-- Its child boxes. -/
noncomputable def chB (d k : ℕ) (lo hi : Fin m → ℝ) : List ((Fin m → ℝ) × (Fin m → ℝ)) :=
  if hk : k < m then
    if hi ⟨k, hk⟩ > thi ⟨k, hk⟩ then
      carveBoxes tlo thi d (k + 1) lo (setCoord hi k (thi ⟨k, hk⟩)) ++ [(setCoord lo k (thi ⟨k, hk⟩), hi)]
    else carveBoxes tlo thi d (k + 1) lo hi
  else [(lo, hi)]

lemma carve_succ' (d k : ℕ) (hk : k < m) (lo hi : Fin m → ℝ) :
    carve tlo thi bld (d + 1) k lo hi =
      if lo ⟨k, hk⟩ < tlo ⟨k, hk⟩ then
        .cut lo hi (bld lo (setCoord hi k (tlo ⟨k, hk⟩))) (chT tlo thi bld d k (setCoord lo k (tlo ⟨k, hk⟩)) hi)
      else chT tlo thi bld d k lo hi := by
  rw [carve_succ tlo thi bld d k hk]
  by_cases h : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩
  · simp only [if_pos h, chT, dif_pos hk]
  · simp only [if_neg h, chT, dif_pos hk]

lemma carveBoxes_succ' (d k : ℕ) (hk : k < m) (lo hi : Fin m → ℝ) :
    carveBoxes tlo thi (d + 1) k lo hi =
      if lo ⟨k, hk⟩ < tlo ⟨k, hk⟩ then
        (lo, setCoord hi k (tlo ⟨k, hk⟩)) :: chB tlo thi d k (setCoord lo k (tlo ⟨k, hk⟩)) hi
      else chB tlo thi d k lo hi := by
  rw [carveBoxes_succ tlo thi d k hk]
  by_cases h : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩
  · simp only [if_pos h, chB, dif_pos hk]
  · simp only [if_neg h, chB, dif_pos hk]

/-- Some axis `≥ k` peels. -/
def PE (lo hi : Fin m → ℝ) (k : ℕ) : Prop :=
  ∃ k' : ℕ, ∃ hk' : k' < m, k ≤ k' ∧ (lo ⟨k', hk'⟩ < tlo ⟨k', hk'⟩ ∨ hi ⟨k', hk'⟩ > thi ⟨k', hk'⟩)

end Defs

/-- The state after the rest of a carve: back at `DISPATCH`, `T` stored through the slot `csl`, its
root box at `cb`; the bounds keep a reserve unless a peel happened before (`pd`). -/
def CPost (Q : Program) (off : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 R0 : ℤ) (s : State) (cb csl : ℤ)
    (S : List (ℤ × ℤ × ℤ)) (T : BSP m) (pd : Bool) (B : ℕ) (t : ℕ) (s' : State) (u : ℤ) : Prop :=
  s'.core.pc = off + 34 ∧ s'.halted = false ∧ Env s' pts r c Z0 ∧ StkAt s' Z0 (s'.core.ptrs 42) S ∧
    s'.integerMemory csl = u ∧
    GoodT s' Z0 R0 (s'.core.ptrs 13) (s.core.ptrs 13) (s'.core.ptrs 14) (s.core.ptrs 14) cb u T ∧
    s.core.ptrs 13 ≤ s'.core.ptrs 13 + 10 * BB.size T + (if pd then 3 else 0) ∧
    s.core.ptrs 14 + (if pd then 0 else 2 * m) ≤ s'.core.ptrs 14 + 6 * m * BB.size T ∧
    t + (if pd then 0 else W1 n m) ≤ W0 n m * BB.size T + B ∧ Fr Q s s' t (fun z => z = csl)

set_option maxHeartbeats 1000000 in
/-- One peel: the node (with box `[lo, hi]` at `cb`) at the slot `csl`, the pushed slab task into
slot `Z - 2` (left, `side`) or `Z - 1` (right), the rest in the other slot. -/
lemma peel_combine (Q : Program) (off : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 R0 : ℤ)
    (f : ℕ) (hT : TaskOK Q off pts r c Z0 R0 f) (side : Bool)
    (s s1 s2 : State) (S : List (ℤ × ℤ × ℤ)) (lo hi slo shi : Fin m → ℝ) (Trest : BSP m) (pd : Bool)
    (Bn B : ℕ) (hBB : Bn ≤ B) (cb csl : ℤ) (t1 t2 : ℕ) (u2 : ℤ)
    (F1 : Fr Q s s1 t1 (fun z => z = csl)) (ht1 : t1 ≤ 28 * m + 80)
    (z1 : s1.core.ptrs 13 = s.core.ptrs 13 - 7) (r1 : s1.core.ptrs 14 = s.core.ptrs 14 - 4 * m)
    (i0 : s1.integerMemory (s.core.ptrs 13 - 4) = 1) (i1 : s1.integerMemory (s.core.ptrs 13 - 3) = cb)
    (i2 : s1.integerMemory csl = s.core.ptrs 13 - 4)
    (hBs : BoxAt s1 (s.core.ptrs 14 - 2 * m) slo shi) (hB0 : BoxAt s cb lo hi)
    (hge : ∀ x ∈ S, s.core.ptrs 13 ≤ x.1) (hcsl : s.core.ptrs 13 ≤ csl) (hcsl0 : csl < Z0)
    (hcbR : s.core.ptrs 14 ≤ cb) (hcb0 : cb + 2 * m ≤ R0) (hZZ : s.core.ptrs 13 ≤ Z0)
    (hns : ¬ Starves pts r c f slo shi)
    (C : CPost Q off pts r c Z0 R0 s1 (s.core.ptrs 14 - 4 * m)
      (if side then s.core.ptrs 13 - 1 else s.core.ptrs 13 - 2)
      ((s.core.ptrs 13 - 7, s.core.ptrs 14 - 2 * m, if side then s.core.ptrs 13 - 2 else s.core.ptrs 13 - 1) :: S)
      Trest true Bn t2 s2 u2) :
    ∃ (t : ℕ) (s' : State) (u : ℤ), CPost Q off pts r c Z0 R0 s cb csl S
      (if side then .cut lo hi (build pts r c f slo shi) Trest else .cut lo hi Trest (build pts r c f slo shi))
      pd B t s' u := by
  set Z := s.core.ptrs 13 with hZdef
  set R := s.core.ptrs 14 with hRdef
  set sa : ℤ := if side then Z - 2 else Z - 1 with hsa
  set sb : ℤ := if side then Z - 1 else Z - 2 with hsb
  have hsa' : sa = Z - 2 ∨ sa = Z - 1 := by rw [hsa]; cases side <;> simp
  have hsb' : sb = Z - 2 ∨ sb = Z - 1 := by rw [hsb]; cases side <;> simp
  have hab : sa ≠ sb := by rw [hsa, hsb]; cases side <;> simp
  obtain ⟨c1, c2, E2, S2, U2, G2, B2, C2, T2, F2⟩ := C
  simp only [if_true] at B2 C2 T2
  obtain ⟨-, -, f13a, f14a, -, -, -, fIa, fMa, -⟩ := id F1
  obtain ⟨-, -, f13b, f14b, -, -, -, fIb, fMb, -⟩ := id F2
  rw [z1] at f13b B2; rw [r1] at f14b C2
  -- the slab task
  obtain ⟨t3, s3, u3, d1, d2, E3, S3, U3, G3, B3, C3, T3, F3⟩ :=
    hT s2 _ _ _ _ _ _ c1 c2 E2 S2
      (by intro x hx; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · simp only; omega
          · have := hge x hx; omega)
      (by rcases hsa' with h | h <;> rw [h] <;> omega) (by rcases hsa' with h | h <;> rw [h] <;> omega)
      (fun x hx => Or.inl (by have := hge x hx; rcases hsa' with h | h <;> rw [h] <;> omega))
      (fun jj => by
        have := jj.isLt
        rw [fMb _ (Or.inr (by omega)), fMb _ (Or.inr (by omega))]; exact hBs jj)
      (by omega) (by omega) (by omega) hns
  obtain ⟨-, -, f13c, f14c, -, -, -, fIc, fMc, -⟩ := id F3
  -- the integer cells of the node
  have hI : ∀ z, Z - 7 ≤ z → z ≠ sa → z ≠ sb → s3.integerMemory z = s1.integerMemory z := by
    intro z h1 h2 h3
    rw [fIc z (Or.inr (by omega)) h2, fIb z (Or.inr (by omega)) h3]
  have hw1 := w1_ge n m
  have hw0 := w0_eq n m
  refine ⟨t1 + t2 + t3, s3, Z - 4, d1, d2, E3, S3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fIc csl (Or.inr (by omega)) (by rcases hsa' with h | h <;> rw [h] <;> omega),
      fIb csl (Or.inr (by omega)) (by rcases hsb' with h | h <;> rw [h] <;> omega)]
    exact i2
  · have G2' := goodT_fr G2 F3 le_rfl le_rfl (by omega) (fun z hz => Or.inr (by rw [z1, hz]; rcases hsa' with h | h <;> rw [h] <;> omega))
    have hu2 : s3.integerMemory sb = u2 := by
      rw [fIc sb (Or.inr (by rcases hsb' with h | h <;> rw [h] <;> omega)) (fun h => hab h.symm)]; exact U2
    have hn0 : s3.integerMemory (Z - 4) = 1 := by
      rw [hI _ (by omega) (by rcases hsa' with h | h <;> rw [h] <;> omega)
        (by rcases hsb' with h | h <;> rw [h] <;> omega)]; exact i0
    have hn1 : s3.integerMemory (Z - 4 + 1) = cb := by
      rw [show Z - 4 + 1 = Z - 3 by ring, hI _ (by omega) (by rcases hsa' with h | h <;> rw [h] <;> omega)
        (by rcases hsb' with h | h <;> rw [h] <;> omega)]; exact i1
    have hbox : ∀ j : Fin m, s3.core.mem (cb + j) = lo j ∧ s3.core.mem (cb + j + m) = hi j := fun j => by
      have := j.isLt
      rw [fMc _ (Or.inr (by omega)), fMb _ (Or.inr (by omega)), fMa _ (Or.inr (by omega)),
        fMc _ (Or.inr (by omega)), fMb _ (Or.inr (by omega)), fMa _ (Or.inr (by omega))]
      exact hB0 j
    cases side
    · simp only [Bool.false_eq_true, if_false] at hsa hsb ⊢
      refine goodT_cut (by omega) (by omega) hZZ (by omega) hcb0 hn0 hn1 hbox
        (by rw [show Z - 4 + 2 = sb by rw [hsb]; ring]; exact hu2)
        (by rw [show Z - 4 + 3 = sa by rw [hsa]; ring]; exact U3) G2' G3
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        le_rfl (by omega) le_rfl (by omega) (by omega) (by omega)
    · simp only [if_true] at hsa hsb ⊢
      refine goodT_cut (by omega) (by omega) hZZ (by omega) hcb0 hn0 hn1 hbox
        (by rw [show Z - 4 + 2 = sa by rw [hsa]; ring]; exact U3)
        (by rw [show Z - 4 + 3 = sb by rw [hsb]; ring]; exact hu2) G3 G2'
        le_rfl (by omega) le_rfl (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · have : BB.size (if side then BSP.cut lo hi (build pts r c f slo shi) Trest
        else BSP.cut lo hi Trest (build pts r c f slo shi)) =
        1 + BB.size Trest + BB.size (build pts r c f slo shi) := by
      cases side <;> simp only [Bool.false_eq_true, if_false, if_true, size_cut] <;> ring
    rw [this]; push_cast
    have : (0 : ℤ) ≤ if pd then 3 else 0 := by split_ifs <;> norm_num
    linarith
  · have : BB.size (if side then BSP.cut lo hi (build pts r c f slo shi) Trest
        else BSP.cut lo hi Trest (build pts r c f slo shi)) =
        1 + BB.size Trest + BB.size (build pts r c f slo shi) := by
      cases side <;> simp only [Bool.false_eq_true, if_false, if_true, size_cut] <;> ring
    rw [this]; push_cast
    have : (if pd then (0 : ℤ) else 2 * m) ≤ 2 * m := by split_ifs <;> omega
    rw [show (6 : ℤ) * m * (1 + (BB.size Trest : ℤ) + (BB.size (build pts r c f slo shi) : ℤ)) =
      6 * m + 6 * m * (BB.size Trest : ℤ) + 6 * m * (BB.size (build pts r c f slo shi) : ℤ) by ring]
    linarith
  · have : BB.size (if side then BSP.cut lo hi (build pts r c f slo shi) Trest
        else BSP.cut lo hi Trest (build pts r c f slo shi)) =
        1 + BB.size Trest + BB.size (build pts r c f slo shi) := by
      cases side <;> simp only [Bool.false_eq_true, if_false, if_true, size_cut] <;> ring
    rw [this, show W0 n m * (1 + BB.size Trest + BB.size (build pts r c f slo shi)) =
      W0 n m + W0 n m * BB.size Trest + W0 n m * BB.size (build pts r c f slo shi) by ring]
    have : (if pd then 0 else W1 n m) ≤ W1 n m := by split_ifs <;> omega
    clear * - this T2 T3 ht1 hw1 hw0 hBB
    generalize W0 n m * BB.size Trest = A at *
    generalize W0 n m * BB.size (build pts r c f slo shi) = A' at *
    generalize (if pd then 0 else W1 n m) = X at *
    generalize (60 * m + 30) * n = Y at *
    omega
  · refine fr_mono (fr_comp (fr_comp F1 F2) F3) (fun z hz => ?_)
    rcases hz with (h | h) | h
    · exact Or.inr h
    · left; rw [h]; rcases hsb' with h' | h' <;> rw [h'] <;> omega
    · left; rw [h]; rcases hsa' with h' | h' <;> rw [h'] <;> omega

end DetANN.HPIM.BD

-- ===== BD_Carve2 =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- The state of the carve loop at `off + pc`: axis `k`, current box `[lo, hi]` at pointer `54`,
current slot in pointer `55`, the tight box at pointer `48`, the stack `S`. -/
def CIn (off : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 R0 : ℤ) (pc : ℕ) (s : State) (k : ℕ)
    (tlo thi lo hi : Fin m → ℝ) (S : List (ℤ × ℤ × ℤ)) : Prop :=
  s.core.pc = off + pc ∧ s.halted = false ∧ Env s pts r c Z0 ∧ s.core.ptrs 53 = k ∧
    StkAt s Z0 (s.core.ptrs 42) S ∧ (∀ x ∈ S, s.core.ptrs 13 ≤ x.1) ∧
    s.core.ptrs 13 ≤ s.core.ptrs 55 ∧ s.core.ptrs 55 < Z0 ∧
    (∀ x ∈ S, s.core.ptrs 55 < x.1 ∨ x.1 + 3 ≤ s.core.ptrs 55) ∧
    BoxAt s (s.core.ptrs 54) lo hi ∧ BoxAt s (s.core.ptrs 48) tlo thi ∧
    s.core.ptrs 14 ≤ s.core.ptrs 54 ∧ s.core.ptrs 54 + 2 * m ≤ R0 ∧ s.core.ptrs 14 ≤ s.core.ptrs 48 ∧
    s.core.ptrs 13 ≤ Z0

lemma fr_quiet {Q : Program} {s s' : State} {t : ℕ} {A : ℤ → Prop} (h : run Q s detTape t = s')
    (hw : s'.work = s.work + t) (hP : ∀ x, (x < 40 ∨ x = 59) → s'.core.ptrs x = s.core.ptrs x)
    (hR : ∀ x, x < 40 → s'.core.regs x = s.core.regs x) (hI : s'.integerMemory = s.integerMemory)
    (hM : s'.core.mem = s.core.mem) (hc : cellsWritten Q s t = ∅) : Fr Q s s' t A :=
  ⟨h, hw, by rw [hP 13 (by decide)], by rw [hP 14 (by decide)], fun x hx _ _ => hP x (Or.inl hx),
    hP 59 (Or.inr rfl), hR, fun z _ _ => by rw [hI], fun z _ => by rw [hM],
    fun w hw => by rw [hc] at hw; simp at hw⟩

/-- Prepend a step without writes or allocation. -/
lemma cpost_pre {Q : Program} {off : ℕ} {pts : Fin n → Fin m → ℝ} {r c : ℝ} {Z0 R0 : ℤ}
    {s s1 s2 : State} {t1 t2 : ℕ} {cb csl u : ℤ} {S : List (ℤ × ℤ × ℤ)} {T : BSP m} {pd : Bool}
    {Bn B : ℕ} (h1 : Fr Q s s1 t1 (fun _ => False)) (e13 : s1.core.ptrs 13 = s.core.ptrs 13)
    (e14 : s1.core.ptrs 14 = s.core.ptrs 14)
    (hC : CPost Q off pts r c Z0 R0 s1 cb csl S T pd Bn t2 s2 u) (hB : t1 + Bn ≤ B) :
    CPost Q off pts r c Z0 R0 s cb csl S T pd B (t1 + t2) s2 u := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hC
  simp only [e13, e14] at c6 c7 c8
  refine ⟨c1, c2, c3, c4, c5, c6, c7, c8, ?_, fr_mono (fr_comp h1 c10) (fun z hz => ?_)⟩
  · clear * - c9 hB
    generalize (if pd then 0 else W1 n m) = X at *
    generalize W0 n m * BB.size T = Y at *
    omega
  · rcases hz with h | h
    · exact h.elim
    · exact Or.inr h

set_option maxHeartbeats 1000000 in
/-- The end of the carve: push the core task and run it. -/
lemma carve_end (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) (f : ℕ)
    (hT : TaskOK Q off pts r c Z0 R0 f) (tlo thi lo hi : Fin m → ℝ) (s : State) (S : List (ℤ × ℤ × ℤ))
    (hC : CIn off pts r c Z0 R0 283 s m tlo thi lo hi S) (hns : ¬ Starves pts r c f lo hi) :
    ∃ (t : ℕ) (s' : State) (u : ℤ), CPost Q off pts r c Z0 R0 s (s.core.ptrs 54) (s.core.ptrs 55) S
      (build pts r c f lo hi) true 20 t s' u := by
  obtain ⟨hpc, hh, hEnv, h53, hS, hge, hcsl, hcsl0, hav, hB, -, hcb, hcb0, -, hZZ⟩ := hC
  have a1 := hEnv.1.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := ck_exit Q off hE s hpc hh (by rw [a1, h53]) hm1
  generalize hs1 : run Q s detTape 1 = s1 at *
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14⟩ :=
    seg_ce Q off hE s1 g1 g2 (by rw [g3]; exact hm1)
  generalize hs2 : run Q s1 detTape 11 = s2 at *
  simp only [g3, g4, g5, g6] at k3 k4 k5 k6 k7 k8 k9 k10 k11 k12 k13 k14
  have P2 : ∀ x, x ≠ 13 → x ≠ 42 → x ≠ 57 → s2.core.ptrs x = s.core.ptrs x := by
    intro x a b d; rw [k6 x a b d]
  have hEnv2 : Env s2 pts r c Z0 :=
    env_of hEnv (fun x hx a b d => P2 x a (by omega) (by omega)) (fun x _ => by rw [k7])
      (fun z hz => k12 z (by omega) (by omega) (by omega)) (fun z _ => by rw [k8])
  have hStk : StkAt s2 Z0 (s2.core.ptrs 42) ((s.core.ptrs 13 - 3, s.core.ptrs 54, s.core.ptrs 55) :: S) := by
    refine ⟨k4, by omega, k9, by rw [show s.core.ptrs 13 - 3 + 1 = s.core.ptrs 13 - 2 by ring]; exact k10, ?_⟩
    rw [show s.core.ptrs 13 - 3 + 2 = s.core.ptrs 13 - 1 by ring, k11]
    exact stkAt_of S _ hS (fun x hx z z1 z2 => by have := hge x hx; rw [k12 z (by omega) (by omega) (by omega)])
  have hr2 : run Q s detTape (1 + 11) = s2 := by rw [run_add, hs1, hs2]
  obtain ⟨t3, s3, u3, d1, d2, E3, S3, U3, G3, B3, C3, T3, F3⟩ :=
    hT s2 _ _ _ _ _ _ k1 k2 hEnv2 hStk
      (by intro x hx; rw [k3]; simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · exact le_rfl
          · have := hge x hx; omega)
      (by rw [k3]; omega) hcsl0 hav (by unfold BoxAt; rw [k8]; exact hB)
      (by rw [P2 14 (by decide) (by decide) (by decide)]; exact hcb) hcb0 (by rw [k3]; omega) hns
  have F2 : Fr Q s s2 12 (fun _ => False) := by
    refine ⟨hr2, by rw [k13, g7], by rw [k3]; omega, by rw [P2 14 (by decide) (by decide) (by decide)],
      fun x hx a b => P2 x a (by omega) (by omega), P2 59 (by decide) (by decide) (by decide),
      fun x _ => by rw [k7], fun z hz _ => k12 z (by rw [k3] at hz; omega) (by rw [k3] at hz; omega)
        (by rw [k3] at hz; omega),
      fun z _ => by rw [k8], ?_⟩
    intro w hw
    rw [show (12 : ℕ) = 1 + 11 from rfl, cellsWritten_add, hs1, g8, Finset.empty_union] at hw
    rcases k14 w hw with rfl | rfl | rfl <;> exact Or.inl ⟨rfl, Or.inl ⟨by rw [k3]; try omega, by simp⟩⟩
  obtain ⟨-, -, f13, f14, -, -, -, -, -, -⟩ := id F3
  rw [k3] at f13 B3
  have p14 : s2.core.ptrs 14 = s.core.ptrs 14 := P2 14 (by decide) (by decide) (by decide)
  rw [p14] at C3 G3 f14
  refine ⟨12 + t3, s3, u3, d1, d2, E3, S3, U3, ?_, by simp only [if_true]; omega,
    by simp only [if_true]; omega, by simp only [if_true]; omega,
    fr_mono (fr_comp F2 F3) (fun z hz => by rcases hz with h | h; exact h.elim; exact Or.inr h)⟩
  rw [k3] at G3
  exact goodT_widen G3 le_rfl (by omega) le_rfl le_rfl

end DetANN.HPIM.BD

-- ===== BD_Carve3 =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

/-- The precondition after a peel. -/
lemma cin_peel {Q : Program} {off : ℕ} {pts : Fin n → Fin m → ℝ} {r c : ℝ} {Z0 R0 : ℤ} {pc pc' : ℕ}
    {s s1 : State} {k k' : ℕ} {tlo thi lo hi lo' hi' : Fin m → ℝ} {S : List (ℤ × ℤ × ℤ)} {t1 : ℕ}
    {sa sl : ℤ} (hC : CIn off pts r c Z0 R0 pc s k tlo thi lo hi S)
    (F1 : Fr Q s s1 t1 (fun z => z = s.core.ptrs 55))
    (q1 : s1.core.pc = off + pc') (q2 : s1.halted = false) (q3 : Env s1 pts r c Z0) (q4 : s1.core.ptrs 53 = k')
    (a13 : s1.core.ptrs 13 = s.core.ptrs 13 - 7) (a14 : s1.core.ptrs 14 = s.core.ptrs 14 - 4 * m)
    (a42 : s1.core.ptrs 42 = s.core.ptrs 13 - 7) (a48 : s1.core.ptrs 48 = s.core.ptrs 48)
    (a54 : s1.core.ptrs 54 = s.core.ptrs 14 - 4 * m) (a55 : s1.core.ptrs 55 = sl)
    (hsl : sl = s.core.ptrs 13 - 1 ∨ sl = s.core.ptrs 13 - 2)
    (hsa : sa = s.core.ptrs 13 - 1 ∨ sa = s.core.ptrs 13 - 2)
    (i7 : s1.integerMemory (s.core.ptrs 13 - 7) = s.core.ptrs 14 - 2 * m)
    (i6 : s1.integerMemory (s.core.ptrs 13 - 6) = sa) (i5 : s1.integerMemory (s.core.ptrs 13 - 5) = s.core.ptrs 42)
    (hBr : BoxAt s1 (s.core.ptrs 14 - 4 * m) lo' hi') :
    CIn off pts r c Z0 R0 pc' s1 k' tlo thi lo' hi'
      ((s.core.ptrs 13 - 7, s.core.ptrs 14 - 2 * m, sa) :: S) := by
  obtain ⟨-, -, -, -, hS, hge, hcsl, hcsl0, hav, hB, hQ, hcb, hcb0, hq, hZZ⟩ := hC
  obtain ⟨-, -, f13, f14, -, -, -, fI, fM, -⟩ := F1
  refine ⟨q1, q2, q3, q4, ⟨a42, by omega, i7, by rw [show s.core.ptrs 13 - 7 + 1 = s.core.ptrs 13 - 6 by ring, i6], ?_⟩,
    ?_, by rw [a13, a55]; omega, by rw [a55]; omega, ?_, by rw [a54]; exact hBr, ?_, by rw [a14, a54],
    by rw [a54]; omega, by rw [a14, a48]; omega, by rw [a13]; omega⟩
  · rw [show s.core.ptrs 13 - 7 + 2 = s.core.ptrs 13 - 5 by ring, i5]
    exact stkAt_of S _ hS (fun x hx z z1 z2 => by
      have := hge x hx
      exact fI z (Or.inr (by omega)) (by rcases hav x hx with h | h <;> omega))
  · intro x hx; simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only; omega
    · have := hge x hx; omega
  · intro x hx; simp only [List.mem_cons] at hx
    rw [a55]
    rcases hx with rfl | hx
    · right; simp only; omega
    · left; have := hge x hx; omega
  · intro jj; have := jj.isLt
    rw [a48, fM _ (Or.inr (by omega)), fM _ (Or.inr (by omega))]; exact hQ jj

/-- The precondition after a step that changes only the axis and the scratch pointer `57`. -/
lemma cin_quiet {off : ℕ} {pts : Fin n → Fin m → ℝ} {r c : ℝ} {Z0 R0 : ℤ} {pc pc' : ℕ}
    {s s1 : State} {k k' : ℕ} {tlo thi lo hi : Fin m → ℝ} {S : List (ℤ × ℤ × ℤ)}
    (hC : CIn off pts r c Z0 R0 pc s k tlo thi lo hi S)
    (q1 : s1.core.pc = off + pc') (q2 : s1.halted = false) (q4 : s1.core.ptrs 53 = k')
    (hP : ∀ x, x ≠ 53 → x ≠ 57 → s1.core.ptrs x = s.core.ptrs x)
    (hR : ∀ x, x < 44 ∨ x = 49 ∨ x = 50 ∨ x = 53 → s1.core.regs x = s.core.regs x)
    (hI : s1.integerMemory = s.integerMemory) (hM : s1.core.mem = s.core.mem) :
    CIn off pts r c Z0 R0 pc' s1 k' tlo thi lo hi S := by
  obtain ⟨-, -, hEnv, -, hS, hge, hcsl, hcsl0, hav, hB, hQ, hcb, hcb0, hq, hZZ⟩ := hC
  have e : ∀ x, x ∈ [13, 14, 42, 48, 54, 55] → s1.core.ptrs x = s.core.ptrs x := by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact hP x (by rcases hx with h | h | h | h | h | h <;> subst h <;> decide)
      (by rcases hx with h | h | h | h | h | h <;> subst h <;> decide)
  have e13 := e 13 (by simp); have e14 := e 14 (by simp); have e42 := e 42 (by simp)
  have e48 := e 48 (by simp); have e54 := e 54 (by simp); have e55 := e 55 (by simp)
  refine ⟨q1, q2, env_of hEnv (fun x hx _ _ _ => hP x (by omega) (by omega)) (fun x hx => hR x (by omega))
      (fun z _ => by rw [hI]) (fun z _ => by rw [hM]), q4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e42]; exact stkAt_of S _ hS (fun x _ z _ _ => by rw [hI])
  · rw [e13]; exact hge
  · rw [e13, e55]; exact hcsl
  · rw [e55]; exact hcsl0
  · rw [e55]; exact hav
  · rw [e54]; unfold BoxAt; rw [hM]; exact hB
  · rw [e48]; unfold BoxAt; rw [hM]; exact hQ
  · rw [e14, e54]; exact hcb
  · rw [e54]; exact hcb0
  · rw [e14, e48]; exact hq
  · rw [e13]; exact hZZ

section Ind

variable (Q : Program) (off : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (Z0 R0 : ℤ) (f : ℕ)
  (tlo thi : Fin m → ℝ)

/-- The carve contract from the low check with `d` axes left. -/
def CKok (d : ℕ) : Prop :=
  ∀ k, k + d = m → ∀ (s : State) (lo hi : Fin m → ℝ) (S : List (ℤ × ℤ × ℤ)) (pd : Bool),
    CIn off pts r c Z0 R0 283 s k tlo thi lo hi S → (pd = false → PE tlo thi lo hi k) →
    (∀ B ∈ carveBoxes tlo thi d k lo hi, ¬ Starves pts r c f B.1 B.2) →
    ∃ (t : ℕ) (s' : State) (u : ℤ), CPost Q off pts r c Z0 R0 s (s.core.ptrs 54) (s.core.ptrs 55) S
      (carve tlo thi (build pts r c f) d k lo hi) pd (40 * d + 20) t s' u

/-- The carve contract from the high check of axis `k`, with `d` axes left after it. -/
def CHok (d : ℕ) : Prop :=
  ∀ k, k + 1 + d = m → ∀ (s : State) (lo hi : Fin m → ℝ) (S : List (ℤ × ℤ × ℤ)) (pd : Bool),
    CIn off pts r c Z0 R0 326 s k tlo thi lo hi S →
    (pd = false → (∀ hk : k < m, hi ⟨k, hk⟩ > thi ⟨k, hk⟩) ∨ PE tlo thi lo hi (k + 1)) →
    (∀ B ∈ chB tlo thi d k lo hi, ¬ Starves pts r c f B.1 B.2) →
    ∃ (t : ℕ) (s' : State) (u : ℤ), CPost Q off pts r c Z0 R0 s (s.core.ptrs 54) (s.core.ptrs 55) S
      (chT tlo thi (build pts r c f) d k lo hi) pd (40 * d + 40) t s' u

end Ind

set_option maxHeartbeats 1000000 in
lemma ch_of_ck (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) (f : ℕ)
    (hT : TaskOK Q off pts r c Z0 R0 f) (tlo thi : Fin m → ℝ) (d : ℕ)
    (h : CKok Q off pts r c Z0 R0 f tlo thi d) : CHok Q off pts r c Z0 R0 f tlo thi d := by
  intro k hkd s lo hi S pd hC hpd hbx
  have hk : k < m := by omega
  have hC0 := hC
  obtain ⟨hpc, hh, hEnv, h53, hS, hge, hcsl, hcsl0, hav, hB, hQ, hcb, hcb0, hq, hZZ⟩ := hC
  unfold chT; rw [dif_pos hk]; unfold chB at hbx; rw [dif_pos hk] at hbx
  have a1 := hEnv.1.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  by_cases hhigh : hi ⟨k, hk⟩ > thi ⟨k, hk⟩
  · rw [if_pos hhigh]; rw [if_pos hhigh] at hbx
    obtain ⟨t1, s1, F1, ht1, q1, q2, q3, a13, a14, a42, a48, a53, a54, a55, i0, i1, i2, i7, i6, i5, hBs, hBr⟩ :=
      axis_high Q off hE pts r c Z0 hm s hpc hh hEnv k hk h53 tlo thi lo hi hQ hB hhigh hcsl hcb hq
        (by omega) (by omega) (by omega)
    have hC1 := cin_peel hC0 F1 q1 q2 q3 a53 a13 a14 a42 a48 a54 a55 (Or.inr rfl) (Or.inl rfl) i7 i6 i5 hBr
    obtain ⟨t2, s2, u2, C⟩ := h (k + 1) (by omega) s1 lo (setCoord hi k (thi ⟨k, hk⟩)) _ true hC1
      (fun h => absurd h (by decide))
      (fun B hB' => hbx B (List.mem_append_left _ hB'))
    rw [a54, a55] at C
    have := peel_combine Q off pts r c Z0 R0 f hT false s s1 s2 S lo hi (setCoord lo k (thi ⟨k, hk⟩)) hi
      _ pd (40 * d + 20) (40 * d + 40) (by omega) (s.core.ptrs 54) (s.core.ptrs 55) t1 t2 u2 F1 ht1
      a13 a14 i0 i1 i2 hBs hB hge hcsl hcsl0 hcb hcb0 hZZ
      (hbx _ (List.mem_append_right _ (List.mem_singleton_self _)))
      (by simp only [Bool.false_eq_true, if_false]; exact C)
    simpa only [Bool.false_eq_true, if_false] using this
  · rw [if_neg hhigh]; rw [if_neg hhigh] at hbx
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
      ch_nohigh Q off hE (thi ⟨k, hk⟩) (hi ⟨k, hk⟩) s hpc hh (by rw [h53, a1]; exact (hQ ⟨k, hk⟩).2)
        (by rw [h53, a1]; exact (hB ⟨k, hk⟩).2) (by linarith) hm1
    generalize hs1 : run Q s detTape 8 = s1 at *
    obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := seg_cn Q off hE s1 g1 g2 (by rw [g4 1 (by decide)]; exact hm1)
    generalize hs2 : run Q s1 detTape 2 = s2 at *
    have hP : ∀ x, x ≠ 53 → x ≠ 57 → s2.core.ptrs x = s.core.ptrs x := fun x a b => by rw [k4 x a, g4 x b]
    have hR : ∀ x, x ≠ 44 → x ≠ 46 → x ≠ 54 → s2.core.regs x = s.core.regs x := fun x a b d => by
      rw [k5, g8 x a b d]
    have hC1 : CIn off pts r c Z0 R0 283 s2 (k + 1) tlo thi lo hi S :=
      cin_quiet hC0 k1 k2 (by rw [k3, g4 53 (by decide), h53]; push_cast; ring) hP
        (fun x hx => hR x (by omega) (by omega) (by omega)) (by rw [k7, g10]) (by rw [k6, g9])
    obtain ⟨t2, s3, u3, C⟩ := h (k + 1) (by omega) s2 lo hi S pd hC1
      (fun hp => by
        rcases hpd hp with h' | h'
        · exact absurd (h' hk) hhigh
        · exact h')
      hbx
    rw [hP 54 (by decide) (by decide), hP 55 (by decide) (by decide)] at C
    refine ⟨10 + t2, s3, u3, cpost_pre (fr_quiet (by rw [show (10 : ℕ) = 8 + 2 from rfl, run_add, hs1, hs2]) (by rw [k8, g11]; try ring)
      (fun x hx => hP x (by omega) (by omega)) (fun x hx => hR x (by omega) (by omega) (by omega))
      (by rw [k7, g10]) (by rw [k6, g9]) (by rw [show (10 : ℕ) = 8 + 2 from rfl, cellsWritten_add, hs1, g12, k9, Finset.empty_union]))
      (hP 13 (by decide) (by decide)) (hP 14 (by decide) (by decide)) C (by omega)⟩

set_option maxHeartbeats 1000000 in
lemma ck_succ_of_ch (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) (f : ℕ)
    (hT : TaskOK Q off pts r c Z0 R0 f) (tlo thi : Fin m → ℝ) (d : ℕ)
    (h : CHok Q off pts r c Z0 R0 f tlo thi d) : CKok Q off pts r c Z0 R0 f tlo thi (d + 1) := by
  intro k hkd s lo hi S pd hC hpd hbx
  have hk : k < m := by omega
  have hC0 := hC
  obtain ⟨hpc, hh, hEnv, h53, hS, hge, hcsl, hcsl0, hav, hB, hQ, hcb, hcb0, hq, hZZ⟩ := hC
  rw [carve_succ' tlo thi (build pts r c f) d k hk]
  rw [carveBoxes_succ' tlo thi d k hk] at hbx
  have a1 := hEnv.1.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  by_cases hlow : lo ⟨k, hk⟩ < tlo ⟨k, hk⟩
  · rw [if_pos hlow]; rw [if_pos hlow] at hbx
    obtain ⟨t1, s1, F1, ht1, q1, q2, q3, a13, a14, a42, a48, a53, a54, a55, i0, i1, i2, i7, i6, i5, hBs, hBr⟩ :=
      axis_low Q off hE pts r c Z0 hm s hpc hh hEnv k hk h53 tlo thi lo hi hQ hB hlow hcsl hcb hq
        (by omega) (by omega) (by omega)
    have hC1 := cin_peel hC0 F1 q1 q2 q3 a53 a13 a14 a42 a48 a54 a55 (Or.inl rfl) (Or.inr rfl) i7 i6 i5 hBr
    obtain ⟨t2, s2, u2, C⟩ := h k (by omega) s1 (setCoord lo k (tlo ⟨k, hk⟩)) hi _ true hC1
      (fun h => absurd h (by decide)) (fun B hB' => hbx B (List.mem_cons_of_mem _ hB'))
    rw [a54, a55] at C
    have := peel_combine Q off pts r c Z0 R0 f hT true s s1 s2 S lo hi lo (setCoord hi k (tlo ⟨k, hk⟩))
      _ pd (40 * d + 40) (40 * (d + 1) + 20) (by omega) (s.core.ptrs 54) (s.core.ptrs 55) t1 t2 u2 F1 ht1
      a13 a14 i0 i1 i2 hBs hB hge hcsl hcsl0 hcb hcb0 hZZ (hbx _ List.mem_cons_self)
      (by simp only [if_true]; exact C)
    simpa only [if_true] using this
  · rw [if_neg hlow]; rw [if_neg hlow] at hbx
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
      ck_nolow Q off hE (tlo ⟨k, hk⟩) (lo ⟨k, hk⟩) s hpc hh (by rw [h53]; exact (hQ ⟨k, hk⟩).1)
        (by rw [h53]; exact (hB ⟨k, hk⟩).1) (by rw [h53, a1]; exact_mod_cast hk) (by linarith) hm1
    generalize hs1 : run Q s detTape 7 = s1 at *
    have hC1 : CIn off pts r c Z0 R0 326 s1 k tlo thi lo hi S :=
      cin_quiet hC0 g1 g2 (by rw [g4 53 (by decide), h53]) (fun x _ b => g4 x b)
        (fun x hx => g8 x (by omega) (by omega) (by omega)) g10 g9
    obtain ⟨t2, s2, u2, C⟩ := h k (by omega) s1 lo hi S pd hC1
      (fun hp => by
        obtain ⟨k', hk', hle, hc'⟩ := hpd hp
        by_cases hkk : k' = k
        · subst hkk
          left; intro hk2
          rcases hc' with h' | h'
          · exact absurd h' hlow
          · exact h'
        · right; exact ⟨k', hk', by omega, hc'⟩)
      hbx
    rw [g4 54 (by decide), g4 55 (by decide)] at C
    exact ⟨7 + t2, s2, u2, cpost_pre (fr_quiet hs1 g11 (fun x hx => g4 x (by omega))
      (fun x hx => g8 x (by omega) (by omega) (by omega)) g10 g9 g12)
      (g4 13 (by decide)) (g4 14 (by decide)) C (by omega)⟩

lemma ck_zero (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) (f : ℕ)
    (hT : TaskOK Q off pts r c Z0 R0 f) (tlo thi : Fin m → ℝ) :
    CKok Q off pts r c Z0 R0 f tlo thi 0 := by
  intro k hkd s lo hi S pd hC hpd hbx
  have hkm : k = m := by omega
  rw [hkm] at hC
  cases pd
  · obtain ⟨k', hk', hle, -⟩ := hpd rfl; omega
  · exact carve_end Q off hE pts r c Z0 R0 hm hZ0 hR0 f hT tlo thi lo hi s S hC
      (hbx (lo, hi) (by rw [carveBoxes_zero]; exact List.mem_singleton_self _))

lemma carve_all (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) (f : ℕ)
    (hT : TaskOK Q off pts r c Z0 R0 f) (tlo thi : Fin m → ℝ) :
    ∀ d, CKok Q off pts r c Z0 R0 f tlo thi d := by
  intro d
  induction d with
  | zero => exact ck_zero Q off hE pts r c Z0 R0 hm hZ0 hR0 f hT tlo thi
  | succ d ih =>
    exact ck_succ_of_ch Q off hE pts r c Z0 R0 hm hZ0 hR0 f hT tlo thi d
      (ch_of_ck Q off hE pts r c Z0 R0 hm hZ0 hR0 f hT tlo thi d ih)

end DetANN.HPIM.BD

-- ===== BD_TaskAll =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

variable {m n : ℕ}

set_option maxHeartbeats 1000000 in
lemma carve_task (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (f : ℕ) (hT : TaskOK Q off pts r c Z0 R0 f)
    (s : State) (e p sl : ℤ) (S : List (ℤ × ℤ × ℤ)) (lo hi : Fin m → ℝ)
    (hS : StkAt s Z0 (s.core.ptrs 42) ((e, p, sl) :: S))
    (hge : ∀ x ∈ (e, p, sl) :: S, s.core.ptrs 13 ≤ x.1)
    (hsl : s.core.ptrs 13 ≤ sl) (hsl0 : sl < Z0) (hav : ∀ x ∈ S, sl < x.1 ∨ x.1 + 3 ≤ sl)
    (hRp : s.core.ptrs 14 ≤ p) (hpR : p + 2 * m ≤ R0) (hZ : s.core.ptrs 13 ≤ Z0)
    (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0)
    (hl : IsLive pts r c lo hi) (hc : Carves pts r lo hi) (hns : ¬ Starves pts r c (f + 1) lo hi)
    (t0 : ℕ) (s3 : State) (hF0 : Fr Q s s3 t0 (fun _ => False))
    (ht0 : t0 ≤ (60 * m + 30) * n + 52 * m + 28) (c1 : s3.core.pc = off + 197) (c2 : s3.halted = false)
    (E3 : Env s3 pts r c Z0) (a43 : s3.core.ptrs 43 = p) (a44 : s3.core.ptrs 44 = sl)
    (a42 : s3.core.ptrs 42 = s.integerMemory (e + 2)) (a48 : s3.core.ptrs 48 = s.core.ptrs 14 - 2 * m)
    (a14 : s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m) (a13 : s3.core.ptrs 13 = s.core.ptrs 13)
    (B3 : BoxAt s3 p lo hi) (Bq : BoxAt s3 (s.core.ptrs 14 - 2 * m) (coreLo pts r lo hi) (coreHi pts r lo hi))
    (h51 : s3.core.regs 51 = sigma (coreLo pts r lo hi) (coreHi pts r lo hi))
    (h52 : s3.core.regs 52 = sigma lo hi) (I3 : s3.integerMemory = s.integerMemory) :
    ∃ (t : ℕ) (s' : State) (u : ℤ), TPost Q off pts r c Z0 R0 s p sl S (build pts r c (f + 1) lo hi) t s' u := by
  have a1 := E3.1.1
  have hm1 : 1 ≤ s3.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  have hc' : s3.core.regs 51 + s3.core.regs 51 - s3.core.regs 52 ≤ 0 := by
    unfold Carves at hc; rw [h51, h52]; linarith
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ := sgd_carve Q off hE s3 c1 c2 hc' hm1
  generalize hs4 : run Q s3 detTape 3 = s4 at *
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := seg_carve Q off hE s4 g1 g2 (by rw [g3]; exact hm1)
  generalize hs5 : run Q s4 detTape 3 = s5 at *
  rw [g3] at k4 k5 k6
  have hP : ∀ x, x ≠ 53 → x ≠ 54 → x ≠ 55 → s5.core.ptrs x = s3.core.ptrs x := fun x a b d => by
    rw [k6 x a b d]
  have hR : ∀ x, x ≠ 54 → s5.core.regs x = s3.core.regs x := fun x a => by rw [k7, g5 x a]
  have hI : s5.integerMemory = s3.integerMemory := by rw [k9, g7]
  have hM : s5.core.mem = s3.core.mem := by rw [k8, g6]
  have hC5 : CIn off pts r c Z0 R0 283 s5 0 (coreLo pts r lo hi) (coreHi pts r lo hi) lo hi S := by
    refine ⟨k1, k2, env_of E3 (fun x hx _ _ _ => hP x (by omega) (by omega) (by omega))
        (fun x hx => hR x (by omega)) (fun z _ => by rw [hI]) (fun z _ => by rw [hM]), k3, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · rw [hP 42 (by decide) (by decide) (by decide), a42]
      exact stkAt_of S _ hS.2.2.2.2 (fun x _ z _ _ => by rw [hI, I3])
    · intro x hx; rw [hP 13 (by decide) (by decide) (by decide), a13]
      exact hge x (List.mem_cons_of_mem _ hx)
    · rw [hP 13 (by decide) (by decide) (by decide), a13, k5, a44]; exact hsl
    · rw [k5, a44]; exact hsl0
    · rw [k5, a44]; exact hav
    · rw [k4, a43]; unfold BoxAt; rw [hM]; exact B3
    · rw [hP 48 (by decide) (by decide) (by decide), a48]; unfold BoxAt; rw [hM]; exact Bq
    · rw [hP 14 (by decide) (by decide) (by decide), a14, k4, a43]; omega
    · rw [k4, a43]; exact hpR
    · rw [hP 14 (by decide) (by decide) (by decide), a14, hP 48 (by decide) (by decide) (by decide), a48]
    · rw [hP 13 (by decide) (by decide) (by decide), a13]; exact hZ
  have hpe : PE (coreLo pts r lo hi) (coreHi pts r lo hi) lo hi 0 := by
    obtain ⟨k, hk, h⟩ := carve_peels pts r c hl hc hns
    exact ⟨k, hk, Nat.zero_le _, h⟩
  have hbx : ∀ B ∈ carveBoxes (coreLo pts r lo hi) (coreHi pts r lo hi) m 0 lo hi,
      ¬ Starves pts r c f B.1 B.2 := by
    intro B hB hs; exact hns ((starves_carve pts r c hl hc).2 ⟨B, hB, hs⟩)
  obtain ⟨t6, s6, u6, d1, d2, E6, S6, U6, G6, B6, C6, T6, F6⟩ :=
    carve_all Q off hE pts r c Z0 R0 hm hZ0 hR0 f hT (coreLo pts r lo hi) (coreHi pts r lo hi) m 0
      (by omega) s5 lo hi S false hC5 (fun _ => hpe) hbx
  have p13 : s5.core.ptrs 13 = s.core.ptrs 13 := by rw [hP 13 (by decide) (by decide) (by decide), a13]
  have p14 : s5.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by rw [hP 14 (by decide) (by decide) (by decide), a14]
  simp only [k4, a43, k5, a44] at G6 U6 F6
  simp only [p13, p14] at G6 B6 C6
  simp only [Bool.false_eq_true, if_false, add_zero] at B6 C6 T6
  rw [← build_succ_carve pts r c f lo hi hl hc] at G6 B6 C6 T6
  have F35 : Fr Q s3 s5 (3 + 3) (fun _ => False) :=
    fr_quiet (by rw [run_add, hs4, hs5]) (by rw [k10, g8]) (fun x hx => hP x (by omega) (by omega) (by omega))
      (fun x hx => hR x (by omega)) hI hM (by rw [cellsWritten_add, hs4, g9, k11, Finset.empty_union])
  have hw1 := w1_ge n m
  have hw0 := w0_eq n m
  refine ⟨t0 + (3 + 3) + t6, s6, u6, d1, d2, E6, S6, U6,
    goodT_widen G6 le_rfl le_rfl le_rfl (by omega), by linarith, by push_cast at C6; linarith, ?_,
    fr_mono (fr_comp (fr_comp hF0 F35) F6) (fun z hz => ?_)⟩
  · clear * - T6 ht0 hw1 hw0
    generalize W0 n m * BB.size (build pts r c (f + 1) lo hi) = A at *
    generalize (60 * m + 30) * n = Y at *
    omega
  · rcases hz with (h | h) | h
    · exact h.elim
    · exact h.elim
    · exact Or.inr h

/-- Every task meets its contract. -/
theorem taskOK_all (Q : Program) (off : ℕ) (hE : Embeds Q (bd off) off) (pts : Fin n → Fin m → ℝ)
    (r c : ℝ) (Z0 R0 : ℤ) (hm : 1 ≤ m) (hZ0 : Z0 ≤ 0) (hR0 : R0 ≤ 0) :
    ∀ f, TaskOK Q off pts r c Z0 R0 f := by
  intro f
  induction f with
  | zero =>
    intro s e p sl S lo hi _ _ _ _ _ _ _ _ _ _ _ _ hns
    exact absurd trivial hns
  | succ f ih =>
    intro s e p sl S lo hi hpc hh hEnv hS hge hsl hsl0 hav hB hRp hpR hZ hns
    rcases task_cases Q off hE pts r c Z0 R0 hm f s e p sl S lo hi hpc hh hEnv hS hge hsl hsl0 hav hB hRp hpR
        hZ hZ0 hR0 with h | ⟨hl, t0, s3, F0, ht0, c1, c2, E3, a43, a44, a42, a48, a14, a13, B3, Bq, h51, h52, I3⟩
    · exact h
    · by_cases hc : Carves pts r lo hi
      · exact carve_task Q off hE pts r c Z0 R0 hm f ih s e p sl S lo hi hS hge hsl hsl0 hav hRp hpR hZ hZ0 hR0
          hl hc hns t0 s3 F0 ht0 c1 c2 E3 a43 a44 a42 a48 a14 a13 B3 Bq h51 h52 I3
      · exact split_task Q off hE pts r c Z0 R0 hm f ih s e p sl S lo hi hS hge hsl hsl0 hav hRp hpR hZ hZ0 hR0
          hl hc hns t0 s3 F0 ht0 c1 c2 E3 a43 a44 a42 a14 a13 B3 h51 h52 I3

end DetANN.HPIM.BD

-- ===== BD_Final =====
namespace DetANN.HPIM.BD

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP DetANN.HPIM.QP
  DetANN.HPIM.BS

set_option maxHeartbeats 1000000 in
theorem build_block' :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n f : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false → LocalPts s pts →
        s.core.regs 11 = r → s.core.regs 12 = c → 0 ≤ s.core.ptrs 17 →
        (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + j) = lo j) →
        (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + m + j) = hi j) →
        s.core.ptrs 13 ≤ 0 → s.core.ptrs 14 ≤ 0 → ¬ Starves pts r c f lo hi →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          BSPAt m (run Q s detTape t) ((run Q s detTape t).core.ptrs 13) (s.core.ptrs 13)
            ((run Q s detTape t).core.ptrs 14) (s.core.ptrs 14) ((run Q s detTape t).core.ptrs 17)
            (build pts r c f lo hi) ∧
          KeepsLow s (run Q s detTape t) [13, 14, 17] [] ∧
          s.core.ptrs 13 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
            (run Q s detTape t).core.ptrs 13 ∧
          s.core.ptrs 14 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
            (run Q s detTape t).core.ptrs 14 ∧
          WritesOnly Q s t (fun w =>
            (if w.1 then s.core.ptrs 14 else s.core.ptrs 13) -
                C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤ w.2 ∧
              w.2 < (if w.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∧
          (run Q s detTape t).work ≤ s.work +
            C * ((build pts r c f lo hi).paths.card + 1) ^ 2 * (n + 1) * (m + 1) ^ 2 := by
  refine ⟨bd, 396, 500, bd_block, ?_⟩
  intro off Q hE m n f pts r c lo hi s hm hn hpc hh hL h11 h12 h17 hlo hhi h13 h14 hns
  have a1 := hL.1
  have hm1 : 1 ≤ s.core.ptrs 1 := by rw [a1]; exact_mod_cast hm
  -- the constants and the root box
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, g19, g20, g21⟩ :=
    seg_init Q off hE s (by rw [hpc]; rfl) hh hm1
  generalize hs1 : run Q s detTape 13 = s1 at *
  rw [a1] at g3 g5 g7
  have P1 : ∀ x, x ≠ 14 → x ≠ 40 → x ≠ 43 → x ≠ 46 → x ≠ 60 → x ≠ 68 → x ≠ 69 →
      s1.core.ptrs x = s.core.ptrs x := g10
  have s1p1 : 1 ≤ s1.core.ptrs 1 := by
    rw [P1 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hm1
  have s1p17 : s1.core.ptrs 17 = s.core.ptrs 17 :=
    P1 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    icp_loop Q off hE (fun z => s.core.mem (s.core.ptrs 17 + z)) (2 * m) (2 * m) 0 s1 (by omega) g1 g2 s1p1
      (by rw [g7]; push_cast; ring) g6 (by rw [g5, s1p17]; push_cast; omega)
      (fun z _ => by rw [g18, s1p17]) (fun z h => absurd h (by omega))
  generalize hs2 : run Q s1 detTape t2 = s2 at *
  rw [g5] at q3 q4 q9
  have s2p1 : 1 ≤ s2.core.ptrs 1 := by rw [q5 1 (by decide) (by decide)]; exact s1p1
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16⟩ :=
    seg_icd Q off hE s2 q1 q2 s2p1
  generalize hs3 : run Q s2 detTape 14 = s3 at *
  have p2_13 : s2.core.ptrs 13 = s.core.ptrs 13 := by
    rw [q5 13 (by decide) (by decide), P1 13 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]
  have p2_40 : s2.core.ptrs 40 = s.core.ptrs 13 := by rw [q5 40 (by decide) (by decide), g4]
  have p2_43 : s2.core.ptrs 43 = s.core.ptrs 14 - 2 * m := by rw [q5 43 (by decide) (by decide), g5]
  simp only [p2_13, p2_40, p2_43] at k3 k4 k5 k7 k11 k12 k13 k14 k16
  -- the pointers and registers of the state at `DISPATCH`
  have P3 : ∀ x, x ≠ 13 → x ≠ 14 → x ≠ 40 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 46 → x ≠ 50 → x ≠ 57 → x ≠ 59 →
      x ≠ 60 → x ≠ 68 → x ≠ 69 → s3.core.ptrs x = s.core.ptrs x := by
    intro x a b d e f g h i j k l o p
    rw [k8 x a e g j k, q5 x h i, P1 x b d f h l o p]
  have R3 : ∀ x, x ≠ 40 → x ≠ 41 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 53 → x ≠ 55 →
      s3.core.regs x = s.core.regs x := by
    intro x a b d e f g h
    rw [k9, q6 x h, g17 x a b d e f g]
  have s3_14 : s3.core.ptrs 14 = s.core.ptrs 14 - 2 * m := by
    rw [k8 14 (by decide) (by decide) (by decide) (by decide) (by decide), q5 14 (by decide) (by decide), g3]
  have hM3 : s3.core.mem = s2.core.mem := k10
  have hEnv3 : Env s3 pts r c (s.core.ptrs 13) := by
    refine ⟨localPts_of hL (P3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (P3 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (P3 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (P3 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (fun z hz => by rw [k14 z (by omega) (by omega) (by omega), q7, g19])
        (fun z hz => by rw [hM3, q4 z (Or.inr (by omega)), g18]),
      by rw [R3 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h11],
      by rw [R3 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), h12],
      by rw [k8 40 (by decide) (by decide) (by decide) (by decide) (by decide), p2_40],
      by rw [k8 60 (by decide) (by decide) (by decide) (by decide) (by decide), q5 60 (by decide) (by decide), g7],
      by rw [k8 68 (by decide) (by decide) (by decide) (by decide) (by decide), q5 68 (by decide) (by decide), g8],
      by rw [k8 69 (by decide) (by decide) (by decide) (by decide) (by decide), q5 69 (by decide) (by decide), g9],
      by rw [k9, q6 40 (by decide), g11, h11], by rw [k9, q6 41 (by decide), g12, h11, h12],
      by rw [k9, q6 49 (by decide), g14, h11], by rw [k9, q6 50 (by decide), g15],
      by rw [k9, q6 53 (by decide), g16]⟩
  -- the root task
  have hBox : BoxAt s3 (s.core.ptrs 14 - 2 * m) lo hi := by
    intro j; have := j.isLt
    rw [hM3]
    refine ⟨by rw [q3 j (by omega)]; exact hlo j, ?_⟩
    have e := q3 (j + m) (by omega)
    push_cast at e
    rw [show s.core.ptrs 14 - 2 * m + j + m = s.core.ptrs 14 - 2 * m + (j + m) by ring, e,
      show s.core.ptrs 17 + ((j : ℤ) + m) = s.core.ptrs 17 + m + j by ring]
    exact hhi j
  have hStk : StkAt s3 (s.core.ptrs 13) (s3.core.ptrs 42)
      [(s.core.ptrs 13 - 4, s.core.ptrs 14 - 2 * m, s.core.ptrs 13 - 1)] :=
    ⟨k4, by omega, k11, by rw [show s.core.ptrs 13 - 4 + 1 = s.core.ptrs 13 - 3 by ring]; exact k12,
      by rw [show s.core.ptrs 13 - 4 + 2 = s.core.ptrs 13 - 2 by ring, k13]; rfl⟩
  obtain ⟨t4, s4, u, d1, d2, E4, S4, U4, G4, B4, C4, T4, F4⟩ :=
    taskOK_all Q off hE pts r c (s.core.ptrs 13) (s.core.ptrs 14) hm h13 h14 f s3 _ _ _ [] lo hi k1 k2 hEnv3
      hStk (by intro x hx; simp only [List.mem_singleton] at hx; rw [hx, k3]) (by rw [k3]; omega) (by omega)
      (fun x hx => by simp at hx) hBox (by rw [s3_14]) (by omega) (by rw [k3]; omega) hns
  -- the end
  have e4_42 : s4.core.ptrs 42 = s.core.ptrs 13 := S4
  have e4_40 : s4.core.ptrs 40 = s.core.ptrs 13 := E4.2.2.2.1
  have s4p1 : 1 ≤ s4.core.ptrs 1 := by rw [E4.1.1]; exact_mod_cast hm
  obtain ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩ := disp_end Q off hE s4 d1 d2 (by rw [e4_42, e4_40]) s4p1
  generalize hs5 : run Q s4 detTape 1 = s5 at *
  obtain ⟨-, -, f13, f14, fP, f59, fR, fI, fM, fW⟩ := id F4
  have e5_59 : s5.core.ptrs 59 = s.core.ptrs 13 - 1 := by rw [z3, f59, k7]
  obtain ⟨y1, y2, y3, y4, y5, y6, y7, y8, y9⟩ :=
    seg_end Q off hE u s5 z1 z2 (by rw [e5_59, z6]; exact U4) (by rw [z3]; exact s4p1)
  generalize hs6 : run Q s5 detTape 1 = s6 at *
  have hrun : run Q s detTape (13 + t2 + 14 + t4 + 1 + 1) = s6 := by
    rw [run_add, run_add, run_add, run_add, run_add, hs1, hs2, hs3, F4.1, hs5, hs6]
  have e6_13 : s6.core.ptrs 13 = s4.core.ptrs 13 := by rw [y4 13 (by decide), z3]
  have e6_14 : s6.core.ptrs 14 = s4.core.ptrs 14 := by rw [y4 14 (by decide), z3]
  rw [k3] at f13 B4 G4; rw [s3_14] at f14 C4 G4
  rw [BB.paths_card]
  have hsz := size_pos (build pts r c f lo hi)
  have hb : (10 : ℤ) * BB.size (build pts r c f lo hi) + 4 ≤
      500 * ((BB.size (build pts r c f lo hi) : ℤ) + 1) * ((m : ℤ) + 1) := by
    have : (1 : ℤ) ≤ m := by exact_mod_cast hm
    clear * - this; nlinarith
  have hb' : 6 * (m : ℤ) * BB.size (build pts r c f lo hi) + 2 * m ≤
      500 * ((BB.size (build pts r c f lo hi) : ℤ) + 1) * ((m : ℤ) + 1) := by
    have : (0 : ℤ) ≤ BB.size (build pts r c f lo hi) := by positivity
    have : (0 : ℤ) ≤ m := by positivity
    clear * - this; nlinarith
  have hP0 : (0 : ℤ) ≤ BB.size (build pts r c f lo hi) := by positivity
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have hmP : (0 : ℤ) ≤ 6 * (m : ℤ) * BB.size (build pts r c f lo hi) := by positivity
  refine ⟨13 + t2 + 14 + t4 + 1 + 1, ?_⟩
  rw [hrun]
  refine ⟨y1, y2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e6_13, e6_14, y3]
    exact G4 s6 (fun z _ _ => by rw [y7, z6]) (fun z _ => by rw [y6, z5])
  · refine ⟨fun x hx hn => ?_, fun x hx _ => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
      obtain ⟨n13, n14, n17⟩ := hn
      rw [y4 x n17, z3, fP x hx n13 n14, P3 x n13 n14 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    · rw [y5, z4, fR x hx, R3 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [e6_13]; push_cast; linarith only [B4, hb]
  · rw [e6_14]; push_cast; linarith only [C4, hb']
  · intro w hw
    have e2 : run Q s detTape (13 + t2) = s2 := by rw [run_add, hs1, hs2]
    have e3 : run Q s detTape (13 + t2 + 14) = s3 := by rw [run_add, e2, hs3]
    have e4 : run Q s detTape (13 + t2 + 14 + t4) = s4 := by rw [run_add, e3, F4.1]
    have e5 : run Q s detTape (13 + t2 + 14 + t4 + 1) = s5 := by rw [run_add, e4, hs5]
    rw [cellsWritten_add Q s _ 1, e5, y9, Finset.union_empty, cellsWritten_add Q s _ 1, e4, z8,
      Finset.union_empty, cellsWritten_add Q s _ t4, e3, cellsWritten_add Q s _ 14, e2,
      cellsWritten_add Q s 13 t2, hs1, g21, Finset.empty_union] at hw
    simp only [Finset.mem_union] at hw
    rcases hw with (hw | hw) | hw
    · obtain ⟨a, b, d⟩ := q9 w hw
      push_cast at b d
      simp only [a, if_true]; push_cast; constructor <;> linarith only [b, d, hb', hmP, hm0]
    · rcases k16 w hw with rfl | rfl | rfl <;> simp only [Bool.false_eq_true, if_false] <;> push_cast <;>
        constructor <;> linarith only [hb, hP0]
    · rcases fW w hw with ⟨a, ⟨b, d⟩ | b⟩ | ⟨a, b, d⟩
      · simp only [a, Bool.false_eq_true, if_false]; push_cast; constructor <;> linarith only [b, d, B4, hb, hP0, k3]
      · simp only [a, Bool.false_eq_true, if_false]; rw [b]; push_cast; constructor <;> linarith only [hb, hP0]
      · simp only [a, if_true]; push_cast; constructor <;> linarith only [b, d, C4, hb', hmP, hm0, s3_14]
  · rw [y8, z7, F4.2.1, k15, q8, g20]
    have hT4 : t4 ≤ 400 * (n + 1) * (m + 1) ^ 2 * BB.size (build pts r c f lo hi) := T4
    clear * - hT4 ht2
    generalize BB.size (build pts r c f lo hi) = P at *
    have hX : m + 1 ≤ (n + 1) * (m + 1) ^ 2 := by nlinarith
    have hY : P ≤ (P + 1) ^ 2 := by nlinarith
    have h1 : (n + 1) * (m + 1) ^ 2 * P ≤ (n + 1) * (m + 1) ^ 2 * (P + 1) ^ 2 := Nat.mul_le_mul_left _ hY
    have h2 : m + 1 ≤ (n + 1) * (m + 1) ^ 2 * (P + 1) ^ 2 :=
      le_trans hX (Nat.le_mul_of_pos_right _ (by positivity))
    nlinarith

end DetANN.HPIM.BD

namespace DetANN.HPIM

open PNormReg PNormRegLib

theorem _root_.solution :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m n f : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) (s : State),
        1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false → LocalPts s pts →
        s.core.regs 11 = r → s.core.regs 12 = c → 0 ≤ s.core.ptrs 17 →
        (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + j) = lo j) →
        (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + m + j) = hi j) →
        s.core.ptrs 13 ≤ 0 → s.core.ptrs 14 ≤ 0 → ¬ Starves pts r c f lo hi →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
          BSPAt m (run Q s detTape t) ((run Q s detTape t).core.ptrs 13) (s.core.ptrs 13)
            ((run Q s detTape t).core.ptrs 14) (s.core.ptrs 14) ((run Q s detTape t).core.ptrs 17)
            (build pts r c f lo hi) ∧
          KeepsLow s (run Q s detTape t) [13, 14, 17] [] ∧
          s.core.ptrs 13 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
            (run Q s detTape t).core.ptrs 13 ∧
          s.core.ptrs 14 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
            (run Q s detTape t).core.ptrs 14 ∧
          WritesOnly Q s t (fun w =>
            (if w.1 then s.core.ptrs 14 else s.core.ptrs 13) -
                C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤ w.2 ∧
              w.2 < (if w.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∧
          (run Q s detTape t).work ≤ s.work +
            C * ((build pts r c f lo hi).paths.card + 1) ^ 2 * (n + 1) * (m + 1) ^ 2 :=
  DetANN.HPIM.BD.build_block'

end DetANN.HPIM
