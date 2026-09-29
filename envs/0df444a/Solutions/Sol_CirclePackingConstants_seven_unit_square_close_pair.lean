-- Prove2me | solution 1 for CirclePackingConstants.seven_unit_square_close_pair
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-26T23:58:47.62243+00:00
-- url     : https://prove2.me/submissions/8a3a66f0-38bf-467b-a066-4f0174298c1b

import Definitions.Def_CirclePackingConstants
import Theorems.Thm_CirclePackingConstants_N7Rep01_n7_pattern_01_infeasible
import Theorems.Thm_CirclePackingConstants_N7Rep02_n7_pattern_02_infeasible
import Theorems.Thm_CirclePackingConstants_n7_pattern_04_infeasible
import Theorems.Thm_CirclePackingConstants_N7Rep05_n7_pattern_05_infeasible
import Theorems.Thm_CirclePackingConstants_N7Rep08_n7_pattern_08_infeasible
import Theorems.Thm_CirclePackingConstants_n7_pattern_13_infeasible
import Theorems.Thm_CirclePackingConstants_n7_pattern_14_infeasible
import Theorems.Thm_CirclePackingConstants_n7_pattern_17_infeasible
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
noncomputable section

namespace CirclePackingConstants
abbrev N7Cell := Fin 3 × Fin 3

def n7flip (x : Fin 3) : Fin 3 := ⟨2 - x.1, by omega⟩
/-- The eight dihedral symmetries in the numbering used by the PDF verifier. -/
def n7sym (k : Fin 8) : N7Cell → N7Cell :=
  match k.1 with
  | 0 => fun p => p
  | 1 => fun p => (n7flip p.2, p.1)
  | 2 => fun p => (n7flip p.1, n7flip p.2)
  | 3 => fun p => (p.2, n7flip p.1)
  | 4 => fun p => (n7flip p.1, p.2)
  | 5 => fun p => (p.1, n7flip p.2)
  | 6 => fun p => (p.2, p.1)
  | _ => fun p => (n7flip p.2, n7flip p.1)

def n7c (x y : Fin 3) : N7Cell := (x, y)
def n7reps : Finset (Finset N7Cell) :=
  { {n7c 0 0, n7c 1 0}, {n7c 0 0, n7c 2 0},
    {n7c 0 0, n7c 1 1}, {n7c 0 0, n7c 2 1},
    {n7c 0 0, n7c 2 2}, {n7c 1 0, n7c 0 1},
    {n7c 1 0, n7c 1 1}, {n7c 1 0, n7c 1 2} }

/-- Every pair of distinct holes is dihedrally equivalent to an appendix representative. -/
theorem n7_hole_pair_classification (a b : N7Cell) (hab : a ≠ b) :
    ∃ k : Fin 8, ({n7sym k a, n7sym k b} : Finset N7Cell) ∈ n7reps := by
  decide +revert

end CirclePackingConstants

noncomputable section
namespace CirclePackingConstants

/-- Deterministic closed-on-the-left 3-band classifier for `[0,1]`. -/
def n7band (x : ℝ) : Fin 3 :=
  if x ≤ 1 / 3 then 0 else if x ≤ 2 / 3 then 1 else 2

def n7cell (p : Point) : Fin 3 × Fin 3 := (n7band p.1, n7band p.2)

lemma n7band_bounds (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (((n7band x).val : ℝ) / 3 ≤ x) ∧
      x ≤ (((n7band x).val : ℝ) + 1) / 3 := by
  by_cases h1 : x ≤ 1 / 3
  · rw [n7band, if_pos h1]
    norm_num
    constructor <;> linarith
  by_cases h2 : x ≤ 2 / 3
  · rw [n7band, if_neg h1, if_pos h2]
    norm_num
    constructor <;> linarith
  · rw [n7band, if_neg h1, if_neg h2]
    norm_num
    constructor <;> linarith

lemma n7band_same_width {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (h : n7band x = n7band y) :
    (x - y)^2 ≤ (1 / 3 : ℝ)^2 := by
  rcases n7band_bounds x hx0 hx1 with ⟨xl, xu⟩
  rcases n7band_bounds y hy0 hy1 with ⟨yl, yu⟩
  have he : ((n7band x).val : ℝ) = ((n7band y).val : ℝ) := by simpa [h]
  have hlo : -(1 / 3 : ℝ) ≤ x - y := by linarith
  have hup : x - y ≤ (1 / 3 : ℝ) := by linarith
  have hp : 0 ≤ (1 / 3 : ℝ) - (x-y) := by linarith
  have hn : 0 ≤ (1 / 3 : ℝ) + (x-y) := by linarith
  nlinarith only [mul_nonneg hp hn]

lemma n7_same_cell_close {p : Fin 7 → Point} {i j : Fin 7}
    (hp : ∀ k, 0 ≤ (p k).1 ∧ (p k).1 ≤ 1 ∧ 0 ≤ (p k).2 ∧ (p k).2 ≤ 1)
    (hcell : n7cell (p i) = n7cell (p j)) :
    sqDist (p i) (p j) ≤ (2 / 9 : ℝ) := by
  have hx := n7band_same_width (hp i).1 (hp i).2.1 (hp j).1 (hp j).2.1
    (congrArg Prod.fst hcell)
  have hy' := n7band_same_width (hp i).2.2.1 (hp i).2.2.2 (hp j).2.2.1 (hp j).2.2.2
    (congrArg Prod.snd hcell)
  dsimp [sqDist]
  nlinarith only [hx, hy']

lemma n7_threshold_gt_grid : (2 / 9 : ℝ) < (4 - 2 * Real.sqrt 3)^2 := by
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  nlinarith

lemma n7_cell_injective {p : Fin 7 → Point}
    (hp : ∀ k, 0 ≤ (p k).1 ∧ (p k).1 ≤ 1 ∧ 0 ≤ (p k).2 ∧ (p k).2 ≤ 1)
    (hsep : ∀ i j, i ≠ j → (4 - 2 * Real.sqrt 3)^2 < sqDist (p i) (p j)) :
    Function.Injective (fun i => n7cell (p i)) := by
  intro i j hij
  by_contra hne
  have hclose := n7_same_cell_close hp hij
  have hfar := hsep i j hne
  have hthr := n7_threshold_gt_grid
  linarith


def n7occ (p : Fin 7 → Point) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.image (fun i => n7cell (p i))

def n7holes (p : Fin 7 → Point) : Finset (Fin 3 × Fin 3) := (n7occ p)ᶜ

lemma n7_holes_card_two {p : Fin 7 → Point}
    (hinj : Function.Injective (fun i => n7cell (p i))) :
    (n7holes p).card = 2 := by
  rw [n7holes, Finset.card_compl]
  have himage : (Finset.univ.image (fun i => n7cell (p i))).card = 7 := by
    rw [Finset.card_image_of_injective Finset.univ hinj]
    norm_num
  change Fintype.card (Fin 3 × Fin 3) -
    (Finset.univ.image (fun i => n7cell (p i))).card = 2
  rw [himage]
  norm_num

lemma n7_occupied_of_not_hole {p : Fin 7 → Point} {c : Fin 3 × Fin 3}
    (hc : c ∉ n7holes p) : ∃ i : Fin 7, n7cell (p i) = c := by
  have hmem : c ∈ n7occ p := by
    simpa [n7holes] using hc
  rcases Finset.mem_image.mp hmem with ⟨i, hi, hci⟩
  exact ⟨i, hci⟩

lemma n7_occupied_unique {p : Fin 7 → Point}
    (hinj : Function.Injective (fun i => n7cell (p i)))
    {c : Fin 3 × Fin 3} {i j : Fin 7}
    (hi : n7cell (p i) = c) (hj : n7cell (p j) = c) : i = j := by
  apply hinj
  change n7cell (p i) = n7cell (p j)
  rw [hi, hj]

lemma n7_two_holes {p : Fin 7 → Point}
    (hinj : Function.Injective (fun i => n7cell (p i))) :
    ∃ a b : Fin 3 × Fin 3, a ≠ b ∧ n7holes p = {a, b} := by
  exact Finset.card_eq_two.mp (n7_holes_card_two hinj)

end CirclePackingConstants

noncomputable section
namespace CirclePackingConstants

def n7_point_sym (k : Fin 8) (p : Point) : Point :=
  match k.1 with
  | 0 => (p.1, p.2)
  | 1 => (1-p.2, p.1)
  | 2 => (1-p.1, 1-p.2)
  | 3 => (p.2, 1-p.1)
  | 4 => (1-p.1, p.2)
  | 5 => (p.1, 1-p.2)
  | 6 => (p.2, p.1)
  | _ => (1-p.2, 1-p.1)

def n7_cell_box (c : N7Cell) (p : Point) : Prop :=
  (c.1.val : ℝ) / 3 ≤ p.1 ∧ p.1 ≤ (c.1.val + 1 : ℝ) / 3 ∧
  (c.2.val : ℝ) / 3 ≤ p.2 ∧ p.2 ≤ (c.2.val + 1 : ℝ) / 3

lemma n7_point_sym_sqDist (k : Fin 8) (p q : Point) :
    sqDist (n7_point_sym k p) (n7_point_sym k q) = sqDist p q := by
  fin_cases k <;> simp [n7_point_sym, sqDist] <;> ring

lemma n7flip_val (x : Fin 3) : (n7flip x).val = 2 - x.val := rfl

lemma n7_point_sym_unit (k : Fin 8) {p : Point}
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1) :
    0 ≤ (n7_point_sym k p).1 ∧ (n7_point_sym k p).1 ≤ 1 ∧
    0 ≤ (n7_point_sym k p).2 ∧ (n7_point_sym k p).2 ≤ 1 := by
  fin_cases k <;> simp_all [n7_point_sym] <;> norm_num <;> linarith

lemma n7_reflect_band {i : Fin 3} {x : ℝ}
    (hL : (i.val:ℝ)/3 ≤ x) (hU : x ≤ (i.val+1:ℝ)/3) :
    ((n7flip i).val:ℝ)/3 ≤ 1-x ∧ 1-x ≤ ((n7flip i).val+1:ℝ)/3 := by
  fin_cases i <;> simp [n7flip, n7flip_val] at hL hU ⊢
  · constructor <;> norm_num <;> linarith
  · constructor <;> norm_num <;> linarith
  · constructor <;> norm_num <;> linarith

lemma n7_point_sym_box (k : Fin 8) {c : N7Cell} {p : Point}
    (hp : n7_cell_box c p) : n7_cell_box (n7sym k c) (n7_point_sym k p) := by
  rcases hp with ⟨hxL,hxU,hyL,hyU⟩
  have rx := n7_reflect_band hxL hxU
  have ry := n7_reflect_band hyL hyU
  have rxU : 1 ≤ ((n7flip c.1).val + 1 : ℝ) / 3 + p.1 := by linarith [rx.2]
  have ryU : 1 ≤ ((n7flip c.2).val + 1 : ℝ) / 3 + p.2 := by linarith [ry.2]
  fin_cases k
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨hxL,hxU,hyL,hyU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨ry.1,ryU,hxL,hxU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨rx.1,rxU,ry.1,ryU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨hyL,hyU,rx.1,rxU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨rx.1,rxU,hyL,hyU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨hxL,hxU,ry.1,ryU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨hyL,hyU,hxL,hxU⟩
  · simpa [n7_point_sym, n7sym, n7_cell_box, n7flip_val] using ⟨ry.1,ryU,rx.1,rxU⟩
end CirclePackingConstants

namespace CirclePackingConstants

def n7symInv (k : Fin 8) : Fin 8 :=
  match k.1 with
  | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1
  | 4 => 4 | 5 => 5 | 6 => 6 | _ => 7

lemma n7flip_flip (x : Fin 3) : n7flip (n7flip x) = x := by
  fin_cases x <;> rfl

lemma n7sym_inv_apply (k : Fin 8) (c : N7Cell) :
    n7sym (n7symInv k) (n7sym k c) = c := by
  fin_cases k <;> simp [n7sym, n7symInv, n7flip_flip]

lemma n7sym_inv_apply' (k : Fin 8) (c : N7Cell) :
    n7sym k (n7sym (n7symInv k) c) = c := by
  fin_cases k <;> simp [n7sym, n7symInv, n7flip_flip]

def n7symEquiv (k : Fin 8) : Equiv N7Cell N7Cell where
  toFun := n7sym k
  invFun := n7sym (n7symInv k)
  left_inv := n7sym_inv_apply k
  right_inv := n7sym_inv_apply' k

lemma n7symEquiv_apply (k : Fin 8) (c : N7Cell) : n7symEquiv k c = n7sym k c := rfl
end CirclePackingConstants

namespace CirclePackingConstants

def n7repHoles (k : Fin 8) : Finset N7Cell :=
  match k.1 with
  | 0 => {n7c 0 0, n7c 1 0}
  | 1 => {n7c 0 0, n7c 2 0}
  | 2 => {n7c 0 0, n7c 1 1}
  | 3 => {n7c 0 0, n7c 2 1}
  | 4 => {n7c 0 0, n7c 2 2}
  | 5 => {n7c 1 0, n7c 0 1}
  | 6 => {n7c 1 0, n7c 1 1}
  | _ => {n7c 1 0, n7c 1 2}

def n7repCells (k : Fin 8) : Fin 7 → N7Cell :=
  match k.1 with
  | 0 => ![(n7c 2 0),(n7c 0 1),(n7c 1 1),(n7c 2 1),(n7c 0 2),(n7c 1 2),(n7c 2 2)]
  | 1 => ![(n7c 1 0),(n7c 0 1),(n7c 1 1),(n7c 2 1),(n7c 0 2),(n7c 1 2),(n7c 2 2)]
  | 2 => ![(n7c 1 0),(n7c 2 0),(n7c 0 1),(n7c 2 1),(n7c 0 2),(n7c 1 2),(n7c 2 2)]
  | 3 => ![(n7c 1 0),(n7c 2 0),(n7c 0 1),(n7c 1 1),(n7c 0 2),(n7c 1 2),(n7c 2 2)]
  | 4 => ![(n7c 1 0),(n7c 2 0),(n7c 0 1),(n7c 1 1),(n7c 2 1),(n7c 0 2),(n7c 1 2)]
  | 5 => ![(n7c 0 0),(n7c 2 0),(n7c 1 1),(n7c 2 1),(n7c 0 2),(n7c 1 2),(n7c 2 2)]
  | 6 => ![(n7c 0 0),(n7c 2 0),(n7c 0 1),(n7c 2 1),(n7c 0 2),(n7c 1 2),(n7c 2 2)]
  | _ => ![(n7c 0 0),(n7c 2 0),(n7c 0 1),(n7c 1 1),(n7c 2 1),(n7c 0 2),(n7c 2 2)]

theorem n7repHoles_range : Finset.univ.image n7repHoles = n7reps := by decide +revert

theorem n7repCells_compl (k : Fin 8) :
    Finset.univ.image (n7repCells k) = Finset.univ \ n7repHoles k := by decide +revert

theorem n7repCells_injective (k : Fin 8) : Function.Injective (n7repCells k) := by decide +revert

end CirclePackingConstants

namespace CirclePackingConstants

lemma n7_cell_box_of_n7cell {p : Point} {c : N7Cell}
    (hp : 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1)
    (hc : n7cell p = c) : n7_cell_box c p := by
  rcases n7band_bounds p.1 hp.1 hp.2.1 with ⟨hxL,hxU⟩
  rcases n7band_bounds p.2 hp.2.2.1 hp.2.2.2 with ⟨hyL,hyU⟩
  rw [← hc]
  exact ⟨hxL,hxU,hyL,hyU⟩

lemma n7_sym_unique_occupant {p : Fin 7 → Point}
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hinj : Function.Injective (fun i => n7cell (p i)))
    (k : Fin 8) (c : N7Cell)
    (hc : n7sym (n7symInv k) c ∉ n7holes p) :
    ∃! i, n7cell (p i) = n7sym (n7symInv k) c ∧
      n7_cell_box c (n7_point_sym k (p i)) := by
  obtain ⟨i,hi⟩ := n7_occupied_of_not_hole hc
  have hbox0 := n7_cell_box_of_n7cell (hp i) hi
  have htarget : n7_cell_box c (n7_point_sym k (p i)) := by
    have := n7_point_sym_box k hbox0
    simpa [n7sym_inv_apply'] using this
  refine ⟨i, ⟨hi,htarget⟩, ?_⟩
  intro j hj
  exact n7_occupied_unique hinj hj.1 hi
end CirclePackingConstants

namespace CirclePackingConstants

lemma n7_choose_rep (p : Fin 7 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hinj : Function.Injective (fun i => n7cell (p i))) :
    ∃ k r : Fin 8, Finset.image (n7sym k) (n7holes p) = n7repHoles r := by
  obtain ⟨a,b,hab,hholes⟩ := n7_two_holes hinj
  obtain ⟨k,hk⟩ := n7_hole_pair_classification a b hab
  rw [← n7repHoles_range] at hk
  rcases Finset.mem_image.mp hk with ⟨r, -, hr⟩
  refine ⟨k,r,?_⟩
  rw [hholes]
  simpa [hr]
end CirclePackingConstants

noncomputable section
namespace CirclePackingConstants

lemma n7_reindex_rep (p : Fin 7 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hinj : Function.Injective (fun i => n7cell (p i)))
    (k r : Fin 8)
    (hholes : Finset.image (n7sym k) (n7holes p) = n7repHoles r) :
    ∃ pick : Fin 7 → Fin 7, ∃ q : Fin 7 → Point,
      (∀ j, n7cell (p (pick j)) = n7sym (n7symInv k) (n7repCells r j)) ∧
      (∀ j, n7_cell_box (n7repCells r j) (q j)) ∧
      Function.Injective pick ∧
      (∀ i j, sqDist (q i) (q j) = sqDist (p (pick i)) (p (pick j))) := by
  have hpre (j : Fin 7) : n7sym (n7symInv k) (n7repCells r j) ∉ n7holes p := by
    intro hh
    have him : n7repCells r j ∈ Finset.image (n7sym k) (n7holes p) := by
      refine Finset.mem_image.mpr ⟨n7sym (n7symInv k) (n7repCells r j), hh, ?_⟩
      exact n7sym_inv_apply' k _
    have hrep : n7repCells r j ∈ n7repHoles r := by simpa [hholes] using him
    have hcomp : n7repCells r j ∈ Finset.univ \ n7repHoles r := by
      rw [← n7repCells_compl r]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp hcomp).2 hrep
  let pick : Fin 7 → Fin 7 := fun j => Classical.choose
    (n7_sym_unique_occupant hp hinj k (n7repCells r j) (hpre j))
  have hpick (j : Fin 7) :
      n7cell (p (pick j)) = n7sym (n7symInv k) (n7repCells r j) ∧
        n7_cell_box (n7repCells r j) (n7_point_sym k (p (pick j))) := by
    exact (Classical.choose_spec (n7_sym_unique_occupant hp hinj k (n7repCells r j) (hpre j))).1
  let q : Fin 7 → Point := fun j => n7_point_sym k (p (pick j))
  refine ⟨pick, q, ?_, ?_, ?_, ?_⟩
  · intro j; exact (hpick j).1
  · intro j; exact (hpick j).2
  · intro i j hij
    apply n7repCells_injective r
    have heq : n7sym (n7symInv k) (n7repCells r i) =
        n7sym (n7symInv k) (n7repCells r j) := by
      rw [← (hpick i).1, ← (hpick j).1, hij]
    have := congrArg (n7sym k) heq
    simpa [n7sym_inv_apply'] using this
  · intro i j
    exact n7_point_sym_sqDist k (p (pick i)) (p (pick j))
end CirclePackingConstants

noncomputable section
namespace CirclePackingConstants

lemma n7_scaled_threshold :
    (2584683:ℝ) < (3000:ℝ)^2 * (4 - 2*Real.sqrt 3)^2 := by
  have hs : (Real.sqrt 3)^2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
  have hn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hu : Real.sqrt 3 < (173205081:ℝ) / 100000000 := by
    nlinarith
  have hl : (53589838:ℝ) / 100000000 < 4 - 2*Real.sqrt 3 := by
    linarith
  have hl0 : 0 < (53589838:ℝ) / 100000000 := by norm_num
  nlinarith

lemma n7_scaled_sep {u v : Point}
    (h : (4 - 2*Real.sqrt 3)^2 < sqDist u v) :
    (2584683:ℝ) < (3000*u.1 - 3000*v.1)^2 + (3000*u.2 - 3000*v.2)^2 := by
  have ht := n7_scaled_threshold
  dsimp [sqDist] at h
  nlinarith

lemma n7_scaled_cell_box {c : N7Cell} {q : Point}
    (h : n7_cell_box c q) :
    (1000 * (c.1.val : ℝ) ≤ 3000*q.1 ∧ 3000*q.1 ≤ 1000 * (c.1.val + 1 : ℝ)) ∧
    (1000 * (c.2.val : ℝ) ≤ 3000*q.2 ∧ 3000*q.2 ≤ 1000 * (c.2.val + 1 : ℝ)) := by
  rcases h with ⟨hxL,hxU,hyL,hyU⟩
  constructor <;> constructor <;> nlinarith

lemma n7_global_reindex (p : Fin 7 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hinj : Function.Injective (fun i => n7cell (p i))) :
    ∃ k r : Fin 8, ∃ pick : Fin 7 → Fin 7, ∃ q : Fin 7 → Point,
      (∀ j, n7cell (p (pick j)) = n7sym (n7symInv k) (n7repCells r j)) ∧
      (∀ j, n7_cell_box (n7repCells r j) (q j)) ∧
      Function.Injective pick ∧
      (∀ i j, sqDist (q i) (q j) = sqDist (p (pick i)) (p (pick j))) := by
  obtain ⟨k,r,hholes⟩ := n7_choose_rep p hp hinj
  obtain ⟨pick,q,hcell,hbox,hpick,hdist⟩ := n7_reindex_rep p hp hinj k r hholes
  exact ⟨k,r,pick,q,hcell,hbox,hpick,hdist⟩
end CirclePackingConstants

namespace CirclePackingConstants
lemma n7_rep_dispatch (r : Fin 8) (q : Fin 7 → Point)
  (hbox : ∀ j, n7_cell_box (n7repCells r j) (q j))
  (hsep : ∀ i j, i ≠ j → (4-2*Real.sqrt 3)^2 < sqDist (q i) (q j)) : False := by
  let X : Fin 7 → ℝ := fun j => 3000 * (q j).1
  let Y : Fin 7 → ℝ := fun j => 3000 * (q j).2
  have hT01 : (2584683:ℝ) < (X 0-X 1)^2+(Y 0-Y 1)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 0 1 (by decide))
  have hT02 : (2584683:ℝ) < (X 0-X 2)^2+(Y 0-Y 2)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 0 2 (by decide))
  have hT03 : (2584683:ℝ) < (X 0-X 3)^2+(Y 0-Y 3)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 0 3 (by decide))
  have hT04 : (2584683:ℝ) < (X 0-X 4)^2+(Y 0-Y 4)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 0 4 (by decide))
  have hT05 : (2584683:ℝ) < (X 0-X 5)^2+(Y 0-Y 5)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 0 5 (by decide))
  have hT06 : (2584683:ℝ) < (X 0-X 6)^2+(Y 0-Y 6)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 0 6 (by decide))
  have hT12 : (2584683:ℝ) < (X 1-X 2)^2+(Y 1-Y 2)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 1 2 (by decide))
  have hT13 : (2584683:ℝ) < (X 1-X 3)^2+(Y 1-Y 3)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 1 3 (by decide))
  have hT14 : (2584683:ℝ) < (X 1-X 4)^2+(Y 1-Y 4)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 1 4 (by decide))
  have hT15 : (2584683:ℝ) < (X 1-X 5)^2+(Y 1-Y 5)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 1 5 (by decide))
  have hT16 : (2584683:ℝ) < (X 1-X 6)^2+(Y 1-Y 6)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 1 6 (by decide))
  have hT23 : (2584683:ℝ) < (X 2-X 3)^2+(Y 2-Y 3)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 2 3 (by decide))
  have hT24 : (2584683:ℝ) < (X 2-X 4)^2+(Y 2-Y 4)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 2 4 (by decide))
  have hT25 : (2584683:ℝ) < (X 2-X 5)^2+(Y 2-Y 5)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 2 5 (by decide))
  have hT26 : (2584683:ℝ) < (X 2-X 6)^2+(Y 2-Y 6)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 2 6 (by decide))
  have hT34 : (2584683:ℝ) < (X 3-X 4)^2+(Y 3-Y 4)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 3 4 (by decide))
  have hT35 : (2584683:ℝ) < (X 3-X 5)^2+(Y 3-Y 5)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 3 5 (by decide))
  have hT36 : (2584683:ℝ) < (X 3-X 6)^2+(Y 3-Y 6)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 3 6 (by decide))
  have hT45 : (2584683:ℝ) < (X 4-X 5)^2+(Y 4-Y 5)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 4 5 (by decide))
  have hT46 : (2584683:ℝ) < (X 4-X 6)^2+(Y 4-Y 6)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 4 6 (by decide))
  have hT56 : (2584683:ℝ) < (X 5-X 6)^2+(Y 5-Y 6)^2 := by simpa [X,Y] using n7_scaled_sep (hsep 5 6 (by decide))
  fin_cases r
  · have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (2000:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (3000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (0:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (1000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (1000:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (2000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (1000:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (2000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (2000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (3000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (0:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (1000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (2000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (3000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (1000:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (2000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.N7Rep01.n7_pattern_01_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56
  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (1000:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (2000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (0:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (1000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (1000:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (2000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (1000:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (2000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (2000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (3000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (0:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (1000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (2000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (3000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (1000:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (2000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.N7Rep02.n7_pattern_02_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56

  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (1000:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (2000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (2000:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (3000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (0:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (1000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (0:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (1000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (2000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (3000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (0:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (1000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (2000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (3000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (1000:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (2000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.n7_pattern_04_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56

  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (1000:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (2000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (2000:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (3000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (0:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (1000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (0:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (1000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (1000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (2000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (0:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (1000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (2000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (3000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (1000:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (2000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.N7Rep05.n7_pattern_05_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56

  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (1000:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (2000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (2000:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (3000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (0:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (1000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (0:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (1000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (1000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (2000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (2000:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (3000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (1000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (2000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (0:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (1000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (1000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (2000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.N7Rep08.n7_pattern_08_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56

  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (0:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (1000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (2000:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (3000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (0:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (1000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (1000:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (2000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (2000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (3000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (0:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (1000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (2000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (3000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (1000:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (2000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    have S56 := hsep 5 6 (by decide)
    have S36 := hsep 3 6 (by decide)
    have S52 := hsep 5 2 (by decide)
    have S32 := hsep 3 2 (by decide)
    have S54 := hsep 5 4 (by decide)
    have S24 := hsep 2 4 (by decide)
    have S31 := hsep 3 1 (by decide)
    have S21 := hsep 2 1 (by decide)
    have S56s : (4-2*Real.sqrt 3)^2 < ((X 5-X 6)/3000)^2+((Y 5-Y 6)/3000)^2 := by
      convert S56 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S36s : (4-2*Real.sqrt 3)^2 < ((X 3-X 6)/3000)^2+((Y 3-Y 6)/3000)^2 := by
      convert S36 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S52s : (4-2*Real.sqrt 3)^2 < ((X 5-X 2)/3000)^2+((Y 5-Y 2)/3000)^2 := by
      convert S52 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S32s : (4-2*Real.sqrt 3)^2 < ((X 3-X 2)/3000)^2+((Y 3-Y 2)/3000)^2 := by
      convert S32 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S54s : (4-2*Real.sqrt 3)^2 < ((X 5-X 4)/3000)^2+((Y 5-Y 4)/3000)^2 := by
      convert S54 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S24s : (4-2*Real.sqrt 3)^2 < ((X 2-X 4)/3000)^2+((Y 2-Y 4)/3000)^2 := by
      convert S24 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S31s : (4-2*Real.sqrt 3)^2 < ((X 3-X 1)/3000)^2+((Y 3-Y 1)/3000)^2 := by
      convert S31 using 1 <;> simp [X, Y, sqDist] <;> ring
    have S21s : (4-2*Real.sqrt 3)^2 < ((X 2-X 1)/3000)^2+((Y 2-Y 1)/3000)^2 := by
      convert S21 using 1 <;> simp [X, Y, sqDist] <;> ring
    exact CirclePackingConstants.n7_pattern_13_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56
      S56s S36s S52s S32s S54s S24s S31s S21s

  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (0:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (1000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (2000:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (3000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (0:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (1000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (0:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (1000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (2000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (3000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (0:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (1000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (2000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (3000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (1000:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (2000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.n7_pattern_14_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56

  ·
    have b0 := n7_scaled_cell_box (hbox 0)
    have b1 := n7_scaled_cell_box (hbox 1)
    have b2 := n7_scaled_cell_box (hbox 2)
    have b3 := n7_scaled_cell_box (hbox 3)
    have b4 := n7_scaled_cell_box (hbox 4)
    have b5 := n7_scaled_cell_box (hbox 5)
    have b6 := n7_scaled_cell_box (hbox 6)
    simp [n7repCells, n7repHoles] at b0 b1 b2 b3 b4 b5 b6
    rcases b0 with ⟨⟨a0,b0⟩,⟨c0,d0⟩⟩
    rcases b1 with ⟨⟨a1,b1⟩,⟨c1,d1⟩⟩
    rcases b2 with ⟨⟨a2,b2⟩,⟨c2,d2⟩⟩
    rcases b3 with ⟨⟨a3,b3⟩,⟨c3,d3⟩⟩
    rcases b4 with ⟨⟨a4,b4⟩,⟨c4,d4⟩⟩
    rcases b5 with ⟨⟨a5,b5⟩,⟨c5,d5⟩⟩
    rcases b6 with ⟨⟨a6,b6⟩,⟨c6,d6⟩⟩
    have A0 : (0:ℝ) ≤ 3000*(q 0).1 := by convert a0 using 1 <;> norm_num [n7c]
    have B0 : 3000*(q 0).1 ≤ (1000:ℝ) := by convert b0 using 1 <;> norm_num [n7c]
    have C0 : (0:ℝ) ≤ 3000*(q 0).2 := by convert c0 using 1 <;> norm_num [n7c]
    have D0 : 3000*(q 0).2 ≤ (1000:ℝ) := by convert d0 using 1 <;> norm_num [n7c]
    have A1 : (2000:ℝ) ≤ 3000*(q 1).1 := by convert a1 using 1 <;> norm_num [n7c]
    have B1 : 3000*(q 1).1 ≤ (3000:ℝ) := by convert b1 using 1 <;> norm_num [n7c]
    have C1 : (0:ℝ) ≤ 3000*(q 1).2 := by convert c1 using 1 <;> norm_num [n7c]
    have D1 : 3000*(q 1).2 ≤ (1000:ℝ) := by convert d1 using 1 <;> norm_num [n7c]
    have A2 : (0:ℝ) ≤ 3000*(q 2).1 := by convert a2 using 1 <;> norm_num [n7c]
    have B2 : 3000*(q 2).1 ≤ (1000:ℝ) := by convert b2 using 1 <;> norm_num [n7c]
    have C2 : (1000:ℝ) ≤ 3000*(q 2).2 := by convert c2 using 1 <;> norm_num [n7c]
    have D2 : 3000*(q 2).2 ≤ (2000:ℝ) := by convert d2 using 1 <;> norm_num [n7c]
    have A3 : (1000:ℝ) ≤ 3000*(q 3).1 := by convert a3 using 1 <;> norm_num [n7c]
    have B3 : 3000*(q 3).1 ≤ (2000:ℝ) := by convert b3 using 1 <;> norm_num [n7c]
    have C3 : (1000:ℝ) ≤ 3000*(q 3).2 := by convert c3 using 1 <;> norm_num [n7c]
    have D3 : 3000*(q 3).2 ≤ (2000:ℝ) := by convert d3 using 1 <;> norm_num [n7c]
    have A4 : (2000:ℝ) ≤ 3000*(q 4).1 := by convert a4 using 1 <;> norm_num [n7c]
    have B4 : 3000*(q 4).1 ≤ (3000:ℝ) := by convert b4 using 1 <;> norm_num [n7c]
    have C4 : (1000:ℝ) ≤ 3000*(q 4).2 := by convert c4 using 1 <;> norm_num [n7c]
    have D4 : 3000*(q 4).2 ≤ (2000:ℝ) := by convert d4 using 1 <;> norm_num [n7c]
    have A5 : (0:ℝ) ≤ 3000*(q 5).1 := by convert a5 using 1 <;> norm_num [n7c]
    have B5 : 3000*(q 5).1 ≤ (1000:ℝ) := by convert b5 using 1 <;> norm_num [n7c]
    have C5 : (2000:ℝ) ≤ 3000*(q 5).2 := by convert c5 using 1 <;> norm_num [n7c]
    have D5 : 3000*(q 5).2 ≤ (3000:ℝ) := by convert d5 using 1 <;> norm_num [n7c]
    have A6 : (2000:ℝ) ≤ 3000*(q 6).1 := by convert a6 using 1 <;> norm_num [n7c]
    have B6 : 3000*(q 6).1 ≤ (3000:ℝ) := by convert b6 using 1 <;> norm_num [n7c]
    have C6 : (2000:ℝ) ≤ 3000*(q 6).2 := by convert c6 using 1 <;> norm_num [n7c]
    have D6 : 3000*(q 6).2 ≤ (3000:ℝ) := by convert d6 using 1 <;> norm_num [n7c]
    exact CirclePackingConstants.n7_pattern_17_infeasible (3000*(q 0).1) (3000*(q 0).2) (3000*(q 1).1) (3000*(q 1).2) (3000*(q 2).1) (3000*(q 2).2) (3000*(q 3).1) (3000*(q 3).2) (3000*(q 4).1) (3000*(q 4).2) (3000*(q 5).1) (3000*(q 5).2) (3000*(q 6).1) (3000*(q 6).2)
      A0 B0 C0 D0 A1 B1 C1 D1 A2 B2 C2 D2 A3 B3 C3 D3 A4 B4 C4 D4 A5 B5 C5 D5 A6 B6 C6 D6
      hT01 hT02 hT03 hT04 hT05 hT06 hT12 hT13 hT14 hT15 hT16 hT23 hT24 hT25 hT26 hT34 hT35 hT36 hT45 hT46 hT56

end CirclePackingConstants
open CirclePackingConstants

noncomputable section

theorem solution : ∀ p : Fin 7 → Point,
  (∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1) →
  ∃ i j, i ≠ j ∧ sqDist (p i) (p j) ≤ (4 - 2*Real.sqrt 3)^2 := by
  intro p hp
  by_contra h
  have hsep : ∀ i j, i ≠ j → (4 - 2*Real.sqrt 3)^2 < sqDist (p i) (p j) := by
    intro i j hij
    by_contra hn
    exact h ⟨i,j,hij,le_of_not_gt hn⟩
  have hinj := n7_cell_injective hp hsep
  obtain ⟨k,r,pick,q,hcell,hbox,hpick,hdist⟩ := n7_global_reindex p hp hinj
  have hsepQ : ∀ i j, i ≠ j → (4 - 2*Real.sqrt 3)^2 < sqDist (q i) (q j) := by
    intro i j hij
    rw [hdist]
    exact hsep (pick i) (pick j) (by intro heq; exact hij (hpick heq))
  exact n7_rep_dispatch r q hbox hsepQ
