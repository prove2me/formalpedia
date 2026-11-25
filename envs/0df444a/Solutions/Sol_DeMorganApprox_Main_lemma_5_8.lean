-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:21:05.243478+00:00
-- url     : https://prove2.me/submissions/79ddb1a3-0d13-40e5-b371-7b4661eefdd7

import Theorems.Thm_DeMorganApprox_Main_lemma_5_9

open DeMorganApprox.Main

private lemma rot_subset {m : ℕ} (t : TieRule) (T : Formula m) :
    rotCols t T ⊆ chainCols t T := by
  induction T generalizing t with
  | lit i b => simp [rotCols]
  | and p q hp hq =>
    cases hd : heavyDir t p q <;>
      simp only [rotCols, chainCols, colsStep, hd, Bool.false_eq_true, if_true, if_false,
        Finset.union_empty] <;>
      exact (Finset.image_subset_image (by first | exact hp _ | exact hq _)).trans Finset.subset_union_left
  | or p q hp hq =>
    cases hd : heavyDir t p q <;>
      simp only [rotCols, chainCols, colsStep, hd, Bool.false_eq_true, if_true, if_false,
        Finset.union_singleton, Finset.insert_subset_iff] <;>
      refine ⟨Finset.mem_insert_self _ _,?_⟩ <;>
      exact ((Finset.image_subset_image (by first | exact hp _ | exact hq _)).trans
        Finset.subset_union_left).trans (Finset.subset_insert _ _)

private lemma block_subset {m : ℕ} (t : TieRule) (T : Formula m) (h : T.isLeaf = false) :
    chainBlockCols t T ⊆ fullCols t T := by
  simp only [chainBlockCols, fullCols, fullColsOf,h,Bool.false_eq_true,if_false]
  exact Finset.insert_subset_insert _ (rot_subset t T)

private lemma restrict_cols {ι J : Type} [Fintype ι] [DecidableEq J] {A B : Finset J}
    (h : A ⊆ B) (V : J → ι → ℝ) (c : ℝ)
    (hn : AbsNormLE (fun (j : B) i => V j.val i) c) :
    AbsNormLE (fun (j : A) i => V j.val i) c := by
  classical
  intro y
  let Y := fun j : J => if hj : j ∈ A then y ⟨j,hj⟩ else 0
  have restrict (f : J → ℝ) (hf : ∀ j, j ∉ A → f j = 0) :
      ∑ j : B, f j.val = ∑ j : A, f j.val := by
    rw [← Finset.sum_subtype B (fun _ => Iff.rfl), ← Finset.sum_subtype A (fun _ => Iff.rfl)]
    exact (Finset.sum_subset h (fun j _ hj => hf j hj)).symm
  have hr (i : ι) : ∑ j : B, |V j.val i| * Y j.val = ∑ j : A, |V j.val i| * y j := by
    simpa [Y] using restrict (fun j => |V j i| * Y j) (by intro j hj; simp [Y,hj])
  have hs : ∑ j : B, (Y j.val)^2 = ∑ j : A, (y j)^2 := by
    calc
      _ = ∑ j : A, (Y j.val)^2 := restrict (fun j => (Y j)^2) (by intro j hj; simp [Y,hj])
      _ = _ := by simp [Y]
  simpa only [hr,hs] using hn (fun j => Y j.val)

theorem solution :
    ∃ c : ℝ, ∀ (m : ℕ) (tie : TieRule) (T : Formula m), T.isLeaf = false →
      AbsNormLE (fun (j : {j // j ∈ chainBlockCols tie T}) (k : {k // k ∈ fullCoords tie T}) =>
        colVec tie T j.1 k.1) c := by
  obtain ⟨c,hc⟩ := lemma_5_9
  refine ⟨c, fun m t T hT => ?_⟩
  exact restrict_cols (block_subset t T hT) (fun j (k : fullCoords t T) => colVec t T j k.val) c (hc m t T)
