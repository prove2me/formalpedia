-- Prove2me | solution 1 for Freiman.lower_h5_priority_cover_identity
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:36:30.808027+00:00
-- url     : https://prove2.me/submissions/e6eadd71-088d-4b81-9dd4-4435191eef37

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie
import Mathlib.Tactic


open Freiman
namespace M7H5Cover14

private theorem cover_identity (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p →
    let q := lowerNormalize p
    lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
    lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ) (hh : lowerHistory t h n) (he : LowerH5PriorityEvent t h n m) :
    lowerLocalLower (h n) ([2],[]) = lowerLocalLower (h m) ([2],[2]) ∧
    lowerH5LocalUpper (h n) ([2],[]) = lowerH5LocalUpper (h m) ([2],[2]) ∧
    lowerLocalCoordinate (h n) t = lowerLocalCoordinate (h m) t := by
  let Z := lowerNormalize (h m)
  have hsm := hh.2.1 m he.earlier.le
  have hsn := hh.2.1 n le_rfl
  have hw : lowerWidth (Z.1++[2]) < lowerWidth Z.2 :=
    (hf (h m) hsm.2.1 hsm.2.2.2).1
  have hstep : h n = (Z.1++[2],Z.2) := by
    rw [he.selected]
    simp [lowerChild,Z]
  have hnorm : lowerNormalize (h n) = (Z.2,Z.1++[2]) := by
    rw [hstep]
    simp only [lowerNormalize, not_le_of_gt hw, ↓reduceIte]
  have hdouble : lowerWidth (Z.2++[2]) < lowerWidth (Z.1++[2]) := by
    have hn := (hf (h n) hsn.2.1 hsn.2.2.2).1
    simpa only [hnorm] using hn
  have hbasepar : (h m).1.length % 2 = (h m).2.length % 2 :=
    not_not.mp he.branch.1
  have hpar : Z.1.length % 2 = Z.2.length % 2 := by
    dsimp only [Z]
    unfold lowerNormalize
    split_ifs
    · exact hbasepar
    · exact hbasepar.symm
  have hcn : lowerChild (h n) ([2],[]) = (Z.2++[2],Z.1++[2]) := by
    simp only [lowerChild, hnorm, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.append_nil]
  have hcm : lowerChild (h m) ([2],[2]) = (Z.1++[2],Z.2++[2]) := by
    simp only [lowerChild, List.reverse_cons, List.reverse_nil, List.nil_append]
    rfl
  have heps (u : Bool) :
      lowerEndpoint (lowerChild (h n) ([2],[])) u =
        lowerEndpoint (lowerChild (h m) ([2],[2])) u := by
    rw [hcn,hcm]
    apply lowerEarlyTerminal_endpoint_swap_nontie
    constructor
    · exact ne_of_lt hdouble
    · intro hbad
      exfalso
      apply hbad
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have hprimary : (lowerNormalize (h n)).1.length % 2 =
      (lowerNormalize (h m)).1.length % 2 := by
    rw [hnorm]
    exact hpar.symm
  simp only [lowerLocalLower, lowerH5LocalUpper, lowerLocalCoordinate, hprimary, heps,
    and_self]

end M7H5Cover14

theorem solution (hf : ∀ (p : LowerPair), lowerGood p → lowerParameterBox p →
    let q := lowerNormalize p
    lowerWidth (q.1++[2]) < lowerWidth q.2 ∧ lowerWidth (q.1++[3]) < lowerWidth q.2 ∧
    lowerWidth (q.1++[1,1]) < lowerWidth q.2 ∧ lowerWidth (q.2++[1]) < lowerWidth q.1)
    (t : ℝ) (h : ℕ → LowerPair) (n m : ℕ) (hh : lowerHistory t h n) (he : LowerH5PriorityEvent t h n m) :
    lowerLocalLower (h n) ([2],[]) = lowerLocalLower (h m) ([2],[2]) ∧
    lowerH5LocalUpper (h n) ([2],[]) = lowerH5LocalUpper (h m) ([2],[2]) ∧
    lowerLocalCoordinate (h n) t = lowerLocalCoordinate (h m) t := by
  exact M7H5Cover14.cover_identity hf t h n m hh he

#print axioms solution
