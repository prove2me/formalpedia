-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.w_normalization
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:53:12.408404+00:00
-- url     : https://prove2.me/submissions/797987ad-33f8-4de4-889a-239b19ee1c93

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix
open ConicQuadIPM.Complementarity
private lemma coordinate {d : ℕ} (v : Fin d → ℝ) (r : ℕ) (hr : r < d) : coord v r = v ⟨r, hr⟩ := by
  unfold coord
  rw [Finset.sum_eq_single ⟨r, hr⟩]
  · simp
  · intro j hj h; simp [show j.val ≠ r by intro he; apply h; exact Fin.ext he]
  · simp

private lemma quad_form (d : ℕ) (v : Fin d → ℝ) :
    v ⬝ᵥ (Qmat .quad d *ᵥ v) = coord v 0 ^ 2 - tailSq v 1 := by
  have hhead : (∑ j : Fin d, if j.val = 0 then v j ^ 2 else 0) = coord v 0 ^ 2 := by
    cases d with
    | zero => simp [coord]
    | succ d =>
      rw [coordinate v 0 (by omega), Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj h; simp [show j.val ≠ 0 by intro he; apply h; exact Fin.ext he]
      · simp
  change (∑ j : Fin d, v j * (Qmat .quad d *ᵥ v) j) = _
  have he : ∀ j : Fin d, v j * (Qmat .quad d *ᵥ v) j =
      (if j.val = 0 then v j ^ 2 else 0) - (if 1 ≤ j.val then v j ^ 2 else 0) := by
    intro j
    simp only [Qmat, Matrix.mulVec_diagonal]
    split_ifs <;> simp_all [pow_two] <;> try omega <;> ring
  simp_rw [he, Finset.sum_sub_distrib]
  rw [hhead]; rfl


private lemma qmatch (d : ℕ) : ConicQuadIPM.NTScaling.Qmat .quad d = Qmat .quad d := by
  ext a b
  simp [ConicQuadIPM.NTScaling.Qmat, Qmat, diagonal_apply]
private lemma wsym {d : ℕ} (w : Fin d → ℝ) : (ConicQuadIPM.NTScaling.WquadArrow w)ᵀ = ConicQuadIPM.NTScaling.WquadArrow w := by
  ext a b
  simp only [transpose_apply, ConicQuadIPM.NTScaling.WquadArrow, of_apply]
  by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
  · have hab : a = b := Fin.ext (ha.trans hb.symm)
    subst b
    simp [ha]
  all_goals simp [ha, hb, eq_comm, mul_comm]
private lemma we {d : ℕ} (hd : 1 ≤ d) (w : Fin d → ℝ) :
    ConicQuadIPM.NTScaling.WquadArrow w *ᵥ e1 = w := by
  ext a
  change (∑ j : Fin d, ConicQuadIPM.NTScaling.WquadArrow w a j * e1 j) = w a
  rw [Finset.sum_eq_single ⟨0, by omega⟩]
  · by_cases ha : a.val = 0
    · have he : a = (⟨0, by omega⟩ : Fin d) := Fin.ext ha
      rw [he]; simp [ConicQuadIPM.NTScaling.WquadArrow, e1]
    · simp [ConicQuadIPM.NTScaling.WquadArrow, e1, ha]
  · intro j hj hn
    have hj0 : j.val ≠ 0 := by intro h; apply hn; exact Fin.ext h
    simp [e1, hj0]
  · simp
open ConicQuadIPM.NTScaling in
theorem solution (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℝ) (hw : 0 < 1 + ConicQuadIPM.Complementarity.coord w 0)
    (hWQW : WquadArrow w * ConicQuadIPM.NTScaling.Qmat .quad d * WquadArrow w = ConicQuadIPM.NTScaling.Qmat .quad d) :
    ConicQuadIPM.Complementarity.coord w 0 ^ 2 - ConicQuadIPM.Complementarity.tailSq w 1 = 1 := by
  rw [← quad_form, ← qmatch]
  have hs := wsym w
  have he := we hd w
  rw [← he, dotProduct_mulVec, vecMul_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hs, hWQW, qmatch]
  have hz : (e1 : Fin d → ℝ) = fun j => if j = (⟨0, by omega⟩ : Fin d) then 1 else 0 := by
    ext j; simp [e1, Fin.ext_iff]
  simp [ConicQuadIPM.Complementarity.Qmat, mulVec_diagonal, dotProduct, hz]

#print axioms solution
