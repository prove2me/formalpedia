-- Prove2me | solution 1 for ConicQuadIPM.NTScaling.eq_62
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:55:51.542776+00:00
-- url     : https://prove2.me/submissions/a4ae1288-fee6-49f9-b4a8-b60fc76d3ca2

import Mathlib
import Definitions.Def_ConicQuadIPM_NTScaling_Setting
import Definitions.Def_ConicQuadIPM_NTScaling_Scaling
open Matrix
open ConicQuadIPM.Complementarity
set_option maxRecDepth 4000
private lemma coordinate {d : ℕ} (v : Fin d → ℝ) (r : ℕ) (hr : r < d) : coord v r = v ⟨r, hr⟩ := by
  unfold coord
  rw [Finset.sum_eq_single ⟨r, hr⟩]
  · simp
  · intro j hj h; simp [show j.val ≠ r by intro he; apply h; exact Fin.ext he]
  · simp


open ConicQuadIPM.NTScaling in
theorem solution (d : ℕ) (hd : 1 ≤ d) (w : Fin d → ℝ)
    (hnorm : ConicQuadIPM.Complementarity.coord w 0 ^ 2 - ConicQuadIPM.Complementarity.tailSq w 1 = 1) (hw : 0 < 1 + ConicQuadIPM.Complementarity.coord w 0) :
    WquadArrow w * WquadArrow w = -ConicQuadIPM.NTScaling.Qmat .quad d + (2 : ℝ) • vecMulVec w w := by
  let z : Fin d := ⟨0, by omega⟩
  have hz : coord w 0 = w z := coordinate w 0 (by omega)
  have hD : 1 + w z ≠ 0 := by rw [← hz]; exact ne_of_gt hw
  have ht : tailSq w 1 = w z ^ 2 - 1 := by rw [hz] at hnorm; linarith
  have htail : (∑ j : Fin d, if j = z then 0 else w j ^ 2) = tailSq w 1 := by
    unfold tailSq
    apply Finset.sum_congr rfl
    intro j hj
    change (if j = z then 0 else w j ^ 2) = if 1 ≤ j.val then w j ^ 2 else 0
    by_cases hjz : j = z
    · subst j; simp [z]
    · have hj0 : j.val ≠ 0 := by intro h; apply hjz; exact Fin.ext h
      simp [hjz, show 1 ≤ j.val by omega]
  have hsym : (WquadArrow w)ᵀ = WquadArrow w := by
    ext a b
    simp only [transpose_apply, WquadArrow, of_apply]
    by_cases ha : a.val = 0 <;> by_cases hb : b.val = 0
    · have hab : a = b := Fin.ext (ha.trans hb.symm)
      subst b
      simp [ha]
    all_goals simp [ha, hb, eq_comm, mul_comm]
  have hrow (b : Fin d) (hb : b ≠ z) :
      (WquadArrow w * WquadArrow w) z b = 2 * w z * w b := by
    have hb0 : b.val ≠ 0 := by intro h; apply hb; exact Fin.ext h
    have he (j : Fin d) :
        WquadArrow w z j * WquadArrow w j b =
          (if j = z then w z * w b else 0) +
          (if j = b then w b else 0) +
          (w b / (1 + w z)) * (if j = z then 0 else w j ^ 2) := by
      by_cases hjz : j = z
      · subst j; simp [WquadArrow, z, hb0, hz, Ne.symm hb]
      · have hj0 : j.val ≠ 0 := by intro h; apply hjz; exact Fin.ext h
        simp [WquadArrow, z, hb0, hj0, hjz, hz]
        by_cases hjb : j = b <;> simp [hjb] <;> ring
    simp only [mul_apply]
    simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [htail, ht]
    field_simp
    <;> ring
  ext a b
  by_cases ha : a = z
  · subst a
    by_cases hb : b = z
    · subst b
      have he (j : Fin d) : WquadArrow w z j * WquadArrow w j z =
          (if j = z then w z ^ 2 else 0) + (if j = z then 0 else w j ^ 2) := by
        by_cases hj : j = z
        · subst j; simp [WquadArrow, z, pow_two]
        · have hj0 : j.val ≠ 0 := by intro h; apply hj; exact Fin.ext h
          simp [WquadArrow, z, hj, hj0, pow_two]
      simp only [mul_apply]
      simp_rw [he, Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [htail, ht]
      simp [ConicQuadIPM.NTScaling.Qmat, vecMulVec, z, pow_two]
      ring
    · rw [hrow b hb]
      have hb0 : b.val ≠ 0 := by intro h; apply hb; exact Fin.ext h
      simp [ConicQuadIPM.NTScaling.Qmat, vecMulVec, hb, Ne.symm hb, z]
      ring
  · by_cases hb : b = z
    · subst b
      have hm : (WquadArrow w * WquadArrow w) a z =
          (WquadArrow w * WquadArrow w) z a := by
        have hs : (WquadArrow w * WquadArrow w)ᵀ = WquadArrow w * WquadArrow w := by rw [transpose_mul, hsym]
        exact congrFun (congrFun hs z) a
      rw [hm, hrow a ha]
      simp [ConicQuadIPM.NTScaling.Qmat, vecMulVec, ha, Ne.symm ha, z]
      ring
    · have ha0 : a.val ≠ 0 := by intro h; apply ha; exact Fin.ext h
      have hb0 : b.val ≠ 0 := by intro h; apply hb; exact Fin.ext h
      have he (j : Fin d) :
          WquadArrow w a j * WquadArrow w j b =
            (if j = z then w a * w b else 0) +
            (if j = a then (if a = b then 1 else 0) + w a * w b / (1 + w z) else 0) +
            (if j = b then w a * w b / (1 + w z) else 0) +
            (w a * w b / (1 + w z)^2) * (if j = z then 0 else w j ^ 2) := by
        by_cases hjz : j = z
        · subst j; simp [WquadArrow, ha0, hb0, z, ha, hb, Ne.symm ha, Ne.symm hb]
        · have hj0 : j.val ≠ 0 := by intro h; apply hjz; exact Fin.ext h
          by_cases hja : j = a
          · subst j
            by_cases hab : a = b
            · subst b
              simp [WquadArrow, ha0, ha, hz]
              field_simp
              <;> ring
            · simp [WquadArrow, ha0, hb0, ha, hz, hab, Ne.symm hab]
              field_simp
              <;> ring
          · by_cases hjb : j = b
            · subst j
              have hab : a ≠ b := Ne.symm hja
              simp [WquadArrow, ha0, hb0, hb, hz, hab, Ne.symm hab]
              field_simp
              <;> ring
            · simp [WquadArrow, ha0, hb0, hj0, hjz, hz, hja, hjb, Ne.symm hja, Ne.symm hjb]
              field_simp
              <;> ring
      simp only [mul_apply]
      simp_rw [he, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [htail, ht]
      simp [ConicQuadIPM.NTScaling.Qmat, vecMulVec, ha0, hb0]
      split_ifs <;> field_simp <;> ring

#print axioms solution
