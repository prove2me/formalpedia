-- Prove2me | solution 1 for ConicQuadIPM.NewtonStep.eq_61
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T03:50:38.845107+00:00
-- url     : https://prove2.me/submissions/d24e3267-9beb-4552-bbb3-24ebd8971ca7

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

open Matrix ConicQuadIPM.Complementarity

private lemma first_dot {d : ℕ} (v : Fin (d + 1) → ℝ) : e1 ⬝ᵥ v = v 0 := by
  simp [e1, dotProduct, Fin.sum_univ_succ]

private lemma arrow_first {d : ℕ} (v w : Fin d → ℝ) :
    e1 ⬝ᵥ (arrow v *ᵥ w) = v ⬝ᵥ w := by
  cases d with
  | zero => simp [dotProduct]
  | succ d =>
      rw [first_dot]
      simp [mulVec, dotProduct, arrow]

private lemma arrow_unit {d : ℕ} (v : Fin d → ℝ) : arrow v *ᵥ e1 = v := by
  cases d with
  | zero => ext i; exact Fin.elim0 i
  | succ d =>
      ext i
      by_cases hi : i = 0
      · subst i
        simp [mulVec, dotProduct, arrow, e1, Fin.sum_univ_succ]
      · have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [mulVec, dotProduct, arrow, e1, Fin.sum_univ_succ, hiv]

private lemma arrow_product {d : ℕ} (v w : Fin d → ℝ) :
    e1 ⬝ᵥ ((arrow v * arrow w) *ᵥ e1) = v ⬝ᵥ w := by
  rw [← mulVec_mulVec, arrow_unit, arrow_first]

private lemma rot_zero (d : ℕ) (v : Fin (d + 2) → ℝ) :
    (Tmat .rot (d + 2) *ᵥ v) 0 =
      (1 / Real.sqrt 2) * v 0 + (1 / Real.sqrt 2) * v (Fin.succ 0) := by
  have hz (i : Fin d) : (0 : Fin (d + 2)) ≠ i.succ.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_succ] at hv
    omega
  simp [mulVec, dotProduct, Tmat, Fin.sum_univ_succ, hz]

private lemma rot_one (d : ℕ) (v : Fin (d + 2) → ℝ) :
    (Tmat .rot (d + 2) *ᵥ v) (Fin.succ 0) =
      (1 / Real.sqrt 2) * v 0 - (1 / Real.sqrt 2) * v (Fin.succ 0) := by
  have h1 (i : Fin d) : (1 : Fin (d + 2)) ≠ i.succ.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_one, Fin.val_succ] at hv
    omega
  simp [mulVec, dotProduct, Tmat, Fin.sum_univ_succ, sub_eq_add_neg, h1]

private lemma rot_tail (d : ℕ) (v : Fin (d + 2) → ℝ) (i : Fin d) :
    (Tmat .rot (d + 2) *ᵥ v) i.succ.succ = v i.succ.succ := by
  simp [mulVec, dotProduct, Tmat, ite_mul]

private lemma rot_dot {d : ℕ} (hd : 2 ≤ d) (v w : Fin d → ℝ) :
    (Tmat .rot d *ᵥ v) ⬝ᵥ (Tmat .rot d *ᵥ w) = v ⬝ᵥ w := by
  obtain ⟨q, rfl⟩ : ∃ q, d = q + 2 := ⟨d - 2, by omega⟩
  have hscale : 2 * (1 / Real.sqrt 2) ^ 2 = (1 : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [dotProduct, Fin.sum_univ_succ, rot_zero, rot_one, rot_tail]
  linear_combination (v 0 * w 0 + v (Fin.succ 0) * w (Fin.succ 0)) * hscale

private lemma transformed_dot {d : ℕ} (c : ConeKind) (hwf : BlockWF c d)
    (v w : Fin d → ℝ) : (Tmat c d *ᵥ v) ⬝ᵥ (Tmat c d *ᵥ w) = v ⬝ᵥ w := by
  cases c with
  | nonneg => simp [Tmat]
  | quad => simp [Tmat]
  | rot => exact rot_dot (hwf.2.2 rfl) v w

theorem solution
    {k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (x s : (i : Fin k) → Fin (n i) → ℝ) :
    (∑ i, ConicQuadIPM.Complementarity.e1 ⬝ᵥ ((ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) * ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i))
        *ᵥ ConicQuadIPM.Complementarity.e1))
      = ∑ i, (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i) ∧
    (∑ i, (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i))
      = ∑ i, x i ⬝ᵥ s i := by
  constructor
  · exact Finset.sum_congr rfl fun i hi => arrow_product _ _
  · exact Finset.sum_congr rfl fun i hi => transformed_dot (kind i) (hwf i) _ _

#print axioms solution
