-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lower_triangular_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:38.806348+00:00
-- url     : https://prove2.me/submissions/b424fe34-3bbb-4072-a22c-77f959c56605

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InverseSplitting
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseSplitting_inv_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_conj_mul_eq_mul_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_conj_inv_eq_inv_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P
namespace InverseSplitting
open C2x2
variable {m : ℕ}
end InverseSplitting
open C2x2 InverseSplitting
private lemma mul_mem_ltset {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.LTset m)
    (hB : B ∈ C2.LTset m) : A * B ∈ C2.LTset m := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : i < k
    · rw [hA.1 i k hik, zero_mul]
    · rw [hB.1 k j (lt_of_le_of_lt (not_lt.1 hik) h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hB.1 k i h, mul_zero]
      · rw [hA.1 i k h, zero_mul]
    · simp
private lemma mul_mem_utset {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m)
    (hB : B ∈ C2.UTset m) : A * B ∈ C2.UTset m := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hki : k < i
    · rw [hA.1 i k hki, zero_mul]
    · rw [hB.1 k j (lt_of_lt_of_le h (not_lt.1 hki)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]
    · simp
private lemma det_eq_one_of_mem_ltset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.LTset m) :
    A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular A (fun i j h => hA.1 i j h)]
  simp [hA.2]
private lemma det_eq_one_of_mem_utset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) :
    A.det = 1 := by
  rw [Matrix.det_of_upperTriangular (fun i j h => hA.1 i j h)]
  simp [hA.2]
private lemma inv_mem_ltset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.LTset m) :
    A⁻¹ ∈ C2.LTset m := by
  have hbt : A.BlockTriangular OrderDual.toDual := fun i j h => hA.1 i j h
  have hdet : IsUnit A.det := by rw [det_eq_one_of_mem_ltset hA]; exact isUnit_one
  haveI := A.invertibleOfIsUnitDet hdet
  have hbi := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j h => hbi h, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2 i, one_mul] at h1
  · simpa using h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hbi h, mul_zero]
    · rw [hA.1 i k h, zero_mul]
  · simp
private lemma inv_mem_utset {m : ℕ} {A : Matrix (Fin m) (Fin m) ℂ} (hA : A ∈ C2.UTset m) :
    A⁻¹ ∈ C2.UTset m := by
  have hbt : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hdet : IsUnit A.det := by rw [det_eq_one_of_mem_utset hA]; exact isUnit_one
  haveI := A.invertibleOfIsUnitDet hdet
  have hbi := Matrix.blockTriangular_inv_of_blockTriangular hbt
  refine ⟨fun i j h => hbi h, fun i => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2 i, one_mul] at h1
  · simpa using h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hA.1 i k h, zero_mul]
    · rw [hbi h, mul_zero]
  · simp
end Formalism.FourierDecayAlt.P
end

set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2 InverseSplitting
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.LowSplit := by
  intro m P hP l hl
  obtain ⟨w, d, hd, rfl⟩ := hP
  set Q : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a i => if i = w a then (d a)⁻¹ else 0 with hQ
  have hQP : Q * C2.monoP w d = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [hQ, C2.monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hab : a = b
    · subst hab
      simp [hd a]
    · simp [Matrix.one_apply_ne hab, w.injective.ne hab, Ne.symm hab]
  have hPinv : (C2.monoP w d)⁻¹ = Q := Matrix.inv_eq_left_inv hQP
  have hPdet : IsUnit (C2.monoP w d).det := Matrix.isUnit_det_of_left_inverse hQP
  have hconj : ∀ (X : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m),
      ((C2.monoP w d)⁻¹ * X * C2.monoP w d) a b = (d a)⁻¹ * X (w a) (w b) * d b := by
    intro X a b
    rw [hPinv, Matrix.mul_apply]
    simp only [Matrix.mul_apply, hQ, C2.monoP, Matrix.of_apply, ite_mul, zero_mul, mul_ite,
      mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have I := inv_step w l hl m
  set A := (lsStep w l m).1 with hAdef
  set B := (lsStep w l m).2 with hBdef
  have hAB : l = A * B := by
    ext i j
    exact (I.prod i j (by omega)).symm
  have hAL : A ∈ C2.LTset m := ⟨fun i j h => (I.up i j h).1, fun i => (I.diag i).1⟩
  have hBL : B ∈ C2.LTset m := ⟨fun i j h => (I.up i j h).2, fun i => (I.diag i).2⟩
  have hAc : (C2.monoP w d)⁻¹ * A * C2.monoP w d ∈ C2.LTset m := by
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [hconj]
      rcases lt_trichotomy (w a) (w b) with h | h | h
      · rw [(I.up _ _ h).1]
        simp
      · exact absurd (w.injective h) (ne_of_lt hab)
      · rw [I.supA _ _ h (by simpa using (not_lt.2 hab.le))]
        simp
    · rw [hconj, (I.diag (w a)).1]
      field_simp [hd a]
  have hBc : (C2.monoP w d)⁻¹ * B * C2.monoP w d ∈ C2.UTset m := by
    refine ⟨fun a b hba => ?_, fun a => ?_⟩
    · rw [hconj]
      rcases lt_trichotomy (w a) (w b) with h | h | h
      · rw [(I.up _ _ h).2]
        simp
      · exact absurd (w.injective h) (ne_of_lt hba).symm
      · rw [I.supB _ _ h (by simpa using hba)]
        simp
    · rw [hconj, (I.diag (w a)).2]
      field_simp [hd a]
  refine ⟨(A, B), ⟨⟨hAL, hAc⟩, ⟨hBL, hBc⟩, hAB⟩, ?_⟩
  rintro ⟨A2, B2⟩ ⟨hA2, hB2, hl2⟩
  have hl2' : l = A2 * B2 := hl2
  have hAdet : IsUnit A.det := by rw [det_eq_one_of_mem_ltset hAL]; exact isUnit_one
  have hB2det : IsUnit B2.det := by rw [det_eq_one_of_mem_ltset hB2.1]; exact isUnit_one
  have hkey : A⁻¹ * A2 = B * B2⁻¹ := by
    calc A⁻¹ * A2 = A⁻¹ * A2 * (B2 * B2⁻¹) := by
          rw [Matrix.mul_nonsing_inv B2 hB2det, Matrix.mul_one]
      _ = A⁻¹ * (A2 * B2) * B2⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * B) * B2⁻¹ := by rw [← hl2', ← hAB]
      _ = B * B2⁻¹ := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hAdet, Matrix.one_mul]
  have hYL : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d ∈ C2.LTset m := by
    rw [conj_mul_eq_mul_conj _ _ _ hPdet, ← conj_inv_eq_inv_conj _ _ hPdet]
    exact mul_mem_ltset (inv_mem_ltset hAc) hA2.2
  have hYU : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d ∈ C2.UTset m := by
    rw [hkey, conj_mul_eq_mul_conj _ _ _ hPdet, ← conj_inv_eq_inv_conj _ _ hPdet]
    exact mul_mem_utset hBc (inv_mem_utset hB2.2)
  have hY : (C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d = 1 := by
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hYL.1 i j h, Matrix.one_apply_ne (ne_of_lt h)]
    · subst h
      rw [hYL.2 i, Matrix.one_apply_eq]
    · rw [hYU.1 i j h, Matrix.one_apply_ne (ne_of_lt h).symm]
  have hZ : A⁻¹ * A2 = 1 := by
    calc A⁻¹ * A2 = C2.monoP w d * ((C2.monoP w d)⁻¹ * (A⁻¹ * A2) * C2.monoP w d) *
          (C2.monoP w d)⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPdet, Matrix.mul_one,
            Matrix.mul_nonsing_inv_cancel_left _ _ hPdet]
      _ = 1 := by rw [hY, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPdet]
  have hA2A : A2 = A := by
    calc A2 = A * (A⁻¹ * A2) := (Matrix.mul_nonsing_inv_cancel_left A A2 hAdet).symm
      _ = A := by rw [hZ, Matrix.mul_one]
  have hB2B : B2 = B := by
    calc B2 = A⁻¹ * (A * B2) := (Matrix.nonsing_inv_mul_cancel_left A B2 hAdet).symm
      _ = A⁻¹ * (A * B) := by rw [← hA2A, ← hl2', hAB, hA2A]
      _ = B := Matrix.nonsing_inv_mul_cancel_left A B hAdet
  rw [hA2A, hB2B]
end Formalism.FourierDecayAlt.P
