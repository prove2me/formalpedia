-- Prove2me | solution 1 for CalibratedCE.Forecast.flow_conservation_solvable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:31:15.661104+00:00
-- url     : https://prove2.me/submissions/56ead235-ad63-4851-929d-a84601a1a428

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist

namespace CalibratedCE.Forecast

theorem aux_fcs_kernel (k : ℕ) (hk : 0 < k) (R : Fin k → Fin k → ℝ) :
    ∃ v : Fin k → ℝ, v ≠ 0 ∧ ∀ i, v i * ∑ j, R i j = ∑ j, v j * R j i := by
  classical
  let A : Matrix (Fin k) (Fin k) ℝ := fun i j => R j i - if i = j then ∑ l, R i l else 0
  have hdet : A.det = 0 := by
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h ⟨0, hk⟩
      simp at this
    · funext j
      simp [Matrix.vecMul, dotProduct, A, Finset.sum_sub_distrib]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, fun i => ?_⟩
  have := congrFun hv i
  simp [Matrix.mulVec, dotProduct, A, sub_mul, Finset.sum_sub_distrib] at this
  have h2 : ∑ j, R j i * v j = ∑ j, v j * R j i :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  linarith

theorem aux_fcs_abs (k : ℕ) (R : Fin k → Fin k → ℝ) (hR : ∀ i j, 0 ≤ R i j) (v : Fin k → ℝ)
    (hv : ∀ i, v i * ∑ j, R i j = ∑ j, v j * R j i) :
    ∀ i, |v i| * ∑ j, R i j = ∑ j, |v j| * R j i := by
  have hle : ∀ i ∈ Finset.univ, |v i| * ∑ j, R i j ≤ ∑ j, |v j| * R j i := by
    intro i _
    have hs : 0 ≤ ∑ j, R i j := Finset.sum_nonneg (fun j _ => hR i j)
    calc |v i| * ∑ j, R i j = |v i * ∑ j, R i j| := by rw [abs_mul, abs_of_nonneg hs]
      _ = |∑ j, v j * R j i| := by rw [hv i]
      _ ≤ ∑ j, |v j * R j i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |v j| * R j i := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hR j i)]
  have heq : ∑ i, |v i| * ∑ j, R i j = ∑ i, ∑ j, |v j| * R j i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro i
  exact this i (Finset.mem_univ i)

end CalibratedCE.Forecast

open CalibratedCE.Forecast

theorem solution (k : ℕ) (hk : 0 < k) (R : Fin k → Fin k → ℝ)
    (hR : ∀ i j, 0 ≤ R i j) :
    ∃ w : Fin k → ℝ, IsDist w ∧ ∀ i, w i * ∑ j, R i j = ∑ j, w j * R j i := by
  obtain ⟨v, hv0, hv⟩ := aux_fcs_kernel k hk R
  have habs := aux_fcs_abs k R hR v hv
  set S := ∑ i, |v i| with hS
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    calc 0 < |v i| := abs_pos.mpr hi
      _ ≤ S := Finset.single_le_sum (f := fun i => |v i|) (fun j _ => abs_nonneg (v j))
          (Finset.mem_univ i)
  refine ⟨fun i => |v i| / S, ⟨fun a => div_nonneg (abs_nonneg _) hSpos.le, ?_⟩, fun i => ?_⟩
  · rw [← Finset.sum_div]; exact div_self hSpos.ne'
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [habs i]
