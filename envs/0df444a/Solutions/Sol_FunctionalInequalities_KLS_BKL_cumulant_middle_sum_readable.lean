-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.cumulant_middle_sum_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:30:30.314995+00:00
-- url     : https://prove2.me/submissions/fc64a0b2-bf45-4952-b3d9-575a92105a5f

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_NoiseBound

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}
 lemma solution
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => EuclideanSpace ℝ (Fin n)) ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) (v : Fin n → ℝ)
    (b : Fin n → EuclideanSpace ℝ (Fin n))
    (w : EuclideanSpace ℝ (Fin n))
    (hw : w = ∑ j, v j • b j) :
    ∑ j, T ![x, b j, z] * v j = T ![x, w, z] := by
  classical
  let m : Fin 3 → EuclideanSpace ℝ (Fin n) := ![x, 0, z]
  have hm :
      Function.update m 1 (∑ j, v j • b j) = ![x, ∑ j, v j • b j, z] := by
    funext i
    fin_cases i <;> simp [m]
  have hsum :
      T ![x, ∑ j, v j • b j, z] =
        ∑ j, T ![x, v j • b j, z] := by
    have h :=
      (T.toMultilinearMap).map_update_sum Finset.univ 1
        (fun j => v j • b j) m
    calc
      T ![x, ∑ j, v j • b j, z] =
          T (Function.update m 1 (∑ j, v j • b j)) := by rw [hm]
      _ = ∑ j, T (Function.update m 1 (v j • b j)) := h
      _ = ∑ j, T ![x, v j • b j, z] := by
        apply Finset.sum_congr rfl
        intro j _
        have hj :
            Function.update m 1 (v j • b j) = ![x, v j • b j, z] := by
          funext i
          fin_cases i <;> simp [m]
        rw [hj]
  calc
    ∑ j, T ![x, b j, z] * v j =
        ∑ j, v j * T ![x, b j, z] := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j, T ![x, v j • b j, z] := by
      apply Finset.sum_congr rfl
      intro j _
      have hj :
          Function.update m 1 (b j) = ![x, b j, z] := by
        funext i
        fin_cases i <;> simp [m]
      have hj' :
          Function.update m 1 (v j • b j) = ![x, v j • b j, z] := by
        funext i
        fin_cases i <;> simp [m]
      have hsmul :=
        (T.toMultilinearMap).map_update_smul m 1 (v j) (b j)
      calc
        v j * T ![x, b j, z] =
            v j • T ![x, b j, z] := by simp [smul_eq_mul]
        _ = v j • T (Function.update m 1 (b j)) := by rw [hj]
        _ = T (Function.update m 1 (v j • b j)) := hsmul.symm
        _ = T ![x, v j • b j, z] := by rw [hj']

    _ = T ![x, w, z] := by
      rw [hw]
      exact hsum.symm
