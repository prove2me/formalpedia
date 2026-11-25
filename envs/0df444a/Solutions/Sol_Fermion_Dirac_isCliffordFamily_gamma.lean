-- Prove2me | solution 1 for Fermion.Dirac.isCliffordFamily_gamma
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:31:47.203801+00:00
-- url     : https://prove2.me/submissions/305f0973-38f5-465b-a206-05e46d2a8e79

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily
import Definitions.Def_FermionDirac_gamma

open Matrix Complex Fermion.Dirac

lemma gamma_rel_0_0 : gamma (Sum.inl 0) * gamma (Sum.inl 0) + gamma (Sum.inl 0) * gamma (Sum.inl 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inl 0) (Sum.inl 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_0_1 : gamma (Sum.inl 0) * gamma (Sum.inr 0) + gamma (Sum.inr 0) * gamma (Sum.inl 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inl 0) (Sum.inr 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_0_2 : gamma (Sum.inl 0) * gamma (Sum.inr 1) + gamma (Sum.inr 1) * gamma (Sum.inl 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inl 0) (Sum.inr 1) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_0_3 : gamma (Sum.inl 0) * gamma (Sum.inr 2) + gamma (Sum.inr 2) * gamma (Sum.inl 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inl 0) (Sum.inr 2) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_1_0 : gamma (Sum.inr 0) * gamma (Sum.inl 0) + gamma (Sum.inl 0) * gamma (Sum.inr 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 0) (Sum.inl 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_1_1 : gamma (Sum.inr 0) * gamma (Sum.inr 0) + gamma (Sum.inr 0) * gamma (Sum.inr 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 0) (Sum.inr 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_1_2 : gamma (Sum.inr 0) * gamma (Sum.inr 1) + gamma (Sum.inr 1) * gamma (Sum.inr 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 0) (Sum.inr 1) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_1_3 : gamma (Sum.inr 0) * gamma (Sum.inr 2) + gamma (Sum.inr 2) * gamma (Sum.inr 0) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 0) (Sum.inr 2) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_2_0 : gamma (Sum.inr 1) * gamma (Sum.inl 0) + gamma (Sum.inl 0) * gamma (Sum.inr 1) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 1) (Sum.inl 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_2_1 : gamma (Sum.inr 1) * gamma (Sum.inr 0) + gamma (Sum.inr 0) * gamma (Sum.inr 1) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 1) (Sum.inr 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_2_2 : gamma (Sum.inr 1) * gamma (Sum.inr 1) + gamma (Sum.inr 1) * gamma (Sum.inr 1) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 1) (Sum.inr 1) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_2_3 : gamma (Sum.inr 1) * gamma (Sum.inr 2) + gamma (Sum.inr 2) * gamma (Sum.inr 1) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 1) (Sum.inr 2) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_3_0 : gamma (Sum.inr 2) * gamma (Sum.inl 0) + gamma (Sum.inl 0) * gamma (Sum.inr 2) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 2) (Sum.inl 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_3_1 : gamma (Sum.inr 2) * gamma (Sum.inr 0) + gamma (Sum.inr 0) * gamma (Sum.inr 2) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 2) (Sum.inr 0) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_3_2 : gamma (Sum.inr 2) * gamma (Sum.inr 1) + gamma (Sum.inr 1) * gamma (Sum.inr 2) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 2) (Sum.inr 1) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

lemma gamma_rel_3_3 : gamma (Sum.inr 2) * gamma (Sum.inr 2) + gamma (Sum.inr 2) * gamma (Sum.inr 2) =
    (2 * (minkowskiMatrix (d := 3) (Sum.inr 2) (Sum.inr 2) : ℂ)) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal] <;> ring_nf

theorem solution : IsCliffordFamily gamma := fun μ ν =>
  match μ, ν with
  | Sum.inl 0, Sum.inl 0 => gamma_rel_0_0
  | Sum.inl 0, Sum.inr 0 => gamma_rel_0_1
  | Sum.inl 0, Sum.inr 1 => gamma_rel_0_2
  | Sum.inl 0, Sum.inr 2 => gamma_rel_0_3
  | Sum.inr 0, Sum.inl 0 => gamma_rel_1_0
  | Sum.inr 0, Sum.inr 0 => gamma_rel_1_1
  | Sum.inr 0, Sum.inr 1 => gamma_rel_1_2
  | Sum.inr 0, Sum.inr 2 => gamma_rel_1_3
  | Sum.inr 1, Sum.inl 0 => gamma_rel_2_0
  | Sum.inr 1, Sum.inr 0 => gamma_rel_2_1
  | Sum.inr 1, Sum.inr 1 => gamma_rel_2_2
  | Sum.inr 1, Sum.inr 2 => gamma_rel_2_3
  | Sum.inr 2, Sum.inl 0 => gamma_rel_3_0
  | Sum.inr 2, Sum.inr 0 => gamma_rel_3_1
  | Sum.inr 2, Sum.inr 1 => gamma_rel_3_2
  | Sum.inr 2, Sum.inr 2 => gamma_rel_3_3
