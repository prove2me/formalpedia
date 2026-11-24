-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.rank_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:54:48.280862+00:00
-- url     : https://prove2.me/submissions/05cd108c-9994-4631-927a-f321ee7b57f2

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightShiftProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
private lemma matrix_rank_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ Module.finrank ℂ ((LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :
          Submodule ℂ (Fin n → ℂ))) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : RankLeTwiceMin := by
  intro N sg X hX
  classical
  set Dp : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => if sg a = true then 1 else 0) with hDp
  set Dm : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun a => if sg a = false then 1 else 0) with hDm
  have hrp : Dp.rank = (univ.filter (fun a => sg a = true)).card := by
    rw [hDp, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have hrm : Dm.rank = (univ.filter (fun a => sg a = false)).card := by
    rw [hDm, Matrix.rank_diagonal, Fintype.card_subtype]
    congr 1
    ext a
    simp
  have hdec : X = Dp * X * Dm + Dm * X * Dp := by
    ext a b
    rw [Matrix.add_apply, hDp, hDm, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
      Matrix.diagonal_mul]
    by_cases hs : sg a = sg b
    · rw [hX a b hs]; simp
    · cases ha : sg a <;> cases hb : sg b <;> simp_all
  have h1 : (Dp * X * Dm).rank ≤ min Dp.rank Dm.rank := by
    refine le_min ?_ (Matrix.rank_mul_le_right _ _)
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  have h2 : (Dm * X * Dp).rank ≤ min Dp.rank Dm.rank := by
    refine le_min (Matrix.rank_mul_le_right _ _) ?_
    rw [Matrix.mul_assoc]
    exact Matrix.rank_mul_le_left _ _
  calc X.rank = (Dp * X * Dm + Dm * X * Dp).rank := by rw [← hdec]
    _ ≤ (Dp * X * Dm).rank + (Dm * X * Dp).rank := matrix_rank_add_le _ _
    _ ≤ _ := by rw [hrp, hrm] at h1 h2; omega
end Formalism.HermitianLattices.GenusMassVolumes
