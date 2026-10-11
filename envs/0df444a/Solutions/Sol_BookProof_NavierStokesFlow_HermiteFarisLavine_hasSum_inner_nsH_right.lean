-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:38.896692+00:00
-- url     : https://prove2.me/submissions/6b120a97-209d-4002-b503-5fce153ef703
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.hasSum_inner_nsH_right
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_crossA
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_summable_crossB
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_conj_mul_hFun
import Theorems.Thm_BookProof_NavierStokesFlow_HermiteFarisLavine_nsH_coe
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_summable_normSq
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato
open BookProof.ChapterContinuityUnitaryInfinite

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) (x y : maxDom (oscSymbol κ)) :
    HasSum (fun n => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n
        + Complex.I * crossB κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) n)
      (inner ℂ (x : L2I ℕ) (nsH κ hκ y : L2I ℕ)) := by

  have hA := summable_crossA (Y := ((y : L2I ℕ) : ℕ → ℂ)) hκ (summable_ampSeq_sq hκ x)
    (summable_normSq (y : L2I ℕ))
  have hB := summable_crossB (Y := ((y : L2I ℕ) : ℕ → ℂ)) hκ (summable_ampSeq_sq hκ x)
    (summable_normSq (y : L2I ℕ))
  have hgoal := (hA.hasSum.mul_left (-Complex.I)).add (hB.hasSum.mul_left Complex.I)
  have hshift := (hA.hasSum.mul_left (-Complex.I)).add
    ((hasSum_shift2_iff.mpr hB.hasSum).mul_left Complex.I)
  have hinner := lp.hasSum_inner (𝕜 := ℂ) ((x : L2I ℕ)) ((nsH κ hκ y : L2I ℕ))
  have heq : (fun m => (inner ℂ (((x : L2I ℕ) : ℕ → ℂ) m)
        (((nsH κ hκ y : L2I ℕ) : ℕ → ℂ) m) : ℂ))
      = fun m => -Complex.I * crossA κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ)) m
          + Complex.I * shift2 (crossB κ ((x : L2I ℕ) : ℕ → ℂ) (((y : L2I ℕ) : ℕ → ℂ))) m := by
    funext m
    rw [RCLike.inner_apply, nsH_coe, mul_comm]
    exact conj_mul_hFun κ _ _ m
  rw [heq] at hinner
  rwa [hshift.unique hinner] at hgoal
