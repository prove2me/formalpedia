-- Prove2me | solution 2 for BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_testState
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:54:47.073686+00:00
-- url     : https://prove2.me/submissions/4a110159-a6c1-4298-a0d3-df63302ca8f5

import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — theorem BookProof.NavierStokesFlow.HermiteFarisLavine.commForm_testState
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine


open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}


theorem solution (hκ : 0 ≤ κ) :
    commForm (nsH κ hκ) (diagMax (oscSymbol κ)) (testState κ) = 8 * κ * amp κ 0 := by
  set a0 : ℂ := (amp κ 0 : ℂ)
  set a2 : ℂ := (amp κ 2 : ℂ)
  have hT : ((testState κ : maxDom (oscSymbol κ)) : L2I ℕ) = lp.single 2 0 (1 : ℂ) + lp.single 2 2 1 := rfl
  have hH : ((nsH κ hκ (testState κ)) : L2I ℕ)
      = lp.single 2 2 (Complex.I * a0) + lp.single 2 4 (Complex.I * a2)
        - lp.single 2 0 (Complex.I * a0) := by
    refine lp.ext (funext fun m => ?_)
    change hFun κ (((testState κ : maxDom (oscSymbol κ)) : L2I ℕ) : ℕ → ℂ) m = _
    rw [hT]
    simp only [hFun, shift2, lp.coeFn_add, lp.coeFn_sub, Pi.add_apply, Pi.sub_apply, lp.single_apply,
      Pi.single_apply]
    rcases m with _ | _ | _ | _ | _ | m <;> simp [a0, a2] <;> ring
  have hN : ((diagMax (oscSymbol κ) (testState κ)) : L2I ℕ)
      = lp.single 2 0 ((oscSymbol κ 0 : ℝ) : ℂ) + lp.single 2 2 ((oscSymbol κ 2 : ℝ) : ℂ) := by
    refine lp.ext (funext fun m => ?_)
    rw [diagMax_coe, hT]
    simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply]
    rcases m with _ | _ | _ | m <;> simp
  unfold commForm
  rw [hH, hN]
  simp only [inner_add_left, inner_sub_left, inner_add_right, lp.inner_single_left,
    lp.single_apply, Pi.single_apply]
  simp [a0, a2, oscSymbol, Complex.mul_re, Complex.mul_im]
  ring

