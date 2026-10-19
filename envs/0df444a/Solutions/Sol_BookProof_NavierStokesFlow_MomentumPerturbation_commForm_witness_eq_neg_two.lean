-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T05:57:27.009934+00:00
-- url     : https://prove2.me/submissions/ecd45465-5050-471b-9ac5-16f0194b41c1

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFockManyMode
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_testState_mem_maxDom
-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.commForm_witness_eq_neg_two
open BookProof.NavierStokesFlow.FockManyMode
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}


theorem solution :
    commForm (pertHam linSymbol (eState 0) (eState 1)) (diagMax linSymbol)
      ⟨testState, testState_mem_maxDom⟩ = -2 := by
  set x : maxDom linSymbol := ⟨testState, testState_mem_maxDom⟩
  have hx : ((x : maxDom linSymbol) : L2I ℕ) = lp.single 2 0 (1 : ℂ) + lp.single 2 1 Complex.I := rfl
  have hN : ((diagMax linSymbol x) : L2I ℕ) = lp.single 2 0 (1 : ℂ) + lp.single 2 1 (2 * Complex.I) := by
    refine lp.ext (funext fun m => ?_)
    rw [diagMax_coe, hx]
    simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply, linSymbol]
    rcases m with _ | _ | m <;> simp
    ring
  have h0 : (inner ℂ (eState 0) ((x : maxDom linSymbol) : L2I ℕ) : ℂ) = 1 := by
    rw [hx, eState, inner_add_right, lp.inner_single_left, lp.inner_single_left]; simp
  have h1 : (inner ℂ (eState 1) ((x : maxDom linSymbol) : L2I ℕ) : ℂ) = Complex.I := by
    rw [hx, eState, inner_add_right, lp.inner_single_left, lp.inner_single_left]; simp
  have hH : ((pertHam linSymbol (eState 0) (eState 1) x) : L2I ℕ)
      = lp.single 2 0 (1 + Complex.I) + lp.single 2 1 (1 + 2 * Complex.I) := by
    have e : pertHam linSymbol (eState 0) (eState 1) x
        = diagMax linSymbol x + rankTwo (eState 0) (eState 1) (x : L2I ℕ) := rfl
    rw [e, hN]
    change _ + ((inner ℂ (eState 0) ((x : maxDom linSymbol) : L2I ℕ) : ℂ) • eState 1
      + (inner ℂ (eState 1) ((x : maxDom linSymbol) : L2I ℕ) : ℂ) • eState 0) = _
    rw [h0, h1]
    refine lp.ext (funext fun m => ?_)
    simp only [eState, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, lp.single_apply,
      Pi.single_apply, smul_eq_mul]
    rcases m with _ | _ | m <;> simp <;> ring
  unfold commForm
  rw [hH, hN]
  simp only [inner_add_left, inner_add_right, lp.inner_single_left, lp.single_apply, Pi.single_apply]
  simp [Complex.mul_re, Complex.mul_im]
  norm_num

