-- Prove2me | solution 1 for BookProof.ModeQuadratic.lop_lop_hermiteMv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T14:00:46.930008+00:00
-- url     : https://prove2.me/submissions/07cae28c-6985-49c7-b3e0-4c79d6ae4e12

-- Generated from ChapterModeQuadraticEsa.lean — solution of BookProof.ModeQuadratic.lop_lop_hermiteMv
import Mathlib
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Theorems.Thm_BookProof_ModeQuadratic_add_single_one_one
import Theorems.Thm_BookProof_ModeQuadratic_sub_single_one_one
import Theorems.Thm_BookProof_ModeQuadratic_add_single_apply_self
import Theorems.Thm_BookProof_ModeQuadratic_sub_single_apply_self
import Theorems.Thm_BookProof_ModeQuadratic_lop_hermiteMv
import Theorems.Thm_BookProof_CarlemanTwoStep_sub_add_singleK
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterHermiteProductCore
open BookProof.ModeQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (t t' : ℂ) (i : Fin d) (a : Fin d →₀ ℕ) :
    lop t i (lop t' i (hermiteMv a))
      = hermiteMv (a + Finsupp.single i 2)
        + (t * ((a i : ℂ) + 1) + t' * (a i : ℂ)) • hermiteMv a
        + (t * t' * (a i : ℂ) * (((a i - 1 : ℕ) : ℂ))) • hermiteMv (a - Finsupp.single i 2) := by

  rw [lop_hermiteMv t' i a, map_add, map_smul, lop_hermiteMv t i (a + Finsupp.single i 1),
    add_single_one_one, add_single_apply_self, add_tsub_cancel_right]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hpos
  · rw [h0]
    simp
  · rw [lop_hermiteMv t i (a - Finsupp.single i 1), sub_single_one_one,
      sub_single_apply_self, sub_add_singleK (by omega : 1 ≤ a i)]
    push_cast [Nat.cast_sub hpos]
    module
