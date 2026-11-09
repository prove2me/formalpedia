-- Prove2me | solution 1 for BookProof.FullQuadratic.shiftm_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T18:09:58.805897+00:00
-- url     : https://prove2.me/submissions/505bb252-be17-4da4-9aea-9fc9794b01da

-- Generated from ChapterFullQuadraticEsa.lean — solution of BookProof.FullQuadratic.shiftm_self_eq
import Mathlib
import Definitions.Def_ChapterFullQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterCarlemanTwoStepPromoted
import Definitions.Def_ChapterCarlemanSimplexPromoted
import Definitions.Def_ChapterModeQuadraticEsaPromoted
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.FullQuadratic




open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {a : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ a i) : shiftm a i i = a := by

  -- `tsub_add_cancel_of_le'` is a CarlemanSimplex *problem node* (Open), so it
  -- cannot be imported; the cancellation is two lines, inline it.
  have hcancel : ∀ {P : Fin d →₀ ℕ}, P ≤ a → a - P + P = a := by
    intro P hP
    ext k
    have hk : P k ≤ a k := (Finsupp.le_def.mp hP) k
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega
  have hle : Finsupp.single i 1 ≤ a := by
    rw [Finsupp.le_def]
    intro k
    by_cases hk : k = i
    · subst hk; simpa using h
    · simp [Ne.symm hk]
  rw [shiftm, hcancel hle]
