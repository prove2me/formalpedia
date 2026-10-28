-- Prove2me | solution 1 for BookProof.HermiteCarleman.sum_cube_split
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:27:11.186407+00:00
-- url     : https://prove2.me/submissions/a3056292-f7fa-408e-9c52-3712f4625b28

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterHermiteCarlemanEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
open BookProof.HermiteCarleman



open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

theorem solution (d N : ℕ) (i : Fin d) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ cube d N, F a = ∑ a ∈ inn d N i, F a + ∑ a ∈ face d N i, F a := by
  classical
  have h1 : face d N i = (cube d N).filter (fun a => ¬ a i < N) := by
    unfold face
    apply Finset.filter_congr
    intro a ha
    have : a i ≤ N := by
      unfold cube at ha
      simp only [Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range] at ha
      obtain ⟨f, hf, rfl⟩ := ha
      simpa using Nat.lt_succ_iff.mp (hf i)
    omega
  rw [h1, inn, Finset.sum_filter_add_sum_filter_not]
