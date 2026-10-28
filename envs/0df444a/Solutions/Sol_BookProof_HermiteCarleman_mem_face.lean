-- Prove2me | solution 1 for BookProof.HermiteCarleman.mem_face
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:26:52.692838+00:00
-- url     : https://prove2.me/submissions/b575127d-24ff-4208-adad-46f4934b448d

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

theorem solution {d N : ℕ} {i : Fin d} {a : Fin d →₀ ℕ} :
    a ∈ face d N i ↔ (∀ j, a j ≤ N) ∧ a i = N := by
  unfold face cube
  simp only [Finset.mem_filter, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨⟨f, hf, rfl⟩, h⟩
    exact ⟨fun j => by simpa using Nat.lt_succ_iff.mp (hf j), h⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨Finsupp.equivFunOnFinite a, fun j => Nat.lt_succ_of_le (by simpa using h j), by simp⟩, h'⟩
