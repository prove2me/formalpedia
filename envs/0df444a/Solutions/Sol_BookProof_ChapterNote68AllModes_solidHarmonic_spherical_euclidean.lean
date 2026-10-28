-- Prove2me | solution 1 for BookProof.ChapterNote68AllModes.solidHarmonic_spherical_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:37:45.583841+00:00
-- url     : https://prove2.me/submissions/9e3b6df8-2820-434c-b10b-555080d91f0e

import Definitions.Def_ChapterSphericalBessel
import Definitions.Def_ChapterBesselHarmonic
import Definitions.Def_ChapterSolidHarmonic
import Mathlib
import Theorems.Thm_BookProof_ChapterSolidHarmonic_solidHarmonic_spherical_inc
import Theorems.Thm_BookProof_ChapterNote68AllModes_inner_stdVec
import Theorems.Thm_BookProof_ChapterNote68AllModes_norm_stdVec
import Definitions.Def_ChapterNote68AllModes
open BookProof.ChapterNote68AllModes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]



open Laplacian InnerProductSpace Polynomial
open BookProof.ChapterSphericalBessel BookProof.ChapterBesselHarmonic
open BookProof.ChapterSolidHarmonic
open scoped RealInnerProductSpace

theorem solution {l μ : ℕ} (hμ : μ ≤ l) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : 0 ≤ Real.sin θ) (φ : ℝ) :
    solidHarmonic (stdVec 0) (stdVec 1) (stdVec 2) l μ
        (spherePt (stdVec 0) (stdVec 1) (stdVec 2) r θ φ)
      = r ^ l * assocLegendre l μ (Real.cos θ) * Real.cos (μ * φ) :=
  BookProof.ChapterSolidHarmonic.solidHarmonic_spherical_inc
    (BookProof.ChapterNote68AllModes.norm_stdVec 0) (BookProof.ChapterNote68AllModes.norm_stdVec 1)
    (BookProof.ChapterNote68AllModes.norm_stdVec 2)
    (BookProof.ChapterNote68AllModes.inner_stdVec (by decide))
    (BookProof.ChapterNote68AllModes.inner_stdVec (by decide))
    (BookProof.ChapterNote68AllModes.inner_stdVec (by decide)) hμ hr hθ φ
