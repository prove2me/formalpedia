-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.blockPoly_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:39.243192+00:00
-- url     : https://prove2.me/submissions/1c24b872-df02-4eea-91e4-e159d1d3ac35

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {A : Type*} [CommRing A] {d S : Type*} [Fintype d] [DecidableEq d] [Fintype S]
    [DecidableEq S] (U : Matrix d S A) (W : Matrix S d A) (hWU : W * U = 1) (B : Matrix S S A) :
    blockPoly (U * W) (U * B * W) = B.charpoly := by
  classical
  have hWU' : W.map (Polynomial.C : A →+* Polynomial A) * U.map Polynomial.C = 1 := by
    simpa [Matrix.map_mul] using congrArg (fun M => M.map (Polynomial.C : A →+* Polynomial A)) hWU
  have key : (Polynomial.X : Polynomial A) • (U * W).map Polynomial.C - (U * B * W).map Polynomial.C +
      (1 - U * W).map Polynomial.C =
      1 + U.map Polynomial.C * (((Polynomial.X : Polynomial A) • 1 - B.map Polynomial.C - 1) *
        W.map Polynomial.C) := by
    have h1 : (1 - U * W).map (Polynomial.C : A →+* Polynomial A) = 1 - U.map Polynomial.C * W.map Polynomial.C := by
      have := map_sub (Polynomial.C : A →+* Polynomial A).mapMatrix 1 (U * W)
      rwa [map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_mul] at this
    rw [h1, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_assoc]
    abel
  unfold blockPoly
  rw [key, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hWU', Matrix.mul_one]
  unfold Matrix.charpoly
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.charmatrix_apply, Matrix.one_apply]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
