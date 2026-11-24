-- Prove2me | solution 1 for Formalism.HN.htImage_map_realize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:14.192227+00:00
-- url     : https://prove2.me/submissions/58730dbd-a035-4654-b004-33dad246f483

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
import Theorems.Thm_Formalism_HN_htImageCv_ext
import Theorems.Thm_Formalism_HN_htImageCv_map
import Theorems.Thm_Formalism_HN_htImageCv_realize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
variable {K : Type*} [Field K] [NumberField K] [StarRing K]
  {V ι : Type*} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type*} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]
namespace Formalism.HN
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] W) (x : V) :
    htImageMap (htImageMat b X b' X' φ) (Formalism.HermitianLatticesTheory.realize b X x) =
      Formalism.HermitianLatticesTheory.realize b' X' (φ x) := by
  apply htImageCv_ext
  intro v
  rw [htImageCv_map, htImageCv_realize, htImageCv_realize]
  simp only [htImageMat, Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec]
  rw [Matrix.mul_assoc _ (X v), Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext i
  simp only [Formalism.HermitianLatticesTheory.vecAt]
  rw [← LinearMap.toMatrix_mulVec_repr b b' φ x, RingHom.map_mulVec]
  rfl
end Formalism.HN
