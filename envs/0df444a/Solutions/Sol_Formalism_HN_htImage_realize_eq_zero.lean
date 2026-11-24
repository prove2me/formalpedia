-- Prove2me | solution 1 for Formalism.HN.htImage_realize_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:28.216806+00:00
-- url     : https://prove2.me/submissions/eb5c5575-ac78-4e52-a157-c3570a05e4ad

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_GramBlock
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtImage
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
    (hX : ∀ v, IsUnit (X v).det) {x : V} (h : Formalism.HermitianLatticesTheory.realize b X x = 0) : x = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace K) := inferInstance
  have h1 : Formalism.HermitianLatticesTheory.fcoord b X v x = 0 := by
    rw [← htImageCv_realize, h]
    funext i
    apply Complex.ext <;> simp [htImageCv]
  have h2 : Formalism.HermitianLatticesTheory.vecAt b v x = 0 := by
    have h3 := congrArg (fun w => (X v).mulVec w) h1
    simp only [Formalism.HermitianLatticesTheory.fcoord, Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h3
    rwa [Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec] at h3
  apply b.repr.injective
  ext i
  have h4 := congrFun h2 i
  simpa [Formalism.HermitianLatticesTheory.vecAt] using h4
end Formalism.HN
