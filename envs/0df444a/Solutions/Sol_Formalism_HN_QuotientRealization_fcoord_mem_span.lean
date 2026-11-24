-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.fcoord_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:23.806441+00:00
-- url     : https://prove2.me/submissions/1c87eb90-9e8e-44f0-9c49-e54a8be2dc06

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (S : Submodule (𝓞 K) V) (v : InfinitePlace K) {y : V}
    (hy : y ∈ Submodule.span K (S : Set V)) :
    Formalism.HermitianLatticesTheory.fcoord b X v y ∈ Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (S : Set V)) := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [Formalism.HermitianLatticesTheory.fcoord_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Formalism.HermitianLatticesTheory.fcoord_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
      have h1 : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
        funext i
        simp [Formalism.HermitianLatticesTheory.vecAt]
      have h2 : Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
        simp only [Formalism.HermitianLatticesTheory.fcoord, h1, Matrix.mulVec_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ hx
end Formalism.HN.QuotientRealization
