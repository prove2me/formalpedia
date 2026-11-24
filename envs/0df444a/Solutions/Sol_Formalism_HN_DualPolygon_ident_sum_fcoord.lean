-- Prove2me | solution 1 for Formalism.HN.DualPolygon.ident_sum_fcoord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:40.214532+00:00
-- url     : https://prove2.me/submissions/26b80061-4105-4521-a313-1a15bda772ce

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_ident_fcoord_dual

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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (f : Module.Dual K V) (x : V) :
    ∑ i, Formalism.HermitianLatticesTheory.fcoord b.dualBasis (dualFrame X) v f i * Formalism.HermitianLatticesTheory.fcoord b X v x i =
      v.embedding (f x) := by
  rw [ident_fcoord_dual b X hX]
  change ((X v).transpose.mulVec _) ⬝ᵥ ((X v)⁻¹.mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)) = _
  rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec]
  conv_rhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, smul_eq_mul, map_mul, dotProduct, Formalism.HermitianLatticesTheory.vecAt]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.HN.DualPolygon
