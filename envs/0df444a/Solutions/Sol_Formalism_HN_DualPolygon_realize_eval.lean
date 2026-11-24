-- Prove2me | solution 1 for Formalism.HN.DualPolygon.realize_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:21.596945+00:00
-- url     : https://prove2.me/submissions/3aab3e05-d4c3-4982-ad40-466ce138c407

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
import Theorems.Thm_Formalism_HN_DualPolygon_dualFrame_dualFrame

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) :
    Formalism.HermitianLatticesTheory.realize b.dualBasis.dualBasis (dualFrame (dualFrame X)) (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.realize b X x := by
  rw [dualFrame_dualFrame X hX]
  have hvec : ∀ v, Formalism.HermitianLatticesTheory.vecAt b.dualBasis.dualBasis v (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.vecAt b v x := by
    intro v
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, Basis.dualBasis_repr, Basis.dualBasis_apply]
  have hf : ∀ v, Formalism.HermitianLatticesTheory.fcoord b.dualBasis.dualBasis X v (Module.Dual.eval K V x) =
      Formalism.HermitianLatticesTheory.fcoord b X v x := by
    intro v
    simp only [Formalism.HermitianLatticesTheory.fcoord, hvec]
  ext p
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw, hf]
end Formalism.HN.DualPolygon
