-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.sub_mem_of_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:17.018451+00:00
-- url     : https://prove2.me/submissions/57ea5143-2b86-42fd-977d-d38ab985f63b

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
variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (hc : ∀ k, U.mkQ (c k) = b'' k) (x : V) :
    x - ∑ k, b''.repr (U.mkQ x) k • c k ∈ U := by
  apply (Submodule.Quotient.eq U).mp
  change U.mkQ x = U.mkQ (∑ k, b''.repr (U.mkQ x) k • c k)
  rw [map_sum]
  simp only [LinearMap.map_smul, hc]
  exact (b''.sum_repr (U.mkQ x)).symm
end Formalism.HN.QuotientRealization
