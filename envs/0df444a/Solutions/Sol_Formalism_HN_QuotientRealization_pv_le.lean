-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.pv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:28.45626+00:00
-- url     : https://prove2.me/submissions/235a0def-83b1-46e5-ac28-d2276966f1c0

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_fcoord_mem_span

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
    (S : Submodule (𝓞 K) V) (v : InfinitePlace K) (z : EuclideanSpace ℂ ι)
    (hz : z ∈ pv b X (Submodule.span K (S : Set V)) v) :
    WithLp.ofLp z ∈ Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (S : Set V)) := by
  induction hz using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      simpa using fcoord_mem_span b X S v hy
  | zero => simp
  | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa using Submodule.smul_mem _ a hx
end Formalism.HN.QuotientRealization
