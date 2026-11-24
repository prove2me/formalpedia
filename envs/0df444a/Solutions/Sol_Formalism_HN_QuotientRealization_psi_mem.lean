-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.psi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:24.246233+00:00
-- url     : https://prove2.me/submissions/4c573b11-7637-4b9f-9e20-c4af0d0c8cea

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_pv_le
import Theorems.Thm_Formalism_HN_PlaceDecomposition_piece_eq_map
import Theorems.Thm_Formalism_HN_PlaceDecomposition_span_real_eq_complex


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
theorem _root_.solution [DecidableEq (InfinitePlace K)] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (S : Submodule (𝓞 K) V) (v : InfinitePlace K)
    (z : EuclideanSpace ℂ ι) (hz : z ∈ pv b X (Submodule.span K (S : Set V)) v) :
    PlaceDecomposition.psi v (WithLp.ofLp z) ∈ Submodule.span ℝ
      (zl (Formalism.HermitianLatticesTheory.realize b X) S : Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) := by
  have h1 := pv_le b X S v z hz
  have h2 : WithLp.ofLp z ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (S : Set V)) := by
    rw [← PlaceDecomposition.span_real_eq_complex b X S v]; exact h1
  have h3 := Submodule.mem_map_of_mem (f := PlaceDecomposition.psi v) h2
  rw [← PlaceDecomposition.piece_eq_map b X S v] at h3
  exact (Submodule.mem_inf.1 h3).1
end Formalism.HN.QuotientRealization
