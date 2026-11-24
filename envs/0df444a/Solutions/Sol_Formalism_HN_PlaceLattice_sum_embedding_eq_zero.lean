-- Prove2me | solution 1 for Formalism.HN.PlaceLattice.sum_embedding_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:19.809862+00:00
-- url     : https://prove2.me/submissions/1e54323e-d0e4-49a9-ac68-5073b2b44be4

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep

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
open Formalism.HN.PlaceLattice
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceLattice
theorem _root_.solution {t : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ}
    (h : ∀ v : InfinitePlace K, ∑ k, (t k : ℂ) * v.embedding (integralBasis K k) = 0) : t = 0 := by
  have hφ : ∀ φ : K →+* ℂ, ∑ k, (t k : ℂ) * φ (integralBasis K k) = 0 := by
    intro φ
    rcases InfinitePlace.embedding_mk_eq φ with hφ | hφ
    · simpa [hφ] using h (InfinitePlace.mk φ)
    · have h2 := congrArg (starRingEnd ℂ) (h (InfinitePlace.mk φ))
      simpa [hφ, map_sum, map_mul, Complex.conj_ofReal] using h2
  have hli := (canonicalEmbedding.latticeBasis K).linearIndependent
  rw [Fintype.linearIndependent_iff] at hli
  have hz := hli (fun k => (t k : ℂ)) (by
    funext φ
    simpa [canonicalEmbedding.latticeBasis_apply, Finset.sum_apply, smul_eq_mul] using hφ φ)
  funext k
  exact_mod_cast hz k
end Formalism.HN.PlaceLattice
