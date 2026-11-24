-- Prove2me | solution 1 for Formalism.HN.HeightGram.majAt_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:18.024687+00:00
-- url     : https://prove2.me/submissions/b2913b6a-ade4-451a-ad6b-afd4e9586609

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_HeightGram_fcoord_smul

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
open Formalism.HN.HeightGram
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.HeightGram
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (a a' : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) (a' • y) =
      star (v.embedding a) * v.embedding a' * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fcoord_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
end Formalism.HN.HeightGram
