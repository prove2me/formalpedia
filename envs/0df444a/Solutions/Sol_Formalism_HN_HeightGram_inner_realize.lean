-- Prove2me | solution 1 for Formalism.HN.HeightGram.inner_realize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:28.932042+00:00
-- url     : https://prove2.me/submissions/87821636-ea98-485f-8179-ca01b94a0f26

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Theorems.Thm_Formalism_HN_HeightGram_realize_apply0
import Theorems.Thm_Formalism_HN_HeightGram_realize_apply1
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply0
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply1


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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x y : V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) =
      ∑ v, (Formalism.HermitianLatticesTheory.majAt b X v x y).re := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_prod_type,
    Fin.sum_univ_two, Formalism.HermitianLatticesTheory.majAt, Complex.re_sum, realize_apply0, realize_apply1]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring
end Formalism.HN.HeightGram
