-- Prove2me | solution 1 for Formalism.ExtensionFiltration.mink_norm_sq_realize
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:07.99659+00:00
-- url     : https://prove2.me/submissions/fdb4a755-0dd4-4118-adc8-ca03a2015bd8

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski

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
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  have h1 : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 = ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 := by
    intro v
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  simp only [h1]
  unfold Formalism.HermitianLatticesTheory.realize Formalism.HermitianLatticesTheory.realizeRaw
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring
end Formalism.ExtensionFiltration
