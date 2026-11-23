-- Prove2me | solution 1 for Formalism.ExtensionFiltration.mink_normAt_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:49.124773+00:00
-- url     : https://prove2.me/submissions/4059f942-cbe8-40ea-a04a-9e2dbc7bd2b8

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (x : V) (hx : x ≠ 0) :
    0 < Formalism.HermitianLatticesTheory.normAt b X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  apply Real.sqrt_pos.mpr
  have hne : Formalism.HermitianLatticesTheory.fcoord b X v x ≠ 0 := by
    unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    intro h0
    have h1 : (fun i => v.embedding (b.repr x i)) = 0 := by
      have h3 := congrArg (fun w => (X v).mulVec w) h0
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec,
        Matrix.mulVec_zero] at h3
      exact h3
    apply hx
    have h2 : b.repr x = 0 := by
      ext i
      have h4 := congrFun h1 i
      simp only [Pi.zero_apply] at h4
      rw [Finsupp.zero_apply]
      exact (map_eq_zero v.embedding).mp h4
    exact b.repr.map_eq_zero_iff.mp h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hpos : 0 < ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => ‖Formalism.HermitianLatticesTheory.fcoord b X v x j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))
end Formalism.ExtensionFiltration
