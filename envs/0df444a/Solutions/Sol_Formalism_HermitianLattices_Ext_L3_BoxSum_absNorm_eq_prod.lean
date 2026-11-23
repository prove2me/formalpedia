-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.absNorm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:24.395151+00:00
-- url     : https://prove2.me/submissions/6b948fbd-0c67-43b9-82fc-f1e224d6db93

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_rEmb_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution [IsTotallyReal F] (n : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n| := by
  have h1 : (Ideal.absNorm (Ideal.span {n}) : ℝ) = |((Algebra.norm ℚ (n : F) : ℚ) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, Nat.cast_natAbs, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [h1, ← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
  have h2 : ∀ w : InfinitePlace F, w.IsReal := fun w => IsTotallyReal.isReal w
  rw [Finset.prod_subtype (p := fun w : InfinitePlace F => w.IsReal) Finset.univ (by simp [h2])
    (fun w => w (n : F) ^ w.mult)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [InfinitePlace.mult, if_pos w.2, pow_one, rEmb_apply, ← Real.norm_eq_abs,
    InfinitePlace.norm_embedding_of_isReal]
end Formalism.HermitianLattices.Ext.L3.BoxSum
