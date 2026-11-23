-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.BoxSum.finite_boxSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:04.847199+00:00
-- url     : https://prove2.me/submissions/c204520a-f77c-41a1-a21a-b7ddb9e7543e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_rEmb_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_mem_boxSet_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_isTotallyReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.BoxSum
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by
  have hR : IsTotallyReal F := QuadraticExtensionConjugation.isTotallyReal hK hF
  have h0 := Embeddings.finite_of_norm_le F ℂ T
  refine Set.Finite.of_finite_image (f := fun n : 𝓞 F => (n : F)) (h0.subset ?_)
    (RingOfIntegers.coe_injective.injOn)
  rintro _ ⟨n, hn, rfl⟩
  refine ⟨n.2, fun ψ => ?_⟩
  have hw : (InfinitePlace.mk ψ).IsReal := IsTotallyReal.isReal _
  have h1 := ((mem_boxSet_iff hK hF).1 hn) ⟨_, hw⟩
  have h2 : ‖ψ (n : F)‖ = |rEmb ⟨_, hw⟩ n| := by
    rw [rEmb_apply, ← Real.norm_eq_abs, InfinitePlace.norm_embedding_of_isReal]
    rfl
  rw [h2, abs_of_pos h1.1]
  exact h1.2
end Formalism.HermitianLattices.Ext.L3.BoxSum
