-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.absNorm_span_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:42:51.498507+00:00
-- url     : https://prove2.me/submissions/a19636fc-cd7c-47a9-91f8-4f5dd136811c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FinrankRingOfIntegers
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormSpanEqProd
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrA_absNorm_eq_tprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (n : 𝓞 F) (hn : n ≠ 0) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (Ideal.absNorm 𝔭.1 : ℝ) ^ vF 𝔭.1 n := by
  have hI : Ideal.span {n} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [BrA.absNorm_eq_tprod hI]
  refine tprod_congr fun 𝔭 => ?_
  unfold vF
  simp only [Ideal.span_singleton_le_iff_mem]
end Formalism.HermitianLattices.Ext.L3
