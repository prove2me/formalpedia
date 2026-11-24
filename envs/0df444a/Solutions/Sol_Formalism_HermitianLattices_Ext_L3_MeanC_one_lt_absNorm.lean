-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanC.one_lt_absNorm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:31:05.996893+00:00
-- url     : https://prove2.me/submissions/c86cc5ba-d166-438e-a940-17e811b8cf17

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanC_ne_bot_of_isMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.MeanC
namespace Formalism.HermitianLattices.Ext.L3.MeanC
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 1 < Ideal.absNorm 𝔭 := by
  have h0 : Ideal.absNorm 𝔭 ≠ 0 := fun h => ne_bot_of_isMaximal h𝔭 (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm 𝔭 ≠ 1 := fun h => h𝔭.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega
end Formalism.HermitianLattices.Ext.L3.MeanC
