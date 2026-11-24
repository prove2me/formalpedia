-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U3.absNorm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:23:20.886078+00:00
-- url     : https://prove2.me/submissions/e0c69419-f6ed-41bd-8cf8-3f2115761153

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlphaStdOneNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_ExtendedPrimeIdeals_ne_bot_of_isMaximal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U3
open ExtendedPrimeIdeals EndomorphismScalars NormOneGroup
namespace Formalism.HermitianLattices.Ext.L3.U3
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < Ideal.absNorm 𝔭 :=
  Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.1 (ne_bot_of_isMaximal h𝔭))
end Formalism.HermitianLattices.Ext.L3.U3
