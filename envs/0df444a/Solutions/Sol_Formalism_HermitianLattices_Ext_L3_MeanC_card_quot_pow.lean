-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanC.card_quot_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:27:02.637907+00:00
-- url     : https://prove2.me/submissions/37e6c92b-ef97-40f3-87a2-9644d5d1c904

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN

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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Nat.card (𝓞 F ⧸ 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ k := by
  rw [← map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
end Formalism.HermitianLattices.Ext.L3.MeanC
