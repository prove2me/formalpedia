-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.NO.mem_zR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:22:37.316681+00:00
-- url     : https://prove2.me/submissions/828bdc56-aa08-4069-ae76-71fafa985d6d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.D2.NO
namespace Formalism.HermitianLattices.Ext.L3.D2.NO
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} {z a : K} : a ∈ zR 𝔭 z ↔ ∃ b ∈ pK K 𝔭 0, z * b = a := Iff.rfl
end Formalism.HermitianLattices.Ext.L3.D2.NO
