-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.exists_star_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:32.931185+00:00
-- url     : https://prove2.me/submissions/ea93fb47-ce86-48a0-abce-d8c57e0820d9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (a : 𝓞 K) : ∃ a' : 𝓞 K, algebraMap (𝓞 K) K a' = star (algebraMap (𝓞 K) K a) :=
  ⟨⟨star (algebraMap (𝓞 K) K a), map_isIntegral_int (starRingEnd K) (RingOfIntegers.isIntegral_coe a)⟩, rfl⟩
end Formalism.HermitianLattices.Ext.L3.MeanB
