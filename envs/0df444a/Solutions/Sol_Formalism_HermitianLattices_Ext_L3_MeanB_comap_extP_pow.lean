-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.comap_extP_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:57.805506+00:00
-- url     : https://prove2.me/submissions/ca9fbd33-8cbe-4f49-9495-d291f5f3c8e6

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
theorem _root_.solution (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (extP K 𝔭 ^ k).comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 ^ k := by
  rw [extP, ← Ideal.map_pow, Ideal.comap_map_eq_self_of_faithfullyFlat]
end Formalism.HermitianLattices.Ext.L3.MeanB
