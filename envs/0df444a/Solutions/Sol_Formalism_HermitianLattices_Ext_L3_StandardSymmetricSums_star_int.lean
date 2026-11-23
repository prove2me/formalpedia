-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.star_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:34.452448+00:00
-- url     : https://prove2.me/submissions/c33e8038-3b62-4575-af35-a8e52ed0c16f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
namespace Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
theorem _root_.solution (r : 𝓞 K) : ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K r) :=
  ⟨RingOfIntegers.mapRingHom (starRingEnd K) r, rfl⟩
end Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
