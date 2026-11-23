-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.MeanB.exists_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:15:30.740004+00:00
-- url     : https://prove2.me/submissions/09eed124-c12c-4afc-9814-eb37b4c01f9d

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
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.MeanB
theorem _root_.solution (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (y : ↥L) :
    ∃ n : 𝓞 F, h (y : V) (y : V) = algebraMap F K (n : F) := by
  obtain ⟨a, ha⟩ := (hF (h y y)).1 (hs.eq y y)
  obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi y y.2 y y.2)
  have hint : IsIntegral ℤ a := by
    rw [← isIntegral_algebraMap_iff (algebraMap F K).injective, ha, ← hz]
    exact RingOfIntegers.isIntegral_coe z
  exact ⟨⟨a, hint⟩, ha.symm⟩
end Formalism.HermitianLattices.Ext.L3.MeanB
