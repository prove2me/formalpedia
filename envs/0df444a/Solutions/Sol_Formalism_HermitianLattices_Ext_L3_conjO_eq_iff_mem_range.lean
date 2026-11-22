-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.conjO_eq_iff_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:43:52.317109+00:00
-- url     : https://prove2.me/submissions/a34aeca0-55ee-4a1a-855d-374a8bd0b20f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSubMemOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_conjO_coe

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
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (x : 𝓞 K) :
    conjO K x = x ↔ x ∈ Set.range (algebraMap (𝓞 F) (𝓞 K)) := by
  constructor
  · intro hx
    have hfix : star (x : K) = x := by rw [← conjO_coe, hx]
    obtain ⟨a, ha⟩ := (hF _).1 hfix
    have hint : IsIntegral ℤ (algebraMap F K a) := by
      rw [ha]
      first
      | exact RingOfIntegers.isIntegral_coe x
      | exact x.2
    have ha' : IsIntegral ℤ a := (isIntegral_algebraMap_iff (algebraMap F K).injective).1 hint
    refine ⟨⟨a, ha'⟩, ?_⟩
    apply RingOfIntegers.ext
    show algebraMap F K a = (x : K)
    exact ha
  · rintro ⟨y, rfl⟩
    apply RingOfIntegers.ext
    rw [conjO_coe]
    have hy : ((algebraMap (𝓞 F) (𝓞 K) y : 𝓞 K) : K) = algebraMap F K (y : F) := rfl
    rw [hy]
    exact (hF _).2 ⟨_, rfl⟩
end Formalism.HermitianLattices.Ext.L3
