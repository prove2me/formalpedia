-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_int_of_star_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:37.005227+00:00
-- url     : https://prove2.me/submissions/111cc801-496d-4997-bfc4-f536bfb529f7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadraticExtensionConjugation_coe_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
theorem _root_.solution (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K))
    (y : 𝓞 K) (hy : star (algebraMap (𝓞 K) K y) = algebraMap (𝓞 K) K y) :
    ∃ z : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) z = y := by
  obtain ⟨u, hu⟩ := (hF _).1 hy
  have hint : IsIntegral ℤ u := by
    have h1 : IsIntegral ℤ (algebraMap F K u) := by
      rw [hu]; exact RingOfIntegers.isIntegral_coe y
    exact (isIntegral_algebraMap_iff (algebraMap F K).injective).mp h1
  refine ⟨⟨u, hint⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_algebraMap (F := F) (K := K) ⟨u, hint⟩).trans hu
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
