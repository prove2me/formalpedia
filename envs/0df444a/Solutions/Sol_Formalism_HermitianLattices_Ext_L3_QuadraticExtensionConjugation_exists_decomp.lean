-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:03.94495+00:00
-- url     : https://prove2.me/submissions/ed1ff84a-eb35-4f7e-8d73-464f58c1c939

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CovolumeIntegerLatticeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop

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
theorem _root_.solution (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) {a : K}
    (ha : star a ≠ a) (x : K) : ∃ u v : F, x = algebraMap F K u + algebraMap F K v * a := by
  have hb : a - star a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  obtain ⟨w, hw⟩ : ∃ w : K, w * (a - star a) = x - star x :=
    ⟨(x - star x) / (a - star a), div_mul_cancel₀ _ hb⟩
  have hsw : star w = w := by
    have h1 := congrArg star hw
    rw [star_mul', star_sub, star_sub, star_star, star_star] at h1
    apply mul_right_cancel₀ hb
    linear_combination -h1 - hw
  obtain ⟨v, hv⟩ := (hF w).1 hsw
  have hz : star (x - w * a) = x - w * a := by
    rw [star_sub, star_mul', hsw]
    linear_combination hw
  obtain ⟨u, hu⟩ := (hF _).1 hz
  exact ⟨u, v, by rw [hu, hv]; ring⟩
end Formalism.HermitianLattices.Ext.L3.QuadraticExtensionConjugation
