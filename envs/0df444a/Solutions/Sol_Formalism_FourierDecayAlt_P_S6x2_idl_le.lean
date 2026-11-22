-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x2.idl_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:23.834866+00:00
-- url     : https://prove2.me/submissions/734e88db-a108-454e-8c06-efedc1350612

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualIdealInclusion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationScaledIdealMemIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x2
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
namespace Formalism.FourierDecayAlt.P.S6x2
theorem _root_.solution (g : ℕ) (ν : ℤ) : idl E g 2 ν ≤ idl E g 1 ν := by
  unfold idl
  have : FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (2 : ℤ)) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ (1 : ℤ))
        * FractionalIdeal.spanSingleton (𝓞 E)⁰ (g : E) := by
    rw [FractionalIdeal.spanSingleton_mul_spanSingleton]; congr 1
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, zpow_one]; ring
  rw [this, ← mul_assoc]
  refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
  rw [FractionalIdeal.mem_spanSingleton] at hj
  obtain ⟨z, rfl⟩ := hj
  have h := (dd E ^ ν * FractionalIdeal.spanSingleton (𝓞 E)⁰
    ((g : E) ^ (1 : ℤ)) : FI E).coeToSubmodule.smul_mem (z * (g : 𝓞 E)) hi
  rw [Algebra.smul_def] at h
  have e : i * z • (g : E) = (algebraMap (𝓞 E) E) (z * (g : 𝓞 E)) * i := by
    rw [Algebra.smul_def]; push_cast; ring
  rw [e]; exact h
end Formalism.FourierDecayAlt.P.S6x2
