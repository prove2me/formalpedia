-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.mem_imI_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:48.872501+00:00
-- url     : https://prove2.me/submissions/0a0fd8c7-e9d8-42ce-a31c-c0aa3b22c775

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_mul_ext
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_add_ext
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_one_ext
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_int_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
theorem _root_.solution {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (x : M) :
    x ∈ imI M σ J ↔
      ∀ b ∈ ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), x * liftM M (σ b) ∈ (algebraMap (𝓞 M) M).range := by
  have hJJ : (1 : E) ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one]
    exact Submodule.mem_one.2 ⟨1, map_one _⟩
  have hint : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
      Submodule (𝓞 E) E), liftM M (σ z) ∈ (algebraMap (𝓞 M) M).range := by
    intro z hz
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hJ, FractionalIdeal.coe_one] at hz
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hz
    exact liftM_int_ext M σ hσ y
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      intro b hb
      rw [← liftM_mul_ext M σ hσ]
      exact hint _ (Submodule.mul_mem_mul ha hb)
    | zero =>
      intro b _
      rw [zero_mul]
      exact zero_mem _
    | add y z _ _ hy hz =>
      intro b hb
      rw [add_mul]
      exact add_mem (hy b hb) (hz b hb)
    | smul r y _ hy =>
      intro b hb
      rw [smul_mul_assoc, Algebra.smul_def]
      exact mul_mem (RingHom.mem_range_self _ r) (hy b hb)
  · intro hx
    have key : ∀ z ∈ (J : Submodule (𝓞 E) E) * ((J⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
        Submodule (𝓞 E) E), x * liftM M (σ z) ∈ imI M σ J := by
      intro z hz
      induction hz using Submodule.mul_induction_on' with
      | mem_mul_mem a ha b hb =>
        obtain ⟨r, hr⟩ := hx b hb
        rw [liftM_mul_ext M σ hσ, mul_comm (liftM M (σ a)), ← mul_assoc, ← hr, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (Submodule.subset_span ⟨a, ha, rfl⟩)
      | add y _ z _ hy hz =>
        rw [liftM_add_ext M σ hσ, mul_add]
        exact add_mem hy hz
    have := key 1 hJJ
    rwa [liftM_one_ext, mul_one] at this
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
