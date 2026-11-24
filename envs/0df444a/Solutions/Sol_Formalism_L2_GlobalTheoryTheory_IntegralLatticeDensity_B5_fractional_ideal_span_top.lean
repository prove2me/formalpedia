-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.fractional_ideal_span_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:02.742785+00:00
-- url     : https://prove2.me/submissions/8789ec8b-d963-4656-a487-086e7090391e

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily

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
theorem _root_.solution (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    Submodule.span K ((I : Submodule (𝓞 E) E) : Set E) = ⊤ := by
  have hne : (I : Submodule (𝓞 E) E) ≠ ⊥ := by
    intro h; apply hI; apply FractionalIdeal.coeToSubmodule_injective; simpa using h
  obtain ⟨a, haI, ha0⟩ := (Submodule.ne_bot_iff _).mp hne
  rw [eq_top_iff]
  intro x _
  obtain ⟨m, hm0, hmz⟩ := exists_integral_multiples ℤ ℚ ({x / a} : Finset E)
  have hw := hmz (x / a) (by simp)
  let w : 𝓞 E := ⟨m • (x / a), hw⟩
  have hwa : w • a ∈ (I : Submodule (𝓞 E) E) := Submodule.smul_mem _ w haI
  have hx : x = ((m : K)⁻¹) • (w • a) := by
    have hm : (m : E) ≠ 0 := by exact_mod_cast hm0
    rw [Algebra.smul_def, Algebra.smul_def]
    show x = algebraMap K E ((m : K)⁻¹) * ((m • (x / a)) * a)
    rw [map_inv₀, map_intCast, zsmul_eq_mul]
    field_simp
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hwa)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
