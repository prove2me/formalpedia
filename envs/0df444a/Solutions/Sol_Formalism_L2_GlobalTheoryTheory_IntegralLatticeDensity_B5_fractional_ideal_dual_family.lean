-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.fractional_ideal_dual_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:03:01.165725+00:00
-- url     : https://prove2.me/submissions/ea577b15-7b75-4f82-8d8c-9057a567d28c

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
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    ∃ (n : ℕ) (g : Fin n → E) (f : Fin n → ((I : Submodule (𝓞 E) E).restrictScalars (𝓞 K) →ₗ[𝓞 K] 𝓞 K)),
      (∀ j, g j ∈ (I : Submodule (𝓞 E) E)) ∧
      ∀ y : (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K), (y : E) = ∑ j, f j y • g j := by
  set P := (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K)
  have : Module.IsTorsionFree (𝓞 K) E := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K E
  have : Module.IsTorsionFree (𝓞 K) P := inferInstance
  have hfg : P.FG := (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).restrictScalars
  have : Module.Finite (𝓞 K) P := Module.Finite.iff_fg.mpr hfg
  have : Module.FinitePresentation (𝓞 K) P := Module.finitePresentation_of_finite (𝓞 K) P
  have : Module.Projective (𝓞 K) P := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, F, G, -, -, hFG⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 K) P
  refine ⟨n, fun i => (F (Pi.single i 1) : E), fun i => (LinearMap.proj i).comp G,
    fun i => (F (Pi.single i 1)).2, fun y => ?_⟩
  have e1 : F (G y) = y := by
    have := congrArg (fun φ => φ y) hFG
    simpa using this
  have e2 : y = ∑ i, ((LinearMap.proj i).comp G) y • F (Pi.single i 1) := by
    conv_lhs => rw [← e1]
    rw [LinearMap.pi_apply_eq_sum_univ F (G y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  conv_lhs => rw [e2]
  simp
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
