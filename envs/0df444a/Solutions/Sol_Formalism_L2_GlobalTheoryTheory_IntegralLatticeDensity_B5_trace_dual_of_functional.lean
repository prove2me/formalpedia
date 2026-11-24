-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.trace_dual_of_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:02:31.536299+00:00
-- url     : https://prove2.me/submissions/e299e6d7-3cfa-4c70-9270-e0daf9aecdea

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
    (P : Submodule (𝓞 K) E) {κ : Type} [Fintype κ] (e : Module.Basis κ K E) (he : ∀ l, e l ∈ P)
    (f : P →ₗ[𝓞 K] 𝓞 K) :
    ∃ b : E, ∀ y (hy : y ∈ P), Algebra.traceForm K E b y = algebraMap (𝓞 K) K (f ⟨y, hy⟩) := by
  let F : E →ₗ[K] K := ∑ l, algebraMap (𝓞 K) K (f ⟨e l, he l⟩) • e.coord l
  refine ⟨((Algebra.traceForm K E).toDual (traceForm_nondegenerate K E)).symm F, fun y hy => ?_⟩
  rw [← LinearMap.BilinForm.toDual_def (traceForm_nondegenerate K E), LinearEquiv.apply_symm_apply]
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image (e.repr y))
  have hc : ∀ l, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = algebraMap (𝓞 K) K d * e.repr y l := by
    intro l
    obtain ⟨c, hc⟩ := hd (e.repr y l) (Finset.mem_image_of_mem _ (Finset.mem_univ l))
    exact ⟨c, by rw [hc]; exact Algebra.smul_def _ _⟩
  choose c hc using hc
  have hdy : (d : 𝓞 K) • (⟨y, hy⟩ : P) = ∑ l, c l • (⟨e l, he l⟩ : P) := by
    apply Subtype.ext
    simp only [SetLike.val_smul, Submodule.coe_sum]
    conv_lhs => rw [← e.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← algebraMap_smul K (c l), hc l, ← algebraMap_smul K (d : 𝓞 K), smul_smul]
  have hf := congrArg (fun z => algebraMap (𝓞 K) K (f z)) hdy
  simp only [map_smul, map_sum, smul_eq_mul, map_mul] at hf
  have hd0 : algebraMap (𝓞 K) K (d : 𝓞 K) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 K) K), (IsFractionRing.injective (𝓞 K) K).eq_iff]
    exact nonZeroDivisors.ne_zero d.2
  apply mul_left_cancel₀ hd0
  rw [hf]
  simp only [hc]
  rw [LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  ring
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
