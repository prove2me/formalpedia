-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.mem_mmR_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:22:10.469511+00:00
-- url     : https://prove2.me/submissions/019c3966-a8f7-4db0-ae1f-320371a19ac6

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_coe_lift_intermediate
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_lift_integral_mem_range
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_sum_emb_eq_trace


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
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (v : ι → M)
    (hv : v ∈ mmR M emb I) :
    ∀ b ∈ ((FractionalIdeal.dual (𝓞 K) K I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : Submodule (𝓞 E) E), ∑ i, v i * liftM M (emb i b) ∈ (algebraMap (𝓞 M) M).range := by
  intro b hb
  have hι : Nonempty ι := by
    rw [← Fintype.card_pos_iff, hcard]; exact Module.finrank_pos
  obtain ⟨i0⟩ := hι
  have hφ : ∀ y, φ₀ y ∈ M := fun y => by rw [← hres i0 y]; exact hM i0 _
  have hb' : ∀ a ∈ (I : Submodule (𝓞 E) E), Algebra.trace K E (b * a) ∈ (algebraMap (𝓞 K) K).range := by
    intro a ha
    have := (FractionalIdeal.mem_dual hI).mp hb a ha
    simpa [Algebra.traceForm_apply] using this
  refine Submodule.span_induction (p := fun v _ => ∑ i, v i * liftM M (emb i b) ∈ (algebraMap (𝓞 M) M).range) ?_ ?_ ?_ ?_ hv
  · rintro w ⟨a, ha, rfl⟩
    have : ∑ i, liftM M (emb i a) * liftM M (emb i b) = liftM M (φ₀ (Algebra.trace K E (a * b))) := by
      rw [← sum_emb_eq_trace K E φ₀ M ι emb hinj hres hcard hM]
      refine Finset.sum_congr rfl fun i _ => ?_
      apply Subtype.ext
      rw [IntermediateField.coe_mul, coe_lift_intermediate (hM i a), coe_lift_intermediate (hM i b), coe_lift_intermediate (hM i (a * b)), map_mul]
    simp only [this]
    obtain ⟨t, ht⟩ := hb' a ha
    apply lift_integral_mem_range M (hφ _)
    rw [mul_comm a b, ← ht]
    exact (t.isIntegral_coe).map φ₀.toIntAlgHom
  · simp
  · intro x y _ _ hx hy
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hx hy
  · intro c x _ hx
    simp only [Pi.smul_apply, Algebra.smul_def, mul_assoc, ← Finset.mul_sum]
    exact mul_mem ⟨c, rfl⟩ hx
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
