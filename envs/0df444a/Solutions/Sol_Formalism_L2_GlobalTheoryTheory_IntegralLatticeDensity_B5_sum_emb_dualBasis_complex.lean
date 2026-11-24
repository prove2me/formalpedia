-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.sum_emb_dualBasis_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:07.580822+00:00
-- url     : https://prove2.me/submissions/ea1e9b4d-ae5d-477d-913e-777cb4a22de9

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_sum_emb_eq_trace_complex

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
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, emb i (e j) * emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j) =
      if i = k then 1 else 0 := by
  have hexp : ∀ x, emb k x = ∑ i', emb i' x * ∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j) := by
    intro x
    conv_lhs => rw [← ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e).sum_repr x]
    rw [map_sum]
    simp only [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, Algebra.smul_def, map_mul,
      hres, ← sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => by ring
  have hLI : LinearIndependent ℂ (fun i => ((emb i : E →+* ℂ) : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp (fun i => (emb i).toMonoidHom)
      (fun i j h => hinj (RingHom.ext fun x => DFunLike.congr_fun h x))
  rw [Fintype.linearIndependent_iff] at hLI
  have h := hLI (fun i' => (∑ j, emb i' (e j) * emb k (((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e) j)) - if i' = k then 1 else 0) (by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul,
      Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, hexp x]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _) i
  rwa [sub_eq_zero] at h
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
