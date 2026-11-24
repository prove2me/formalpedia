-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.sum_emb_eq_trace_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:53:28.52599+00:00
-- url     : https://prove2.me/submissions/0e8d60b1-3486-4571-9e9c-ac78f277ed93

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex

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
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (a : E) :
    ∑ i, emb i a = φ₀ (Algebra.trace K E a) := by
  letI : Algebra K ℂ := φ₀.toAlgebra
  haveI : FiniteDimensional K E := Module.Finite.of_restrictScalars_finite ℚ K E
  let f : ι → (E →ₐ[K] ℂ) := fun i => { emb i with commutes' := fun y => hres i y }
  have hfinj : Function.Injective f := fun i j h => hinj (RingHom.ext fun x => AlgHom.congr_fun h x)
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, by rw [hcard, AlgHom.card K E ℂ]⟩
  have htr := trace_eq_sum_embeddings ℂ (K := K) (L := E) (x := a)
  calc ∑ i, emb i a = ∑ i, f i a := rfl
    _ = ∑ σ : E →ₐ[K] ℂ, σ a := hbij.sum_comp (fun σ => σ a)
    _ = φ₀ (Algebra.trace K E a) := htr.symm
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
