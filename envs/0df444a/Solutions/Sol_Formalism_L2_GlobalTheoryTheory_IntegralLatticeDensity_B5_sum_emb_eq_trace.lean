-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.sum_emb_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:04:08.635919+00:00
-- url     : https://prove2.me/submissions/e7a9b9a3-2e8b-443c-839b-97b852fc0e43

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_coe_of_mem
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
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (a : E) :
    ∑ i, liftM M (emb i a) = liftM M (φ₀ (Algebra.trace K E a)) := by
  have hsum := sum_emb_eq_trace_complex K E φ₀ ι emb hinj hres hcard a
  have hmem : φ₀ (Algebra.trace K E a) ∈ M := hsum ▸ M.sum_mem (fun i _ => hM i a)
  apply Subtype.ext
  rw [IntermediateField.coe_sum, liftM_coe_of_mem M hmem, ← hsum]
  exact Finset.sum_congr rfl fun i _ => liftM_coe_of_mem M (hM i a)
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
