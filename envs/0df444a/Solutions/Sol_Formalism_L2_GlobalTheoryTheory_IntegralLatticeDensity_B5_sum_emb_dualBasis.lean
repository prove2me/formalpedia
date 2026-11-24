-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.sum_emb_dualBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:14:44.73835+00:00
-- url     : https://prove2.me/submissions/cc5c8e23-a938-4500-9419-a2fe284abca4

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_liftM_coe_of_mem
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_sum_emb_dualBasis_complex

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
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, liftM M (emb i (e j)) *
        liftM M (emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j)) =
      if i = k then 1 else 0 := by
  have hc := sum_emb_dualBasis_complex K E φ₀ ι emb hinj hres hcard e i k
  apply Subtype.ext
  rw [IntermediateField.coe_sum]
  simp only [IntermediateField.coe_mul, liftM_coe_of_mem M (hM _ _)]
  rw [hc]
  split_ifs <;> simp
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
