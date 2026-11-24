-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.sum_re_cmType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:16:43.917704+00:00
-- url     : https://prove2.me/submissions/e268b24f-9b22-440e-84c6-85fc5aed0aa2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix
open scoped ComplexConjugate
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (z : K) :
    ∑ i, (σ i z).re = (1 / 2 : ℝ) * ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
  have h1 : (algebraMap ℚ ℂ) (Algebra.trace ℚ K z) = ∑ τ : K →+* ℂ, τ z := by
    rw [trace_eq_sum_embeddings ℂ (x := z)]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ (fun _ => rfl)
  have h2 : ∑ τ : K →+* ℂ, τ z = ∑ i, σ i z + ∑ i, conj (σ i z) := by
    rw [← Equiv.sum_comp (cmEquiv σ hinj hcm), Fintype.sum_sum_type]
    rfl
  have h3 := congrArg Complex.re (h1.trans h2)
  simp only [Complex.add_re, Complex.re_sum, Complex.conj_re] at h3
  have h4 : ((algebraMap ℚ ℂ) (Algebra.trace ℚ K z)).re = ((Algebra.trace ℚ K z : ℚ) : ℝ) := by
    simp
  rw [h4] at h3
  linarith
end Formalism.L2.Pj.FundamentalDomainD5
