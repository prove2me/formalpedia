-- Prove2me | solution 1 for Formalism.L2.Pj.FundamentalDomainD5.trace_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:23:13.45032+00:00
-- url     : https://prove2.me/submissions/c4efd7b5-b4e0-417a-8651-36c75fa8ef8e

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_HQsmulRight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ThetaDotSelf
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_rho_dot
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_sgn_conj
import Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_sum_re_cmType


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
open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}
namespace Formalism.L2.Pj.FundamentalDomainD5
theorem _root_.solution (σ : ι → K →+* ℂ) (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ)
    (Q : ι → Matrix (Fin r) (Fin r) ℂ) (p : ℕ) (S : HermForm K r)
    (hform : ∀ i x y, σ i (S.h x y) = jForm p (Q i *ᵥ embVec (σ i) x) (Q i *ᵥ embVec (σ i) y))
    {N : ℕ} (eqv : Fin N ≃ ι × Fin r × Fin 2) (y v : Fin r → K) :
    rho eqv (Theta p (Phi σ Q y)) ⬝ᵥ rho eqv (Phi σ Q v) =
      (1 / 2 : ℝ) * ((Algebra.trace ℚ K (S.h y v) : ℚ) : ℝ) := by
  rw [rho_dot, ← sum_re_cmType σ hinj hcm (S.h y v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hform i y v, jForm, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Theta, Phi, map_mul, sgn_conj]
  ring_nf
end Formalism.L2.Pj.FundamentalDomainD5
