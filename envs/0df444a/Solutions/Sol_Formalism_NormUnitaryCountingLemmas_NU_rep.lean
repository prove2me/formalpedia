-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NU.rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:15.675872+00:00
-- url     : https://prove2.me/submissions/e5f13a34-6c3e-40ad-bb74-7d062bb6657d

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormUnitary
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_coeff_P
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NU_card_fib

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas Formalism.NormUnitaryCountingLemmas.NU
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
namespace Formalism.NormUnitaryCountingLemmas.NU
theorem _root_.solution {d : ℕ} (F : MvPolynomial σ ℂ) (hF : ∀ e ∈ F.support, ∑ i, e i = d) :
    P (T d F) = F := by
  ext e
  rw [coeff_P]
  have hsum : (∑ t : Fin d → σ, if cnt t = e then T d F t else 0)
      = ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) *
        (coeff e F * fct e / d.factorial) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_congr rfl (g := fun _ => coeff e F * fct e / d.factorial)]
    · simp
    · intro t ht
      simp only [T, (Finset.mem_filter.1 ht).2]
  rw [hsum]
  by_cases he : ∑ i, e i = d
  · have hc := card_fib e he
    have hc' : ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) * (fct e : ℂ) =
        d.factorial := by exact_mod_cast hc
    have hd : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
    calc ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) *
          (coeff e F * fct e / d.factorial)
        = coeff e F * (((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) * (fct e : ℂ))
          / d.factorial := by ring
      _ = coeff e F := by rw [hc', mul_div_assoc, div_self hd, mul_one]
  · have hz : coeff e F = 0 := by
      by_contra h
      exact he (hF e (mem_support_iff.2 h))
    simp [hz]
end Formalism.NormUnitaryCountingLemmas.NU
