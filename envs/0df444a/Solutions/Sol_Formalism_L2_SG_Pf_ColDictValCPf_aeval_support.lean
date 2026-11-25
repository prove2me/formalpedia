-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.aeval_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:42.600415+00:00
-- url     : https://prove2.me/submissions/0f70b5ac-12af-44b8-a7f6-ab219e684cd8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_aeval_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (P : MvPolynomial σ ℂ) (j : ℕ) (m' : σ →₀ ℕ)
    (h : coeff m' ((aeval f P).coeff j) ≠ 0) :
    ∃ m, coeff m P ≠ 0 ∧ Finsupp.weight w m' + j * c = Finsupp.weight w m := by
  rw [P.as_sum, map_sum, Polynomial.finsetSum_coeff, coeff_sum] at h
  obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨m, mem_support_iff.mp hm, tgood_aeval_monomial w c f hf m _ j m' hm0⟩
end Formalism.L2.SG.Pf.ColDictValCPf
