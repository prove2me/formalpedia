-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.bigDiv_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:29.207805+00:00
-- url     : https://prove2.me/submissions/098de538-15da-4a2e-82fe-38d5dacc2316

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_aeval_support
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_gen

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
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (hab : a < b) (k : ℕ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (m' : ι × Fin n × Fin n →₀ ℕ)
    (h : coeff m' (bigDiv τ a b k P) ≠ 0) :
    ∃ m, coeff m P ≠ 0 ∧ Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m' + k * ((b : ℕ) - a)
      = Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m :=
  aeval_support _ _ _ (tgood_gen τ a b hab) P k m' h
end Formalism.L2.SG.Pf.ColDictValCPf
