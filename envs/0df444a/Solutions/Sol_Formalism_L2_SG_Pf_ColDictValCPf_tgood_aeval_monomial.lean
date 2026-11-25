-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.tgood_aeval_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:09:34.826214+00:00
-- url     : https://prove2.me/submissions/04d1dbae-5bd8-4a6e-9966-18dbd4e7780d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_CC
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_mul
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_pow
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tgood_prod
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
variable {σ : Type*}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (w : σ → ℕ) (c : ℕ) (f : σ → Polynomial (MvPolynomial σ ℂ))
    (hf : ∀ v, TGood w c (w v) (f v)) (m : σ →₀ ℕ) (r : ℂ) :
    TGood w c (Finsupp.weight w m) (aeval f (monomial m r)) := by
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, Polynomial.algebraMap_apply,
    MvPolynomial.algebraMap_eq]
  have h1 := tgood_CC w c r
  have h2 := tgood_prod w c m.support (fun i => m i • w i) (fun i => f i ^ m i)
    (fun i _ => by simpa only [smul_eq_mul] using tgood_pow w c (hf i) (m i))
  have := tgood_mul w c h1 h2
  rwa [zero_add] at this
end Formalism.L2.SG.Pf.ColDictValCPf
