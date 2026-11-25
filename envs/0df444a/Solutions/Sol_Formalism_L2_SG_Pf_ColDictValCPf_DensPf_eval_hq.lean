-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.DensPf.eval_hq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:07.418807+00:00
-- url     : https://prove2.me/submissions/8c2c3ea9-9c9e-4e94-bdb1-496b1531c597

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_CayleyIsometry
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_DensPf_eval_dp
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
open Matrix MvPolynomial
open scoped ComplexOrder
open Formalism.L2.SG.Pf.ColDictValCPf.DensPf
variable {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf.DensPf
theorem _root_.solution (G : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ)
    (z : Bool × Fin n × Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : (eval z).mapMatrix (Lp G) = A)
    (hd : det (1 + A) ≠ 0) :
    eval z (hq G p) = det (1 + A) ^ p.totalDegree *
      eval (fun x => ((1 - A) * (1 + A)⁻¹) x.1 x.2) p := by
  have hMm : (eval z).mapMatrix (Mp G) = (1 - A) * adjugate (1 + A) := by
    rw [Mp, map_mul, map_sub, map_one, RingHom.map_adjugate, map_add, map_one, hA]
  have hM : ∀ i j, eval z (Mp G i j) = det (1 + A) * ((1 - A) * (1 + A)⁻¹) i j := by
    intro i j
    have h2 : (1 - A) * (1 + A)⁻¹ = (det (1 + A))⁻¹ • ((1 - A) * adjugate (1 + A)) := by
      rw [inv_def, Ring.inverse_eq_inv', Matrix.mul_smul]
    rw [h2, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul, ← hMm]
    rfl
  have hdz : eval z (dp G) = det (1 + A) := by rw [eval_dp, hA]
  rw [hq, map_sum]
  conv_rhs => rw [eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hdm => ?_
  simp only [map_mul, map_pow, map_prod, eval_C, hdz, hM, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hle : d.degree ≤ p.totalDegree := le_totalDegree hdm
  rw [← Finsupp.degree_eq_sum,
    show det (1 + A) ^ p.totalDegree = det (1 + A) ^ (p.totalDegree - d.degree) * det (1 + A) ^ d.degree by
      rw [← pow_add, Nat.sub_add_cancel hle]]
  ring
end Formalism.L2.SG.Pf.ColDictValCPf.DensPf
