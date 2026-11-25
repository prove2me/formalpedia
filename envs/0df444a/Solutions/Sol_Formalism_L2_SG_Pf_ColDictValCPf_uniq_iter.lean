-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.uniq_iter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:06.012547+00:00
-- url     : https://prove2.me/submissions/9fa5fda9-f910-4f12-b074-85622fa7b65f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_uniq_block
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (lam : ι → DomWeight n) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : Q ∈ CSpanV lam)
    (hk : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0) (s : Finset ι) :
    ∀ x : ι × Fin n × Fin n → ℂ, eval x Q =
      (∏ τ ∈ s, eval (fun p => x (τ, p)) (extremal ℂ n (lam τ))) *
        eval (fun v => if v.1 ∈ s then idPoint ℂ n n v.2 else x v) Q := by
  induction s using Finset.induction_on with
  | empty => intro x; simp
  | @insert τ s hτ ih =>
    intro x
    have hb : eval (fun v : ι × Fin n × Fin n => if v.1 ∈ s then idPoint ℂ n n v.2 else x v) Q =
        eval (fun p => x (τ, p)) (extremal ℂ n (lam τ)) *
          eval (fun v : ι × Fin n × Fin n => if v.1 ∈ insert τ s then idPoint ℂ n n v.2 else x v) Q := by
      convert (uniq_block lam Q hQ hk τ (fun v => if v.1 ∈ s then idPoint ℂ n n v.2 else x v)) using 4
      · funext p; simp [hτ]
      · funext v; by_cases h1 : v.1 = τ <;> simp [h1]
    rw [ih x, hb, Finset.prod_insert hτ]
    ring
end Formalism.L2.SG.Pf.ColDictValCPf
