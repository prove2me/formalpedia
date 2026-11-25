-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.uniq_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:10.040284+00:00
-- url     : https://prove2.me/submissions/4ae89e92-8556-491b-9d60-044127e6e38d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_natW_anti_v
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_delSq_le_dual
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_hw_id
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_eval_sl
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_sl_mem
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_rowDiv_sl
import Theorems.Thm_Formalism_GradedWeylDivisibility_highest_weight_line


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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution (lam : ι → DomWeight n) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : Q ∈ CSpanV lam)
    (hk : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0) (τ₀ : ι)
    (x : ι × Fin n × Fin n → ℂ) :
    eval x Q = eval (fun p => x (τ₀, p)) (extremal ℂ n (lam τ₀)) *
      eval (fun v => if v.1 = τ₀ then idPoint ℂ n n v.2 else x v) Q := by
  obtain ⟨c, hc⟩ := highest_weight_line ℂ n n le_rfl (lam τ₀).natW (natW_anti_v _) (sl τ₀ x Q)
    (delSq_le_dual _ (sl_mem lam τ₀ x hQ))
    (fun a b hab k hk1 => by rw [rowDiv_sl, hk τ₀ a b hab k hk1, map_zero])
  have h1 := congrArg (eval (fun p => x (τ₀, p))) hc
  have h2 := congrArg (eval (idPoint ℂ n n)) hc
  rw [eval_sl, smul_eval] at h1 h2
  rw [eval_hw_id, mul_one] at h2
  have hx : (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then x (τ₀, v.2) else x v) = x := by
    funext v
    split_ifs with h
    · rw [← h]
    · rfl
  rw [hx] at h1
  rw [h1, ← h2, mul_comm]
  rfl
end Formalism.L2.SG.Pf.ColDictValCPf
