-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.divisor_closed_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:01.135815+00:00
-- url     : https://prove2.me/submissions/4e1d0198-cf0e-4bcf-a651-379d53370e61

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivisorClosedHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_map_genAct
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_ColDictValCPf_eval_push__3947714a735e
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_famAct_elem
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_isUnit_one_add_elem
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
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution : DivClosedOf := by
  intro hDens ι _ _ n G hGd M hM τ a b k P hP
  by_contra hnot
  obtain ⟨φ, hφP, hφM⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ0 : ∀ Q ∈ M, φ Q = 0 := by
    intro Q hQ
    have : φ Q ∈ M.map φ := Submodule.mem_map_of_mem hQ
    rw [hφM] at this
    exact (Submodule.mem_bot ℂ).mp this
  set p := pushφ φ (genAct τ P) with hp
  have hval : ∀ g : Matrix (Fin n) (Fin n) ℂ,
      eval (fun x => g x.1 x.2) p = φ (famAct (Function.update (fun _ => 1) τ g) P) := by
    intro g; rw [hp, eval_pushφ, map_genAct]

  have hU : ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G τ * g = G τ → eval (fun x => g x.1 x.2) p = 0 := by
    intro g hg
    rw [hval]
    apply hφ0
    apply hM _ _ P hP
    intro σ
    by_cases hσ : σ = τ
    · subst hσ; simpa using hg
    · simp [hσ]
  have hall : ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit (1 + g).det → eval (fun x => g x.1 x.2) p = 0 := by
    rcases hGd τ with hpd | hpd
    · exact hDens n (G τ) hpd p hU
    · refine hDens n (-G τ) hpd p fun g hg => hU g ?_
      have := congrArg Neg.neg hg
      simpa [Matrix.mul_neg, Matrix.neg_mul] using this

  set q := bigGen τ a b P with hq
  set r : Polynomial ℂ := q.sum fun j c => Polynomial.monomial j (φ c) with hr
  have hr_eval : ∀ t : ℂ, r.eval t = φ (q.eval (C t)) := by
    intro t
    rw [hr, Polynomial.sum_def, Polynomial.eval_finset_sum, Polynomial.eval_eq_sum (p := q), Polynomial.sum_def,
      map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Polynomial.eval_monomial, ← map_pow, mul_comm (q.coeff j), MvPolynomial.C_mul', map_smul, smul_eq_mul,
      mul_comm]
  have hr0 : r = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ)) Nat.cast_injective
    intro m
    show r.eval (m : ℂ) = 0
    rw [hr_eval, ← famAct_elem, ← hval]
    exact hall _ (isUnit_one_add_elem a b m)
  have hcoeff : r.coeff k = φ (bigDiv τ a b k P) := by
    rw [hr, Polynomial.sum_def, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single k (fun j _ hj => if_neg hj) (fun hk => by
      rw [if_pos rfl, Polynomial.notMem_support_iff.mp hk, map_zero])]
    rw [if_pos rfl]
    rfl
  apply hφP
  rw [← hcoeff, hr0, Polynomial.coeff_zero]
end Formalism.L2.SG.Pf.ColDictValCPf
