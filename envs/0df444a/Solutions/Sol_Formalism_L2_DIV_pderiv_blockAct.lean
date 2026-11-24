-- Prove2me | solution 1 for Formalism.L2.DIV.pderiv_blockAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:09:03.43658+00:00
-- url     : https://prove2.me/submissions/42ae2827-07c6-4542-9d72-0650d3bc7d18

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_blockAct_X
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
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K]
variable {ι : Type} [Fintype ι] {n : ℕ}
omit [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution [DecidableEq ι] (V : ι → Matrix (Fin n) (Fin n) K) (s : ι) (a t : Fin n) (g : Pol K ι n) :
    pderiv (s, (a, t)) (Formalism.GradedWeylDivisibility.blockAct K V g) =
      ∑ b : Fin n, C (V s b a) * Formalism.GradedWeylDivisibility.blockAct K V (pderiv (s, (b, t)) g) := by
  induction g using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p k hp =>
    have hX : pderiv (s, (a, t)) (Formalism.GradedWeylDivisibility.blockAct K V (X k)) =
        if k.1 = s ∧ k.2.2 = t then C (V s k.2.1 a) else 0 := by
      rw [blockAct_X, map_sum]
      by_cases hk : k.1 = s ∧ k.2.2 = t
      · obtain ⟨h1, h2⟩ := hk
        subst h1; subst h2
        rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single a]
        · simp [pderiv_X]
        · intro b _ hb
          rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne (by
            intro h; exact hb (by simpa using congrArg (fun z : ι × Fin n × Fin n => z.2.1) h))]
          simp
        · simp
      · rw [if_neg hk]
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [Derivation.leibniz, pderiv_C, pderiv_X_of_ne (by
          intro h
          apply hk
          exact ⟨by simpa using congrArg (fun z : ι × Fin n × Fin n => z.1) h,
            by simpa using congrArg (fun z : ι × Fin n × Fin n => z.2.2) h⟩)]
        simp
    rw [map_mul, Derivation.leibniz, hX, hp, smul_eq_mul, smul_eq_mul]
    simp_rw [Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib]
    congr 1
    · by_cases hk : k.1 = s ∧ k.2.2 = t
      · obtain ⟨h1, h2⟩ := hk
        subst h1; subst h2
        rw [if_pos ⟨rfl, rfl⟩, Finset.sum_eq_single k.2.1]
        · rw [show ((k.1, (k.2.1, k.2.2)) : ι × Fin n × Fin n) = k from rfl, pderiv_X_self, map_one]; ring
        · intro b _ hb
          rw [pderiv_X_of_ne (by
            intro h; exact hb (by simpa using (congrArg (fun z : ι × Fin n × Fin n => z.2.1) h).symm))]
          simp
        · simp
      · rw [if_neg hk, mul_zero]
        symm
        refine Finset.sum_eq_zero fun b _ => ?_
        rw [pderiv_X_of_ne (by
          intro h
          apply hk
          exact ⟨by simpa using congrArg (fun z : ι × Fin n × Fin n => z.1) h,
            by simpa using congrArg (fun z : ι × Fin n × Fin n => z.2.2) h⟩)]
        simp
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
end Formalism.L2.DIV
