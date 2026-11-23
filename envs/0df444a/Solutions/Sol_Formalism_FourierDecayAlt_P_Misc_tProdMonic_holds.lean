-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Misc.tProdMonic_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:58.96701+00:00
-- url     : https://prove2.me/submissions/7f6fd660-f319-41f5-829a-8e4b0853268f

import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferProductMonic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Misc_tpolyProd_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Misc
open Formalism.FourierDecayAlt.I Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Misc
theorem _root_.solution : TProdMonic := by
  intro A _ _ n p c ci
  induction n with
  | zero => simp [TpolyProd]
  | succ n ih =>
    obtain ⟨hm, hd, hb⟩ := ih
    have e00 : TpolyProd (n + 1) p c ci 0 0 =
        (X + C (p (n + 1))) * TpolyProd n p c ci 0 0 - C (c (n + 1)) * TpolyProd n p c ci 1 0 := by
      rw [tpolyProd_succ]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two, sub_eq_add_neg]
    have e10 : TpolyProd (n + 1) p c ci 1 0 = C (ci (n + 1)) * TpolyProd n p c ci 0 0 := by
      rw [tpolyProd_succ]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two]
    have hXm : (X + C (p (n + 1)) : A[X]).Monic := monic_X_add_C _
    have hprod : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).Monic := hXm.mul hm
    have hpd : ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).natDegree = n + 1 := by
      rw [hXm.natDegree_mul hm, natDegree_X_add_C, hd]; ring
    have hlow : (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree <
        ((X + C (p (n + 1))) * TpolyProd n p c ci 0 0).degree := by
      rw [degree_eq_natDegree hprod.ne_zero, hpd]
      calc (C (c (n + 1)) * TpolyProd n p c ci 1 0).degree
          ≤ (C (c (n + 1))).degree + (TpolyProd n p c ci 1 0).degree := degree_mul_le _ _
        _ ≤ 0 + (TpolyProd n p c ci 1 0).degree := by gcongr; exact degree_C_le
        _ < (n : WithBot ℕ) := by simpa using hb
        _ ≤ ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.le_succ n
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; exact hprod.sub_of_left hlow
    · rw [e00]; exact (natDegree_eq_of_degree_eq (degree_sub_eq_left_of_degree_lt hlow)).trans hpd
    · rw [e10]
      calc (C (ci (n + 1)) * TpolyProd n p c ci 0 0).degree
          ≤ (C (ci (n + 1))).degree + (TpolyProd n p c ci 0 0).degree := degree_mul_le _ _
        _ ≤ 0 + (TpolyProd n p c ci 0 0).degree := by gcongr; exact degree_C_le
        _ = (n : WithBot ℕ) := by rw [zero_add, degree_eq_natDegree hm.ne_zero, hd]
        _ < ((n + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self n
end Formalism.FourierDecayAlt.P.Misc
