-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg.coeff_all
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:28:53.237122+00:00
-- url     : https://prove2.me/submissions/f459797a-2761-4b95-af87-19ed68911b9b

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.GroupTheory.Perm.Support
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTRTopActAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_TopAlg_natDegree_prodP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
open Formalism.REAL
open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
variable {A : Type*} [Ring A] [Algebra ℂ A]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
theorem _root_.solution : ∀ {m : ℕ} (B : Fin m → A),
    (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff m = 1 ∧
      (1 ≤ m → (List.ofFn fun l => (X + C (B l) : A[X])).prod.coeff (m - 1) = ∑ l, B l)
  | 0, B => by simp
  | m + 1, B => by
    have ih := solution (fun l : Fin m => B l.succ)
    have hdeg : (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod.natDegree ≤ m := by
      have := natDegree_prodP (fun _ : Fin m => True) (fun l => B l.succ)
      simp only [if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at this
      simpa [prodP, fac] using this
    rw [List.ofFn_succ, List.prod_cons]
    set Q := (List.ofFn fun l : Fin m => (X + C (B l.succ) : A[X])).prod with hQ
    refine ⟨?_, fun _ => ?_⟩
    · rw [add_mul, coeff_add, coeff_X_mul, ih.1, coeff_C_mul,
        coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < m + 1), mul_zero, add_zero]
    · rw [Fin.sum_univ_succ, add_mul, coeff_add, coeff_C_mul, Nat.add_sub_cancel, ih.1, mul_one]
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        simp
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [coeff_X_mul, add_comm]
        congr 1
        have := ih.2 (by omega)
        simpa using this
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.TopAlg
