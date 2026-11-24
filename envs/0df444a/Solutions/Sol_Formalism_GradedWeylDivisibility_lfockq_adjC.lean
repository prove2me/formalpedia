-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_adjC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:45.325619+00:00
-- url     : https://prove2.me/submissions/a7b13333-043d-488e-af7e-dd8bb3e428f1

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_mat_conjTranspose
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_eval_rowGen
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_fockF_eval_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_fockF_eval_right
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_rowAct_eq_sub
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_rowMat_conjTranspose
import Theorems.Thm_Formalism_GradedWeylDivisibility_LFocks_subAdj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (a b : Fin r) (k : ℕ) (F G : MvPolynomial (Fin r × Fin n) ℂ) :
    fockF (rowDiv ℂ a b k F) G = fockF F (rowDiv ℂ b a k G) := by
  classical
  set N := max (max (rowGen ℂ a b F).natDegree (rowGen ℂ b a G).natDegree) k + 1 with hNdef
  have h1 : (rowGen ℂ a b F).natDegree < N := by omega
  have h2 : (rowGen ℂ b a G).natDegree < N := by omega
  have hk : k < N := by omega
  have key : ∀ t : ℂ, ∑ i ∈ Finset.range N, t ^ i * fockF ((rowGen ℂ a b F).coeff i) G =
      ∑ i ∈ Finset.range N, t ^ i * fockF F ((rowGen ℂ b a G).coeff i) := by
    intro t
    have hadj : fockF (rowAct ℂ (lfockq_mat a b t) F) G =
        fockF F (rowAct ℂ (lfockq_mat a b t).conjTranspose G) := by
      rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]
    rw [lfockq_mat_conjTranspose, ← lfockq_eval_rowGen, ← lfockq_eval_rowGen,
      lfockq_fockF_eval_left _ N h1, lfockq_fockF_eval_right _ N h2] at hadj
    rw [hadj]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_pow, star_star]
  let p : Polynomial ℂ := ∑ i ∈ Finset.range N,
    Polynomial.C (fockF ((rowGen ℂ a b F).coeff i) G) * Polynomial.X ^ i
  let q : Polynomial ℂ := ∑ i ∈ Finset.range N,
    Polynomial.C (fockF F ((rowGen ℂ b a G).coeff i)) * Polynomial.X ^ i
  have hpq : p = q := by
    apply Polynomial.funext
    intro t
    simp only [p, q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    calc _ = ∑ i ∈ Finset.range N, t ^ i * fockF ((rowGen ℂ a b F).coeff i) G :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∑ i ∈ Finset.range N, t ^ i * fockF F ((rowGen ℂ b a G).coeff i) := key t
      _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hc := congrArg (fun s : Polynomial ℂ => s.coeff k) hpq
  simp only [p, q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow] at hc
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq] at hc
  simpa [rowDiv, Finset.mem_range.mpr hk] using hc
end Formalism.GradedWeylDivisibility
