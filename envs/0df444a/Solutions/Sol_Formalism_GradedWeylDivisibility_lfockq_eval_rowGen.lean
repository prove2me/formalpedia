-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_eval_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:16.890723+00:00
-- url     : https://prove2.me/submissions/b2fbf5bf-cdbf-4477-b20b-0c2b41135f28

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj

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
theorem _root_.solution {r n : ℕ} (a b : Fin r) (t : ℂ) (f : MvPolynomial (Fin r × Fin n) ℂ) :
    Polynomial.eval (C t) (rowGen ℂ a b f) = rowAct ℂ (lfockq_mat a b t) f := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp [rowGen, rowAct]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, hp, hq, map_add]
  | mul_X p v hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    rcases v with ⟨i, j⟩
    simp only [rowGen, rowAct, MvPolynomial.aeval_X, lfockq_mat]
    by_cases hv : i = b
    · subst hv
      simp [add_mul, Finset.sum_add_distrib, apply_ite (C : ℂ → MvPolynomial (Fin r × Fin n) ℂ),
        ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
      exact mul_comm _ _
    · simp [hv, add_mul, Finset.sum_add_distrib, apply_ite (C : ℂ → MvPolynomial (Fin r × Fin n) ℂ),
        ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']
end Formalism.GradedWeylDivisibility
