-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldiag_aeval_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:31.874816+00:00
-- url     : https://prove2.me/submissions/3005fb5b-ccdf-4358-bf23-a8c471ac2dea

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DomPow
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockDiagBound
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldiag_prod_rowDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open Formalism.REAL (fockF)
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (t : Fin r → ℂ) (u : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    aeval (fun v : Fin r × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin r, t a ^ rowDeg u a) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, ← ldiag_prod_rowDeg,
    MvPolynomial.algebraMap_eq, MvPolynomial.C_mul]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  ring
end Formalism.GradedWeylDivisibility
