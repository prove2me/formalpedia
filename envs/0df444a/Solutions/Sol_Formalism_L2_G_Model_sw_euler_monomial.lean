-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_euler_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:42.205898+00:00
-- url     : https://prove2.me/submissions/50407dff-db27-47b2-807c-dfd7f537b06c

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_rowGen_monomial
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model
open Formalism.GradedWeylDivisibility
namespace Formalism.L2.G.Model
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    rowDiv R a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) • monomial m c := by
  rw [rowDiv, sw_rowGen_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow,
    Nat.choose_one_right, smul_eq_C_mul, mul_comm]
  simp
end Formalism.L2.G.Model
