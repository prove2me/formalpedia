-- Prove2me | solution 1 for Formalism.L2.G.Model.sw_coeff_euler
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:56.647572+00:00
-- url     : https://prove2.me/submissions/29fc59cf-9420-4faa-ae05-cad3dd5cebf6

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowDivZero
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LGradedLemmas
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_SwRowGenMonomial
import Theorems.Thm_Formalism_L2_G_Model_sw_euler_monomial
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
theorem _root_.solution (R : Type) [CommRing R] {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) R)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv R a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : R) * coeff m f := by
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [sw_euler_monomial, coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h; rfl
    · simp
  | add p q hp hq => rw [rowDiv_add, coeff_add, coeff_add, hp, hq, mul_add]
end Formalism.L2.G.Model
