-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lehwShift_rowGen_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:19.523011+00:00
-- url     : https://prove2.me/submissions/8b0a5cd5-45ff-4549-8e4d-54b0eb7bce0c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwlineLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_lehwShift_gen
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
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
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LehwShift w (rowGen R a b (monomial d c)) (Finsupp.weight w d) δ := by
  unfold rowGen
  rw [MvPolynomial.aeval_monomial, Finsupp.weight_apply]
  have h := lehwShift_mul (lehwShift_algebraMap (R := R) w c δ)
    (lehwShift_prod d.support _ (fun v => d v • w v) δ
      (fun v _ => lehwShift_pow (lehwShift_gen (R := R) w δ a b hstep v) (d v)))
  simpa [Finsupp.prod, Finsupp.sum] using h
end Formalism.GradedWeylDivisibility
