-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldbasis_initMinor_rowHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:23.574923+00:00
-- url     : https://prove2.me/submissions/01e95f05-7e23-420c-b115-b331d7fe07df

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldbasis_sum_single_perm
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hprod : IsWeightedHomogeneous (rowW r n)
      (∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (∑ p, Pi.single (I p) 1) := by
    rw [← ldbasis_sum_single_perm I σ]
    exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R (rowW r n) _)
  intro d hd
  apply hprod
  intro h0
  apply hd
  show coeff d ((Equiv.Perm.sign σ) •
    ∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) = 0
  rw [Units.smul_def, coeff_smul, h0, smul_zero]
end Formalism.GradedWeylDivisibility
