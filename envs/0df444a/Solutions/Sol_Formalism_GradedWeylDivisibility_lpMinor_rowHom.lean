-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lpMinor_rowHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:57.487013+00:00
-- url     : https://prove2.me/submissions/d469ba51-e357-4233-bc2e-84b1519cb691

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_hwrow_sum_single_castLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GradedWeylDivisibility
open MvPolynomial
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (R : Type*) [CommRing R] {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (lpMinor R s hr hn)
      (fun a => if a.val < s then 1 else 0) := by
  unfold lpMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hk : IsWeightedHomogeneous (rowW r n)
      (∏ i, (Matrix.of fun p q : Fin s =>
        (X (Fin.castLE hr p, Fin.castLE hn q) : MvPolynomial (Fin r × Fin n) R)) (σ i) i)
      (fun a : Fin r => if a.val < s then 1 else 0) := by
    rw [← hwrow_sum_single_castLE hr σ]
    apply IsWeightedHomogeneous.prod
    intro i _
    simp only [Matrix.of_apply]
    exact isWeightedHomogeneous_X R (rowW r n) _
  rw [← mem_weightedHomogeneousSubmodule] at hk ⊢
  rw [Units.smul_def]
  exact zsmul_mem hk _
end Formalism.GradedWeylDivisibility
