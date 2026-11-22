-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.bnd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:03.726198+00:00
-- url     : https://prove2.me/submissions/91a23a79-cb44-451d-8ede-bd3234e18cf0

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℚ_[p]) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ s, Bnd B (f i)) : Bnd B (∑ i ∈ s, f i) := by

  classical
  intro m
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, MvPolynomial.coeff_add]
    exact (Padic.nonarchimedean _ _).trans (max_le (h a (Finset.mem_insert_self _ _) m)
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
end Formalism.GM.M.PhiIntegrality
