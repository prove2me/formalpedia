-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.orderedProd_smul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:01.579126+00:00
-- url     : https://prove2.me/submissions/c48306f2-76ab-42f0-bea3-d8fa8e2af90c

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_orderedProd_smul_of_scalar_actions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {k : Type} [CommRing k] {𝒰 : Type} [Ring 𝒰] [Algebra k 𝒰] {V : Type} [AddCommGroup V]
  [Module k V] [Module 𝒰 V] [IsScalarTower k 𝒰 V]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (v : V) : ∀ (N : ℕ) (f : Fin N → 𝒰) (c : Fin N → k) (j0 : Fin N),
    f j0 • v = 0 → (∀ j, j0 < j → f j • v = c j • v) → (List.ofFn f).prod • v = 0 := by
  intro N
  induction N with
  | zero =>
    intro f c j0
    exact j0.elim0
  | succ N ih =>
    intro f c j0 h0 hlater
    rw [List.ofFn_succ, List.prod_cons, mul_smul]
    rcases Fin.eq_zero_or_eq_succ j0 with rfl | ⟨j', rfl⟩
    · rw [orderedProd_smul_of_scalar_actions v N (fun j => f j.succ) (fun j => c j.succ)
        (fun j => hlater j.succ (Fin.succ_pos j))]
      rw [← algebraMap_smul 𝒰 _ v, ← mul_smul, ← Algebra.commutes, mul_smul, h0, smul_zero]
    · rw [ih (fun j => f j.succ) (fun j => c j.succ) j' h0
        (fun j hj => hlater j.succ (Fin.succ_lt_succ_iff.mpr hj)), smul_zero]
end Formalism.CohomologicalDescent.HeightDescentMinors
