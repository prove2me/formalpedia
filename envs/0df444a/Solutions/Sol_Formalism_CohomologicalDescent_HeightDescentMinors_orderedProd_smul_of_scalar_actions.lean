-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.orderedProd_smul_of_scalar_actions
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:45.977806+00:00
-- url     : https://prove2.me/submissions/600701fc-9cdb-4fb6-81dc-7f10ab7886a2

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
theorem _root_.solution (v : V) : ∀ (N : ℕ) (f : Fin N → 𝒰) (c : Fin N → k),
    (∀ j, f j • v = c j • v) → (List.ofFn f).prod • v = (∏ j, c j) • v := by
  intro N
  induction N with
  | zero =>
    intro f c _
    simp
  | succ N ih =>
    intro f c h
    rw [List.ofFn_succ, List.prod_cons, mul_smul,
      ih (fun j => f j.succ) (fun j => c j.succ) (fun j => h j.succ), Fin.prod_univ_succ]
    rw [← algebraMap_smul 𝒰 (∏ j : Fin N, c j.succ) v, ← mul_smul, ← Algebra.commutes, mul_smul, h 0,
      algebraMap_smul, smul_smul, mul_comm]
end Formalism.CohomologicalDescent.HeightDescentMinors
