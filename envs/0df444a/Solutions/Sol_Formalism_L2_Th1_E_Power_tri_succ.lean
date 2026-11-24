-- Prove2me | solution 1 for Formalism.L2.Th1.E.Power.tri_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:23:55.884955+00:00
-- url     : https://prove2.me/submissions/c9951d67-7dba-4752-a45d-588c5c1515da

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ScaledXEqOffOrigin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Power
variable {R : Type} [CommRing R] [IsDomain R]
namespace Formalism.L2.Th1.E.Power
theorem _root_.solution (φ : ℕ → R) (m : ℕ) :
    ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m + 1 - j) =
      (∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j)) * ∏ j ∈ Finset.range (m + 1), φ (j + 1) := by
  have h1 : ∏ j ∈ Finset.range m, φ (j + 1) ^ (m - j) =
      ∏ j ∈ Finset.range (m + 1), φ (j + 1) ^ (m - j) := by
    rw [Finset.prod_range_succ]; simp
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← pow_succ]
  congr 1
  omega
end Formalism.L2.Th1.E.Power
