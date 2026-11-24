-- Prove2me | solution 1 for Formalism.REAL.height_operator_weight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:35:01.235041+00:00
-- url     : https://prove2.me/submissions/a70f85c6-4dc5-4d00-a0ea-46da74512d68

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution {ν : Fin n → ℝ} {y : V} (hy : IsWeight F ν y) :
    heightOperator F y = ((heightFunctional ν : ℝ) : ℂ) • y := by
  rw [heightOperator, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, show ∀ a, F a a y = ((ν a : ℝ) : ℂ) • y from hy, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  simp [heightFunctional]
end Formalism.REAL
