-- Prove2me | solution 1 for Formalism.REAL.shiftedGenerator_eq_smul_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:35:55.501574+00:00
-- url     : https://prove2.me/submissions/18e9ceea-bcdd-47a0-8f9b-4b97f7d5f679

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (r : ℂ)
    (p q : Fin n) : Tm E r p q = (if p = q then r else 0) • (1 : A) + E p q := by
  unfold Tm
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]
end Formalism.REAL
