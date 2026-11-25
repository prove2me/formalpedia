-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.Wc_hol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:19:17.297496+00:00
-- url     : https://prove2.me/submissions/46a1e888-c31d-45dc-8ae0-5dd5266de078

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open Filter
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.WirtingerDerivatives
variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants.WirtingerDerivatives
theorem _root_.solution (k l : Fin m) (c : ℂ) (T : (Fin m → ℂ) →L[ℝ] ℂ) (hT : ∀ v, T v = c * v k) :
    Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) T = (if l = k then c else 0) ∧
      Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I T = 0 := by
  refine ⟨?_, ?_⟩ <;> rw [Wc_apply, hT, hT] <;> by_cases hl : l = k
  · simp only [hl, Pi.single_eq_same, if_true, smul_eq_mul]
    linear_combination (-c / 2) * Complex.I_sq
  · simp [hl, Pi.single_eq_of_ne (Ne.symm hl)]
  · simp only [hl, Pi.single_eq_same, smul_eq_mul]
    linear_combination (c / 2) * Complex.I_sq
  · simp [Pi.single_eq_of_ne (Ne.symm hl)]
end Formalism.QuantumDeterminants.WirtingerDerivatives
