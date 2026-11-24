-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.dco_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:42:14.935925+00:00
-- url     : https://prove2.me/submissions/18dc47cf-f544-45c8-8799-cbb7795d1226

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_coef
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_coef

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
theorem _root_.solution {x : Fin m → ℂ} (hx : x ∈ OmX m) (l k : Fin m) (i j : Fin 6)
    (hc : l ≠ k ∨ (holoIdx i ↔ ¬ holoIdx j)) : dco l i k j x = 0 := by
  match i with
  | 0 =>
    show wirt l (coef k j) x = 0
    rw [wirt_coef hx, if_neg]
    rintro ⟨hj, hlk⟩
    rcases hc with h | h
    · exact h hlk
    · exact (h.mp (show holoIdx (0 : Fin 6) by unfold holoIdx; decide)) hj
  | 3 =>
    show wirtBar l (coef k j) x = 0
    rw [wirtBar_coef hx, if_neg]
    rintro ⟨hj, hlk⟩
    rcases hc with h | h
    · exact h hlk
    · exact absurd (h.mpr hj) (show ¬ holoIdx (3 : Fin 6) by unfold holoIdx; decide)
  | 1 => rfl
  | 2 => rfl
  | 4 => rfl
  | 5 => rfl
end Formalism.QuantumDeterminants.WirtingerDerivatives
