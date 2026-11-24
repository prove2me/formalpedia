-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.Dop_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:12:10.632406+00:00
-- url     : https://prove2.me/submissions/604d3cee-5141-42c1-b29a-096f6c9b0668

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_comm
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_fun
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_fun

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
theorem _root_.solution {g : (Fin m → ℂ) → E} (hg : Reg g) {x : Fin m → ℂ} (hx : x ∈ OmX m)
    (l k : Fin m) (i j : Fin 6) : Dop l i (Dop k j g) x = Dop k j (Dop l i g) x := by
  match i with
  | 0 =>
    match j with
    | 0 =>
      show wirt l (wirt k g) x = wirt k (wirt l g) x
      rw [wirt_fun k g, wirt_fun l g, wirt_eq l, wirt_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 3 =>
      show wirt l (wirtBar k g) x = wirtBar k (wirt l g) x
      rw [wirtBar_fun k g, wirt_fun l g, wirt_eq l, wirtBar_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 1 => rfl
    | 2 => rfl
    | 4 => rfl
    | 5 => rfl
  | 3 =>
    match j with
    | 0 =>
      show wirtBar l (wirt k g) x = wirt k (wirtBar l g) x
      rw [wirt_fun k g, wirtBar_fun l g, wirtBar_eq l, wirt_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 3 =>
      show wirtBar l (wirtBar k g) x = wirtBar k (wirtBar l g) x
      rw [wirtBar_fun k g, wirtBar_fun l g, wirtBar_eq l, wirtBar_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 1 => rfl
    | 2 => rfl
    | 4 => rfl
    | 5 => rfl
  | 1 => rfl
  | 2 => rfl
  | 4 => rfl
  | 5 => rfl
end Formalism.QuantumDeterminants.WirtingerDerivatives
