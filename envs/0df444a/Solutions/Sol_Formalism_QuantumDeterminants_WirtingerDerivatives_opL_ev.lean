-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.opL_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:13.969632+00:00
-- url     : https://prove2.me/submissions/24fe9361-e042-442f-8bab-caf4af2bbb58

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_isOpen_omX

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
theorem _root_.solution (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    opL k j g =ᶠ[𝓝 x] fun y => coef k j y • Dop k j g y := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ OmX m := (isOpen_omX m).mem_nhds hx
  match j with
  | 0 =>
    filter_upwards [hev] with y hy
    show pOp k g y = y k • wirt k g y
    simp [pOp, hy]
  | 1 => exact Filter.Eventually.of_forall fun y => rfl
  | 2 => exact Filter.Eventually.of_forall fun y => rfl
  | 3 =>
    filter_upwards [hev] with y hy
    show pbOp k g y = star (y k) • wirtBar k g y
    simp [pbOp, hy]
  | 4 => exact Filter.Eventually.of_forall fun y => rfl
  | 5 => exact Filter.Eventually.of_forall fun y => rfl
end Formalism.QuantumDeterminants.WirtingerDerivatives
