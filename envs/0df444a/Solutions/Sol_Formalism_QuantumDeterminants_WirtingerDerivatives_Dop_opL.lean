-- Prove2me | solution 1 for Formalism.QuantumDeterminants.WirtingerDerivatives.Dop_opL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:12:33.582212+00:00
-- url     : https://prove2.me/submissions/014a1a3b-6e39-49ee-a91b-d262658de7b9

import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirt_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_wirtBar_eq
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_diff_of_reg
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_Wc_smul
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_coef_contDiffAt
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_ev
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_opL_on
import Theorems.Thm_Formalism_QuantumDeterminants_WirtingerDerivatives_reg_Dop

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
    (l k : Fin m) (i j : Fin 6) :
    Dop l i (opL k j g) x = dco l i k j x • Dop k j g x + coef k j x • Dop l i (Dop k j g) x := by
  have hc := diff_of_reg (coef_contDiffAt (k := k) hx j)
  have hd := diff_of_reg (reg_Dop hg k j x hx)
  have hfe : fderiv ℝ (opL k j g) x = fderiv ℝ (fun y => coef k j y • Dop k j g y) x :=
    (opL_ev k j g hx).fderiv_eq
  match i with
  | 0 =>
    show wirt l (opL k j g) x = wirt l (coef k j) x • Dop k j g x + coef k j x • wirt l (Dop k j g) x
    rw [wirt_eq, wirt_eq, wirt_eq, hfe, Wc_smul hc hd]
  | 1 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
  | 2 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
  | 3 =>
    show wirtBar l (opL k j g) x =
      wirtBar l (coef k j) x • Dop k j g x + coef k j x • wirtBar l (Dop k j g) x
    rw [wirtBar_eq, wirtBar_eq, wirtBar_eq, hfe, Wc_smul hc hd]
  | 4 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
  | 5 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
end Formalism.QuantumDeterminants.WirtingerDerivatives
