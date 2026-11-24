-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.Pmin_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:05:59.04381+00:00
-- url     : https://prove2.me/submissions/e892f493-2c5f-40a0-ae87-17c3592abf72

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_map
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_mem_harmK
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_rowInv
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_rowDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (O : Subring k) (cc : T → T) (isX : T → Prop) (hcc : ∀ τ, isX τ → cc τ ≠ τ)
    (hβ : Function.Injective β) (ha : Dom r a) :
    MvPolynomial.map (Int.castRingHom k) (Pmin r n β a) ∈ HaO r n k O cc isX a := by
  unfold HaO HHa
  refine ⟨?_, fun m => ?_⟩
  · rw [crP_map]
    exact ⟨crP_mem_harmK k β a cc isX hcc hβ, crP_rowInv k β a, crP_rowDeg k β a ha⟩
  · rw [coeff_map, eq_intCast]
    exact intCast_mem O _
end Formalism.L2.Pj.Crude
