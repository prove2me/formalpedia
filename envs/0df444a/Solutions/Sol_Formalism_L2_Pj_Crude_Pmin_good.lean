-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.Pmin_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:47.409237+00:00
-- url     : https://prove2.me/submissions/57b8da9b-3ba0-421e-a6b5-aa2dd36e1779

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_map
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_mem_supported

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
theorem _root_.solution (m : Letter T r n →₀ ℕ) (hm : m ∈ (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).support)
    (ℓ : Letter T r n) (hℓ : m ℓ ≠ 0) : ℓ ∈ GoodL r n β := by
  rw [crP_map] at hm
  have h1 := crP_mem_supported k β a
  rw [mem_supported] at h1
  exact h1 ((mem_vars ℓ).mpr ⟨m, hm, Finsupp.mem_support_iff.mpr hℓ⟩)
end Formalism.L2.Pj.Crude
