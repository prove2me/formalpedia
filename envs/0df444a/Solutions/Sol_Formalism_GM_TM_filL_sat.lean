-- Prove2me | solution 1 for Formalism.GM.TM.filL_sat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:04.731084+00:00
-- url     : https://prove2.me/submissions/21967180-519c-41f8-a8a4-1a1f8e0b00c6

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_support_zpsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}
namespace Formalism.GM.TM
theorem _root_.solution (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (e : ℕ) (a : ℤ_[p]) (ha : a ≠ 0)
    (x : MvPolynomial σ ℚ_[p]) (hx : x ∈ L) (h : a • x ∈ filL L v e) : x ∈ filL L v e := by
  refine Submodule.mem_inf.mpr ⟨hx, ?_⟩
  have h2 := (Submodule.mem_inf.mp h).2
  change a • x ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [mem_restrictSupport_iff] at h2 ⊢
  rwa [support_zpsmul a ha] at h2
end Formalism.GM.TM
