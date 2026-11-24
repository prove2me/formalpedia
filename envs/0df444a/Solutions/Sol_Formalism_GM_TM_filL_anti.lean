-- Prove2me | solution 1 for Formalism.GM.TM.filL_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:13.149819+00:00
-- url     : https://prove2.me/submissions/c2d8c00c-950e-4451-896e-af6f6811cfeb

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM

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
theorem _root_.solution (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) {e e' : ℕ} (h : e ≤ e') :
    filL L v e' ≤ filL L v e := by
  intro x hx
  refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).1, ?_⟩
  have h2 := (Submodule.mem_inf.mp hx).2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [mem_restrictSupport_iff] at h2 ⊢
  intro m hm
  exact le_trans h (h2 hm)
end Formalism.GM.TM
