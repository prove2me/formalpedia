-- Prove2me | solution 1 for Formalism.GM.TM.filL_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:15.55652+00:00
-- url     : https://prove2.me/submissions/78a8dbed-19f8-4f92-b24b-b1a766cb201c

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
theorem _root_.solution (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (v : σ) (D : ℕ)
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) (e : ℕ) (he : D < e) : filL L v e = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  have h1 := (Submodule.mem_inf.mp hx).1
  have h2 := (Submodule.mem_inf.mp hx).2
  change x ∈ MvPolynomial.restrictSupport ℚ_[p] _ at h2
  rw [mem_restrictSupport_iff] at h2
  by_contra hne
  obtain ⟨m, hm⟩ : ∃ m, m ∈ x.support := by
    by_contra hc; push Not at hc
    exact hne (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have := hD x h1 m hm
  have := h2 (Finset.mem_coe.mpr hm)
  simp only [Set.mem_setOf_eq] at this
  omega
end Formalism.GM.TM
