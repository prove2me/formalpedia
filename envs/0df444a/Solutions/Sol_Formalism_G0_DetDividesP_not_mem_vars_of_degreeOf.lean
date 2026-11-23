-- Prove2me | solution 1 for Formalism.G0.DetDividesP.not_mem_vars_of_degreeOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:21.157817+00:00
-- url     : https://prove2.me/submissions/18a432c4-660d-4dd7-ab4e-9a839989a2ed

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
namespace Formalism.G0.DetDividesP
theorem _root_.solution {σ : Type} {p : MvPolynomial σ K} {x : σ} (h : degreeOf x p = 0) :
    x ∉ p.vars := by
  intro hx
  rw [mem_vars_iff_mem_support] at hx
  obtain ⟨d, hd, hxd⟩ := hx
  have h1 := Finset.le_sup (f := fun m : σ →₀ ℕ => m x) hd
  rw [← degreeOf_eq_sup, h] at h1
  rw [Finsupp.mem_support_iff] at hxd
  exact hxd (by simpa using h1)
end Formalism.G0.DetDividesP
