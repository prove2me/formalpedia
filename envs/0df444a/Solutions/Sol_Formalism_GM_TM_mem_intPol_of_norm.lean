-- Prove2me | solution 1 for Formalism.GM.TM.mem_intPol_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:08.350657+00:00
-- url     : https://prove2.me/submissions/453aea03-168c-4056-bf6d-f98414640ee9

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
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.TM
theorem _root_.solution {σ : Type} (x : MvPolynomial σ ℚ_[p]) (h : ∀ m, ‖x.coeff m‖ ≤ 1) :
    x ∈ IntPol p σ := by
  have : (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by
    intro a ha
    rw [Finset.mem_coe, mem_coeffs_iff] at ha
    obtain ⟨m, _, rfl⟩ := ha
    exact ⟨⟨x.coeff m, h m⟩, rfl⟩
  rw [← mem_range_map_iff_coeffs_subset] at this
  simpa [IntPol, LinearMap.mem_range, AlgHom.toLinearMap_apply, mapAlgHom_apply, Set.mem_range] using this
end Formalism.GM.TM
