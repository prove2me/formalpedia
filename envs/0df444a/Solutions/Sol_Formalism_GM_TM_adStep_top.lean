-- Prove2me | solution 1 for Formalism.GM.TM.adStep_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:04.919462+00:00
-- url     : https://prove2.me/submissions/68a5ed08-a026-4315-b007-ccf293d5859e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Theorems.Thm_Formalism_GM_TM_filL_top

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
    (hD : ∀ x ∈ L, ∀ m ∈ x.support, m v ≤ D) : AdStep L v (D + 1) := by
  refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, linearIndependent_empty_type, ?_, fun b => b.elim, ?_⟩
  · rw [filL_top L v D hD _ (by omega), Set.range_eq_empty, Submodule.span_empty]
  · intro e' he'
    rw [filL_top L v D hD _ (by omega)]
    have : (Empty.elim : Empty → MvPolynomial σ ℚ_[p]) '' {b | e' ≤ (Empty.elim : Empty → ℕ) b} = ∅ := by
      ext x; simp
    rw [this, Submodule.span_empty]
end Formalism.GM.TM
