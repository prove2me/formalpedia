-- Prove2me | solution 1 for Formalism.GM.gaussR_attained
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:04.754801+00:00
-- url     : https://prove2.me/submissions/a7b6bb31-6b30-4ebc-944a-211090c8cb6f

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]
namespace Formalism.GM
theorem _root_.solution (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ k, ‖P.coeff k‖₊ * ρ ^ k = gaussR ρ P := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  exact ⟨k, hk.symm⟩
end Formalism.GM
