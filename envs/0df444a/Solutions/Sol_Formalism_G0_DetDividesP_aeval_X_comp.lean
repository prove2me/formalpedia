-- Prove2me | solution 1 for Formalism.G0.DetDividesP.aeval_X_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:21.896809+00:00
-- url     : https://prove2.me/submissions/313d82d8-496f-43f2-8986-6cf1a8c8d3de

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
theorem _root_.solution {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ K) :
    aeval (fun q => (X (f q) : MvPolynomial τ K)) p = rename f p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]
end Formalism.G0.DetDividesP
