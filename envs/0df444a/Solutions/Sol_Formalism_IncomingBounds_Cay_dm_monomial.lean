-- Prove2me | solution 1 for Formalism.IncomingBounds.Cay.dm_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:05.156344+00:00
-- url     : https://prove2.me/submissions/66570c14-4a18-42a0-8f88-d89e267a7670

import Definitions.Def_Formalism_IncomingBounds_StatementThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Cayley
import Theorems.Thm_Formalism_IncomingBounds_Cay_supp_sum_monomial

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
open Formalism Formalism.IncomingBounds Formalism.IncomingBounds.Cay
open MvPolynomial Matrix Formalism.IncomingBounds
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.IncomingBounds.Cay
theorem _root_.solution {σ : Type} (m a : σ →₀ ℕ) (c : K) :
    dm m (monomial a c) =
      if m ≤ a then monomial (a - m) (c * ((mfact a : K) / (mfact (a - m) : K))) else 0 := by
  unfold dm
  exact supp_sum_monomial (fun b x => if m ≤ b then
      monomial (b - m) (x * ((Formalism.IncomingBounds.mfact b : K) / (Formalism.IncomingBounds.mfact (b - m) : K))) else 0)
    (fun b => by simp) a c
end Formalism.IncomingBounds.Cay
