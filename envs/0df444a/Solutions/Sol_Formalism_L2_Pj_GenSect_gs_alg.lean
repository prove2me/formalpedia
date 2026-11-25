-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.gs_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:07:58.725405+00:00
-- url     : https://prove2.me/submissions/6e3e33fe-894c-4c79-b2d2-6ad296b89a72

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Theorems.Thm_Formalism_L2_Pj_GenSect_trdeg_CT
import Theorems.Thm_Formalism_L2_Pj_GenSect_gs_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial Cardinal
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution [CharZero K] (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (htr : Algebra.trdeg K Ω = D)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x j₀))) ω) :
    Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀) :=
  ((gs_indep x j₀ hx₀ htr halg).isTranscendenceBasis_of_trdeg_le_of_finite
    (by rw [trdeg_CT j₀ htr, Cardinal.mk_fintype])).isAlgebraic
end Formalism.L2.Pj.GenSect
