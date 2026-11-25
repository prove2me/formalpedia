-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.trdeg_CT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:43:57.760784+00:00
-- url     : https://prove2.me/submissions/197e989d-27d1-4341-bfca-8c5365812053

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectB
import Theorems.Thm_Formalism_L2_Pj_GenSect_card_Z

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
theorem _root_.solution (j₀ : Fin m) (htr : Algebra.trdeg K Ω = D) :
    Algebra.trdeg K (CT Ω D j₀) = (Fintype.card (Fin (D + 1) × Fin m) : Cardinal) := by
  classical
  have hle : D ≤ Fintype.card (Fin (D + 1) × Fin m) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have := j₀.pos
    nlinarith
  rw [← trdeg_add_eq (R := K) (S := Ω) (A := CT Ω D j₀), htr,
    MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype,
    Fintype.card_subtype_compl, card_Z, ← Nat.cast_add, Nat.add_sub_of_le hle]
end Formalism.L2.Pj.GenSect
