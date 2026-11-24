-- Prove2me | solution 1 for Formalism.REAL.pfil_le_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:36.231611+00:00
-- url     : https://prove2.me/submissions/19a25ced-9358-4486-8522-df3a0e9194b7

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
import Theorems.Thm_Formalism_REAL_cyclic_submodule_stable
import Theorems.Thm_Formalism_REAL_compact_span_le_cyclic
import Theorems.Thm_Formalism_REAL_ew_cons
import Theorems.Thm_Formalism_REAL_ew_nil

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (u : V)
namespace Formalism.REAL
theorem _root_.solution (j : ℕ) : pfil ε E u j ≤ cyc E u := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, -, -, y, hy, rfl⟩
  rw [SetLike.mem_coe]
  have hy' : y ∈ cyc E u := compact_span_le_cyclic ε E u hy
  clear hy
  induction w with
  | nil => rw [ew_nil]; exact hy'
  | cons p w ih => rw [ew_cons]; exact cyclic_submodule_stable E u p.1 p.2 _ ih
end Formalism.REAL
