-- Prove2me | solution 1 for Formalism.REAL.mem_noncompact_arr_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:46:14.387866+00:00
-- url     : https://prove2.me/submissions/6c903c42-b66a-486e-ae5a-4bbed6311a67

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil

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
theorem _root_.solution {j : ℕ} (F : Arr V n j) :
    F ∈ arrV0 ε E u j ↔ ∀ α, F α ∈ (if ∀ i, ε (α i).1 ≠ ε (α i).2 then kSpan ε E u else ⊥) := by
  unfold arrV0
  rw [Submodule.mem_iInf]
  first | rfl | exact Iff.rfl | (simp only [Submodule.mem_comap]; rfl)
end Formalism.REAL
