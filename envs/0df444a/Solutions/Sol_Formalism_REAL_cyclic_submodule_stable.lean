-- Prove2me | solution 1 for Formalism.REAL.cyclic_submodule_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:09.902792+00:00
-- url     : https://prove2.me/submissions/bbc6a287-0c0c-443b-b218-862fb3fdf008

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
theorem _root_.solution (a b : Fin n) (x : V) (hx : x ∈ cyc E u) : E a b x ∈ cyc E u := by
  unfold cyc at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro W hW
  exact hW.2 a b x (hx W hW)
end Formalism.REAL
