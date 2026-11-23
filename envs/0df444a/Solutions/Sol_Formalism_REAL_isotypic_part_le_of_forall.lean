-- Prove2me | solution 1 for Formalism.REAL.isotypic_part_le_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:59.523201+00:00
-- url     : https://prove2.me/submissions/6413dd09-8561-491d-a2e1-c10d73d0d7f3

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional

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
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {W : Type} [AddCommGroup W] [Module ℂ W] {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ W} {T : Set (Fin n → ℝ)} {S M : Submodule ℂ W}
    (h : ∀ y ∈ S, ∀ μ ∈ T, KHighest ε F μ y → kSpan ε F y ≤ M) : isoPart ε F T S ≤ M :=
  iSup₂_le fun y hy => h y hy.1 hy.2.choose hy.2.choose_spec.1 hy.2.choose_spec.2
end Formalism.REAL
