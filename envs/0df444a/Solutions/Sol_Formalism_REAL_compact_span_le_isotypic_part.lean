-- Prove2me | solution 1 for Formalism.REAL.compact_span_le_isotypic_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:09.45437+00:00
-- url     : https://prove2.me/submissions/0cd1eb09-b03c-4264-82ff-45fff0502e37

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
    {F : Fin n → Fin n → Module.End ℂ W} {T : Set (Fin n → ℝ)} {S : Submodule ℂ W} {y : W}
    {μ : Fin n → ℝ} (hy : y ∈ S) (hμ : μ ∈ T) (hyh : KHighest ε F μ y) :
    kSpan ε F y ≤ isoPart ε F T S :=
  le_iSup₂_of_le (f := fun y (_ : y ∈ S ∧ ∃ μ ∈ T, KHighest ε F μ y) => kSpan ε F y) y
    ⟨hy, μ, hμ, hyh⟩ le_rfl
end Formalism.REAL
