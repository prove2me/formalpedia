-- Prove2me | solution 1 for Formalism.REAL.lowering_span_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:00:17.944613+00:00
-- url     : https://prove2.me/submissions/528ab1f5-3792-434c-b80b-31947c42d9df

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Theorems.Thm_Formalism_REAL_lowering_word_raises_in_span

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ} {ε : Fin n → Bool}
  {F : Fin n → Fin n → Module.End ℂ V}
namespace Formalism.REAL
theorem _root_.solution (h : KRel ε F) {μ : Fin n → ℝ} {x : V} (hx : KHighest ε F μ x) :
    KStable ε F (lowSpan ε F x) := by
  intro a b hab z hz
  have : lowSpan ε F x ≤ (lowSpan ε F x).comap (F a b) := by
    refine Submodule.span_le.mpr ?_
    rintro y ⟨w, hw, rfl⟩
    exact lowering_word_raises_in_span h hx w hw a b hab
  exact this hz
end Formalism.REAL
