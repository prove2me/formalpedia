-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.mem_PT_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:42.319011+00:00
-- url     : https://prove2.me/submissions/e3c72ecd-5258-4cc9-9cd2-e9c965986aeb

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.TA1
theorem _root_.solution (Sg : ℕ → ℕ → Finset E) (n : ℕ) (p : Pt E) :
    p ∈ PT Sg (n + 1) ↔ ∃ m, m < n + 1 ∧ ∃ h ∈ PT Sg m, ∃ t ∈ Sg (n + 1) (n + 1 - m),
      Formalism.FourierDecayAlt.TA.ext h (n + 1 - m) t = p := by
  rw [PT]
  simp only [mem_biUnion, mem_attach, true_and, mem_image, Subtype.exists, mem_range]
  constructor
  · rintro ⟨m, hm, h, hh, t, ht, rfl⟩; exact ⟨m, hm, h, hh, t, ht, rfl⟩
  · rintro ⟨m, hm, h, hh, t, ht, rfl⟩; exact ⟨m, hm, h, hh, t, ht, rfl⟩
end Formalism.FourierDecayAlt.P.TA1
