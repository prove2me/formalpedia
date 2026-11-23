-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback.last_size
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:49.925073+00:00
-- url     : https://prove2.me/submissions/75977a59-be71-4757-bdd3-6b20408d64c6

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveSemidefinitePullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
open Finset Matrix Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
noncomputable section
open Classical
variable {E W : Type} [Field E]
namespace Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
theorem _root_.solution (T : Tower E) {i : ℕ} (hi : 1 ≤ i) {p : Pt E} (hp : p ∈ T.X i) :
    ∃ s ∈ Icc 1 i, p.getLast?.map Prod.fst = some s := by
  obtain ⟨hl, hb⟩ := (T.isTower i p).1 hp
  rcases List.eq_nil_or_concat p with rfl | ⟨h, b, rfl⟩
  · simp [level] at hl; omega
  · refine ⟨b.1, ?_, by simp⟩
    have h1 : 1 ≤ b.1 := by simpa using (hb h.length (by simp)).1
    have h2 : level (h.concat b) = level h + b.1 := by simp [level]
    rw [Finset.mem_Icc]
    exact ⟨h1, by omega⟩
end Formalism.FourierDecayAlt.P.PositiveSemidefinitePullback
