-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.onBoxes_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:55:18.488809+00:00
-- url     : https://prove2.me/submissions/eb9ea09a-fa83-4029-8a59-58ddf6e3b190

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DegreeOfProdLinearLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (S : Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) ↔ ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero => intro Y; simp [Sys.OnBoxes]
  | succ N ih =>
    intro Y
    rw [List.ofFn_succ]
    show (Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)) ↔ _
    rw [List.length_ofFn, ih]
    constructor
    · rintro ⟨h0, h1⟩ a
      refine Fin.cases ?_ (fun b => ?_) a
      · simpa using h0
      · have := h1 b
        have e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ) := by
          simp only [Fin.val_succ]; omega
        rw [e]; exact this
    · intro h
      refine ⟨by simpa using h 0, fun b => ?_⟩
      have := h b.succ
      have e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ) := by
        simp only [Fin.val_succ]; omega
      rw [e] at this; exact this
end Formalism.FourierDecayAlt.P.LEx2
