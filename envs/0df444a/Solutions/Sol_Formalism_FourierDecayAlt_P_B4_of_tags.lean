-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B4.of_tags
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:30:20.433888+00:00
-- url     : https://prove2.me/submissions/7578aab5-0a67-422d-9982-be785d030570

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma tags_false_lemma : ∀ (w : List (Bool × Mat k r)) (b : ℕ),
    w.map Prod.fst = List.replicate b false → w = (w.map Prod.snd).map (fun X => (false, X)) := by
  intro w
  induction w with
  | nil => intro b _; rfl
  | cons x w ih =>
    intro b h
    cases b with
    | zero => simp at h
    | succ b =>
      simp only [List.map_cons, List.replicate_succ, List.cons.injEq] at h
      obtain ⟨hx, hw⟩ := h
      simp only [List.map_cons]
      rw [← ih b hw]
      congr 1
      exact Prod.ext hx rfl
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.B4
theorem _root_.solution : ∀ (w : List (Bool × Mat k r)) (a b : ℕ),
    w.map Prod.fst = List.replicate a true ++ List.replicate b false →
    ∃ u v : List (Mat k r), u.length = a ∧ w = lr u v := by
  intro w a
  induction a generalizing w with
  | zero =>
    intro b h
    simp only [List.replicate_zero, List.nil_append] at h
    refine ⟨[], w.map Prod.snd, rfl, ?_⟩
    conv_lhs => rw [tags_false_lemma w b h]
    simp [lr]
  | succ a ih =>
    intro b h
    cases w with
    | nil => simp at h
    | cons x w =>
      simp only [List.map_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at h
      obtain ⟨hx, hw⟩ := h
      obtain ⟨u, v, hu, rfl⟩ := ih w b hw
      refine ⟨x.2 :: u, v, by simp [hu], ?_⟩
      simp only [lr, List.map_cons, List.cons_append]
      congr 1
      exact Prod.ext hx rfl
end Formalism.FourierDecayAlt.P.B4
