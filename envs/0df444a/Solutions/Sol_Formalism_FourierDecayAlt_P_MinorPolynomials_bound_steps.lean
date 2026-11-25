-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.bound_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:32:47.650312+00:00
-- url     : https://prove2.me/submissions/94d73e36-9ba4-4ff0-a573-d7963b4e4923

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IsOpenBigCellSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MemStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_bound_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} :
    ∀ (w : List (Mat k r)) (Lf : FS k r nf), ∀ e' ∈ steps D w Lf, ∃ e ∈ Lf,
      e'.1.q.totalDegree ≤ e.1.q.totalDegree + (2 * r + 2) * w.length ∧
      e'.2.length + fo e'.1.es ≤ e.2.length + fo e.1.es + w.length := by
  intro w
  induction w with
  | nil =>
    intro Lf e' he'
    exact ⟨e', he', by simp, by simp⟩
  | cons X w ih =>
    intro Lf e' he'
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨e, he, hd, ho⟩ := ih Lf e'' he''
    obtain ⟨hd', ho'⟩ := bound_step D X e'' e' he'
    refine ⟨e, he, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simp only [List.length_cons]
      omega
end Formalism.FourierDecayAlt.P.MinorPolynomials
