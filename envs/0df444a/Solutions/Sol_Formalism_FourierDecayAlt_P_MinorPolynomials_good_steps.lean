-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.good_steps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:53:04.5938+00:00
-- url     : https://prove2.me/submissions/290e005a-dfa4-4c63-ae77-a43bb9722420

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtCvs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtEpart
import Theorems.Thm_Formalism_FourierDecayAlt_P_MinorPolynomials_good_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {nf : ℕ} {L : Finset (Fin (r + 2))} :
    ∀ (w : List (Mat k r)), (∀ X ∈ w, inLie k r X) → ∀ (Lf : FS k r nf), (∀ e ∈ Lf, Good L e) →
      ∀ e' ∈ steps D w Lf, Good L e' ∧ ∃ e ∈ Lf, e'.2.length ≤ e.2.length + w.length := by
  intro w
  induction w with
  | nil =>
    intro _ Lf hLf e' he'
    exact ⟨hLf e' he', e', he', by simp⟩
  | cons X w ih =>
    intro hw Lf hLf e' he'
    have hX : inLie k r X := hw X (by simp)
    have hw' : ∀ Y ∈ w, inLie k r Y := fun Y hY => hw Y (List.mem_cons_of_mem _ hY)
    simp only [steps, List.foldr_cons, step, List.mem_flatMap] at he'
    obtain ⟨e'', he'', he'⟩ := he'
    obtain ⟨hg, e, he, hlen⟩ := ih hw' Lf hLf e'' he''
    obtain ⟨hg', hlen'⟩ := good_step D hX hg e' he'
    refine ⟨hg', e, he, ?_⟩
    simp only [List.length_cons]
    omega
end Formalism.FourierDecayAlt.P.MinorPolynomials
