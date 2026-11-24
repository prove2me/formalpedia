-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.lss_of_ckOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:05:17.124392+00:00
-- url     : https://prove2.me/submissions/672d2af0-488b-40ae-8c27-5da58b00862d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Sq2UnitOfEqOneOfSq2EqDiv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleWordLengthLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution {f : Mat k r → E} {UU S : Set (Mat k r)} (hf : CkOn ⊤ UU f) (hS : S ⊆ UU) : LSS f S := by
  intro g hg
  obtain ⟨U, f', hU, hgU, hf', hfU⟩ := hf g (hS hg)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU g hgU
  let χ : ContDiffBump g := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hcl : Metric.closedBall g (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  refine ⟨fun x => χ x • f' x, ?_, Metric.ball g (ε / 4), Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.closedBall g (ε / 2)
    · exact χ.contDiff.contDiffAt.smul (hf'.contDiffAt (hU.mem_nhds (hcl hx)))
    · have hzero : (fun x => χ x • f' x) =ᶠ[𝓝 x] fun _ => (0 : E) := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hx] with y hy
        have hy' : ε / 2 ≤ dist y g := by
          simp only [mem_compl_iff, Metric.mem_closedBall, not_le] at hy
          exact hy.le
        have : χ y = 0 := χ.zero_of_le_dist hy'
        simp [this]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro g' hg' hgb
    have h1 : χ g' = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hgb)
    dsimp only
    rw [h1, one_smul]
    exact hfU g' (hball (Metric.ball_subset_ball (by linarith) hgb)) hg'
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
