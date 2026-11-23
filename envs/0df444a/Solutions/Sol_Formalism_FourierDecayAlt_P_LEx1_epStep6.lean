-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.epStep6
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:54.8628+00:00
-- url     : https://prove2.me/submissions/8b16c5ea-a756-4b6c-8d5c-f99d4dfe7733

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_smoothLog_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_ld_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : EpStep6 := by
  intro hCut B X c hJet hPol hLoc ε hε
  obtain ⟨m, cc, hc⟩ := hJet
  have hε1 : 0 < ε / 8 := by positivity
  have h1u : mulF B (fun _ => (1:ℝ)) X.u = X.u := by funext ω a; simp [mulF]
  have hbig : ∀ ω, ε / 8 < B.G ω → ∀ a, X.gw (mulF B (c.sc (ε/8) 1) X.u) ω a = X.gw X.u ω a := by
    intro ω hω a
    have e1 := hc (c.sc (ε/8) 1) (smoothLog_sc c _ 1) ω a
    have e2 := hc (fun _ => (1:ℝ)) (by unfold SmoothLog; exact contDiff_const) ω a
    rw [h1u] at e2
    rw [e1, e2]
    refine Finset.sum_congr rfl fun q _ => ?_
    obtain ⟨C, hC⟩ := hCut c 1 q le_rfl
    rw [(hC (ε/8) (B.G ω) hε1 (B.G_pos ω)).2.2 hω, ld_one]
  have hsmall : ∀ ω, B.G ω ≤ ε / 8 → ∀ a, X.gw (mulF B (c.sc ε 2) X.u) ω a = 0 := by
    intro ω hω a
    rw [hc (c.sc ε 2) (smoothLog_sc c _ 2) ω a]
    refine Finset.sum_eq_zero fun q _ => ?_
    obtain ⟨C, hC⟩ := hCut c 2 q (by norm_num)
    rw [(hC ε (B.G ω) hε (B.G_pos ω)).2.1 (by linarith)]; simp
  have hsc : ∀ ω, B.G ω ≤ ε / 8 → c.sc ε 2 (B.G ω) = 0 := by
    intro ω hω
    have : B.G ω / ε ≤ 1 / 2 := by rw [div_le_iff₀ hε]; linarith
    simp [Cut.sc, c.zero _ this]
  calc X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)
      = X.beta (X.Cw (mulF B (c.sc (ε/8) 1) X.u)) (mulF B (c.sc ε 2) X.u) := by
        unfold EP.beta
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [pr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases lt_or_ge (ε/8) (B.G ω) with h | h
        · rw [hLoc (ε/8) ω hε1 h a]
        · simp [mulF, hsc ω h]
    _ = ∫ ω, pr B X.dw (X.gw (mulF B (c.sc (ε/8) 1) X.u)) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ :=
        hPol (ε/8) ε 1 2 hε1 hε le_rfl (by norm_num)
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only [pr]
        refine Finset.sum_congr rfl fun a _ => ?_
        rcases lt_or_ge (ε/8) (B.G ω) with h | h
        · rw [hbig ω h a]
        · simp [hsmall ω h a]
end Formalism.FourierDecayAlt.P.LEx1
