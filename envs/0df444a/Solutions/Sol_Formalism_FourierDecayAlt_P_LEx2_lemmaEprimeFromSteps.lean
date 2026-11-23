-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.lemmaEprimeFromSteps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:38.470674+00:00
-- url     : https://prove2.me/submissions/8619f5c2-57ed-4035-bb09-8347fde65e11

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_int_pr_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_smoothLog_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_measurable_apply_mulF_of_jetLocal

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
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : LemmaEprimeFromSteps := by
  intro hLeib hCut hL2 hPair h5 h6 B X c M hpos hMeas hJet hPoly hCoef hPol hLoc hBeta
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  have hI0 : Integrable (LE.sq B X.dw (X.gw X.u)) B.μ := by
    have := hCoef 0; rwa [dS_zero] at this
  have hmg : ∀ a, Measurable fun ω => X.gw X.u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  have L1 := hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 1 le_rfl hpos hmd hJet hPoly hmS hCoef
  have L2 := hL2 hLeib hCut B X.R X.ι X.gw X.u X.dw c M 2 (by norm_num) hpos hmd hJet hPoly hmS hCoef
  have hmT : ∀ (m : ℕ) (ε : ℝ) (a : X.ι), Measurable fun ω => X.gw (mulF B (c.sc ε m) X.u) ω a :=
    fun m ε a => measurable_apply_mulF_of_jetLocal hLeib B X.gw X.u M hJet hPoly hmS _ (smoothLog_sc c ε m) a
  have hzero : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B X.dw (fun ω a => X.gw X.u ω a - X.gw X.u ω a) ω ∂B.μ)
      (𝓝[>] 0) (𝓝 0) := by
    simp [LE.sq]

  have P2 := hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun _ => X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 2) X.u))
    hpos hmd hmg hmg (fun _ a _ => hmg a) (fun ε a _ => hmT 2 ε a) hI0 hI0 (fun _ _ => hI0) L2.1 hzero L2.2
  have T5 := h5 B X c ⟨hmu, hmC, hmd, hmS⟩ hBeta
  have hev : (fun ε : ℝ => X.beta (X.Cw X.u) (mulF B (c.sc ε 2) X.u)) =ᶠ[𝓝[>] 0]
      fun ε : ℝ => ∫ ω, pr B X.dw (X.gw X.u) (X.gw (mulF B (c.sc ε 2) X.u)) ω ∂B.μ := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact h6 hCut B X c hJet hPol hLoc ε hε
  have heq : ∫ ω, pr B X.dw (X.gw X.u) (X.gw X.u) ω ∂B.μ = X.beta (X.Cw X.u) X.u :=
    tendsto_nhds_unique P2 (T5.congr' hev)
  refine ⟨hI0, ?_, ?_⟩
  · rw [← int_pr_self]; exact heq
  · have P1 := hPair B X.ι X.dw (X.gw X.u) (X.gw X.u) (fun ε => X.gw (mulF B (c.sc ε 1) X.u))
      (fun ε => X.gw (mulF B (c.sc ε 1) X.u))
      hpos hmd hmg hmg (fun ε a _ => hmT 1 ε a) (fun ε a _ => hmT 1 ε a) hI0 hI0 L1.1 L1.1 L1.2 L1.2
    rw [heq] at P1
    refine P1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hPol ε ε 1 1 hε hε le_rfl le_rfl).symm
end Formalism.FourierDecayAlt.P.LEx2
