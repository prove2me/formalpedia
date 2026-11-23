-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.limitB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:30:38.546916+00:00
-- url     : https://prove2.me/submissions/0cf3ddc1-d41c-42e7-85e5-3dd073ed5192

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
theorem _root_.solution : LimitB := by
  intro hA hL2 hPair hCoef hLeib hCut B N F c hInf hImp hCl Y hY
  obtain ⟨hM, hPos, hFac, hBN, hMon, hJet⟩ := hImp
  obtain ⟨hPoly, hp⟩ := hA hCoef B N F hInf hM hPos hFac hBN hMon hCl Y hY
  have hpos : ∀ ω a, 0 ≤ F.dw Y ω a := fun ω a =>
    mul_nonneg (pow_nonneg (hPos.1 ω).le N) (hPos.2 Y hY a).le
  have hmw : ∀ a, Measurable fun ω => F.dw Y ω a := fun a => (hM.1.pow_const N).mul_const _
  have hmS : ∀ p a, Measurable fun ω => dS B (F.gw Y) F.u p ω a := fun p a => (hp p).1 a
  have L := hL2 hLeib hCut B F.R F.ι (F.gw Y) F.u (F.dw Y) c (N * (F.r + 1)) 1 le_rfl hpos hmw (hJet Y hY) hPoly
    hmS (fun p => (hp p).2)
  have hmg : ∀ a, Measurable fun ω => F.gw Y F.u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  have hmT : ∀ (ε : ℝ) a, Measurable fun ω => F.gw Y (mulF B (c.sc ε 1) F.u) ω a :=
    fun ε a => measurable_apply_mulF_of_jetLocal hLeib B (F.gw Y) F.u _ (hJet Y hY) hPoly hmS _ (smoothLog_sc c ε 1) a
  have P := hPair B F.ι (F.dw Y) (F.gw Y F.u) (F.gw Y F.u) (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u))
    (fun ε => F.gw Y (mulF B (c.sc ε 1) F.u)) hpos hmw hmg hmg (fun ε a _ => hmT ε a) (fun ε a _ => hmT ε a)
    (hCl Y hY) (hCl Y hY) L.1 L.1 L.2 L.2
  simp_rw [int_pr_self] at P
  have := (Complex.continuous_re.tendsto _).comp P
  simpa [Function.comp_def] using this
end Formalism.FourierDecayAlt.P.LEx2
