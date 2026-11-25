-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.rawR_phase
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:22.908165+00:00
-- url     : https://prove2.me/submissions/156e1835-d725-4cf4-bea3-29d1f28a5daf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_hsVec_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (u : M.Ty P → ℂ → ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μsec (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fun q => star (u ρ q.1.2) * rawR P μsec e Φ ρ q := by
  funext q
  simp only [rawR, hsVec_smul, inner_smul_left]
  rw [show star (u ρ q.1.2) = (starRingEnd ℂ) (u ρ q.1.2) from rfl]
  ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
