-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.star_modA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:04.129806+00:00
-- url     : https://prove2.me/submissions/c104307a-9391-4958-a85e-4538084aa775

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGenTransferCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut

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
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution (P : M.Par) (ρ : M.Ty P) (ζ : ℂ) : star (modA P ρ ζ) = modB P ρ ζ := by
  simp only [modA, modB]
  first
  | (rw [star_div₀, star_mul', star_sub, star_star]; simp [Complex.conj_ofReal]; done)
  | (simp [map_div₀, Complex.conj_ofReal]; done)
  | (rw [star_div₀, star_mul', star_sub, star_star]
     simp only [Complex.star_def, Complex.conj_ofReal]; done)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
