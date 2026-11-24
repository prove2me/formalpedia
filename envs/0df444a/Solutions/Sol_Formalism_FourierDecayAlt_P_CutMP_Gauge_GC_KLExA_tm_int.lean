-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.tm_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:40.872904+00:00
-- url     : https://prove2.me/submissions/643cf2f2-13b4-4508-afa3-9c76a19ec1f4

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'} (f : V →ₗ[ℂ] V')
    (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (a b : Fin n) (x : V) :
    f (Tm E u a b x) = Tm E' u a b (f x) := by
  unfold Tm
  split_ifs <;> simp [Module.algebraMap_end_apply, hf]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
