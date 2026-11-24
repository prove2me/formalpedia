-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qdet_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:27.46633+00:00
-- url     : https://prove2.me/submissions/24d06287-923e-4db7-87a7-053ca57d784a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_KLExA_qminor_int

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
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {E' : Fin n → Fin n → Module.End ℂ V'}
    (f : V →ₗ[ℂ] V') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (u : ℂ) (x : V) :
    f (qdet E u x) = qdet E' u (f x) :=
  qminor_int f hf id id u x
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
