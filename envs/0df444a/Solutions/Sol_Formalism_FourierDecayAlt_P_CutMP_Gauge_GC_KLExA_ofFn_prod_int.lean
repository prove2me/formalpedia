-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.ofFn_prod_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:39.28071+00:00
-- url     : https://prove2.me/submissions/0392bf63-34d7-43cc-bc3e-621b441b68f3

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ


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
theorem _root_.solution {t : ℕ} (F : Fin t → Module.End ℂ V) (F' : Fin t → Module.End ℂ V') (f : V →ₗ[ℂ] V')
    (h : ∀ k x, f (F k x) = F' k (f x)) (x : V) : f ((List.ofFn F).prod x) = (List.ofFn F').prod (f x) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply,
      h, ih (fun k => F k.succ) (fun k => F' k.succ) (fun k y => h k.succ y)]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA
