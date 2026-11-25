-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_foldr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:09.095668+00:00
-- url     : https://prove2.me/submissions/9ff7c956-d774-4726-b0f2-814d1b87d349

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution {g₀ : Q.Mx k r} (L : List ((Q.Mx k r → E) → (Q.Mx k r → E)))
    (hL : ∀ T ∈ L, ∀ (N : ℕ) (h : Q.Mx k r → E), ZJ k r (N + 1) h g₀ → ZJ k r N (T h) g₀) :
    ∀ (N : ℕ) (f : Q.Mx k r → E), ZJ k r (N + L.length) f g₀ →
      ZJ k r N (L.foldr (fun T h => T h) f) g₀ := by
  induction L with
  | nil =>
    intro N f h
    simpa using h
  | cons T L ih =>
    intro N f h
    simp only [List.foldr_cons]
    apply hL T List.mem_cons_self N
    apply ih (fun T' hT' => hL T' (List.mem_cons_of_mem _ hT')) (N + 1) f
    simp only [List.length_cons] at h
    rwa [show N + 1 + L.length = N + (L.length + 1) by omega]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
