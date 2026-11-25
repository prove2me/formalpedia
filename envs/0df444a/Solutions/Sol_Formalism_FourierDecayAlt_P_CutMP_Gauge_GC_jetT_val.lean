-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:34.785128+00:00
-- url     : https://prove2.me/submissions/9c411e40-0fc5-4350-b991-805a18edc070

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet

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
theorem _root_.solution {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (hg₀ : g₀ ∈ Q.Glev k r (Fin.last r))
    (h : ZJ k r N f g₀) : f g₀ = 0 := by
  obtain ⟨U, F, hU, hgU, hF, hfF, hv⟩ := h
  rw [hfF g₀ hgU hg₀]
  have h0 := hv 0 (Nat.zero_le _)
  calc F g₀ = iteratedFDeriv ℝ 0 F g₀ (fun i => Fin.elim0 i) := (iteratedFDeriv_zero_apply _).symm
    _ = 0 := by rw [h0]; rfl
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
