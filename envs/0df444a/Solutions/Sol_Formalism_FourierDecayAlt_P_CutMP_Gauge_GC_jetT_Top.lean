-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_Top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:49:24.288384+00:00
-- url     : https://prove2.me/submissions/41b814ec-54b5-4e9d-a381-1efac44650b7

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_EH

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
theorem _root_.solution {N : ℕ} {f : Q.Mx k r → E} {g₀ : Q.Mx k r} (u : ℂ) (a b : Fin (Q.mdim k r (Fin.last r)))
    (h : ZJ k r (N + 1) f g₀) :
    ZJ k r N (Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f) g₀ := by
  by_cases hab : Q.posL k r (Fin.last r) a = Q.posL k r (Fin.last r) b
  · have he : Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f =
        fun g => u • f g + Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f g := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, hab, if_true]
    rw [he]
    exact jetT_add (jetT_smul u (jetT_mono (Nat.le_succ N) h)) (jetT_EH a b h)
  · have he : Top (Q.EH k r) u (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f =
        Q.EH k r (Q.posL k r (Fin.last r) a) (Q.posL k r (Fin.last r) b) f := by
      funext g
      simp only [Formalism.QuantumDeterminants.Top, hab, if_false, zero_add]
    rw [he]
    exact jetT_EH a b h
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
