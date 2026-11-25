-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCPhase_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:58:21.66857+00:00
-- url     : https://prove2.me/submissions/f2f9185a-cd8b-4eb7-b1d2-b05f2e0a711a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGenTransferCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_modA_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_star_modA

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
theorem _root_.solution : GTCPhaseOfCut := by
  intro hR hC hH hA hT Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hk A B hAB hConn
  have hTT := hT Wp Wq P Bs X d hyp
  have hex : ∀ ρ : M.Ty P, ∃ u : ℂ → ℂ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {ζ : ℂ | P.TT < Complex.normSq ζ} ∧
      ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
        ‖u ζ‖ = 1 ∧ star (u ζ) * NF.dZ u ζ = modA P ρ ζ - A ρ ζ ∧
          star (u ζ) * NF.dZb u ζ = -star (modA P ρ ζ - A ρ ζ) := by
    intro ρ
    refine hA P.TT (fun w => modA P ρ w - A ρ w) hTT ((modA_smooth P ρ hTT).sub (hAB ρ).1) ?_ ?_
    · intro ζ hζ
      exact hC Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ
    · intro R hR0 hR2
      exact hH Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ R hR0 hR2
  choose u hu using hex
  refine ⟨u, fun ρ => ⟨(hu ρ).1, fun ζ hζ => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := (hu ρ).2 ζ hζ
  refine ⟨h1, ?_, ?_⟩
  · rw [h2]; ring
  · rw [h3, hR Wp Wq P Bs X d hyp e he hk A B hAB hConn ρ ζ hζ, star_sub, star_modA]; ring
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
