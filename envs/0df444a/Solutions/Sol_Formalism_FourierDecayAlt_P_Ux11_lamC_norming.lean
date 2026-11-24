-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.lamC_norming
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:10.204701+00:00
-- url     : https://prove2.me/submissions/c54c76ec-8ab3-4563-a3ba-67f9d600aee8

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution (M : U.CCModel k ρ E a mm S V) (w : V) (c : ℝ) (h : ∀ t, ‖lamC M t w‖ ≤ c) : ‖w‖ ≤ c := by
  refine M.least w c ⟨(M.mem w).1, fun u v hu hv hl g hg => ?_⟩
  have := h ⟨(u, v, g), hu, hv, hl, hg⟩
  have e : ‖lamC M ⟨(u, v, g), hu, hv, hl, hg⟩ w‖ = B.gN g ^ a * ‖B.dLR u v (M.ev w) g‖ := by
    show ‖((B.gN g ^ a : ℝ) : ℂ) • B.dLR u v (M.ev w) g‖ = _
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (gNa_nonneg _ _)]
  exact (le_of_eq e.symm).trans this
end Formalism.FourierDecayAlt.P.Ux11
