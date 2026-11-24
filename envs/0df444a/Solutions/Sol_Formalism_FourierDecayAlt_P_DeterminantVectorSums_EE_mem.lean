-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DeterminantVectorSums.EE_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:24.906882+00:00
-- url     : https://prove2.me/submissions/205e7c77-9dd5-4006-9823-d3dded13275a

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StarSumLemmas
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_vecD
import Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantVectorSums_EE_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DeterminantVectorSums
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} (E : Fin (N + 1) → Fin (N + 1) → Module.End ℂ V)
namespace Formalism.FourierDecayAlt.P.DeterminantVectorSums
theorem _root_.solution (hE : GlRel E) (v : V) : ∀ x ∈ Gd E v, EE E x ∈ Gd E v := by
  rintro x ⟨y, hy, hx⟩
  refine ⟨_, vecD E hE y hy, fun l => ?_⟩
  rw [EE_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun c _ => by rw [hx]; rfl)
end Formalism.FourierDecayAlt.P.DeterminantVectorSums
