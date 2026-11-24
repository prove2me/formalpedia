-- Prove2me | solution 1 for Formalism.REAL.hermitian_small_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:59.558034+00:00
-- url     : https://prove2.me/submissions/c2df08cc-645b-4ba3-abd7-334b3bb3b893

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Theorems.Thm_Formalism_REAL_f1auxiliary_hs_eq
import Theorems.Thm_Formalism_REAL_continuous_hs_real_place_taylor
import Theorems.Thm_Formalism_REAL_f1auxiliary_closed
import Theorems.Thm_Formalism_REAL_f1auxiliary_entry_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : HSBall := by
  intro n ε
  refine ⟨fun R => ?_, fun g k hk => ⟨?_, ?_⟩⟩
  · have hcpt : IsCompact (Set.pi Set.univ fun _ : Fin n =>
        Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) (Real.sqrt R)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hcpt.of_isClosed_subset ((f1auxiliary_closed ε).inter (isClosed_le continuous_hs_real_place_taylor continuous_const)) ?_
    rintro g ⟨_, hg⟩ i _ j _
    have h1 := (f1auxiliary_entry_le g i j).trans hg
    simpa using Real.abs_le_sqrt h1
  · have hk1 : k * kᴴ = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show kᴴ * gᴴ * (g * k) = kᴴ * (gᴴ * g * k) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm, Matrix.mul_assoc, hk1, Matrix.mul_one]
  · have hk2 : kᴴ * k = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact Matrix.mem_unitaryGroup_iff'.1 hk.1
    rw [f1auxiliary_hs_eq, f1auxiliary_hs_eq, conjTranspose_mul]
    congr 1
    rw [show gᴴ * kᴴ * (k * g) = gᴴ * (kᴴ * k) * g by simp only [Matrix.mul_assoc], hk2, Matrix.mul_one]
end Formalism.REAL
