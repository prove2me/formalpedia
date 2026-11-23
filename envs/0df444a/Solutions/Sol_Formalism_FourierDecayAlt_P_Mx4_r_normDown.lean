-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.r_normDown
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:38.317807+00:00
-- url     : https://prove2.me/submissions/aa207f69-e9c1-4d4a-94fa-f56a0f0e895f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_down
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrmFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_fun
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_up_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_sR_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    sR P l * (sR P l).transpose = Matrix.diagonal (NrmDown P l) := by
  ext π1 π2
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases h : π1 = π2
  · subst h
    rw [Matrix.diagonal_apply_eq]
    by_cases hu : ∃ π', Up P l π' π1
    · obtain ⟨π', hU⟩ := hu
      rw [Finset.sum_eq_single π' (fun b _ hb => by
        rw [sR_neg (fun hb' => hb (up_inj P l π1 b π' hb' hU)), zero_mul])
        (fun h => absurd (Finset.mem_univ _) h), sR_pos hU, nrm_down P l hl π' π1 hU]
      exact Real.mul_self_sqrt (nrm_pos P hP l hl π' π1 hU).le
    · rw [(nrmFacts P hP l hl π1).2.2 hu]
      apply Finset.sum_eq_zero
      intro b _
      rw [sR_neg (fun hb => hu ⟨b, hb⟩), zero_mul]
  · rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : Up P l b π1
    · rw [sR_neg (π := b) (π' := π2) (fun h2 => h (up_fun P l b π1 π2 h1 h2)), mul_zero]
    · rw [sR_neg h1, zero_mul]
end Formalism.FourierDecayAlt.P.Mx4
