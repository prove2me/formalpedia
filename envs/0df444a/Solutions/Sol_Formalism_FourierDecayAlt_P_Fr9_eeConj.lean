-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr9.eeConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:42:47.493807+00:00
-- url     : https://prove2.me/submissions/bdd280b7-21a4-45b0-9fb6-2bf237161845

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CommuteLevelZeroElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_zc
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_m_b_c2aaaddc0865
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mG
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_mGi
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_Fr9_hat___ff400f1de6e6
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_commutator_GG_l0
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_comm_kapL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_commute_level_zero_element
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_io_fn_comm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_kapL_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_ee_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr9_DD_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_io_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_divided_difference_l
import Theorems.Thm_Formalism_FourierDecayAlt_P_frame_gives_one_letter_hyps
import Theorems.Thm_Formalism_YangianSpanCharacter_P_wedgeMapInLieAlgebra


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr9
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
  {r : ℕ}
variable {L : LevelData A r} {f : FrameData S A}
namespace Formalism.FourierDecayAlt.P.Fr9
theorem _root_.solution (h : IsFrame L f) {Y Ya : ℂ} (hY : Y ∈ f.inv) (hY1 : Y + 1 ∈ f.inv) (ha : Ya ∈ f.inv)
    (ha1 : Ya + 1 ∈ f.inv) (hne : Y ≠ Ya) : f.xi Ya * f.ee Y * f.x Ya - f.DD Y Ya = f.ee Y := by
  obtain ⟨H, Hl⟩ := frame_gives_one_letter_hyps A S r L f h
  have y1 := Formalism.YangianSpanCharacter.P.wedgeMapInLieAlgebra ℂ (SlopeTestRemainingChoices S A) f.hatT _ f.hatQ f.inv H Ya Y ha hY hne.symm
  unfold eta at y1
  rw [Hl Y hY hY1, Hl Ya ha ha1, divided_difference_l A S r L f Ya Y hne.symm, DD_symm,
    hat_τ h (h.inv_reg ha)] at y1
  have gg2 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by rw [← Wd11.io_mul, L.GGi_GG, Wd11.io_one]
  refine ee_abs (g := io L.GG) (w := io (L.ζb * L.GGi)) gg2 kapL_inv (h.x_xi Ya ha).2
    (comm_kapL (h.x_fn Ya)).eq (h.ee_fn Y _ (mG L)).eq
    (comm_kapL (fun g hg => io_fn_comm (mG L) hg)).eq.symm
    (commute_level_zero_element (h.x_fn Ya) (h.x_nab Ya) Y).eq ?_ ?_ y1
  · rw [← Wd11.io_mul, ← Wd11.io_mul, ← Wd11.io_mul, ← io_sub, commutator_GG_l0, zc L (mζb L) (mGi L), ← mul_assoc,
      L.GG_GGi, one_mul]
  · rw [Wd11.io_mul]
    exact ((h.x_fn Ya _ (mζb L)).mul_right (h.x_fn Ya _ (mGi L))).eq.symm
end Formalism.FourierDecayAlt.P.Fr9
