-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leading_term_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:51.705912+00:00
-- url     : https://prove2.me/submissions/cd741cfd-c260-44e2-ae61-dd9b99eff0ac

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_qminor_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_lc_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_dual_vector_eq_zeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_sum_xb_y
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_chat_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_capelli_two_polynomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_coefOf_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.Leading := by
  intro E _ _ k r z z' i hz hz'
  refine ⟨Qx2.lowC k r z z' i, fun D f hD hf g hg Y => ?_⟩
  have hUH : g ∈ UH (Hpk k r) := hg.1.1
  have hu : ∀ Y : ℂ, uC k r i Y - 1 = Y + (((mdim k r i : ℂ) - 1) / 2 - 1) := fun Y => by
    unfold uC
    ring
  have hu0 : ∀ Y : ℂ, uC k r i Y = Y + ((mdim k r i : ℂ) - 1) / 2 := fun Y => rfl
  have s00 : Qx2.PolyAt (mdim k r i) (fun Y => tL k r z z' i Y 0 0 f g - Y ^ mdim k r i • f g) :=
    (Qx2.qminor_poly hD hf hg id id (((mdim k r i : ℂ) - 1) / 2)).congr fun Y => by
      rw [Qx2.lc_self id Function.injective_id, one_smul]
      rfl
  have s01 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 0 1 f g +
      (zetaL k r z z' i g * Y ^ (mdim k r i - 1)) • f g) :=
    (Qx2.chat_poly hD hf hg (fun _ => xv k r z' i) (ybv k r z i)
      (((mdim k r i : ℂ) - 1) / 2 - 1)).neg.congr fun Y => by
      rw [show tL k r z z' i Y 0 1 f g = -(chatL (EH k r) (posL k r i) (uC k r i Y - 1)
        (fun _ => xv k r z' i) (ybv k r z i) f g) from rfl, hu, Qx2.sum_dual_vector_eq_zeta z hz' g]
      module
  have s10 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 0 f g +
      (star (zetaL k r z z' i g) * Y ^ (mdim k r i - 1)) • f g) :=
    (Qx2.chat_poly hD hf hg (yv k r z i) (fun _ => xbv k r z' i)
      (((mdim k r i : ℂ) - 1) / 2)).neg.congr fun Y => by
      rw [show tL k r z z' i Y 1 0 f g = -(chatL (EH k r) (posL k r i) (uC k r i Y)
        (yv k r z i) (fun _ => xbv k r z' i) f g) from rfl, hu0, Qx2.sum_xb_y z hz' hUH]
      module
  have s11 : Qx2.PolyAt (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 1 f g) :=
    (Qx2.capelli_two_polynomial hD hf hg (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i)
      (((mdim k r i : ℂ) - 1) / 2 - 1)).neg.congr fun Y => by
      rw [show tL k r z z' i Y 1 1 f g = -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i)
        (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) f g) from rfl, hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sub_eq_iff_eq_add'.mp (Qx2.coefOf_spec s00 Y)
  · exact eq_neg_add_of_add_eq ((add_comm _ _).trans (Qx2.coefOf_spec s01 Y))
  · exact eq_neg_add_of_add_eq ((add_comm _ _).trans (Qx2.coefOf_spec s10 Y))
  · exact Qx2.coefOf_spec s11 Y
end Formalism.FourierDecayAlt.P
