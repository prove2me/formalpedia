-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.psd_compress
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:27:10.680024+00:00
-- url     : https://prove2.me/submissions/1318389c-178e-4a10-ba27-3871b4b04402

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_decay_sum_mult
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution {Z X J : Type} [Fintype J] [DecidableEq Z] (P : Finset Z) (H : Z → Z → ℂ)
    (hH : PSDOn P H) (Y : J → Finset X) (g : J → X → Z) (hg : ∀ j, ∀ h ∈ Y j, g j h ∈ P) :
    Matrix.PosSemidef (Matrix.of fun j k : J => ∑ h ∈ Y j, ∑ h' ∈ Y k, H (g j h) (g k h')) := by
  have hH' : Matrix.PosSemidef (Matrix.of fun x y : P => H x y) := hH
  have key : ∀ (j : J) (F : Z → ℂ),
      ∑ p : P, (∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0) * F p = ∑ h ∈ Y j, F (g j h) :=
    fun j F => sum_mult P F (Y j) (g j) (hg j)
  have hst : ∀ (j : J) (p : P), star (∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0)
      = ∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0 := by
    intro j p
    rw [star_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  have hmat := hH'.conjTranspose_mul_mul_same
    (Matrix.of fun (p : P) (j : J) => ∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0)
  convert hmat using 1
  ext j k
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hst]
  have e1 : ∀ q : P, ∑ p : P, (∑ h ∈ Y j, if g j h = (p : Z) then (1 : ℂ) else 0) * H p q
      = ∑ h ∈ Y j, H (g j h) q := fun q => key j (fun z => H z q)
  simp only [e1]
  have e2 : ∑ q : P, (∑ h ∈ Y j, H (g j h) q) * (∑ h' ∈ Y k, if g k h' = (q : Z) then (1 : ℂ) else 0)
      = ∑ h' ∈ Y k, ∑ h ∈ Y j, H (g j h) (g k h') := by
    refine Eq.trans ?_ (key k (fun z => ∑ h ∈ Y j, H (g j h) z))
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [e2, Finset.sum_comm]
end Formalism.FourierDecayAlt.P.JCx1.decay
