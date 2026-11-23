-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.det8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:04:08.625537+00:00
-- url     : https://prove2.me/submissions/d9c8843e-4c5c-40ce-8d07-8a5b891e5741

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_shift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_IsPoly_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_det_eight_at_good_point
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_q
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_diagonal_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_t21
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_upper_right_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_isPoly_upper_left_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx7_good_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (hSc : SSScalar) (hSh : SSShift) (hR : RhoUp) (hLF : LevFns) (hLN : LevNab) (hLNs : LevNabs)
    (hSG : StarGens) (hN : NabSS) (hNorm : SSNorm) (hMix : SSMixed) (hCurv : Curvature) (hQN : QQNormal)
    (P : Par) (hP : P.OK) (Y : ℂ) : Det8 P Y := by
  have hg : ∀ Z, Z ∉ (↑(badSet P) : Set ℂ) → Det8 P Z := by
    intro Z hZ
    have hZ' : Z ∉ badSet P := by simpa using hZ
    refine det_eight_at_good_point hSc hSh hR hLF hLN hLNs hSG hN hNorm hMix hCurv hQN P hP Z ?_ ?_ ?_
    · intro π; have := good_of P Z hZ' 0 (Or.inl rfl) π; rwa [add_zero] at this
    · exact good_of P Z hZ' 1 (Or.inr (Or.inl rfl))
    · intro π; have := good_of P Z hZ' 2 (Or.inr (Or.inr rfl)) π
      rwa [show Z + 2 = Z + 1 + 1 by ring] at this
  have hfin : (↑(badSet P) : Set ℂ).Finite := Finset.finite_toSet _
  have p11 := isPoly_upper_left_entry P
  have p12 := isPoly_upper_right_entry P
  have p21 := isPoly_t21 P
  have p22 := isPoly_diagonal_entry P
  have s11 := p11.shift 1
  have s12 := p12.shift 1
  have s21 := p21.shift 1
  have s22 := p22.shift 1
  have pq := isPoly_q P
  have p0 : IsPoly (fun _ : ℂ => (0 : A P)) := IsPoly.const 0
  exact ⟨((s11.mul p21).sub (s21.mul p11)).ext p0 hfin (fun Z hZ => (hg Z hZ).1) Y,
    ((s11.mul p22).sub (s21.mul p12)).ext pq hfin (fun Z hZ => (hg Z hZ).2.1) Y,
    ((s12.mul p21).sub (s22.mul p11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.1) Y,
    ((s12.mul p22).sub (s22.mul p12)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.1) Y,
    ((p11.mul s12).sub (p12.mul s11)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.2.1) Y,
    ((p11.mul s22).sub (p12.mul s21)).ext pq hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.1) Y,
    ((p21.mul s12).sub (p22.mul s11)).ext pq.neg hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.2.1) Y,
    ((p21.mul s22).sub (p22.mul s21)).ext p0 hfin (fun Z hZ => (hg Z hZ).2.2.2.2.2.2.2) Y⟩
end Formalism.FourierDecayAlt.P.Mx7
