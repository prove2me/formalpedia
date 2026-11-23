-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.pw_shape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:25.918279+00:00
-- url     : https://prove2.me/submissions/839ac6ac-030b-4c9d-976b-93d7f32c6bae

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_one_add_EE
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_ys_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_pw_lastE_rev
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution {m : ℕ} (hm : 1 ≤ m) (t c : K) (ξ : Fin m → K) (N : Pr (m + 1) → K) :
    Hm t c ξ (1 + EE N) = HH t (Fin.cons (t * lastE ξ) (xs (t • N)) : Fin (m + 1) → K)
      (ys (t • N) (pw_Mx t (1 + EE N) *ᵥ ξ + pw_bv c)) := by
  ext i j
  refine Fin.cases ?_ (fun i' => ?_) i
  · refine Fin.cases ?_ (fun j' => ?_) j
    · have h0 : (0 : Fin (m + 1)) ≠ Fin.last m := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      simp only [Hm, HH, Fin.cases_zero, if_true, Fin.cons_zero, if_neg h0, add_zero]
      rw [pw_lastE_rev, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pw_one_add_EE]
      by_cases hk : k.val = 0
      · have : k.castSucc = 0 := by ext; simpa using hk
        rw [if_pos this, if_pos hk]; ring
      · have : k.castSucc ≠ 0 := by
          intro h; apply hk; have := congrArg Fin.val h; simpa using this
        rw [if_neg this, if_neg hk, dif_neg (by simp)]; ring
    · have h0 : (0 : Fin (m + 1)) ≠ j'.succ := (Fin.succ_ne_zero j').symm
      have h1 : (0 : Fin (m + 1)) < j'.succ := Fin.succ_pos j'
      simp only [Hm, HH, Fin.cases_zero, if_neg h0, dif_pos h1]
      rw [pw_ys_zero]
      simp only [Pi.add_apply, Matrix.mulVec, dotProduct, pw_Mx, pw_bv]
      congr 1
      rw [← Equiv.sum_comp Fin.revPerm]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      ring
  · simp only [Hm, HH, Fin.cases_succ]
    rw [pw_one_add_EE]
    by_cases h1 : i'.succ = j
    · subst h1
      have h2 : i'.castSucc ≠ i'.succ := (Fin.castSucc_lt_succ).ne
      rw [if_pos rfl, if_neg h2, dif_pos Fin.castSucc_lt_succ, Fin.cons_succ]
      rfl
    · rw [if_neg h1]
      by_cases h2 : i'.succ < j
      · have h3 : i'.castSucc < j := lt_trans Fin.castSucc_lt_succ h2
        rw [dif_pos h2, if_neg h3.ne, dif_pos h3, pw_ys_succ _ _ _ _ h2 h3]
        rfl
      · rw [dif_neg h2]
        by_cases h3 : j.val + 1 = i'.succ.val
        · have h4 : i'.castSucc = j := by ext; simp at h3 ⊢; omega
          rw [if_pos h3, if_pos h4, mul_one]
        · have h4 : i'.castSucc ≠ j := by
            intro h; apply h3; rw [← h]; simp
          have h5 : ¬ i'.castSucc < j := by
            intro h
            rw [Fin.lt_def] at h h2
            have h6 : i'.succ.val ≠ j.val := fun e => h1 (Fin.ext e)
            simp at h h2 h6; omega
          rw [if_neg h3, if_neg h4, dif_neg h5, mul_zero]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
