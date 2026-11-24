-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TInvW.transfer_invariance_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:23:27.967993+00:00
-- url     : https://prove2.me/submissions/4a0466b1-dde0-4656-967c-11182bfdea64

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceRestriction
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_TransferInvarianceCongruence
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_hpart1_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_hpart2_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_rdV_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_rdV_right
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpart1_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_hpart2_conj
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_exp_conj_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_bvec_posL_outer
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_col
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_inv
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_glev_unit
import Theorems.Thm_Formalism_FourierDecayAlt_Q_TInvW_posL_inj
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_mul__c26af469cc3a
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_Q_TInvW_glev_row__71270a473e04


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TInvW
theorem _root_.solution : StepRight := by
  intro E _ _ k r i D a b f s' g hD hf hs' hg hgs
  have hgs'G : g * s' ∈ Glev k r i := glev_mul' hg hs'
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf (g * s') ⟨hgs'G, hgs⟩
  have hu := glev_unit hs'
  have hiG := glev_inv hs'
  have hsU : s' ∈ UH (Hpk k r) := by
    have h0 := hs'
    simp only [Glev, Set.mem_setOf_eq] at h0
    exact h0.1
  have hEH : ∀ Z : Mx k r, (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • hpart1 (Hpk k r) Z) ∈ Glev k r i) →
      (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • hpart2 (Hpk k r) Z) ∈ Glev k r i) →
      RdV (hpart1 (Hpk k r) Z) f (g * s') + Complex.I • RdV (hpart2 (Hpk k r) Z) f (g * s') =
        lam (fderiv ℝ F (g * s')) (g * s') Z := by
    intro Z h1 h2
    rw [rdV_ext i _ h1 f F U (g * s') hU hgU hgs'G hF hfF, rdV_ext i _ h2 f F U (g * s') hU hgU hgs'G hF hfF]
    rfl
  have hinj : ∀ c c' : Fin (mdim k r i), posL k r i c = posL k r i c' ↔ c = c' :=
    fun c c' => ⟨posL_inj, congrArg _⟩
  have hconj : s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s' =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ) := by
    ext x y
    have hL : (s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s') x y =
        s'⁻¹ x (posL k r i a) * s' (posL k r i b) y := by
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and, ite_mul]
    rw [hL]
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, blk]
    by_cases hx : ∃ c, posL k r i c = x
    · by_cases hy : ∃ d, posL k r i d = y
      · obtain ⟨c0, rfl⟩ := hx
        obtain ⟨d0, rfl⟩ := hy
        simp [hinj, ite_and]
      · push_neg at hy
        have h0 : s' (posL k r i b) y = 0 := by
          rw [glev_col hs' _ y (fun d e => hy d e.symm), (bvec_posL_outer b y (fun d e => hy d e.symm)).1]
        simp [h0, hy]
    · push_neg at hx
      have h0 : s'⁻¹ x (posL k r i a) = 0 := by
        rw [glev_row' hiG x _ (fun c e => hx c e.symm), (bvec_posL_outer a x (fun c e => hx c e.symm)).2]
      simp [h0, hx]
  calc EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g
      = lam (fderiv ℝ F (g * s')) (g * s') (s'⁻¹ * Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * s') := by
        show RdV _ (fun x => f (x * s')) g + Complex.I • RdV _ (fun x => f (x * s')) g = _
        rw [rdV_right _ _ _ _ hu.1 hu.2, rdV_right _ _ _ _ hu.1 hu.2, ← hpart1_conj hsU, ← hpart2_conj hsU]
        exact hEH _ (fun t => by rw [hpart1_conj hsU]; exact exp_conj_mem hs' (exp_hpart1_mem i a b) t)
          (fun t => by rw [hpart2_conj hsU]; exact exp_conj_mem hs' (exp_hpart2_mem i a b) t)
    _ = ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) •
          lam (fderiv ℝ F (g * s')) (g * s') (Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) := by
        rw [hconj]
        change lamL (fderiv ℝ F (g * s')) (g * s')
          (∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • Matrix.single (posL k r i c) (posL k r i d) (1 : ℂ)) = _
        simp only [map_sum, map_smul]
        rfl
    _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← hEH _ (exp_hpart1_mem i c d) (exp_hpart2_mem i c d)]
        rfl
end Formalism.FourierDecayAlt.Q.TInvW
