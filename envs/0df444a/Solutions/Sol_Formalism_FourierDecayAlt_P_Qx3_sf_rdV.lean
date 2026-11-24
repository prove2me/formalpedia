-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sf_rdV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:36:38.280684+00:00
-- url     : https://prove2.me/submissions/cb36a0bd-65cd-4001-8140-a5e6f4125304

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_glev_mul
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution {Φ : Fn k r E} {X : Mx k r} (hX : LieLev i X) (h : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c => RdV X (Φ c)) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  let L : XX k r →L[ℝ] XX k r := (ContinuousLinearMap.inr ℝ (Fin r → ℂ) (Mx k r)).comp
    ((mulRightRealCLM X).comp (ContinuousLinearMap.snd ℝ (Fin r → ℂ) (Mx k r)))
  refine ⟨U, fun x => fderiv ℝ F x (L x), hU, hxU, ?_, ?_⟩
  · exact (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply L.contDiff.contDiffOn
  · intro x hx hxG
    have hγ : HasDerivAt (fun t : ℝ => ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r)) (L x) 0 :=
      (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 X)
    have hγ0 : ((x.1, x.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) : XX k r) = x := by
      simp [NormedSpace.exp_zero]
    have hFd : DifferentiableAt ℝ F x :=
      (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    have hcomp : HasDerivAt (fun t : ℝ => F (x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)))
        (fderiv ℝ F x (L x)) 0 :=
      hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
    have hev : (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
        (fun t : ℝ => F (x.1, x.2 * NormedSpace.exp ((t : ℂ) • X))) := by
      have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r) ∈ U :=
        hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hx)
      filter_upwards [hmem] with t ht
      exact hΦ _ ht (glev_mul hxG (hX t))
    show deriv (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • X))) 0 = _
    rw [hev.deriv_eq]
    exact hcomp.deriv
end Formalism.FourierDecayAlt.P.Qx3
