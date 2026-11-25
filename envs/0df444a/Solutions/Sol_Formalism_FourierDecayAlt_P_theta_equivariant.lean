-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theta_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:08.154818+00:00
-- url     : https://prove2.me/submissions/6970b2e3-4d57-4f28-a16f-5c2a9ce2860f

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_op_local
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_op_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_omPlus_open
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_sgs_GV
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_sgs_Om
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_sgs_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordKeyIdentity_glev0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.JF.ThetaEquiv := by
  intro k r Wp Wq _ _ _ _ _ D Θ f hC hf hE p hp g hg
  have hx₀ : sgs p g ∈ Om k r D.z D.z' := PositiveOrbitOpen.sgs_Om D hp hg
  obtain ⟨U, F', hU, hx₀U, hF', hfe⟩ := hf (sgs p g) ⟨WordKeyIdentity.glev0 hx₀.1, hx₀.2⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU (sgs p g) hx₀U
  let b : ContDiffBump (sgs p g) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let ft : Mat k r → (Wq →L[ℂ] Wp) := fun y => b y • F' y
  have hft : ContDiff ℝ ((opOrder Θ : ℕ∞) : WithTop ℕ∞) ft := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Metric.ball (sgs p g) ε
    · exact b.contDiff.contDiffAt.smul (hF'.contDiffAt (hU.mem_nhds (hball hy)))
    · have hy' : y ∈ (Metric.closedBall (sgs p g) (ε / 2))ᶜ := by
        rw [Metric.mem_ball, not_lt] at hy
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
        linarith
      have he : ft =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy'] with w hw
        have : b w = 0 := by
          apply b.zero_of_le_dist
          simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hw
          exact hw.le
        show b w • F' w = 0
        rw [this, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hftCk : CkOn (opOrder Θ : ℕ∞) (GV k r) ft :=
    fun _ _ => ⟨Set.univ, ft, isOpen_univ, trivial, hft.contDiffOn, fun _ _ _ => rfl⟩
  have hagree : ∀ y ∈ Metric.ball (sgs p g) (ε / 4), y ∈ GV k r → ft y = f y := by
    intro y hy hyG
    have h1 : b y = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    show b y • F' y = f y
    rw [h1, one_smul, hfe y (hball (Metric.ball_subset_ball (by linarith) hy)) (WordKeyIdentity.glev0 hyG)]
  have hε4 : 0 < ε / 4 := by positivity
  have s5 : opApply Θ ft (sgs p g) = opApply Θ f (sgs p g) :=
    PositiveOrbitOpen.op_local Θ Metric.isOpen_ball hagree _ (Metric.mem_ball_self hε4) hx₀.1
  have s3 : opApply Θ (rho D p f) g = opApply Θ (rho D p ft) g := by
    refine PositiveOrbitOpen.op_local Θ (Metric.isOpen_ball.preimage (PositiveOrbitOpen.sgs_cont p)) (fun y hy hyG => ?_) g
      (Set.mem_preimage.2 (Metric.mem_ball_self hε4)) hg.1
    have hy' : sgs p y ∈ Metric.ball (sgs p g) (ε / 4) := hy
    unfold rho
    rw [hagree _ hy' (PositiveOrbitOpen.sgs_GV D hp hyG)]
  have s1 : opApply Θ f g = opApply Θ (xiP D p • rho D p f) g :=
    PositiveOrbitOpen.op_local Θ (PositiveOrbitOpen.omPlus_open D.z D.z') (fun y hy hyG => (hE p hp y ⟨hyG, hy⟩).symm) g hg.2 hg.1
  rw [s1, PositiveOrbitOpen.op_smul, s3, hC p hp ft hftCk g hg]
  unfold rho
  rw [s5]
end Formalism.FourierDecayAlt.P
