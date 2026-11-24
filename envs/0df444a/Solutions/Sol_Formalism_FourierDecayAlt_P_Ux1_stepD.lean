-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux1.stepD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:48.593898+00:00
-- url     : https://prove2.me/submissions/92c98684-cfa1-498e-8116-1df77d84ea70

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactlySupportedBanachModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_tuo_of_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_continuous_gN
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux1_cv_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gN_pos


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux1
theorem _root_.solution {b : Bool} {X g : Mat k r} (hX : inLie k r X) (hg : g ∈ GV k r) (a : ℝ)
    (Hn : ℕ → Mat k r → E) (H0 H1 : Mat k r → E) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hC : ∀ n, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Hn n))
    (h0 : ∀ n, ∀ h ∈ GV k r, ‖Hn n h - H0 h‖ ≤ gN h ^ (-a) * ε n)
    (h1 : ∀ n, ∀ h ∈ GV k r, ‖op b X (Hn n) h - H1 h‖ ≤ gN h ^ (-a) * ε n) :
    op b X H0 g = H1 g := by
  set γ : ℝ → Mat k r := fun t => cv b X t g with hγ
  have hγc : Continuous γ := cv_continuous b X g
  have hγG : ∀ t, γ t ∈ GV k r := fun t => cv_mem hX hg t
  have hwc : ContinuousOn (fun t => gN (γ t) ^ (-a)) (Metric.closedBall (0:ℝ) 1) := by
    intro t _
    exact (ContinuousAt.comp_of_eq (g := fun x : ℝ => x ^ (-a)) (f := fun t => gN (γ t))
      (Real.continuousAt_rpow_const _ _ (Or.inl (gN_pos (hγG t)).ne'))
      ((continuous_gN.comp hγc).continuousAt) rfl).continuousWithinAt
  obtain ⟨Bw, hBw⟩ := (isCompact_closedBall (0:ℝ) 1).exists_bound_of_continuousOn hwc
  have hεa : Tendsto (fun n => |ε n|) atTop (𝓝 0) := by simpa using hε.abs
  have hbd : ∀ t ∈ Metric.ball (0:ℝ) 1, ∀ n, gN (γ t) ^ (-a) * ε n ≤ Bw * |ε n| := by
    intro t ht n
    calc gN (γ t) ^ (-a) * ε n ≤ |gN (γ t) ^ (-a) * ε n| := le_abs_self _
      _ = ‖gN (γ t) ^ (-a)‖ * |ε n| := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ Bw * |ε n| := mul_le_mul_of_nonneg_right (hBw t (Metric.ball_subset_closedBall ht))
          (abs_nonneg _)
  have tu0 : TendstoUniformlyOn (fun n t => Hn n (γ t)) (fun t => H0 (γ t)) atTop (Metric.ball (0:ℝ) 1) :=
    tuo_of_bound hεa fun n t ht => le_trans (h0 n _ (hγG t)) (hbd t ht n)
  have tu1 : TendstoUniformlyOn (fun n t => op b X (Hn n) (γ t)) (fun t => H1 (γ t)) atTop
      (Metric.ball (0:ℝ) 1) :=
    tuo_of_bound hεa fun n t ht => le_trans (h1 n _ (hγG t)) (hbd t ht n)
  have hder : ∀ n, ∀ t ∈ Metric.ball (0:ℝ) 1,
      HasDerivAt (fun t => Hn n (γ t)) (op b X (Hn n) (γ t)) t := by
    intro n t _
    have hd := ckOn_diff 0 b (hC n) hX (hγG t)
    have e : (fun t' => Hn n (γ t')) = fun t' => Hn n (cv b X (t' - t) (γ t)) := by
      funext t'; simp only [hγ]; rw [← cv_add]; congr 2; ring
    rw [e]
    have h2 : HasDerivAt (fun s => Hn n (cv b X s (γ t))) (op b X (Hn n) (γ t)) (t - t) := by
      rw [sub_self]; exact hd.hasDerivAt
    exact h2.comp_sub_const t t
  have key := hasDerivAt_of_tendstoUniformlyOn (l := atTop) (f := fun n t => Hn n (γ t))
    (g := fun t => H0 (γ t)) (f' := fun n t => op b X (Hn n) (γ t)) (g' := fun t => H1 (γ t))
    Metric.isOpen_ball tu1 (Eventually.of_forall hder) (fun t ht => tu0.tendsto_at ht)
    (Metric.mem_ball_self one_pos)
  have e0 : γ 0 = g := cv_zero b X g
  show deriv (fun t => H0 (cv b X t g)) 0 = H1 g
  rw [key.deriv]
  simp only [e0]
end Formalism.FourierDecayAlt.P.Ux1
