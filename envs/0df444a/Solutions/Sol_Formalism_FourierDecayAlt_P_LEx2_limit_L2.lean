-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.limit_L2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:06.401238+00:00
-- url     : https://prove2.me/submissions/4203f152-0271-4891-8ac4-900b09be8365

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_smoothLog_sc
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_ld
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_sq_comb_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_sq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : CutoffLimitInL2 := by
  intro hLeib hCut B A A' _ T u wt c M m hm hpos hmw hJ hP hmS hI
  choose Cf hCf using fun p => hCut c m p hm
  set K : ℝ := (∑ p ∈ range (M+1), |Cf p|) + 1 with hKdef
  have hCK : ∀ p ∈ range (M+1), |Cf p| ≤ K - 1 := by
    intro p hp
    have := Finset.single_le_sum (f := fun p => |Cf p|) (fun i _ => abs_nonneg _) hp
    simp only [hKdef]; linarith
  have hg : Integrable (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) B.μ :=
    (integrable_finsetSum _ fun p _ => hI p).const_mul _
  have hform : ∀ ε : ℝ, T (mulF B (c.sc ε m) u) =
      fun ω a => ∑ p ∈ range (M + 1), ((ld p (c.sc ε m) (B.G ω) : ℝ) : ℂ) * dS B T u p ω a / p.factorial := by
    intro ε; funext ω a; exact hLeib B A A' T u M hJ hP _ (smoothLog_sc c ε m) ω a
  have hmT : ∀ (ε : ℝ) a, Measurable fun ω => T (mulF B (c.sc ε m) u) ω a := by
    intro ε a
    rw [hform]
    refine Finset.measurable_sum _ fun p _ => ?_
    refine Measurable.div_const (Measurable.mul ?_ (hmS p a)) _
    exact Complex.measurable_ofReal.comp ((meas_ld p _ (smoothLog_sc c ε m)).comp B.G_meas)
  have hmTu : ∀ a, Measurable fun ω => T u ω a := by
    intro a; have := hmS 0 a; rwa [dS_zero] at this
  constructor
  · intro ε hε
    refine hg.mono' (meas_sq B wt _ hmw (hmT ε)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hform]
    refine sq_comb_le B wt hpos (dS B T u) M (fun p ω => ld p (c.sc ε m) (B.G ω)) K ?_ ω
    intro p hp ω
    have := (hCf p ε (B.G ω) hε (B.G_pos ω)).1
    have h2 := hCK p hp
    linarith [le_abs_self (Cf p)]
  · have hdiff : ∀ ε : ℝ, (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) =
        fun ω a => ∑ p ∈ range (M + 1),
          ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial := by
      intro ε; funext ω a
      rw [hform]
      have : T u ω a = ∑ p ∈ range (M+1), (((if p = 0 then 1 else 0 : ℝ)) : ℂ) * dS B T u p ω a / p.factorial := by
        rw [Finset.sum_eq_single 0]
        · simp [dS_zero]
        · intro p _ hp; simp [hp]
        · intro h; simp at h
      rw [this, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      push_cast; ring
    suffices key : Tendsto (fun ε : ℝ => ∫ ω, LE.sq B wt (fun ω a => T (mulF B (c.sc ε m) u) ω a - T u ω a) ω ∂B.μ)
        (𝓝[>] 0) (𝓝 (∫ _ω, (0:ℝ) ∂B.μ)) by simpa using key
    refine tendsto_integral_filter_of_dominated_convergence
      (fun ω => ((M:ℝ) + 1) * K ^ 2 * ∑ p ∈ range (M + 1), LE.sq B wt (dS B T u p) ω) ?_ ?_ hg ?_
    · refine Eventually.of_forall fun ε => ?_
      exact (meas_sq B wt _ hmw (fun a => (hmT ε a).sub (hmTu a))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω), hdiff]
      refine sq_comb_le B wt hpos (dS B T u) M
        (fun p ω => ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0)) K ?_ ω
      intro p hp ω
      have h1 := (hCf p ε (B.G ω) hε (B.G_pos ω)).1
      have h2 := hCK p hp
      have h3 : |(if p = 0 then (1:ℝ) else 0)| ≤ 1 := by split_ifs <;> simp
      calc _ ≤ |ld p (c.sc ε m) (B.G ω)| + |(if p = 0 then (1:ℝ) else 0)| := abs_sub _ _
        _ ≤ K := by linarith [le_abs_self (Cf p)]
    · refine Eventually.of_forall fun ω => ?_
      refine tendsto_const_nhds.congr' ?_
      have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω) := Ioo_mem_nhdsGT (B.G_pos ω)
      filter_upwards [this] with ε hε
      rw [hdiff]
      unfold LE.sq
      symm
      refine Finset.sum_eq_zero fun a _ => ?_
      have : ∑ p ∈ range (M + 1),
          ((ld p (c.sc ε m) (B.G ω) - (if p = 0 then 1 else 0) : ℝ) : ℂ) * dS B T u p ω a / p.factorial = 0 := by
        refine Finset.sum_eq_zero fun p _ => ?_
        rw [(hCf p ε (B.G ω) hε.1 (B.G_pos ω)).2.2 hε.2]; simp
      beta_reduce
      rw [this]; simp
end Formalism.FourierDecayAlt.P.LEx2
