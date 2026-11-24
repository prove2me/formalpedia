-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx1.stepOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:39:56.581851+00:00
-- url     : https://prove2.me/submissions/01b21064-886d-4232-92d5-7d498570d46e

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MinLeTruncatedExponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_isExt_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_exists_max_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_mn_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_min_le_truncated_exponential
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_fsv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx1_ae_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_sup_bound_of_truncated_integral


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx1
open Finset Filter Topology MeasureTheory Real
open Formalism.FourierDecayAlt.TBB
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.TBBx1
theorem _root_.solution : StepOne := by
  intro Wp Wq _ _ _ _ _ _ P p nn F Y Λ K N hK hΛ hI2 hI3 j hj h hh w hw hlen c hc
  obtain ⟨φ, hφc, hφi, hφe⟩ := hI2 j hj h hh w hw (by omega)
  have hself : IsExt P p.l0 Y N K w w := isExt_self hw (by omega)
  obtain ⟨wm, hwm, hmax⟩ := exists_max_ext K w (fun w' => Ew p nn F j w' h) hself
  set M := Ew p nn F j wm h with hMdef
  have hint : ∀ s : ℂ, ∫ c, Complex.exp (2 * Complex.I * ((s * c).im : ℂ)) * φ c
      = ∫ c, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)]) := by
    intro s
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with c hc
    rw [fsv_eq, hφe c hc]
  have hbd : ∀ s : ℂ, ‖∫ c, P5.fsv s c * NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])‖ ≤
      mn Λ K ‖s‖ * M := by
    intro s
    obtain ⟨w', hw', hb⟩ := hI3 j hj h hh w hw hlen s
    exact hb.trans (mul_le_mul_of_nonneg_left (hmax w' hw') (mn_nonneg hΛ K (norm_nonneg _)))
  have hM : 0 ≤ M := by
    have h0 := hbd 0
    simp only [norm_zero, mn, if_true, one_mul] at h0
    exact (norm_nonneg _).trans h0
  have key : ∀ x : ℝ, 0 < x → Λ ≤ x → ‖φ c‖ ≤ 3 / π * x ^ 2 * M := by
    intro x hx hΛx
    refine Formalism.HermitianLatticeCounting.P.sup_bound_of_truncated_integral φ x M hφc hφi hx (fun s => ?_) c
    rw [hint s, mul_comm M]
    exact (hbd s).trans (mul_le_mul_of_nonneg_right (min_le_truncated_exponential hΛ hΛx hK (norm_nonneg _)) hM)
  have hre : Ew p nn F (j + 1) w (h ++ [(1, c)]) ≤ ‖φ c‖ := by
    show (NP p nn F (j + 1) w (h ++ [(1, c)]) (h ++ [(1, c)])).re ≤ _
    rw [← hφe c hc]
    exact Complex.re_le_norm _
  refine ⟨wm, hwm, hre.trans ?_⟩
  rcases hΛ.lt_or_eq with hpos | h0
  · exact key Λ hpos le_rfl
  · rw [← h0]
    have ht : Tendsto (fun x : ℝ => 3 / π * x ^ 2 * M) (𝓝[>] 0) (𝓝 (3 / π * 0 ^ 2 * M)) :=
      ((by fun_prop : Continuous fun x : ℝ => 3 / π * x ^ 2 * M).tendsto 0).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact key x hx (h0 ▸ le_of_lt hx)
end Formalism.FourierDecayAlt.P.TBBx1
