-- Prove2me | solution 1 for Formalism.ZF.perron_mellinConvergent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:34:39.395601+00:00
-- url     : https://prove2.me/submissions/9bbb892a-e0c9-4cae-b933-64253e0f3c9b

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Theorems.Thm_Formalism_ZF_perron_Sz_eq_Sa
import Theorems.Thm_Formalism_ZF_perron_Sz_eq_zero_of_le_one
import Theorems.Thm_P2M_Formalism_ZF_perron_mellinSgen___d65ae26d1cac

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {σ₀ : ℝ} (hσ : 1 < σ₀) :
    MellinConvergent (fun x : ℝ => (Formalism.Sz x : ℂ)) ((-σ₀ : ℝ) : ℂ) := by
  unfold MellinConvergent
  have h2 := perron_mellinSgen_Λ.2.1 σ₀ hσ
  rw [← perron_Sz_eq_Sa] at h2
  have hmeas : Measurable Formalism.Sz := by
    rw [perron_Sz_eq_Sa]; exact perron_mellinSgen_Λ.1
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (((-σ₀ : ℝ) : ℂ) - 1) • ((Formalism.Sz t : ℝ) : ℂ)) (Ioi 1) := by
    refine Integrable.mono' h2 ?_ ?_
    · exact ((Complex.continuous_ofReal.measurable.pow_const _).smul
        (Complex.continuous_ofReal.measurable.comp hmeas)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht), Complex.norm_real,
        Real.norm_eq_abs]
      simp [mul_comm]
  have hsplit : Ioi (0:ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ hI1
  refine (integrableOn_zero).congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp [perron_Sz_eq_zero_of_le_one ht.2]
end Formalism.ZF
