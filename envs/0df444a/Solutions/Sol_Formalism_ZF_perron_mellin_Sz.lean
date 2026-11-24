-- Prove2me | solution 1 for Formalism.ZF.perron_mellin_Sz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:34:43.405798+00:00
-- url     : https://prove2.me/submissions/cb278d39-4e7d-4d8c-bb34-004df37e45eb

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
theorem _root_.solution {w : ℂ} (hw : 1 < w.re) :
    mellin (fun x : ℝ => (Formalism.Sz x : ℂ)) (-w) =
      -(deriv riemannZeta w / riemannZeta w) / (w * (w - 1)) := by
  have h1 := perron_mellinSgen_Λ.2.2 w hw
  rw [← perron_Sz_eq_Sa] at h1
  rw [mellin]
  have hzero : ∀ t ∈ Ioi (0:ℝ) \ Ioi 1, (t : ℂ) ^ (-w - 1) • ((Formalism.Sz t : ℝ) : ℂ) = 0 := by
    intro t ht
    have : t ≤ 1 := not_lt.1 ht.2
    rw [perron_Sz_eq_zero_of_le_one this]
    simp
  rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi zero_le_one) hzero]
  simp_rw [smul_eq_mul, mul_comm ((_ : ℂ) ^ (-w - 1))]
  rw [h1, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hw]
  ring
end Formalism.ZF
