-- Prove2me | solution 1 for Formalism.ZF.perron_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:52.670193+00:00
-- url     : https://prove2.me/submissions/335d9b15-44f9-4dce-b202-88ea0ea2661a

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Theorems.Thm_Formalism_ZF_perron_Sz_continuousAt
import Theorems.Thm_Formalism_ZF_perron_integrable_Fy
import Theorems.Thm_Formalism_ZF_perron_mellin_Sz
import Theorems.Thm_Formalism_ZF_perron_mellinConvergent
import Theorems.Thm_Formalism_ZF_perron_verticalIntegrable

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
theorem _root_.solution : Perron := by
  intro y hy σ₀ hσ
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  refine ⟨perron_integrable_Fy hy0 hσ, ?_⟩
  have hinv := mellinInv_mellin_eq (-σ₀) (fun x : ℝ => (Formalism.Sz x : ℂ)) hy0 (perron_mellinConvergent hσ)
    (perron_verticalIntegrable hσ) (perron_Sz_continuousAt y)
  rw [← hinv, mellinInv, Complex.real_smul]
  push_cast
  congr 1
  have hneg := integral_neg_eq_self (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) volume
  rw [← hneg]
  congr 1
  funext t
  have hre : 1 < ((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I).re := by simpa using hσ
  rw [show -(σ₀ : ℂ) + t * I = -((σ₀ : ℂ) + ((-t : ℝ) : ℂ) * I) by push_cast; ring,
    perron_mellin_Sz hre, neg_neg]
  unfold Fy
  rw [smul_eq_mul]
  ring
end Formalism.ZF
