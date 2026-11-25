-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.levelPlace_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:38:51.62346+00:00
-- url     : https://prove2.me/submissions/c93cbe5e-6f2b-4a89-9341-bf003c5f12fe

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_levelCeil_tower
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_levelPlace_any

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (nnL nnF q Z1 Z2 : K) (T c : ℕ) (DL Dk g : ℝ) (ρ1 ρ2 : ℤ) (h1 : nnL ≠ 0) (h2 : nnF ≠ 0) (h3 : q ≠ 0)
    (h4 : Z1 ≠ 0) (h5 : Z2 ≠ 0) (z1 : vw w Z1 = 0) (z2 : vw w Z2 = 0) (hq : 0 ≤ vw w q) (hT : 1 ≤ T) (h0 : 0 ≤ DL)
    (hTD : (T : ℝ) * DL ≤ Dk) (hg : 2 * Dk + 2 < g) (r1 : 0 ≤ ρ1) (r2 : 0 ≤ ρ2) (hρ : ramw w = ρ1 * ρ2) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ - vw w ((nnL * Z1) ^ T * (nnF * q ^ c * Z2)) ≤
      ramw w * (2 * (T : ℤ)) - vw w (nnL ^ T * nnF) := by
  exact levelPlace_any K w nnL nnF q Z1 Z2 T c _ h1 h2 h3 h4 h5 z1 z2 hq hT
    (by rw [hρ]; exact levelCeil_tower ρ1 ρ2 T DL Dk g r1 r2 h0 hTD hg)
end Formalism.EigenvalueLevelCeiling
