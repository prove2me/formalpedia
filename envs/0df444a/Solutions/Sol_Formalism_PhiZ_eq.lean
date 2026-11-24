-- Prove2me | solution 1 for Formalism.PhiZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:11:15.21267+00:00
-- url     : https://prove2.me/submissions/6aeabd9b-2e5f-4447-810a-dc6e9cccda20

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_AZ_eq
import Theorems.Thm_Formalism_AZ_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution {ε C θ : ℝ} {s : ℂ} (hs1 : s ≠ 1) (hs0 : s ≠ 0) (hZ : riemannZeta₁ s ≠ 0) :
    PhiZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold PhiZ
  rw [dslope_of_ne _ hs1, slope_def_field, AZ_one, sub_zero, AZ_eq hZ]
  field_simp
end Formalism
