-- Prove2me | solution 1 for Formalism.PhiZ_eq_IZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:54.856523+00:00
-- url     : https://prove2.me/submissions/bf897fc4-6f66-4493-8502-6f39d99e7001

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_mellin_HZ
import Theorems.Thm_Formalism_PhiZ_eq
import Theorems.Thm_Formalism_ne_one_of_one_lt_re
import Theorems.Thm_Formalism_ne_zero_of_lt_re
import Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_one_le_re


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
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) : PhiZ ε C θ s = IZ ε C θ s := by
  rw [mellin_HZ h3 h5 hθ hs, PhiZ_eq (ne_one_of_one_lt_re hs) (ne_zero_of_lt_re zero_le_one hs)
    (riemannZetaOne_ne_zero_of_one_le_re hs.le)]
end Formalism
