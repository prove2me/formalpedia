-- Prove2me | solution 1 for Formalism.mellin_Gz_n
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:08.25936+00:00
-- url     : https://prove2.me/submissions/e793a1ed-74d4-4720-85bd-abd545ee7a8b

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_logderiv_zeta_eq
import Theorems.Thm_Formalism_mellin_Gz
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
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {s : ℂ} (hs : 1 < s.re) :
    ∫ x in Ioi (1:ℝ), (Gz x : ℂ) * (x : ℂ) ^ (-s - 1) = nZ s / (s * (s - 1)) := by
  have hs1 : s ≠ 1 := ne_one_of_one_lt_re hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hs0 : s ≠ 0 := ne_zero_of_lt_re zero_le_one hs
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  have hZ1 := riemannZetaOne_ne_zero_of_one_le_re hs.le
  rw [(mellin_Gz h3 h5 hs).2, logderiv_zeta_eq hs1 hz]
  unfold nZ linZ
  field_simp
  ring
end Formalism
