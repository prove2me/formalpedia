-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.neg_log_deriv_eq_lseries_re_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:57:45.261677+00:00
-- url     : https://prove2.me/submissions/54ae66b7-7a31-45bb-b721-fdca1d489a92

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharRe_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharIm_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_lseries_summable_of_vonMangoldt_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_eq_lseries_mul_vonMangoldt

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
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {w : ℂ} (hw : 1 < w.re) :
    negLD χ w = LSeries (fun n => (vonMangoldtCharRe χ n : ℂ)) w +
      I * LSeries (fun n => (vonMangoldtCharIm χ n : ℂ)) w := by
  have h1 := lseries_summable_of_vonMangoldt_bound (vonMangoldtCharRe_bound χ) hw
  have h2 := lseries_summable_of_vonMangoldt_bound (vonMangoldtCharIm_bound χ) hw
  rw [neg_log_deriv_eq_lseries_mul_vonMangoldt χ hw, ← LSeries_smul, ← LSeries_add h1 (h2.smul I)]
  congr 1
  funext n
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, vonMangoldtCharRe, vonMangoldtCharIm]
  push_cast
  conv_lhs => rw [← Complex.re_add_im (χ (n : ZMod q))]
  ring
end Formalism.ZeroFreeDirichlet
