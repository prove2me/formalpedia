-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.chebyshev_character_integrableOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:33:20.810328+00:00
-- url     : https://prove2.me/submissions/66ca58a4-08ec-4547-931b-84ea25f8f122

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharRe_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharIm_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_re_im
import Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_rpow_integrableOn

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
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-w - 1) • Schi χ x) (Ioi 1) := by
  refine ((summatory_rpow_integrableOn (vonMangoldtCharRe_bound χ) hw).add
    ((summatory_rpow_integrableOn (vonMangoldtCharIm_bound χ) hw).const_mul I)).congr_fun (fun x _ => ?_) measurableSet_Ioi
  rw [Pi.add_apply, chebyshev_character_re_im χ x, smul_eq_mul]
  ring
end Formalism.ZeroFreeDirichlet
