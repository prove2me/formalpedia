-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.mellin_chebyshev_character
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:28.663795+00:00
-- url     : https://prove2.me/submissions/9da092de-f91a-40a6-8f23-73ca8a14718e

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharRe_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_vonMangoldtCharIm_bound
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_re_im
import Theorems.Thm_Formalism_ZeroFreeDirichlet_chebyshev_character_eq_zero_of_le_one
import Theorems.Thm_Formalism_ZeroFreeDirichlet_neg_log_deriv_eq_lseries_re_im
import Theorems.Thm_Formalism_ZeroFreeDirichlet_summatory_rpow_integrableOn
import Theorems.Thm_Formalism_mellinSgen


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
    mellin (fun x : ℝ => Schi χ x) (-w) = negLD χ w / (w * (w - 1)) := by
  have h1 := (Formalism.mellinSgen _ 1 (vonMangoldtCharRe_bound χ)).2.2 w hw
  have h2 := (Formalism.mellinSgen _ 1 (vonMangoldtCharIm_bound χ)).2.2 w hw
  unfold mellin
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi zero_le_one) ?_]
  · calc ∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-w - 1) • Schi χ t
        = ∫ t in Ioi (1:ℝ), ((Formalism.Sa (vonMangoldtCharRe χ) t : ℂ) * (t : ℂ) ^ (-w - 1) +
            I * ((Formalism.Sa (vonMangoldtCharIm χ) t : ℂ) * (t : ℂ) ^ (-w - 1))) := by
          congr 1; funext t; rw [chebyshev_character_re_im χ t, smul_eq_mul]; ring
      _ = (∫ t in Ioi (1:ℝ), (Formalism.Sa (vonMangoldtCharRe χ) t : ℂ) * (t : ℂ) ^ (-w - 1)) +
            I * ∫ t in Ioi (1:ℝ), (Formalism.Sa (vonMangoldtCharIm χ) t : ℂ) * (t : ℂ) ^ (-w - 1) := by
          rw [integral_add (summatory_rpow_integrableOn (vonMangoldtCharRe_bound χ) hw)
            ((summatory_rpow_integrableOn (vonMangoldtCharIm_bound χ) hw).const_mul I), integral_const_mul]
      _ = _ := by
          rw [h1, h2, neg_log_deriv_eq_lseries_re_im χ hw]
          ring
  · intro x hx
    have hx1 : x ≤ 1 := not_lt.mp hx.2
    simp [chebyshev_character_eq_zero_of_le_one χ hx1]
end Formalism.ZeroFreeDirichlet
