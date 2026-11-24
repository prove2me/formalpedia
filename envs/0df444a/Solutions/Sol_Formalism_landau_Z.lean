-- Prove2me | solution 1 for Formalism.landau_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:21.183347+00:00
-- url     : https://prove2.me/submissions/6b181acd-a224-48ac-95f6-dfc08f72708b

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_measurable_HZ
import Theorems.Thm_Formalism_rint_HZ
import Theorems.Thm_Formalism_PhiZ_eq_IZ
import Theorems.Thm_Formalism_PhiZ_analyticAt
import Theorems.Thm_Formalism_ne_ofReal_of_lt_re
import Theorems.Thm_Formalism_ne_zero_of_lt_re
import Theorems.Thm_Formalism_ofReal_ne_ofReal_of_lt
import Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_one_le_re
import Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_real_mem_Ioo


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
theorem _root_.solution (h2 : LandauEq) (h3 : MellinSgen) (h5 : MellinElem) (h8 : ZetaRealNonvanish)
    {ε C θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x) :
    ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1) := by
  intro σ hσ
  refine (h2 (HZ ε C θ) θ 1 hθ1 (measurable_HZ h3 ε C θ).aestronglyMeasurable
    (fun x hx => hH x (le_of_lt hx)) (fun σ hσ => rint_HZ h3 h5 hθ1 hσ) (PhiZ ε C θ)
    ?_ ?_ (fun s hs => PhiZ_eq_IZ h3 h5 hθ1 hs) σ hσ).1
  · intro s hs
    exact PhiZ_analyticAt ε C θ (ne_zero_of_lt_re zero_le_one hs)
      (riemannZetaOne_ne_zero_of_one_le_re hs.le) (ne_ofReal_of_lt_re (by linarith))
  · intro σ h1' h2'
    have hσ0 : (σ : ℂ) ≠ 0 := by exact_mod_cast (show σ ≠ 0 by linarith)
    have hσθ : (σ : ℂ) ≠ θ := ofReal_ne_ofReal_of_lt (by linarith)
    refine PhiZ_analyticAt ε C θ hσ0 ?_ hσθ
    rcases h2'.lt_or_eq with h2' | h2'
    · exact riemannZetaOne_ne_zero_of_real_mem_Ioo h8 (by linarith) h2'
    · subst h2'
      exact riemannZetaOne_ne_zero_of_one_le_re (by simp)
end Formalism
