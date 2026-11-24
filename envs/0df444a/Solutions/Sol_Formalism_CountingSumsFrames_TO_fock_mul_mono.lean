-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.fock_mul_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:55.73988+00:00
-- url     : https://prove2.me/submissions/5b260c88-faf9-4566-9b71-ed1e01d21dad

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_mul_monomial_orthogonal
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_prod
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (j0 : ℕ) {g g' : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hg : IsF (fsj N r j0) g)
    (hg' : IsF (fsj N r j0) g') (m m' : Fin N × Fin r →₀ ℕ) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) :
    fock p (g * monomial m 1) (g' * monomial m' 1) =
      if m = m' then fock p g g' * (m.prod fun _ k => (k.factorial : ℚ_[p])) else 0 := by
  have := fock_mul_monomial_orthogonal j0 g.support g'.support (fun a => coeff a g) (fun b => coeff b g')
    (fun a ha => hg a ha) (fun b hb => hg' b hb) m m' hm hm'
  rwa [← g.as_sum, ← g'.as_sum] at this
end Formalism.CountingSumsFrames.TO
