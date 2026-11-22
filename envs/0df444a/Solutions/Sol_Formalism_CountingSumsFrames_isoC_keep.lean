-- Prove2me | solution 1 for Formalism.CountingSumsFrames.isoC_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:06.018537+00:00
-- url     : https://prove2.me/submissions/e688992a-f5eb-4b38-a06d-c1444a178e55

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_isoC_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_hwc_le_isoC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hh : ∀ x ∈ HWC p LL j univ la, Q x ∈ HWC p LL j univ la) :
    ∀ x ∈ IsoC p LL j univ la, Q x ∈ IsoC p LL j univ la := by
  have : IsoC p LL j univ la ≤ IsoC p LL j univ la ⊓ (IsoC p LL j univ la).comap Q := by
    refine sInf_le ⟨fun x hx => ⟨hwc_le_isoC LL j la hx, hwc_le_isoC LL j la (hh x hx)⟩, ?_⟩
    intro c _ d _ x hx
    refine ⟨isoC_glStable LL j la c d x hx.1, ?_⟩
    change Q (glAct p LL j c d x) ∈ IsoC p LL j univ la
    rw [hc]
    exact isoC_glStable LL j la c d _ hx.2
  exact fun x hx => (this hx).2
end Formalism.CountingSumsFrames
