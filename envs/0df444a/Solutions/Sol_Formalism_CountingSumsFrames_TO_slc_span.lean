-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.slc_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:46.994997+00:00
-- url     : https://prove2.me/submissions/5cdae16c-47ae-41a7-85a7-8a8953ef9d87

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_sl_mul
import Theorems.Thm_Formalism_CountingSumsFrames_TO_isF_of_polLz
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_rep_span


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
theorem _root_.solution (L : Letters N) (j0 : ℕ) (VF : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hVF : VF ≤ Pol p r (Lz L j0)) {z : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hz : z ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ VF,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q})
    (m : Fin N × Fin r →₀ ℕ) : slc (fsj N r j0) m z ∈ VF := by
  classical
  obtain ⟨s, a, hs, ha, rfl⟩ := rep_span VF j0 hz
  rw [map_sum]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hL : IsL (fsj N r j0) (monomial b (1 : ℚ_[p])) := by
    intro m' hm' v hv hfs
    have : m' = b := Finset.mem_singleton.mp (support_monomial_subset hm')
    subst this
    exact hv (hs m' hb v hfs)
  rw [sl_mul (fsj N r j0) m (isF_of_polLz L j0 (hVF (ha b))) hL]
  exact VF.smul_mem _ (ha b)
end Formalism.CountingSumsFrames.TO
