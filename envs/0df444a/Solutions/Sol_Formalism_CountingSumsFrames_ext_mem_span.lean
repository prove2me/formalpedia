-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ext_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:42.996796+00:00
-- url     : https://prove2.me/submissions/aa5528ef-32d5-4cbf-b534-00eb9d488658

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_ext_eq_sum
import Theorems.Thm_Formalism_CountingSumsFrames_monomial_ltr_supported

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (j0 : ℕ) (U : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (hφ : ∀ x, φ x ∈ U)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ x ∈ Submodule.span ℚ_[p] {x | ∃ g ∈ U,
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | j0 ≤ (v.1 : ℕ)}, x = g * q} := by
  classical
  rw [ext_eq_sum (fsj N r j0) φ x (x.support.image (ltr (fsj N r j0))) (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨m', -, rfl⟩ := Finset.mem_image.mp hm
  exact Submodule.subset_span ⟨_, hφ _, _, monomial_ltr_supported j0 m', rfl⟩
end Formalism.CountingSumsFrames
