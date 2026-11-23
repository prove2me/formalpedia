-- Prove2me | solution 1 for Formalism.CountingSumsFrames.cartan_eig
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:19.425193+00:00
-- url     : https://prove2.me/submissions/0b302da3-e41b-41cb-94ab-cacdc80edbd4

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (μ : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ WtSpC p LL j univ μ) (c : Fin r) : glAct p LL j c c x = ((μ c : ℤ) : ℚ_[p]) • x := by
  unfold WtSpC at hx
  rw [MvPolynomial.mem_restrictSupport_iff] at hx
  ext m
  rw [coeff_cartan, coeff_smul, smul_eq_mul]
  by_cases hm : coeff m x = 0
  · rw [hm, mul_zero, mul_zero]
  · have h2 : ∀ c ∈ univ, wt LL j c m = μ c := hx (MvPolynomial.mem_support_iff.mpr hm)
    rw [h2 c (Finset.mem_univ c)]
end Formalism.CountingSumsFrames
