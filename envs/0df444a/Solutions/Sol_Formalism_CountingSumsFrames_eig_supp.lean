-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eig_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:19.50375+00:00
-- url     : https://prove2.me/submissions/f08b5214-c6b7-44c4-9f18-f52adf60961f

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (c : Fin r) (k : ℤ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hy : glAct p LL j c c y = ((k : ℤ) : ℚ_[p]) • y) :
    y ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | wt LL j c m = k} := by
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  simp only [Finset.mem_coe, MvPolynomial.mem_support_iff] at hm
  have h1 := congrArg (coeff m) hy
  rw [coeff_cartan, coeff_smul, smul_eq_mul] at h1
  have h2 : ((wt LL j c m : ℤ) : ℚ_[p]) = ((k : ℤ) : ℚ_[p]) := mul_right_cancel₀ hm h1
  show wt LL j c m = k
  exact_mod_cast h2
end Formalism.CountingSumsFrames
