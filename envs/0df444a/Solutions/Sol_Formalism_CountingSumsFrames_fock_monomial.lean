-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:23.540919+00:00
-- url     : https://prove2.me/submissions/f83d9d11-eafe-4bc4-a6f6-0a2a21c92a03

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

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
theorem _root_.solution {σ : Type} (z : MvPolynomial σ ℚ_[p]) (m0 : σ →₀ ℕ) (hm0 : m0 ∈ z.support) :
    fock p z (monomial m0 1) = coeff m0 z * (m0.prod fun _ k => (k.factorial : ℚ_[p])) := by
  classical
  unfold fock
  rw [Finset.sum_eq_single m0]
  · rw [coeff_monomial, if_pos rfl, mul_one]
  · intro b _ hb; rw [coeff_monomial, if_neg (Ne.symm hb)]; ring
  · intro h; exact absurd hm0 h
end Formalism.CountingSumsFrames
