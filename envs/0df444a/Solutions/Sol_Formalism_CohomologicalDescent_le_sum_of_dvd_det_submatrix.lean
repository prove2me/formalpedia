-- Prove2me | solution 1 for Formalism.CohomologicalDescent.le_sum_of_dvd_det_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:35.478631+00:00
-- url     : https://prove2.me/submissions/e498bf0d-bb04-4bbc-92bd-9096ffb44b21

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWAssembled
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MinorValuationBoundHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightExchangeChainHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Theorems.Thm_Formalism_CohomologicalDescent_lw_det_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] (π : R) (hπ : Prime π) {t n : ℕ}
    (Φ : Matrix (Fin n) (Fin n) R) (b : Fin n → ℕ) (pos : Fin t → Fin n)
    (hinj : Function.Injective pos) (hpos : ∀ s j, b j = b (pos s) → j = pos s)
    (hΦ : Φ.BlockTriangular b) (al : Fin t → ℕ)
    (hdiag : ∀ s, ∃ u : Rˣ, Φ (pos s) (pos s) = (u : R) * π ^ al s) (c : ℕ)
    (hdvd : π ^ c ∣ (Φ.submatrix pos pos).det) : c ≤ ∑ s, al s := by
  have hbp : Function.Injective (b ∘ pos) := fun s s' hs => hinj (hpos s' (pos s) hs)
  have hdet := lw_det_inj (Φ.submatrix pos pos) (b ∘ pos) hΦ.submatrix hbp
  simp only [Matrix.submatrix_apply] at hdet
  choose u hu using hdiag
  rw [hdet, Finset.prod_congr rfl (fun s _ => hu s), Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Units.coe_prod, Units.dvd_mul_left] at hdvd
  exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_unit).1 hdvd
end Formalism.CohomologicalDescent
