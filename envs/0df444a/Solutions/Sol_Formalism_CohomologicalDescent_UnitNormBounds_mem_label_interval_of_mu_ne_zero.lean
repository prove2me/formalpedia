-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.mem_label_interval_of_mu_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:24:30.254108+00:00
-- url     : https://prove2.me/submissions/bffb88ee-5d15-496f-95b0-ed5bb73b8e65

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_rowStart_rev_eq
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_content_label_eq
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_good_labels_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (k j t w M i : ℕ) (lam : Fin (k + j) → ℕ) (xm xp : ℤ) (hR : Rows k j t w M lam xm xp)
    (ct : ℤ) (hmu : mu t (M - w) i (dual M lam) (cont t w M ct) ≠ 0) : maxB t w < ct ∧ ct < xp := by
  have hb : ∀ a, w ≤ lam a ∧ lam a ≤ M := fun a => ⟨hR.low a, hR.high a⟩
  unfold mu at hmu
  obtain ⟨tau, htau, hbx⟩ := (Finset.lt_sup_iff).mp (Nat.pos_of_ne_zero hmu)
  unfold boxesOfContent at hbx
  obtain ⟨b, hbm⟩ := Finset.card_pos.mp hbx
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hbm).2
  have hU := rowStart_rev_eq k j t w M lam hb b
  have hc := content_label_eq t w M (le_trans (hb b).1 (hb b).2) ct
  obtain ⟨col, hcol⟩ : ∃ col : ℕ, (col : ℤ) = cont t w M ct + (b.val : ℤ) :=
    ⟨(cont t w M ct + (b.val : ℤ)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hg := (good_labels_holds k j t w M i lam hb tau htau b col (by omega) (by omega)).1
  unfold label at hg
  constructor
  · omega
  · by_cases hk : (Fin.rev b).val < k
    · have := (hR.cloud (Fin.rev b) hk).2
      omega
    · have := hR.rest (Fin.rev b) (by omega)
      have := hR.le
      omega
end Formalism.CohomologicalDescent.UnitNormBounds
