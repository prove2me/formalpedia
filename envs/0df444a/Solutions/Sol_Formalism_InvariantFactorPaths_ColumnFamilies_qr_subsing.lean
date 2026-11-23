-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_subsing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:19:27.110649+00:00
-- url     : https://prove2.me/submissions/09acd746-13ae-41ed-92d4-e08f873918da

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_colH_low
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qr_colH_high

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {m : ℕ} [NeZero m] {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hn : Dominant nu) {c : ℤ} (hc : c ∉ TCols nu) :
    Subsingleton {S : Finset (Fin m) // S.card = colH nu c} := by
  simp only [TCols, Finset.mem_Ioc, not_and_or, not_lt, not_le] at hc
  constructor
  rintro ⟨S, hS⟩ ⟨S', hS'⟩
  apply Subtype.ext
  show S = S'
  rcases hc with hc | hc
  · rw [qr_colH_low hn hc] at hS hS'
    rw [Finset.eq_univ_of_card S (by simpa using hS), Finset.eq_univ_of_card S' (by simpa using hS')]
  · rw [qr_colH_high hn hc] at hS hS'
    rw [Finset.card_eq_zero.1 hS, Finset.card_eq_zero.1 hS']
end Formalism.InvariantFactorPaths.ColumnFamilies
