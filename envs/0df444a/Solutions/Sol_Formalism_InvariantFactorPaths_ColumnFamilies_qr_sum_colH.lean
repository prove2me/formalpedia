-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_sum_colH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:44.986609+00:00
-- url     : https://prove2.me/submissions/6d919108-0500-4bfe-aaae-5afe87305b00

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightSpaceFinite
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestWeightIntegral

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
variable {m : ℕ} {lam : Fin (m + 1) → ℤ} {nu : Fin m → ℤ}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} (mu : Fin n → ℤ) (L U : ℤ) (h : ∀ a, L ≤ mu a ∧ mu a ≤ U) :
    ∑ c ∈ Finset.Ioc L U, (colH mu c : ℤ) = ∑ a, (mu a - L) := by
  have h1 : ∀ c, (colH mu c : ℤ) = ∑ a, if c ≤ mu a then 1 else 0 := by
    intro c
    rw [colH, Finset.card_filter]; push_cast; rfl
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have h2 : (Finset.Ioc L U).filter (fun c => c ≤ mu a) = Finset.Ioc L (mu a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    have := (h a).2
    constructor
    · rintro ⟨⟨h3, _⟩, h4⟩; exact ⟨h3, h4⟩
    · rintro ⟨h3, h4⟩; exact ⟨⟨h3, h4.trans this⟩, h4⟩
  rw [h2, Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.2 (h a).1)]
end Formalism.InvariantFactorPaths.ColumnFamilies
