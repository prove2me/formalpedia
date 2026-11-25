-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.ratioPowLeProdMaxPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:58:23.434967+00:00
-- url     : https://prove2.me/submissions/1d1cd57d-4737-4336-9d0f-d1bd3e42e8f7

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem one_le_finset_prod_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := by
  calc (1:ℝ) = ∏ v ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ v ∈ s, y v := Finset.prod_le_prod (fun _ _ => zero_le_one) h
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Threshold := by
  intro N p D H₂ l hH hD hDl hlt
  have hQ1 : 1 < D l / H₂ := by rw [lt_div_iff₀ hH, one_mul]; exact hlt
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (Fin.pos l)
  have hN0 : (N:ℝ) ≠ 0 := hN.ne'
  have hP1 : 1 ≤ ∏ i, max 1 (D i / H₂) := one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _)
  have hPpos : 0 < ∏ i, max 1 (D i / H₂) := lt_of_lt_of_le one_pos hP1
  have hPQ : ∏ i, max 1 (D i / H₂) ≤ (D l / H₂) ^ N := by
    calc ∏ i, max 1 (D i / H₂) ≤ ∏ _i : Fin N, D l / H₂ :=
          Finset.prod_le_prod (fun _ _ => zero_le_one.trans (le_max_left _ _))
            (fun i _ => max_le hQ1.le (div_le_div_of_nonneg_right (hDl i) hH.le))
      _ = (D l / H₂) ^ N := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have ha : 0 ≤ 2 * (p:ℝ) / N := by positivity
  rw [Real.rpow_neg hPpos.le]
  have h2 : (∏ i, max 1 (D i / H₂)) ^ (2 * (p:ℝ) / N) ≤ (D l / H₂) ^ (2 * p) := by
    calc (∏ i, max 1 (D i / H₂)) ^ (2 * (p:ℝ) / N) ≤ ((D l / H₂) ^ N) ^ (2 * (p:ℝ) / N) :=
          Real.rpow_le_rpow hPpos.le hPQ ha
      _ = (D l / H₂) ^ (2 * p) := by
          rw [← Real.rpow_natCast (D l / H₂) N, ← Real.rpow_mul (by linarith),
            show (N:ℝ) * (2 * p / N) = ((2 * p : ℕ) : ℝ) by push_cast; field_simp,
            Real.rpow_natCast]
  calc (H₂ / D l) ^ (2 * p) = ((D l / H₂) ^ (2 * p))⁻¹ := by rw [← inv_pow, inv_div]
    _ ≤ ((∏ i, max 1 (D i / H₂)) ^ (2 * (p:ℝ) / N))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hPpos _) h2
end Formalism.HermitianLatticeCounting.P
