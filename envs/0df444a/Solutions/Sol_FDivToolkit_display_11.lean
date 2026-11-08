-- Prove2me | solution 1 for FDivToolkit.display_11
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:09:54.611215+00:00
-- url     : https://prove2.me/submissions/8a67133d-8bda-464f-9cbb-52dee334507e

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_weibullH

open FDivToolkit in
theorem solution {k θ : ℝ} (hk : 0 < k) (hθ : max k 1 < θ) :
    (∀ x : ℝ, weibullH k θ (weibullHinv k θ x) = x) ∧
    (∀ y : ℝ, weibullHinv k θ (weibullH k θ y) = y) ∧
    Hinv (weibullH k θ) = weibullHinv k θ := by
  have hθ1 : 1 < θ := lt_of_le_of_lt (le_max_right k 1) hθ
  have hθpos : 0 < θ := by linarith
  have hkθ : k / θ * (θ / k) = 1 := by field_simp
  have hθk : θ / k * (k / θ) = 1 := by field_simp
  have hkθp : 0 ≤ k / θ := (div_pos hk hθpos).le
  have hθkp : 0 ≤ θ / k := (div_pos hθpos hk).le
  have h1 : ∀ x : ℝ, weibullH k θ (weibullHinv k θ x) = x := by
    intro x
    by_cases hx : 0 ≤ x
    · have ha : 1 ≤ θ / k * x + 1 := by
        have : 0 ≤ θ / k * x := mul_nonneg hθkp hx
        linarith
      have hb : 1 ≤ (θ / k * x + 1) ^ (k / θ) := Real.one_le_rpow ha hkθp
      unfold weibullHinv
      rw [if_pos hx]
      unfold weibullH
      rw [if_pos (by linarith), sub_add_cancel, ← Real.rpow_mul (by linarith), hkθ,
        Real.rpow_one, add_sub_cancel_right, ← mul_assoc, hkθ, one_mul]
    · unfold weibullHinv
      rw [if_neg hx]
      unfold weibullH
      rw [if_neg hx]
  have h2 : ∀ y : ℝ, weibullHinv k θ (weibullH k θ y) = y := by
    intro y
    by_cases hy : 0 ≤ y
    · have hb : 1 ≤ (y + 1) ^ (θ / k) := Real.one_le_rpow (by linarith) hθkp
      have hnn : 0 ≤ k / θ * ((y + 1) ^ (θ / k) - 1) := mul_nonneg hkθp (by linarith)
      unfold weibullH
      rw [if_pos hy]
      unfold weibullHinv
      rw [if_pos hnn, ← mul_assoc, hθk, one_mul, sub_add_cancel, ← Real.rpow_mul (by linarith),
        hθk, Real.rpow_one, add_sub_cancel_right]
    · unfold weibullH
      rw [if_neg hy]
      unfold weibullHinv
      rw [if_neg hy]
  refine ⟨h1, h2, ?_⟩
  have hinj : Function.Injective (weibullH k θ) := fun a b hab => by
    rw [← h2 a, ← h2 b, hab]
  unfold Hinv
  funext x
  apply hinj
  rw [Function.invFun_eq ⟨_, h1 x⟩, h1 x]
