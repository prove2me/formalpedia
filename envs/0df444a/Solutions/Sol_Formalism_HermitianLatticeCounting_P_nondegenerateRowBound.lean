-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.nondegenerateRowBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:44.522801+00:00
-- url     : https://prove2.me/submissions/b9f1f7dd-ddb2-4543-9a9b-a9d2ca2735eb

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : NonDegRow := by
  intro k f s g v NT G₁ G₂ Xi W count A₁ A₂ l₁ l₂ τ hk hs hg hv hNT hG₁ hG₂ hXi hW hA₁ hA₂ hτ
    hcount h₁ h₂
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nTot at h₁ h₂
  obtain ⟨E, hE⟩ : ∃ E, E = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hE' : E ≠ 0 := hE0.ne'
  rw [← hE] at h₁ h₂
  obtain ⟨a, ha⟩ : ∃ x, x = Real.sqrt (G₁ / NT) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = Real.sqrt (G₂ / NT) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have ha2 : a ^ 2 = G₁ / NT := by rw [ha, Real.sq_sqrt (by positivity)]
  have hb2 : b ^ 2 = G₂ / NT := by rw [hb, Real.sq_sqrt (by positivity)]
  have hab : Real.sqrt (G₁ * G₂) / NT = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (div_nonneg hG₁.le hNT.le),
      show G₁ / NT * (G₂ / NT) = (G₁ * G₂) / NT ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hG₁.le hG₂.le), Real.sqrt_sq hNT.le]
  obtain ⟨u₁, hu₁⟩ : ∃ x, x = A₁ * a ^ k := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = A₂ * b ^ k := ⟨_, rfl⟩
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  have hl1 : E * u₁ ^ 2 ≤ l₁ * τ := by
    have e : E * u₁ ^ 2 = E * (G₁ / NT) ^ k * A₁ ^ 2 := by rw [hu₁, ← ha2]; ring
    rw [e]; exact h₁
  have hl2 : E * u₂ ^ 2 ≤ l₂ * τ := by
    have e : E * u₂ ^ 2 = E * (G₂ / NT) ^ k * A₂ ^ 2 := by rw [hu₂, ← hb2]; ring
    rw [e]; exact h₂
  have hkey : E * (u₁ * u₂) ≤ Real.sqrt (l₁ * l₂) * τ := by
    have hprod : (E * (u₁ * u₂)) ^ 2 ≤ (l₁ * τ) * (l₂ * τ) := by
      have e : (E * (u₁ * u₂)) ^ 2 = (E * u₁ ^ 2) * (E * u₂ ^ 2) := by ring
      rw [e]
      exact mul_le_mul hl1 hl2 (by positivity) (le_trans (by positivity) hl1)
    have h0 : 0 ≤ E * (u₁ * u₂) := by positivity
    calc E * (u₁ * u₂) = Real.sqrt ((E * (u₁ * u₂)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt ((l₁ * τ) * (l₂ * τ)) := Real.sqrt_le_sqrt hprod
      _ = Real.sqrt (l₁ * l₂ * τ ^ 2) := by congr 1; ring
      _ = Real.sqrt (l₁ * l₂) * τ := by rw [Real.sqrt_mul' _ (sq_nonneg τ), Real.sqrt_sq hτ]
  have hid : ((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W * (A₁ * A₂) =
      (2 / g) ^ ((s - 1) * k * f) * Xi * W * (u₁ * u₂) := by
    rw [mul_div_assoc, hab, hu₁, hu₂]; ring
  have hAA : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  calc count * A₁ * A₂ = count * (A₁ * A₂) := by ring
    _ ≤ (((2 / g) ^ ((s - 1) * f) * Real.sqrt (G₁ * G₂) / NT) ^ k * Xi * W) * (A₁ * A₂) :=
        mul_le_mul_of_nonneg_right hcount hAA
    _ = (2 / g) ^ ((s - 1) * k * f) * Xi * W * (u₁ * u₂) := hid
    _ = (2 / g) ^ ((s - 1) * k * f) * Xi * W * E⁻¹ * (E * (u₁ * u₂)) := by
        rw [mul_assoc _ E⁻¹, inv_mul_cancel_left₀ hE']
    _ ≤ (2 / g) ^ ((s - 1) * k * f) * Xi * W * E⁻¹ * (Real.sqrt (l₁ * l₂) * τ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 / g) ^ ((s - 1) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
          Xi * W * Real.sqrt (l₁ * l₂) * τ := by
        rw [hE, ← inv_pow, inv_div]; ring
end Formalism.HermitianLatticeCounting.P
