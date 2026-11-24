-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.degenerateRowBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:06.893811+00:00
-- url     : https://prove2.me/submissions/9b054381-d040-4ea6-8f83-700ce5468779

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
theorem _root_.solution : DegRow := by
  intro k f s g v T NT G₁ G₂ K₁ K₂ Xi W count A₁ A₂ lam₁ lam₂ hk hs hg hv hT hNT hG₁ hG₂ hK₁ hK₂
    hXi hW hA₁ hA₂ hcount h₁ h₂
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.nTot at h₁ h₂
  obtain ⟨E, hE⟩ : ∃ E, E = (Real.exp 1 * Real.pi / (k * v)) ^ (k * f) := ⟨_, rfl⟩
  have hE0 : 0 < E := by rw [hE]; positivity
  have hE' : E ≠ 0 := hE0.ne'
  rw [← hE] at h₁ h₂
  obtain ⟨a, ha⟩ : ∃ x, x = Real.sqrt (G₁ / NT) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ x, x = Real.sqrt (G₂ / NT) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ x, x = Real.sqrt T⁻¹ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hb0 : 0 ≤ b := by rw [hb]; positivity
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have ha2 : a ^ 2 = G₁ / NT := by rw [ha, Real.sq_sqrt (by positivity)]
  have hb2 : b ^ 2 = G₂ / NT := by rw [hb, Real.sq_sqrt (by positivity)]
  have hc2 : c ^ 2 = T⁻¹ := by rw [hc, Real.sq_sqrt (by positivity)]
  have hab : Real.sqrt (G₁ * G₂) / NT = a * b := by
    rw [ha, hb, ← Real.sqrt_mul (div_nonneg hG₁.le hNT.le),
      show G₁ / NT * (G₂ / NT) = (G₁ * G₂) / NT ^ 2 by ring,
      Real.sqrt_div (mul_nonneg hG₁.le hG₂.le), Real.sqrt_sq hNT.le]
  obtain ⟨u₁, hu₁⟩ : ∃ x, x = A₁ * a ^ k * K₁ ^ k * c ^ (k * f) := ⟨_, rfl⟩
  obtain ⟨u₂, hu₂⟩ : ∃ x, x = A₂ * b ^ k * K₂ ^ k * c ^ (k * f) := ⟨_, rfl⟩
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; positivity
  have hu₂0 : 0 ≤ u₂ := by rw [hu₂]; positivity
  have hl1 : E * u₁ ^ 2 ≤ lam₁ := by
    have e : E * u₁ ^ 2 = E * (G₁ / NT) ^ k * A₁ ^ 2 * K₁ ^ (2 * k) * T⁻¹ ^ (k * f) := by
      rw [hu₁, ← ha2, ← hc2]; ring
    rw [e]; exact h₁
  have hl2 : E * u₂ ^ 2 ≤ lam₂ := by
    have e : E * u₂ ^ 2 = E * (G₂ / NT) ^ k * A₂ ^ 2 * K₂ ^ (2 * k) * T⁻¹ ^ (k * f) := by
      rw [hu₂, ← hb2, ← hc2]; ring
    rw [e]; exact h₂
  have hkey : E * (u₁ * u₂) ≤ Real.sqrt (lam₁ * lam₂) := by
    have hprod : (E * (u₁ * u₂)) ^ 2 ≤ lam₁ * lam₂ := by
      have e : (E * (u₁ * u₂)) ^ 2 = (E * u₁ ^ 2) * (E * u₂ ^ 2) := by ring
      rw [e]
      exact mul_le_mul hl1 hl2 (by positivity) (le_trans (by positivity) hl1)
    have h0 : 0 ≤ E * (u₁ * u₂) := by positivity
    calc E * (u₁ * u₂) = Real.sqrt ((E * (u₁ * u₂)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (lam₁ * lam₂) := Real.sqrt_le_sqrt hprod
  have hid : ((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W *
      (A₁ * A₂) = (2 / g) ^ ((s - 2) * k * f) * Xi * W * (u₁ * u₂) := by
    rw [show (2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT =
        (2 / g) ^ ((s - 2) * f) * (Real.sqrt (G₁ * G₂) / NT) * T⁻¹ ^ f * K₁ * K₂ by ring,
      hab, ← hc2, hu₁, hu₂]
    ring
  have hAA : 0 ≤ A₁ * A₂ := mul_nonneg hA₁ hA₂
  calc count * A₁ * A₂ = count * (A₁ * A₂) := by ring
    _ ≤ (((2 / g) ^ ((s - 2) * f) * Real.sqrt (G₁ * G₂) * T⁻¹ ^ f * K₁ * K₂ / NT) ^ k * Xi * W) *
          (A₁ * A₂) := mul_le_mul_of_nonneg_right hcount hAA
    _ = (2 / g) ^ ((s - 2) * k * f) * Xi * W * (u₁ * u₂) := hid
    _ = (2 / g) ^ ((s - 2) * k * f) * Xi * W * E⁻¹ * (E * (u₁ * u₂)) := by
        rw [mul_assoc _ E⁻¹, inv_mul_cancel_left₀ hE']
    _ ≤ (2 / g) ^ ((s - 2) * k * f) * Xi * W * E⁻¹ * Real.sqrt (lam₁ * lam₂) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (2 / g) ^ ((s - 2) * k * f) * (k * v / (Real.exp 1 * Real.pi)) ^ (k * f) *
          Xi * W * Real.sqrt (lam₁ * lam₂) := by
        rw [hE, ← inv_pow, inv_div]; ring
end Formalism.HermitianLatticeCounting.P
