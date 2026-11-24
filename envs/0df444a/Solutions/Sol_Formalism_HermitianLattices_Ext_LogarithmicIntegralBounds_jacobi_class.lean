-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.jacobi_class
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:55.511712+00:00
-- url     : https://prove2.me/submissions/74f7204c-b634-4464-bf74-7d0f58fea454

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqJac
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_pos
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_soutPart_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_jacobi_class_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ a₀ N : ℕ) (h8 : 8 ∣ m₀) (ha : a₀.Coprime m₀) (hN : 0 < N) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ ∀ q : ℕ, q.Prime → q % m₀ = a₀ % m₀ → N < q →
      jacobiSym (N : ℤ) q = σ * jacobiSym (q : ℤ) (soutPart m₀ N) := by
  have hcop1 : ∀ q : ℕ, q.Prime → N < q → (N : ℤ).gcd q = 1 := by
    intro q hq hNq
    rw [Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr fun h => absurd (Nat.le_of_dvd hN h) (by omega)).symm
  have hcop2 : ∀ q : ℕ, q.Prime → N < q → (q : ℤ).gcd (soutPart m₀ N) = 1 := by
    intro q hq hNq
    have hle := soutPart_le m₀ N hN
    rw [Int.gcd_natCast_natCast]
    exact (Nat.Prime.coprime_iff_not_dvd hq).mpr fun h =>
      absurd (Nat.le_of_dvd (soutPart_pos m₀ N) h) (by omega)
  by_cases hex : ∃ q₀ : ℕ, q₀.Prime ∧ q₀ % m₀ = a₀ % m₀ ∧ N < q₀
  · obtain ⟨q₀, hq₀, hq₀m, hNq₀⟩ := hex
    refine ⟨jacobiSym (N : ℤ) q₀ * jacobiSym (q₀ : ℤ) (soutPart m₀ N), ?_, fun q hq hqm hNq => ?_⟩
    · rcases jacobiSym.eq_one_or_neg_one (hcop1 q₀ hq₀ hNq₀) with h | h <;>
        rcases jacobiSym.eq_one_or_neg_one (hcop2 q₀ hq₀ hNq₀) with h' | h' <;> simp [h, h']
    · have hc := jacobi_class_congr h8 hN hq hq₀ (hqm.trans hq₀m.symm) hNq hNq₀
      have hsq : jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 = 1 := jacobiSym.sq_one (hcop2 q hq hNq)
      rw [← hc]
      calc jacobiSym (N : ℤ) q = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) ^ 2 := by
            rw [hsq, mul_one]
        _ = jacobiSym (N : ℤ) q * jacobiSym (q : ℤ) (soutPart m₀ N) * jacobiSym (q : ℤ) (soutPart m₀ N) := by
            ring
  · exact ⟨1, Or.inl rfl, fun q hq hqm hNq => absurd ⟨q, hq, hqm, hNq⟩ hex⟩
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
