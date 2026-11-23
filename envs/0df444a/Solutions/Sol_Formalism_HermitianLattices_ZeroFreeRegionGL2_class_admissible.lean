-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.class_admissible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:55.148321+00:00
-- url     : https://prove2.me/submissions/6b3c732e-f0ce-4a70-99b5-5ecd09ada212

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : ClassAdmissible := by
  intro y z q₁ hy hq h8 hz
  set M := oddM y q₁ with hMdef
  have hMpf : ∀ p : ℕ, p.Prime → p ∣ M → p = q₁ ∨ (3 ≤ p ∧ (p : ℝ) ≤ y) := by
    intro p hp hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hq).1 h)
    · obtain ⟨r, hr, hpr⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
      simp only [mem_filter, mem_Icc] at hr
      have : p = r := (Nat.prime_dvd_prime_iff_eq hp hr.2).1 hpr
      subst this
      exact Or.inr ⟨hr.1.1, (Nat.le_floor_iff (by linarith)).1 hr.1.2⟩
  have hMpos : 0 < M := by
    apply Nat.mul_pos hq.pos
    exact Finset.prod_pos fun p hp => (mem_filter.1 hp).2.pos
  have hcop : Nat.Coprime 16 M := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    apply Nat.Coprime.pow_left
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    rcases hMpf 2 Nat.prime_two h with h | h
    · omega
    · omega
  obtain ⟨a₀, h16, hM⟩ := Nat.chineseRemainder hcop 7 (M - 1)
  have h16' : a₀ % 16 = 7 := h16
  have hM' : M ∣ a₀ + 1 := by
    have : a₀ + 1 ≡ (M - 1) + 1 [MOD M] := Nat.ModEq.add_right 1 hM
    rw [Nat.sub_add_cancel hMpos] at this
    exact (Nat.modEq_zero_iff_dvd).1 (this.trans (by simp [Nat.ModEq]))
  have hcM : a₀.Coprime M := by
    have : Nat.Coprime a₀ (a₀ + 1) := by simp
    exact Nat.Coprime.coprime_dvd_right hM' this
  have hc16 : a₀.Coprime 16 := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    omega
  refine ⟨a₀, h16', hM', Nat.Coprime.mul_right hc16 hcM, by omega, Dvd.dvd.mul_right (by norm_num) _, ?_, ?_⟩
  · intro p hp hdiv
    rcases (Nat.Prime.dvd_mul hp).1 hdiv with h | h
    · have : p ∣ 2 ^ 4 := by simpa using h
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
      subst this; left; exact_mod_cast hy
    · rcases hMpf p hp h with h | h
      · subst h; exact Or.inr hz
      · exact Or.inl h.2
  · intro d hd
    have hd' : d ≡ a₀ [MOD 16 * M] := hd
    have d16 : d ≡ a₀ [MOD 16] := Nat.ModEq.of_mul_right M hd'
    have dM : d ≡ a₀ [MOD M] := Nat.ModEq.of_mul_left 16 hd'
    refine ⟨d16.trans h16, ?_⟩
    exact (Nat.modEq_zero_iff_dvd).1 ((Nat.ModEq.add_right 1 dM).trans ((Nat.modEq_zero_iff_dvd).2 hM'))
end Formalism.HermitianLattices.ZeroFreeRegionGL2
