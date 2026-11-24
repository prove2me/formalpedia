-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.density_split_primes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:46.197497+00:00
-- url     : https://prove2.me/submissions/94e8bb9d-5bc6-4022-ab98-5d2ac51b8e63

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SplitDensity := by
  intro F _ _ _ M β hM hβ
  classical
  set q := Fintype.card F with hq
  have hq0 : 0 < q := Fintype.card_pos
  have fib : ∀ x : Fin M → F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = β} =
      if x = 0 then 0 else q ^ (M - 1) := by
    intro x
    split_ifs with hx
    · subst hx
      rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨y, hy⟩ => hβ (by simpa using hy.symm)⟩
    · obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (funext h)

      have key : ∀ t : F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = t} =
          Fintype.card {y : Fin M → F // ∑ i, x i * y i = 0} := by
        intro t
        apply Fintype.card_congr
        exact
          { toFun := fun y => ⟨y.1 - Pi.single j (t / x j), by
              have h := y.2
              change dotProduct x (y.1 - Pi.single j (t / x j)) = 0
              change dotProduct x y.1 = t at h
              rw [dotProduct_sub, dotProduct_single, h, mul_div_cancel₀ _ hj, sub_self]⟩
            invFun := fun y => ⟨y.1 + Pi.single j (t / x j), by
              have h := y.2
              change dotProduct x (y.1 + Pi.single j (t / x j)) = t
              change dotProduct x y.1 = 0 at h
              rw [dotProduct_add, dotProduct_single, h, mul_div_cancel₀ _ hj, zero_add]⟩
            left_inv := fun y => by ext; simp
            right_inv := fun y => by ext; simp }
      have hsum : ∑ t : F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = t} = q ^ M := by
        rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv _), Fintype.card_fun,
          Fintype.card_fin]
      rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_const, Finset.card_univ,
        smul_eq_mul] at hsum
      rw [key β]
      obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, mul_comm (q ^ k)] at *
      exact Nat.eq_of_mul_eq_mul_left hq0 hsum
  have e : Fintype.card {p : (Fin M → F) × (Fin M → F) // ∑ i, p.1 i * p.2 i = β} =
      ∑ x : Fin M → F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = β} := by
    rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (x y : Fin M → F) => ∑ i, x i * y i = β)), Fintype.card_sigma]
  have hcnt : ∑ x : Fin M → F, Fintype.card {y : Fin M → F // ∑ i, x i * y i = β} =
      (q ^ M - 1) * q ^ (M - 1) := by
    rw [Finset.sum_congr rfl (fun x _ => fib x), Finset.sum_ite, Finset.sum_const_zero, zero_add,
      Finset.sum_const, smul_eq_mul, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [e, hcnt]
  have h1 : 1 ≤ q ^ M := Nat.one_le_pow _ _ hq0
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
  have h2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [h2, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_sub h1]
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
  push_cast
  simp only [inv_pow]
  field_simp
  ring
end Formalism.HermitianLattices.GenusMassVolumes
