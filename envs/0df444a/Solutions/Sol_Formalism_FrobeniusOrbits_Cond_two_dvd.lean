-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Cond.two_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:03:26.960638+00:00
-- url     : https://prove2.me/submissions/1251916b-8bb9-4414-8944-58d3128b8715

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_EqZeroOfNegEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_prim_pow
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_aut
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_fix
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_cop_of_mod_one
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_eq_zero_of_neg_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Polynomial
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
namespace Cond
section Gauss
variable {K : Type*} [Field K] [CharZero K]
end Gauss
section Cyc
end Cyc
section Div
end Div
section Two
private theorem sq_add_inv_sq_eq_add_inv_sq_sub_two {F : Type*} [Field F] {y : F} (hy : y ≠ 0) :
    y ^ 2 + (y ^ 2)⁻¹ = (y + y⁻¹) ^ 2 - 2 := by
  field_simp
  ring
private theorem pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ {F : Type*} [Field F] {x : F} {n : ℕ}
    (hx : IsPrimitiveRoot x (2 ^ (n + 1))) : x ^ 2 ^ n = -1 := by
  have h4 : (x ^ 2 ^ n) ^ 2 = 1 := by
    rw [← pow_mul, ← pow_succ]
    exact hx.pow_eq_one
  have hne : x ^ 2 ^ n ≠ 1 :=
    hx.pow_ne_one_of_pos_of_lt (by positivity) (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have h5 : (x ^ 2 ^ n - 1) * (x ^ 2 ^ n + 1) = 0 := by linear_combination h4
  rcases mul_eq_zero.mp h5 with h6 | h6
  · exact absurd (sub_eq_zero.mp h6) hne
  · linear_combination h6
private theorem pow_two_pow_add_inv_eq_zero_of_isPrimitiveRoot {F : Type*} [Field F] {x : F} {n : ℕ}
    (hx : IsPrimitiveRoot x (2 ^ (n + 2))) : x ^ 2 ^ n + (x ^ 2 ^ n)⁻¹ = 0 := by
  have hy2 : (x ^ 2 ^ n) ^ 2 = -1 := by
    rw [← pow_mul, ← pow_succ]
    exact pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ (show IsPrimitiveRoot x (2 ^ (n + 1 + 1)) from hx)
  have hinv : (x ^ 2 ^ n)⁻¹ = -x ^ 2 ^ n :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← sq, hy2, neg_neg])
  rw [hinv]
  ring
end Two
end Cond
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Cond
namespace Formalism.FrobeniusOrbits.Cond
theorem _root_.solution {e q d : ℕ} (hH : HostHyp q d) (he : e ≠ 0) {L : Type} [Field L]
    [NumberField L] {ζ a b : L} (h : IsLayer (e + 2) q d ζ a b) {m : ℕ} [NeZero m]
    (φ : hostE ζ a b →ₐ[ℚ] Cyc m) : 2 ^ (e + 2) ∣ m := by
  by_contra hndvd
  have hζ0 : ζ ≠ 0 := h.1.ne_zero (by positivity)
  obtain ⟨j, m', hm'o, hmj⟩ : ∃ j m', Odd m' ∧ m = 2 ^ j * m' := by
    exact Nat.exists_eq_two_pow_mul_odd (NeZero.ne m)
  have hje : j ≤ e + 1 := by
    by_contra hj
    apply hndvd
    rw [hmj]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) _
  obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (e + 1) * m' := ⟨_, rfl⟩
  have hmM : m ∣ M := by
    rw [hmj, hM]
    exact mul_dvd_mul_right (pow_dvd_pow 2 hje) m'
  have hm'0 : m' ≠ 0 := hm'o.pos.ne'
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact mul_ne_zero (by positivity) hm'0
  haveI : NeZero M := ⟨hM0⟩
  haveI : NeZero (2 * M) := ⟨mul_ne_zero two_ne_zero hM0⟩
  have hMe : M = 2 * (2 ^ e * m') := by rw [hM]; ring
  have hv2 : (1 + M) % 2 = 1 % 2 := by rw [hMe]; omega
  have hcop : Nat.Coprime (1 + M) (2 * M) :=
    Nat.Coprime.mul_right (cop_of_mod_one hv2) (cop_of_mod_one (Nat.add_mod_right 1 M))
  obtain ⟨σ, hσ⟩ := aut (2 * M) (1 + M) hcop
  obtain ⟨ι⟩ := emb M (2 * M) (dvd_mul_left M 2)
  obtain ⟨ι'⟩ := emb m M hmM
  obtain ⟨ψ, hψ⟩ : ∃ ψ : hostE ζ a b →ₐ[ℚ] Cyc (2 * M), ∀ x, σ (ψ x) = ψ x :=
    ⟨ι.comp (ι'.comp φ), fun x => fix (dvd_mul_left M 2) ι σ (1 + M) hσ (Nat.add_mod_right 1 M) _⟩
  have h2N : 2 ^ (e + 2) ∣ 2 * M := ⟨m', by rw [hM]; ring⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Cyc (2 * M), IsPrimitiveRoot ω (2 ^ (e + 2)) := ⟨_, prim_pow h2N⟩
  have hω0 : ω ≠ 0 := hω.ne_zero (by positivity)
  have hωN : ω ^ (2 * M) = 1 := (hω.pow_eq_one_iff_dvd _).mpr h2N
  have hωM : ω ^ M = -1 := by
    calc ω ^ M = ω ^ (2 ^ (e + 1) * m') := congrArg (fun n => ω ^ n) hM
      _ = (ω ^ 2 ^ (e + 1)) ^ m' := pow_mul ω _ _
      _ = -1 := by
        rw [pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ (show IsPrimitiveRoot ω (2 ^ (e + 1 + 1)) from hω), hm'o.neg_one_pow]
  have hσω : σ ω = -ω := by rw [hσ ω hωN, pow_add, pow_one, hωM, mul_neg_one]
  have h2mem : (2 : L) ∈ hostE ζ a b := by
    simpa using IntermediateField.algebraMap_mem (hostE ζ a b) (2 : ℚ)
  have hF1 : F1 ζ ≤ hostE ζ a b := by
    unfold hostE
    exact le_sup_right
  have hcmem : ∀ j : ℕ, ζ ^ 2 ^ j + (ζ ^ 2 ^ j)⁻¹ ∈ hostE ζ a b := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_one]
      apply hF1
      unfold F1
      exact IntermediateField.mem_adjoin_simple_self ℚ _
    | succ j ih =>
      rw [pow_succ, pow_mul, sq_add_inv_sq_eq_add_inv_sq_sub_two (pow_ne_zero _ hζ0)]
      exact sub_mem (pow_mem ih 2) h2mem
  obtain ⟨C, hCval⟩ : ∃ C : ℕ → hostE ζ a b, ∀ j, (C j : L) = ζ ^ 2 ^ j + (ζ ^ 2 ^ j)⁻¹ :=
    ⟨fun j => ⟨_, hcmem j⟩, fun j => rfl⟩
  have hrec : ∀ j, ψ (C (j + 1)) = ψ (C j) ^ 2 - 2 := by
    intro j
    have hC : C (j + 1) = C j ^ 2 - 2 := by
      apply Subtype.val_injective
      have e1 : ((C j ^ 2 - 2 : hostE ζ a b) : L) = (C j : L) ^ 2 - 2 := by
        rfl
      rw [e1, hCval, hCval, pow_succ, pow_mul, sq_add_inv_sq_eq_add_inv_sq_sub_two (pow_ne_zero _ hζ0)]
    rw [hC, map_sub, map_pow, map_ofNat]
  have hS : ∀ i, i ≤ e → ∃ t, Odd t ∧
      ψ (C (e - i)) = (ω ^ t) ^ 2 ^ (e - i) + ((ω ^ t) ^ 2 ^ (e - i))⁻¹ := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨1, odd_one, ?_⟩
      have hCe : C e = 0 := Subtype.val_injective (by
        rw [hCval]
        exact pow_two_pow_add_inv_eq_zero_of_isPrimitiveRoot h.1)
      rw [Nat.sub_zero, hCe, map_zero, pow_one, pow_two_pow_add_inv_eq_zero_of_isPrimitiveRoot hω]
    | succ i ih =>
      intro hi
      obtain ⟨t, ht, hteq⟩ := ih (by omega)
      obtain ⟨j, hj⟩ : ∃ j, j = e - (i + 1) := ⟨_, rfl⟩
      have hji : e - i = j + 1 := by omega
      rw [← hj]
      rw [hji] at hteq
      obtain ⟨W, hW⟩ : ∃ W, W = (ω ^ t) ^ 2 ^ j := ⟨_, rfl⟩
      have hW0 : W ≠ 0 := by
        rw [hW]
        exact pow_ne_zero _ (pow_ne_zero _ hω0)
      have h1 : (ω ^ t) ^ 2 ^ (j + 1) = W ^ 2 := by
        rw [hW, ← pow_mul (ω ^ t) (2 ^ j) 2, ← pow_succ]
      rw [h1, hrec j, sq_add_inv_sq_eq_add_inv_sq_sub_two hW0] at hteq
      have hsq : (ψ (C j) - (W + W⁻¹)) * (ψ (C j) + (W + W⁻¹)) = 0 := by
        linear_combination hteq
      rcases mul_eq_zero.mp hsq with h2 | h2
      · refine ⟨t, ht, ?_⟩
        rw [← hW]
        linear_combination h2
      · refine ⟨t + 2 ^ (e + 1 - j), ht.add_even (Nat.even_pow.mpr ⟨even_two, by omega⟩), ?_⟩
        have hneg : (ω ^ (t + 2 ^ (e + 1 - j))) ^ 2 ^ j = -W := by
          rw [pow_add, mul_pow, ← pow_mul ω (2 ^ (e + 1 - j)) (2 ^ j), ← pow_add 2 (e + 1 - j) j,
            Nat.sub_add_cancel (by omega : j ≤ e + 1),
            pow_two_pow_eq_neg_one_of_isPrimitiveRoot_two_pow_succ (show IsPrimitiveRoot ω (2 ^ (e + 1 + 1)) from hω), hW]
          ring
        rw [hneg, inv_neg]
        linear_combination h2
  obtain ⟨t, ht, ht0⟩ := hS e le_rfl
  rw [Nat.sub_self, pow_zero, pow_one] at ht0
  have hfix0 := hψ (C 0)
  rw [ht0, map_add, map_inv₀, map_pow, hσω, ht.neg_pow, inv_neg] at hfix0
  have hz : ψ (C 0) = 0 := by
    rw [ht0]
    apply eq_zero_of_neg_eq
    linear_combination hfix0
  have hC0 : C 0 = 0 := by
    exact RingHom.injective ψ.toRingHom (by simpa using hz)
  have hc0 : ζ + ζ⁻¹ = 0 := by
    have h5 := hCval 0
    rw [hC0, pow_zero, pow_one] at h5
    exact h5.symm
  have h4 : ζ ^ 2 + 1 = 0 := by
    have h6 : ζ ^ 2 + 1 = ζ * (ζ + ζ⁻¹) := by
      rw [mul_add, mul_inv_cancel₀ hζ0]
      ring
    rw [h6, hc0, mul_zero]
  have hζ4 : ζ ^ 4 = 1 := by linear_combination (ζ ^ 2 - 1) * h4
  have h48 : 4 < 2 ^ (e + 2) := by
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact h.1.pow_ne_one_of_pos_of_lt (by norm_num) h48 hζ4
end Formalism.FrobeniusOrbits.Cond
