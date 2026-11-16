-- Prove2me | solution 1 for CNFEncComplexity.uniformNativeExpander
-- status  : ACCEPTED   (prove)
-- author  : @bersubs
-- created : 2026-11-15T06:55:50.373796+00:00
-- url     : https://prove2.me/submissions/7b7d8822-cf6c-47e6-9b70-d44eb55c0220

import Definitions.Def_CNFEncComplexity_teutschNbr
import Definitions.Def_TimeSpaceMA_RAM
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_CNFEncComplexity_teutschNbr_native
import Theorems.Thm_TimeSpaceMA_theorem_A_1

namespace CNFEncComplexity
open Turing.MultiTapeTM

/-- Teutsch's disjoint union of normalized dispersers gives Hall expansion up to `2^k`. -/
theorem mergeNbr_properties
    (degree : ℕ → ℕ) (layer : ℕ × ℕ × ℕ × ℕ → Option ℕ)
    (hdegree : ∀ N, 0 < degree N)
    (hbound : ∀ j N l i ρ : ℕ, 2 ^ j ≤ N → l < N → i < degree N →
      layer (N, j, l, i) = some ρ → ρ < 2 ^ (j+2))
    (hspread : ∀ j N : ℕ, 2 ^ j ≤ N → ∀ S : Finset (Fin N), 2 ^ j ≤ S.card →
      2 ^ (j+1) ≤ (S.biUnion fun l => (Finset.range (degree N)).biUnion
        fun i => (layer (N, j, (l : ℕ), i)).toFinset).card) :
    ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k+3) ∧
      (∀ l < N, ∀ i : ℕ, (k+1) * degree N ≤ i → mergeNbr degree layer (N, k, l, i) = none) ∧
      (∀ l < N, ∀ i ρ : ℕ, mergeNbr degree layer (N, k, l, i) = some ρ → ρ < r) ∧
      ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
        S.card ≤ (S.biUnion fun l => (Finset.range ((k+1) * degree N)).biUnion
          fun i => (mergeNbr degree layer (N, k, (l : ℕ), i)).toFinset).card := by
  intro k N hkN
  have hN : N ≠ 0 := by
    have hp : 0 < (2 : ℕ)^k := Nat.pow_pos (by decide)
    omega
  have hklog : k ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by decide) hkN
  have hfour (j : ℕ) : 4 ≤ (2 : ℕ)^(j+2) := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 2 ≤ j+2 by omega))
  let r := 2 ^ (k+3) - 4
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · have hfourk : 4 ≤ (2 : ℕ)^(k+3) := hfour (k+1)
    dsimp [r]
    omega
  · intro l _ i hi
    have hdiv : k + 1 ≤ i / degree N := (Nat.le_div_iff_mul_le (hdegree N)).2 hi
    have hn : ¬ (i / degree N ≤ k ∧ i / degree N ≤ Nat.log 2 N) := by omega
    simp [mergeNbr, hn]
  · intro l hl i ρ hnbr
    let j := i / degree N
    change (if j ≤ k ∧ j ≤ Nat.log 2 N then
      (layer (N, j, l, i % degree N)).map ((2 ^ (j+2)-4) + ·) else none) = some ρ at hnbr
    split at hnbr
    next hj =>
      cases hy : layer (N, j, l, i % degree N) with
      | none => simp [hy] at hnbr
      | some y =>
        have hyb := hbound j N l (i % degree N) y (Nat.pow_le_of_le_log hN hj.2)
          hl (Nat.mod_lt _ (hdegree N)) hy
        simp only [hy, Option.map_some, Option.some.injEq] at hnbr
        have hpow : (2 : ℕ)^(j+3) ≤ 2^(k+3) :=
          Nat.pow_le_pow_right (by decide) (by omega)
        have hdouble : (2 : ℕ)^(j+3) = 2^(j+2) * 2 := pow_succ _ _
        have := hfour j
        dsimp [r]
        omega
    next _ => simp at hnbr
  · intro S hS
    by_cases hzero : S.card = 0
    · simp [hzero]
    let j := Nat.log 2 S.card
    have hjlow : 2^j ≤ S.card := Nat.pow_log_le_self 2 hzero
    have hjup : S.card ≤ 2^(j+1) := Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) _)
    have hjk : j ≤ k := by
      have hh := Nat.log_mono_right (b := 2) hS
      simpa [j, Nat.log_pow (by decide : 1 < (2 : ℕ))] using hh
    have hjlog : j ≤ Nat.log 2 N := hjk.trans hklog
    let localNbrs := S.biUnion fun l => (Finset.range (degree N)).biUnion
      fun i => (layer (N, j, (l : ℕ), i)).toFinset
    let allNbrs := S.biUnion fun l => (Finset.range ((k+1) * degree N)).biUnion
      fun i => (mergeNbr degree layer (N, k, (l : ℕ), i)).toFinset
    let shift : ℕ ↪ ℕ := ⟨((2 ^ (j+2)-4) + ·), fun _ _ h => Nat.add_left_cancel h⟩
    have hsub : localNbrs.map shift ⊆ allNbrs := by
      intro ρ hρ
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hρ
      obtain ⟨l, hl, ht⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨i, hi, hs⟩ := Finset.mem_biUnion.mp ht
      have hi' := Finset.mem_range.mp hi
      have hdiv : (i + degree N * j) / degree N = j := by
        rw [Nat.add_mul_div_left _ _ (hdegree N), Nat.div_eq_of_lt hi', Nat.zero_add]
      have hmod : (i + degree N * j) % degree N = i := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi']
      have hu : i + degree N * j < (k+1) * degree N := by
        apply (Nat.div_lt_iff_lt_mul (hdegree N)).1
        rw [hdiv]
        omega
      apply Finset.mem_biUnion.mpr
      refine ⟨l, hl, Finset.mem_biUnion.mpr ⟨i + degree N * j, Finset.mem_range.mpr hu, ?_⟩⟩
      simp only [Option.mem_toFinset] at hs ⊢
      change (if (i + degree N * j) / degree N ≤ k ∧
          (i + degree N * j) / degree N ≤ Nat.log 2 N then
        (layer (N, (i + degree N * j) / degree N, (l : ℕ),
          (i + degree N * j) % degree N)).map ((2 ^ ((i + degree N * j) / degree N + 2) - 4) + ·)
        else none) = some (shift y)
      rw [hdiv, hmod, if_pos ⟨hjk, hjlog⟩, hs]
      rfl
    have hlocal := hspread j N (Nat.pow_le_of_le_log hN hjlog) S hjlow
    have hcards := Finset.card_le_card hsub
    rw [Finset.card_map] at hcards
    exact hjup.trans (hlocal.trans hcards)

end CNFEncComplexity
namespace CNFEncComplexity
open Turing.MultiTapeTM

private theorem expander_degree_mul_le {k N a : ℕ} (hN : 2 ^ k ≤ N) :
    (k + 1) * (a * (Nat.log 2 N + 1) ^ a) ≤
      (a + 1) * (Nat.log 2 N + 1) ^ (a + 1) := by
  let b := Nat.log 2 N + 1
  have hk : k + 1 ≤ b := Nat.succ_le_succ (Nat.le_log_of_pow_le (by decide) hN)
  calc
    (k + 1) * (a * b ^ a) ≤ b * (a * b ^ a) := Nat.mul_le_mul_right _ hk
    _ = a * b ^ (a + 1) := by rw [Nat.pow_succ]; ac_rfl
    _ ≤ (a + 1) * b ^ (a + 1) := Nat.mul_le_mul_right _ (Nat.le_succ a)

private theorem expander_raise_cutoff
    (nbr : ℕ × ℕ × ℕ × ℕ → Option ℕ) {k N p q r : ℕ}
    (hpq : p ≤ q)
    (hnone : ∀ l < N, ∀ i : ℕ, p ≤ i → nbr (N, k, l, i) = none)
    (hbound : ∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r)
    (hspread : ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
      S.card ≤ (S.biUnion fun l => (Finset.range p).biUnion
        fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card) :
    (∀ l < N, ∀ i : ℕ, q ≤ i → nbr (N, k, l, i) = none) ∧
    (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
    ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
      S.card ≤ (S.biUnion fun l => (Finset.range q).biUnion
        fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card := by
  refine ⟨fun l hl i hi => hnone l hl i (hpq.trans hi), hbound, ?_⟩
  intro S hS
  refine (hspread S hS).trans (Finset.card_le_card ?_)
  intro ρ hρ
  obtain ⟨l, hl, hρ⟩ := Finset.mem_biUnion.mp hρ
  exact Finset.mem_biUnion.mpr ⟨l, hl, Finset.biUnion_subset_biUnion_of_subset_left
    _ (Finset.range_mono hpq) hρ⟩

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

private theorem expander_canonical_degree
    (nbr : ℕ × ℕ × ℕ × ℕ → Option ℕ) (a : ℕ)
    (h : ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k + 3) ∧
      (∀ l < N, ∀ i : ℕ, (k+1) * (a * (Nat.log 2 N + 1)^a) ≤ i →
        nbr (N, k, l, i) = none) ∧
      (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
      ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
        S.card ≤ (S.biUnion fun l => (Finset.range ((k+1) * (a * (Nat.log 2 N + 1)^a))).biUnion
          fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card) :
    ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k + 3) ∧
      (∀ l < N, ∀ i : ℕ, (a+1) * (Nat.log 2 N + 1) ^ (a+1) ≤ i →
        nbr (N, k, l, i) = none) ∧
      (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
      ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
        S.card ≤ (S.biUnion fun l => (Finset.range ((a+1) * (Nat.log 2 N + 1) ^ (a+1))).biUnion
          fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card := by
  intro k N hN
  obtain ⟨r, hr, hnone, hbound, hspread⟩ := h k N hN
  exact ⟨r, hr, expander_raise_cutoff nbr (expander_degree_mul_le hN) hnone hbound hspread⟩

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

/-- Absorb the degree of a disperser and its polynomial clone factor into the fixed
shape used by Lemma 14. -/
private theorem expander_clone_degree_le (e C n : ℕ) (hn : 0 < n) :
    (n ^ e + e) * 2^(C + 3 * (Nat.log 2 n+1)) ≤
      (2^(C+3) * (e+1) + e+3) * n ^ (2^(C+3) * (e+1) + e+3) := by
  have hpow : 1 ≤ n ^ e := Nat.pow_pos hn
  have he : e ≤ e * n^e := by simpa using Nat.mul_le_mul_left e hpow
  have hbase : 2 ^ (Nat.log 2 n+1) ≤ 2*n := by
    rw [Nat.pow_succ, Nat.mul_comm (2:ℕ) n]
    exact Nat.mul_le_mul_right 2 (Nat.pow_log_le_self 2 (by omega))
  have hclone : (2:ℕ)^(C + 3 * (Nat.log 2 n+1)) ≤ 2^(C+3) * n^3 := by
    rw [Nat.pow_add 2 C, Nat.mul_comm 3, Nat.pow_mul, Nat.pow_add 2 C 3, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by
      simpa only [Nat.mul_pow] using (Nat.pow_le_pow_left hbase 3))
  calc
    (n ^ e + e) * 2^(C + 3 * (Nat.log 2 n+1)) ≤
        (n^e + e * n^e) * (2^(C+3) * n^3) :=
      Nat.mul_le_mul (Nat.add_le_add_left he _) hclone
    _ = (2^(C+3) * (e+1)) * n^(e+3) := by
      rw [Nat.pow_add n e 3]
      ring
    _ ≤ (2^(C+3) * (e+1) + e+3) * n^(2^(C+3) * (e+1) + e+3) := by
      apply Nat.mul_le_mul
      · omega
      · exact Nat.pow_le_pow_right hn (by omega)

end CNFEncComplexity
namespace CNFEncComplexity
open Turing.MultiTapeTM

private theorem lemma_14_from_layers
    (a : ℕ) (ha : 0 < a)
    (layer : ℕ × ℕ × ℕ × ℕ → Option ℕ)
    (hbound : ∀ j N l i ρ : ℕ, 2 ^ j ≤ N → l < N → i < a * (Nat.log 2 N + 1)^a →
      layer (N, j, l, i) = some ρ → ρ < 2 ^ (j+2))
    (hspread : ∀ j N : ℕ, 2 ^ j ≤ N → ∀ S : Finset (Fin N), 2 ^ j ≤ S.card →
      2 ^ (j+1) ≤ (S.biUnion fun l => (Finset.range (a * (Nat.log 2 N + 1)^a)).biUnion
        fun i => (layer (N, j, (l : ℕ), i)).toFinset).card)
    (hmachine : ComputableTidilyInPolyTime (mergeNbr (fun N => a * (Nat.log 2 N + 1)^a) layer) (encPair encNat (encPair encNat (encPair encNat encNat))) (encOption encNat)) :
    ∃ c : ℕ, ∃ nbr : ℕ × ℕ × ℕ × ℕ → Option ℕ,
      ComputableTidilyInPolyTime nbr (encPair encNat (encPair encNat (encPair encNat encNat))) (encOption encNat) ∧
      ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k + 3) ∧
        (∀ l < N, ∀ i : ℕ, c * (Nat.log 2 N + 1) ^ c ≤ i → nbr (N, k, l, i) = none) ∧
        (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
        ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
          S.card ≤ (S.biUnion fun l => (Finset.range (c * (Nat.log 2 N + 1) ^ c)).biUnion
            fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card := by
  refine ⟨a+1, _, hmachine, ?_⟩
  apply expander_canonical_degree _ a
  exact mergeNbr_properties _ layer
    (fun N => Nat.mul_pos ha (Nat.pow_pos (Nat.succ_pos _))) hbound hspread

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

/-- A constant positive real factor can be offset by a fixed power of two. -/
theorem fold_padding_constant {c : ℝ} (hc : 0 < c) :
    ∃ C : ℕ, (4 : ℝ) ≤ c * 2^C := by
  obtain ⟨C, hC⟩ := pow_unbounded_of_one_lt (4 / c) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨C, ?_⟩
  have hm := (div_lt_iff₀ hc).1 hC
  nlinarith

/-- The Teutsch normalization may use a power of two as its available number of clone slots.
The chosen clone count times the residue modulus is exactly the normalized right size. -/
theorem fold_padding_parameters
    (c : ℝ) (C j n d R : ℕ) (hc : 0 < c) (hC : (4 : ℝ) ≤ c * 2^C)
    (hn : 0 < n) (hd : 0 < d) (hR : 0 < R)
    (hlower : c * (2 : ℝ)^j * (d : ℝ) / (n : ℝ)^3 ≤ (R : ℝ)) :
    let B := C + 3 * (Nat.log 2 n + 1)
    let M := (2 : ℕ)^((j+2)-B)
    let u := (2 : ℕ)^(min (j+2) B)
    u * M = 2^(j+2) ∧ M ≤ R := by
  dsimp only
  let B := C + 3 * (Nat.log 2 n + 1)
  let M := (2 : ℕ)^((j+2)-B)
  let u := (2 : ℕ)^(min (j+2) B)
  change u * M = 2^(j+2) ∧ M ≤ R
  constructor
  · dsimp only [u, M]
    rw [← pow_add]
    congr 1
    omega
  by_cases hsmall : j+2 ≤ B
  · have hz : j+2-B = 0 := Nat.sub_eq_zero_of_le hsmall
    simpa [M, hz] using (show 1 ≤ R by omega)
  have hB : B ≤ j+2 := by omega
  have hpowNat : M * (2 : ℕ)^B = 2^(j+2) := by
    dsimp only [M]
    rw [← pow_add, Nat.sub_add_cancel hB]
  have hpow : (M : ℝ) * (2 : ℝ)^B = 2^(j+2) := by exact_mod_cast hpowNat
  have hnReal : 0 < (n : ℝ)^3 := by positivity
  have hnTwo : (n : ℝ) ≤ (2 : ℝ)^(Nat.log 2 n + 1) := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (b := 2) (by decide) n).le
  have hnCube : (n : ℝ)^3 ≤ (2 : ℝ)^(3 * (Nat.log 2 n + 1)) := by
    rw [mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hnTwo 3
  have hCB : 4 * (n : ℝ)^3 ≤ c * 2^B := by
    dsimp only [B]
    rw [pow_add, ← mul_assoc]
    exact mul_le_mul hC hnCube (by positivity) (by positivity)
  have hscaled : (M : ℝ) * (4 * (n : ℝ)^3) ≤ 4 * (c * 2^j) := by
    calc
      _ ≤ (M : ℝ) * (c * 2^B) := mul_le_mul_of_nonneg_left hCB (Nat.cast_nonneg M)
      _ = c * ((M : ℝ) * 2^B) := by ring
      _ = c * 2^(j+2) := by rw [hpow]
      _ = _ := by rw [pow_add]; ring
  have hscale' : (M : ℝ) * (n : ℝ)^3 ≤ c * 2^j := by nlinarith
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdegree : c * (2 : ℝ)^j ≤ c * 2^j * (d : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hd' (show 0 ≤ c * (2 : ℝ)^j by positivity)
  have hlast : (M : ℝ) * (n : ℝ)^3 ≤ (R : ℝ) * (n : ℝ)^3 :=
    hscale'.trans (hdegree.trans ((div_le_iff₀ hnReal).1 hlower))
  exact_mod_cast (le_of_mul_le_mul_right hlast hnReal)

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

/-- Three-quarters coverage of an interval gives half coverage after reduction modulo
any positive modulus no larger than the original interval. -/
theorem card_disperserRemainders (A : Finset ℕ) {R M : ℕ}
    (hM : 0 < M) (hMR : M ≤ R) (hA : A ⊆ Finset.range R)
    (hDense : 3 * R ≤ 4 * A.card) : M ≤ 2 * (A.image fun y => y % M).card := by
  let t := R / M
  let T := t * M
  let B : Finset ℕ := Finset.range T ∩ A
  have ht : 0 < t := Nat.div_pos hMR hM
  have hTR : T ≤ R := Nat.div_mul_le_self R M
  have hMT : M ≤ T := by
    dsimp [T]
    simpa using Nat.mul_le_mul_right M (show 1 ≤ t by omega)
  have hRT : R ≤ 2 * T := by
    have hrem := Nat.mod_lt R hM
    have hdiv : T + R % M = R := by
      simpa [T, t, Nat.mul_comm] using Nat.div_add_mod R M
    omega
  have hB : T ≤ 2 * B.card := by
    have hcompl : Finset.range T \ A ⊆ Finset.range R \ A := by
      intro a ha
      rcases Finset.mem_sdiff.mp ha with ⟨ha, hn⟩
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp ha).trans_le hTR), hn⟩
    have hcards := Finset.card_le_card hcompl
    rw [Finset.card_sdiff, Finset.card_range, Finset.card_sdiff_of_subset hA,
      Finset.card_range] at hcards
    rw [Finset.inter_comm] at hcards
    change T - B.card ≤ R - A.card at hcards
    have hcA := Finset.card_le_card hA
    have hcB : B.card ≤ T := by
      simpa using Finset.card_le_card (Finset.inter_subset_left : B ⊆ Finset.range T)
    simp only [Finset.card_range] at hcA
    omega
  have hBupper : B.card ≤ t * (A.image fun y => y % M).card := by
    let f := fun y : ℕ => (y / M, y % M)
    have hinj : Function.Injective f := by
      intro a b heq
      have hdiv : a / M = b / M := congrArg Prod.fst heq
      have hmod : a % M = b % M := congrArg Prod.snd heq
      rw [← Nat.div_add_mod a M, ← Nat.div_add_mod b M, hdiv, hmod]
    have hsub : B.image f ⊆ (Finset.range t) ×ˢ (A.image fun y => y % M) := by
      intro p hp
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
      rcases Finset.mem_inter.mp hy with ⟨hyT, hyA⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_image_of_mem _ hyA⟩
      apply (Nat.div_lt_iff_lt_mul hM).mpr
      simpa [T, Nat.mul_comm] using Finset.mem_range.mp hyT
    simpa only [Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.card_range] using
      Finset.card_le_card hsub
  have hmul : t * M ≤ t * (2 * (A.image fun y => y % M).card) := by
    dsimp [T] at hB
    calc
      t * M ≤ 2 * B.card := hB
      _ ≤ 2 * (t * (A.image fun y => y % M).card) := Nat.mul_le_mul_left _ hBupper
      _ = t * (2 * (A.image fun y => y % M).card) := by ac_rfl
  exact Nat.le_of_mul_le_mul_left hmul ht

/-- Copy the folded graph into disjoint intervals. The lower bound is half of the
entire new right-hand side, independently of the copy count. -/
theorem card_normalizedDisperser (A : Finset ℕ) {R M C : ℕ}
    (hM : 0 < M) (hMR : M ≤ R) (hA : A ⊆ Finset.range R)
    (hDense : 3 * R ≤ 4 * A.card) :
    C * M ≤ 2 * (((Finset.range C) ×ˢ (A.image fun y => y % M)).image
      fun p => p.1 * M + p.2).card := by
  let U := (Finset.range C) ×ˢ (A.image fun y => y % M)
  let f := fun p : ℕ × ℕ => p.1 * M + p.2
  have hright (p : ℕ × ℕ) (hp : p ∈ U) : p.2 < M := by
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (Finset.mem_product.mp hp).2
    rw [← hy]
    exact Nat.mod_lt _ hM
  have hinj : Set.InjOn f U := by
    intro a ha b hb heq
    change a.1 * M + a.2 = b.1 * M + b.2 at heq
    have hright_eq : a.2 = b.2 := by
      have hmod := congrArg (fun z => z % M) heq
      simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (hright a ha),
        Nat.mod_eq_of_lt (hright b hb)] using hmod
    have hleft_mul : a.1 * M = b.1 * M := by rw [hright_eq] at heq; omega
    exact Prod.ext (Nat.eq_of_mul_eq_mul_right hM hleft_mul) hright_eq
  change C * M ≤ 2 * (U.image f).card
  rw [Finset.card_image_of_injOn hinj]
  dsimp [U]
  rw [Finset.card_product, Finset.card_range]
  calc
    C * M ≤ C * (2 * (A.image fun y => y % M).card) :=
      Nat.mul_le_mul_left _ (card_disperserRemainders A hM hMR hA hDense)
    _ = 2 * (C * (A.image fun y => y % M).card) := by ac_rfl

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

/-- A universe of size `N` embeds into the strings of length `log₂ N + 1`. -/
theorem disperser_input_universe (N : ℕ) : N ≤ 2^(Nat.log 2 N + 1) :=
  (Nat.lt_pow_succ_log_self (b := 2) (by decide) N).le

/-- Every valid size threshold fits in the number of bits used for the left universe. -/
theorem disperser_input_threshold {N j : ℕ} (h : 2 ^ j ≤ N) :
    j ≤ Nat.log 2 N + 1 :=
  (Nat.le_log_of_pow_le (by decide) h).trans (Nat.le_succ _)

/-- The initial segment of a larger finite universe, keeping the numeric left label. -/
def disperserLeftEmbed {N L : ℕ} (hNL : N ≤ L) : Fin N ↪ Fin L :=
  ⟨fun l => ⟨l.val, l.isLt.trans_le hNL⟩, fun _ _ h => Fin.ext (congrArg (fun v : Fin L => v.val) h)⟩

/-- Decode a finite right vertex into its numeric label. -/
def disperserRightEmbed (R : ℕ) : Fin R ↪ ℕ :=
  ⟨Fin.val, fun _ _ h => Fin.ext h⟩

/-- Restrict the left universe and decode the right labels. Under pointwise agreement of
raw outputs and graph edges on valid slots, the two descriptions give the same neighbor set. -/
theorem fold_raw_neighbors_embed {N L d R : ℕ} (hNL : N ≤ L)
    (Γ : Fin L → Fin d → Fin R) (raw : ℕ → ℕ → Option ℕ)
    (hraw : ∀ (l : Fin N) (i : Fin d), raw l.val i.val = some (Γ (disperserLeftEmbed hNL l) i).val)
    (S : Finset (Fin N)) :
    let A := S.biUnion fun l => (Finset.range d).biUnion fun i => (raw l.val i).toFinset
    let AG := (S.map (disperserLeftEmbed hNL)).biUnion fun v => Finset.univ.image (Γ v)
    A = AG.map (disperserRightEmbed R) ∧ A.card = AG.card ∧ A ⊆ Finset.range R := by
  classical
  let A := S.biUnion fun l => (Finset.range d).biUnion fun i => (raw l.val i).toFinset
  let AG := (S.map (disperserLeftEmbed hNL)).biUnion fun v => Finset.univ.image (Γ v)
  change A = AG.map (disperserRightEmbed R) ∧ A.card = AG.card ∧ A ⊆ Finset.range R
  have heq : A = AG.map (disperserRightEmbed R) := by
    ext ρ
    constructor
    · intro hρ
      obtain ⟨l, hl, hleft⟩ := Finset.mem_biUnion.mp hρ
      obtain ⟨i, hi, hright⟩ := Finset.mem_biUnion.mp hleft
      let t : Fin d := ⟨i, Finset.mem_range.mp hi⟩
      rw [Option.mem_toFinset, show raw l.val i = _ from hraw l t] at hright
      have hval := Option.mem_some.mp hright
      refine Finset.mem_map.mpr ⟨Γ (disperserLeftEmbed hNL l) t, ?_, hval⟩
      exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_map.mpr ⟨l, hl, rfl⟩,
        Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩
    · intro hρ
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hρ
      obtain ⟨v, hv, hright⟩ := Finset.mem_biUnion.mp hy
      obtain ⟨l, hl, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hright
      exact Finset.mem_biUnion.mpr ⟨l, hl, Finset.mem_biUnion.mpr
        ⟨i.val, Finset.mem_range.mpr i.isLt, Option.mem_toFinset.mpr (Option.mem_def.mpr (hraw l i))⟩⟩
  refine ⟨heq, by rw [heq, Finset.card_map], ?_⟩
  intro ρ hρ
  rw [heq] at hρ
  obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hρ
  exact Finset.mem_range.mpr y.isLt

end CNFEncComplexity

namespace TimeSpaceMA

private theorem Program.step_fixed_or_work_increases (P : Program) (tape : ℕ → Bool)
    (st : State) :
    P.step tape st = st ∨ st.work + 1 ≤ (P.step tape st).work := by
  by_cases hhalt : st.halted = true
  · left
    simp [Program.step, hhalt]
  · cases hp : P[st.pc]? with
    | none => left; simp [Program.step, hhalt, hp]
    | some instr =>
      right
      cases instr <;> simp [Program.step, hhalt, hp] <;> omega

/-- A halted log-cost RAM computation is reached using no more iterations than its work. -/
theorem Program.runsTo_iterate_of_work_le (P : Program) {mem : ℕ → ℕ} {st : State} {F : ℕ}
    (hrun : P.RunsTo zeroTape mem st) (hF : st.work ≤ F) :
    (P.step zeroTape)^[F] (State.init mem) = st := by
  obtain ⟨T, hT, hhalt⟩ := hrun
  let f := P.step zeroTape
  have hshorten (n : ℕ) (s : State) (hn : f^[n] s = st) :
      ∃ m : ℕ, m + s.work ≤ st.work ∧ f^[m] s = st := by
    induction n generalizing s with
    | zero =>
      have hs : s = st := by simpa using hn
      exact ⟨0, by simp [hs], hn⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply] at hn
      rcases P.step_fixed_or_work_increases zeroTape s with hs | hs
      · change f s = s at hs
        rw [hs] at hn
        exact ih s hn
      · obtain ⟨m, hwork, hm⟩ := ih (f s) hn
        change s.work + 1 ≤ (f s).work at hs
        exact ⟨m + 1, by omega, by rw [Function.iterate_succ_apply]; exact hm⟩
  obtain ⟨m, hmwork, hm⟩ := hshorten T (State.init mem) hT
  have hmF : m ≤ F := by
    simpa [State.init] using Nat.le_trans hmwork hF
  have hfixed : f st = st := by simp [f, Program.step, hhalt]
  change f^[F] (State.init mem) = st
  calc
    f^[F] (State.init mem) = f^[F - m + m] (State.init mem) := by rw [Nat.sub_add_cancel hmF]
    _ = f^[F - m] st := by rw [Function.iterate_add_apply, hm]
    _ = st := Function.iterate_fixed hfixed _

end TimeSpaceMA

namespace CNFEncComplexity
open Turing.MultiTapeTM

private theorem fold_value_bound {i u M y : ℕ} (hu : 0 < u) (hM : 0 < M) :
    i % u * M + y % M < u * M := by
  have hi : i % u + 1 ≤ u := Nat.succ_le_of_lt (Nat.mod_lt i hu)
  calc
    _ < i % u * M + M := Nat.add_lt_add_left (Nat.mod_lt y hM) _
    _ = (i % u + 1) * M := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ u * M := Nat.mul_le_mul_right M hi

private theorem cloned_image_subset
    {N d u M p : ℕ} (S : Finset (Fin N)) (hcap : d * u ≤ p)
    (raw : ℕ → ℕ → Option ℕ) (folded : ℕ → ℕ → Option ℕ)
    (heval : ∀ l ∈ S, ∀ i < d, ∀ a < u, ∀ y : ℕ, raw (l : ℕ) i = some y →
      folded (l : ℕ) (i * u + a) = some (a * M + y % M)) :
    let A := S.biUnion fun l => (Finset.range d).biUnion fun i => (raw (l : ℕ) i).toFinset
    (((Finset.range u) ×ˢ (A.image fun y => y % M)).image
      fun a => a.1 * M + a.2) ⊆
      S.biUnion fun l => (Finset.range p).biUnion fun i => (folded (l : ℕ) i).toFinset := by
  dsimp only
  intro v hv
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  have ha' := Finset.mem_range.mp ha
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨l, hl, hy⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨i, hi, hy⟩ := Finset.mem_biUnion.mp hy
  have hi' := Finset.mem_range.mp hi
  have hiz : i * u + a < p := calc
    _ < i * u + u := Nat.add_lt_add_left ha' _
    _ = (i+1) * u := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ d * u := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi')
    _ ≤ p := hcap
  exact Finset.mem_biUnion.mpr ⟨l, hl, Finset.mem_biUnion.mpr
    ⟨i*u+a, Finset.mem_range.mpr hiz,
      Option.mem_toFinset.mpr (heval l hl i hi' a ha' y (Option.mem_toFinset.mp hy))⟩⟩

private theorem fold_run_properties (P : TimeSpaceMA.Program) (e C j N : ℕ)
    (hN : 2^j ≤ N) :
    let n := Nat.log 2 N + 1
    let B := C + 3 * (Nat.log 2 n + 1)
    let M := (2 : ℕ)^((j+2)-B)
    let u := (2 : ℕ)^(min (j+2) B)
    (∀ l i ρ, l < N → ramFoldedLayer P e C (N,j,l,i) = some ρ → ρ < u*M) ∧
    ∀ l < N, ∀ st : TimeSpaceMA.State,
      (P.step TimeSpaceMA.zeroTape)^[n^e+e]
        (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l])) = st →
      st.halted = true →
      ∀ i < st.mem 0, ∀ a < u,
        ramFoldedLayer P e C (N,j,l,i*u+a) =
          some (a*M+st.mem (1+i) % M) := by
  dsimp only
  let n := Nat.log 2 N + 1
  let B := C + 3 * (Nat.log 2 n + 1)
  let M := (2 : ℕ)^((j+2)-B)
  let u := (2 : ℕ)^(min (j+2) B)
  have hj := Nat.le_log_of_pow_le (b := 2) (by decide) hN
  have hu : 0 < u := Nat.pow_pos (by decide)
  have hM : 0 < M := Nat.pow_pos (by decide)
  constructor
  · intro l i ρ hl h
    simp only [ramFoldedLayer, if_pos (And.intro hj hl)] at h
    split at h
    · have he := Option.some.inj h
      rw [← he]
      exact fold_value_bound hu hM
    · cases h
  · intro l hl st hst hhalt i hi a ha
    have hd : (i*u+a)/u = i := by
      rw [Nat.mul_comm i u, Nat.add_comm, Nat.add_mul_div_left _ _ hu,
        Nat.div_eq_of_lt ha, Nat.zero_add]
    have hm : (i*u+a)%u = a := by
      rw [Nat.mul_comm i u, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
    simp only [ramFoldedLayer, if_pos (And.intro hj hl)]
    change (if ((P.step TimeSpaceMA.zeroTape)^[n^e+e]
        (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l]))).halted = true ∧
        (i*u+a)/u < ((P.step TimeSpaceMA.zeroTape)^[n^e+e]
          (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l]))).mem 0
      then some ((i*u+a)%u*M + ((P.step TimeSpaceMA.zeroTape)^[n^e+e]
        (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l]))).mem (1+(i*u+a)/u) % M)
      else none) = _
    rw [hst, hd, hm, if_pos ⟨hhalt,hi⟩]

end CNFEncComplexity

namespace CNFEncComplexity
open Turing.MultiTapeTM

private theorem teutsch_layers (c : ℝ) (e C : ℕ) (P : TimeSpaceMA.Program)
    (hc : 0 < c) (hC : (4 : ℝ) ≤ c * 2^C)
    (hTUZ : ∀ n j : ℕ, 1 ≤ n → j ≤ n →
      ∃ (d R : ℕ) (Γ : Fin (2 ^ n) → Fin d → Fin R),
      1 ≤ d ∧ d ≤ n ^ e + e ∧
      c * (2 : ℝ) ^ j * (d : ℝ) / (n : ℝ) ^ 3 ≤ (R : ℝ) ∧
      (∀ D : Finset (Fin (2 ^ n)), 2 ^ j ≤ D.card →
        (1 - (1 / 4 : ℝ)) * (R : ℝ) ≤
          ((D.biUnion fun v => Finset.univ.image (Γ v)).card : ℝ)) ∧
      ∀ v : Fin (2 ^ n),
        ∃ st, P.RunsTo TimeSpaceMA.zeroTape (TimeSpaceMA.memOf [n,j,v.val]) st ∧
          st.work ≤ n^e+e ∧ st.mem 0 = d ∧
          ∀ i : Fin d, st.mem (1+i.val) = (Γ v i).val) :
    let a := 2^(C+3) * (e+1) + e+3
    (∀ j N l i ρ : ℕ, 2 ^ j ≤ N → l < N → i < a * (Nat.log 2 N + 1)^a →
      ramFoldedLayer P e C (N, j, l, i) = some ρ → ρ < 2 ^ (j+2)) ∧
    (∀ j N : ℕ, 2 ^ j ≤ N → ∀ S : Finset (Fin N), 2 ^ j ≤ S.card →
      2 ^ (j+1) ≤ (S.biUnion fun l => (Finset.range (a * (Nat.log 2 N + 1)^a)).biUnion
        fun i => (ramFoldedLayer P e C (N, j, (l : ℕ), i)).toFinset).card) := by
  classical
  dsimp only
  let a := 2^(C+3) * (e+1) + e+3
  have combined (j N : ℕ) (hN : 2^j ≤ N) :
      (∀ l i ρ : ℕ, l < N → ramFoldedLayer P e C (N,j,l,i) = some ρ → ρ < 2^(j+2)) ∧
      (∀ S : Finset (Fin N), 2^j ≤ S.card →
        2^(j+1) ≤ (S.biUnion fun l => (Finset.range (a*(Nat.log 2 N+1)^a)).biUnion
          fun i => (ramFoldedLayer P e C (N,j,(l : ℕ),i)).toFinset).card) := by
    let n := Nat.log 2 N + 1
    let B := C + 3 * (Nat.log 2 n + 1)
    let M := (2 : ℕ)^((j+2)-B)
    let u := (2 : ℕ)^(min (j+2) B)
    let p := a*n^a
    let hNL : N ≤ 2^n := disperser_input_universe N
    have hn : 0 < n := Nat.succ_pos _
    have hM : 0 < M := Nat.pow_pos (by decide)
    obtain ⟨d, R, Γ, hd, hdlim, hRlow, hΓ, hP⟩ := hTUZ n j hn
      (disperser_input_threshold hN)
    have hd0 : 0 < d := hd
    have hR : 0 < R :=
      Nat.zero_lt_of_lt (Γ ⟨0, Nat.pow_pos (by decide)⟩ ⟨0, hd0⟩).isLt
    obtain ⟨hmul, hMR⟩ : u*M = 2^(j+2) ∧ M ≤ R :=
      fold_padding_parameters c C j n d R hc hC hn hd0 hR hRlow
    have hu : u ≤ 2^B := Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)
    have hcap : d*u ≤ p :=
      (Nat.mul_le_mul hdlim hu).trans (expander_clone_degree_le e C n hn)
    obtain ⟨hright, hslot⟩ := fold_run_properties P e C j N hN
    refine ⟨?_, ?_⟩
    · intro l i ρ hl hy
      exact hmul ▸ (hright l i ρ hl hy : ρ < u*M)
    · intro S hS
      let sim (l : ℕ) := (P.step TimeSpaceMA.zeroTape)^[n^e+e]
        (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l]))
      let raw (l i : ℕ) := some ((sim l).mem (1+i))
      have hst (l : Fin N) : (sim l.val).halted = true ∧ (sim l.val).mem 0 = d ∧
            ∀ i : Fin d, (sim l.val).mem (1+i.val) = (Γ (disperserLeftEmbed hNL l) i).val := by
        obtain ⟨st, hrun, hwork, hdeg, hout⟩ := hP (disperserLeftEmbed hNL l)
        have he : sim l.val = st := P.runsTo_iterate_of_work_le hrun hwork
        exact ⟨by rw [he]; obtain ⟨_, _, hhalt⟩ := hrun; exact hhalt, by rw [he, hdeg], by rw [he]; exact hout⟩
      let A := S.biUnion fun l => (Finset.range d).biUnion fun i => (raw l.val i).toFinset
      let AG := (S.map (disperserLeftEmbed hNL)).biUnion fun v => Finset.univ.image (Γ v)
      obtain ⟨_, hcard, hA⟩ : A = AG.map (disperserRightEmbed R) ∧
          A.card = AG.card ∧ A ⊆ Finset.range R :=
        fold_raw_neighbors_embed hNL Γ raw
          (fun l i => congrArg some ((hst l).2.2 i)) S
      have hSmap : 2^j ≤ (S.map (disperserLeftEmbed hNL)).card := by simpa using hS
      have hAG : (1 - (1/4 : ℝ)) * (R : ℝ) ≤ (AG.card : ℝ) := hΓ _ hSmap
      have hcoverReal : (3 : ℝ) * R ≤ 4 * A.card := by rw [hcard]; nlinarith
      have hcover : 3*R ≤ 4*A.card := by exact_mod_cast hcoverReal
      have hfold := card_normalizedDisperser (C := u) A hM hMR hA hcover
      let folded (l i : ℕ) := ramFoldedLayer P e C (N,j,l,i)
      have hsub := cloned_image_subset (M := M) S hcap raw folded
        (by
          intro l _ i hi t ht y hy
          have hy' : (sim l.val).mem (1+i) = y := Option.some.inj hy
          have hi' : i < (sim l.val).mem 0 := by rw [(hst l).2.1]; exact hi
          change ramFoldedLayer P e C (N,j,l.val,i*u+t) = _
          rw [← hy']
          exact hslot l.val l.isLt (sim l.val) rfl (hst l).1 i hi' t ht)
      have hcard' : (((Finset.range u) ×ˢ (A.image fun y => y % M)).image
          fun t => t.1 * M + t.2).card ≤
          (S.biUnion fun l => (Finset.range p).biUnion fun i => (folded l.val i).toFinset).card :=
        Finset.card_le_card hsub
      change _ ≤ (S.biUnion fun l => (Finset.range p).biUnion fun i => (folded l.val i).toFinset).card
      rw [hmul, show (2 : ℕ)^(j+2) = 2^(j+1) * 2 from pow_succ _ _] at hfold
      omega
  exact ⟨fun j N l i ρ hN hl _ hy => (combined j N hN).1 l i ρ hl hy,
    fun j N hN => (combined j N hN).2⟩

end CNFEncComplexity

open CNFEncComplexity Turing.MultiTapeTM

theorem solution :
    ∃ c : ℕ, ∃ nbr : ℕ × ℕ × ℕ × ℕ → Option ℕ,
      ComputableTidilyInPolyTime nbr (encPair encNat (encPair encNat (encPair encNat encNat))) (encOption encNat) ∧
      ∀ k N : ℕ, 2 ^ k ≤ N → ∃ r : ℕ, r < 2 ^ (k + 3) ∧
        (∀ l < N, ∀ i : ℕ, c * (Nat.log 2 N + 1) ^ c ≤ i → nbr (N, k, l, i) = none) ∧
        (∀ l < N, ∀ i ρ : ℕ, nbr (N, k, l, i) = some ρ → ρ < r) ∧
        ∀ S : Finset (Fin N), S.card ≤ 2 ^ k →
          S.card ≤ (S.biUnion fun l => (Finset.range (c * (Nat.log 2 N + 1) ^ c)).biUnion
            fun i => (nbr (N, k, (l : ℕ), i)).toFinset).card := by
  obtain ⟨c, e, P, hc, hP, hTUZ⟩ := TimeSpaceMA.theorem_A_1 (1/4) (by norm_num)
  obtain ⟨C, hC⟩ := fold_padding_constant hc
  obtain ⟨hbound, hspread⟩ := teutsch_layers c e C P hc hC hTUZ
  let a := 2^(C+3)*(e+1)+e+3
  have ha : 0 < a := by dsimp [a]; omega
  exact lemma_14_from_layers a ha (ramFoldedLayer P e C) hbound hspread
    (teutschNbr_native P e C a)
