-- Prove2me | solution 1 for DermanSeqDecisions.LinProg.freq_solution_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:58:33.725994+00:00
-- url     : https://prove2.me/submissions/457cb7c5-2654-436d-b51a-d4503fdfd699

import Mathlib
import Definitions.Def_JewellMRP_InfiniteStep_Model
import Definitions.Def_DermanSeqDecisions_LinProg_Model

open Matrix


namespace DermanSeqDecisions.LinProg

theorem dm_vecMul_pow {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ) (w : I → ℝ)
    (hw : w ᵥ* P = w) (k : ℕ) : w ᵥ* (P ^ k) = w := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hw]

theorem dm_inv_zero {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hP : P.IsIrreducible) (w : I → ℝ) (hw0 : ∀ i, 0 ≤ w i) (hw : w ᵥ* P = w) (j : I)
    (hj : w j = 0) : ∀ i, w i = 0 := by
  intro i
  obtain ⟨k, -, hk⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hP.nonneg).1 hP i j
  have hPk : ∀ a b, 0 ≤ (P ^ k) a b := fun a b => Matrix.pow_apply_nonneg hP.nonneg k a b
  have h1 := congrFun (dm_vecMul_pow P w hw k) j
  rw [Matrix.vecMul, dotProduct, hj] at h1
  have h2 : w i * (P ^ k) i j ≤ ∑ l, w l * (P ^ k) l j :=
    Finset.single_le_sum (f := fun l => w l * (P ^ k) l j)
      (fun l _ => mul_nonneg (hw0 l) (hPk l j)) (Finset.mem_univ i)
  have : w i * (P ^ k) i j = 0 := le_antisymm (by linarith) (mul_nonneg (hw0 i) (hPk i j))
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

theorem dm_stat_pos {I : Type*} [Fintype I] [DecidableEq I] (P : Matrix I I ℝ)
    (hP : P.IsIrreducible) (π : I → ℝ) (hπ : JewellMRP.InfiniteStep.IsStationary P π) :
    ∀ j, 0 < π j := by
  intro j
  rcases (hπ.1 j).lt_or_eq with h | h
  · exact h
  · have := dm_inv_zero P hP π hπ.1 hπ.2.2 j h.symm
    have h2 := hπ.2.1
    simp [this] at h2

theorem fsc_core {I Act : Type*} [Fintype I] [DecidableEq I] [Fintype Act]
    (q : I → Act → I → ℝ) (hq : IsTransitionLaw q)
    (hA : ∀ D : I → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible) :
    (∀ D : I → Act → ℝ, IsStationaryRandomized D → ∀ π : I → ℝ,
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π →
      IsFreqSolution q (fun j k => π j * D j k) ∧ ∀ j, 0 < ∑ k, π j * D j k) ∧
    ∀ x : I → Act → ℝ, IsFreqSolution q x →
      (∀ j, 0 < ∑ k, x j k) ∧ IsStationaryRandomized (decode x) ∧
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q (decode x)) (fun j => ∑ k, x j k) ∧
      ∀ j k, x j k = (∑ k', x j k') * decode x j k := by
  constructor
  · intro D hD π hπ
    have hpos := dm_stat_pos _ (hA D hD) π hπ
    have hrow : ∀ j, ∑ k, π j * D j k = π j := by
      intro j; rw [← Finset.mul_sum, hD.2 j, mul_one]
    refine ⟨⟨fun j k => mul_nonneg (hπ.1 j) (hD.1 j k), ?_, ?_⟩, ?_⟩
    · intro j
      have h := congrFun hπ.2.2 j
      simp only [Matrix.vecMul, dotProduct, chainMatrix, Matrix.of_apply] at h
      rw [hrow j]
      have : ∑ i, ∑ k, π i * D i k * q i k j = ∑ i, π i * ∑ a, q i a j * D i a := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => by ring
      rw [this, h]; ring
    · simp_rw [hrow]; exact hπ.2.1
    · intro j; rw [hrow]; exact hpos j
  · intro x hx
    obtain ⟨hx0, hbal, hsum⟩ := hx
    set s : I → ℝ := fun j => ∑ k, x j k with hs
    have hs0 : ∀ j, 0 ≤ s j := fun j => Finset.sum_nonneg fun k _ => hx0 j k
    have hAct : Nonempty Act := by
      by_contra h
      rw [not_nonempty_iff] at h
      have h0 : ∀ j, s j = 0 := fun j => by simp [hs]
      simp [h0] at hsum
    let D' : I → Act → ℝ := fun j k => if s j = 0 then (Fintype.card Act : ℝ)⁻¹ else x j k / s j
    have hcard : (0 : ℝ) < Fintype.card Act := by exact_mod_cast Fintype.card_pos
    have hD' : IsStationaryRandomized D' := by
      refine ⟨fun j k => ?_, fun j => ?_⟩
      · simp only [D']; split_ifs
        · positivity
        · exact div_nonneg (hx0 j k) (hs0 j)
      · simp only [D']; split_ifs with h
        · simp [Finset.card_univ]
        · rw [← Finset.sum_div]; exact div_self h
    have hmul : ∀ i k, s i * D' i k = x i k := by
      intro i k
      simp only [D']; split_ifs with h
      · have : x i k = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hx0 i k)).1 h k
          (Finset.mem_univ k)
        rw [h, this, zero_mul]
      · field_simp
    have hstat : JewellMRP.InfiniteStep.IsStationary (chainMatrix q D') s := by
      refine ⟨hs0, hsum, ?_⟩
      funext j
      simp only [Matrix.vecMul, dotProduct, chainMatrix, Matrix.of_apply]
      have : ∑ i, s i * ∑ a, q i a j * D' i a = ∑ i, ∑ k, x i k * q i k j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun a _ => ?_
        rw [← hmul i a]; ring
      rw [this]; linarith [hbal j]
    have hpos := dm_stat_pos _ (hA D' hD') s hstat
    have hdec : decode x = D' := by
      funext j k
      simp only [decode, D']
      rw [if_neg (hpos j).ne']
    refine ⟨hpos, hdec ▸ hD', hdec ▸ hstat, ?_⟩
    intro j k
    rw [hdec]; exact (hmul j k).symm

end DermanSeqDecisions.LinProg

open DermanSeqDecisions.LinProg


theorem solution {I Act : Type*} [Fintype I] [DecidableEq I] [Fintype Act]
    (q : I → Act → I → ℝ) (hq : IsTransitionLaw q)
    (hA : ∀ D : I → Act → ℝ, IsStationaryRandomized D → (chainMatrix q D).IsIrreducible) :
    (∀ D : I → Act → ℝ, IsStationaryRandomized D → ∀ π : I → ℝ,
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q D) π →
      IsFreqSolution q (fun j k => π j * D j k) ∧ ∀ j, 0 < ∑ k, π j * D j k) ∧
    ∀ x : I → Act → ℝ, IsFreqSolution q x →
      (∀ j, 0 < ∑ k, x j k) ∧ IsStationaryRandomized (decode x) ∧
      JewellMRP.InfiniteStep.IsStationary (chainMatrix q (decode x)) (fun j => ∑ k, x j k) ∧
      ∀ j k, x j k = (∑ k', x j k') * decode x j k := by
  exact fsc_core q hq hA
