-- Prove2me | solution 1 for FixpNash.Blocks.support_property
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:47:26.772728+00:00
-- url     : https://prove2.me/submissions/5b6ff3e0-cf12-4027-83ab-35275cb1a680

import Definitions.Def_FixpNash_Blocks_Form
import Definitions.Def_DGPNash_NashMap_nashMap

open scoped BigOperators
open FixpNash.Blocks DGPNash.NashMap AGT
set_option maxHeartbeats 1600000

private lemma nf_prof {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] (x : ∀ i, S i → ℝ) (i : ι) (w : S i → ℝ)
    (s : ∀ i, S i) : profileProb (Function.update x i w) s =
      w (s i) * ∏ k ∈ Finset.univ.erase i, x k (s k) := by
  classical
  unfold profileProb
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

private lemma nf_mix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (w : S i → ℝ) :
    expectedPayoff u (Function.update x i w) i = ∑ j, w j * purePayoff u x i j := by
  classical
  unfold purePayoff expectedPayoff
  simp_rw [nf_prof, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  simp [mul_ite, ite_mul, mul_assoc]

private lemma nf_self {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) :
    expectedPayoff u x i = ∑ j, x i j * purePayoff u x i j := by
  simpa only [Function.update_eq_self] using nf_mix u x i (x i)

private lemma nf_pure {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) :
    IsMixedNash u x ↔ IsMixedProfile x ∧ ∀ i j, purePayoff u x i j ≤ expectedPayoff u x i := by
  classical
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun i j => h i (fun k => if k=j then 1 else 0) ?_⟩
    constructor
    · intro k; dsimp; split_ifs <;> norm_num
    · simp
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro i w hw
    rw [nf_mix]
    calc
      (∑ j, w j * purePayoff u x i j) ≤ ∑ j, w j * expectedPayoff u x i :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h i j) (hw.1 j))
      _ = expectedPayoff u x i := by rw [← Finset.sum_mul, hw.2, one_mul]

private lemma nf_support {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (hNE : IsMixedNash u x) :
    ∀ i j, 0 < x i j → purePayoff u x i j = expectedPayoff u x i := by
  classical
  have h := (nf_pure u x).mp hNE
  intro i j hj
  have hz : ∑ k, x i k * (expectedPayoff u x i - purePayoff u x i k) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, (h.1 i).2, one_mul, ← nf_self]
    ring
  have hp (k : S i) : 0 ≤ x i k * (expectedPayoff u x i-purePayoff u x i k) :=
    mul_nonneg ((h.1 i).1 k) (sub_nonneg.mpr (h.2 i k))
  have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hp k) (Finset.mem_univ j)
  rw [hz] at hh
  nlinarith [h.2 i j]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)]
    (u : ι → (∀ k, S k) → ℝ) (x : ∀ k, S k → ℝ) (hx : AGT.IsMixedNash u x)
    (p : ι) (j : S p) :
    DGPNash.NashMap.purePayoff u x p j ≤ AGT.expectedPayoff u x p ∧
      (0 < x p j → DGPNash.NashMap.purePayoff u x p j = AGT.expectedPayoff u x p) := by
  exact ⟨((nf_pure u x).mp hx).2 p j, nf_support u x hx p j⟩
