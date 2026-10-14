-- Prove2me | solution 1 for FixpNash.WeakApprox.isEpsApproxNash_iff_pure
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:59:17.571975+00:00
-- url     : https://prove2.me/submissions/8bfb1270-cd4e-4e3c-9105-ded3264cd3e1

import Mathlib
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_FixpNash_WeakApprox_NashFunction
import Definitions.Def_FixpNash_WeakApprox_GameConstants
open scoped BigOperators
open AGT FixpNash.WeakApprox
open DGPNash.NashMap (purePayoff)
set_option maxHeartbeats 1000000

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

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

private lemma wa_pure (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) :
    DGPNash.WellSupported.IsEpsApproxNash u x ε ↔
      IsMixedProfile x ∧ ∀ i j, purePayoff u x i j ≤ expectedPayoff u x i + ε := by
  classical
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro i j
    have hp : IsLottery (fun k : S i => if k=j then (1 : ℝ) else 0) := by
      constructor
      · intro k; dsimp; split_ifs <;> norm_num
      · simp
    have hh := h i _ hp
    change purePayoff u x i j - ε ≤ expectedPayoff u x i at hh
    linarith
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    intro i w hw
    rw [nf_mix]
    have hh : (∑ j, w j * purePayoff u x i j) ≤ expectedPayoff u x i + ε := by
      calc
        _ ≤ ∑ j, w j * (expectedPayoff u x i + ε) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h i j) (hw.1 j))
        _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]
    linarith


 theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (ε : ℝ) :
    DGPNash.WellSupported.IsEpsApproxNash u x ε ↔
      AGT.IsMixedProfile x ∧
        ∀ (i : ι) (j : S i),
          DGPNash.NashMap.purePayoff u x i j ≤ AGT.expectedPayoff u x i + ε := by
  exact wa_pure u x ε
#print axioms solution
