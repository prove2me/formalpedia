-- Prove2me | solution 1 for DGPNash.WellSupported.eq28_best_response
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:38:20.924287+00:00
-- url     : https://prove2.me/submissions/b81a1be1-87ce-45b3-a9a9-c7810a91ecfb

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_WellSupported_Equilibria

set_option autoImplicit false

namespace DGPNash.WellSupported.Eq28Aux

open Finset

theorem prod_update_split {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    (τ : ∀ i, β i) (q : ι) (c : β q) (G : ∀ i, β i → ℝ) :
    ∏ i, G i (Function.update τ q c i) = G q c * ∏ i ∈ univ.erase q, G i (τ i) := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ q)]
  simp only [Function.update_self]
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (ne_of_mem_erase hi)]

theorem expected_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (p : ι) :
    AGT.expectedPayoff u x p = ∑ j : S p, DGPNash.NashMap.purePayoff u x p j * x p j := by
  have hP : ∀ (c : S p → ℝ) (s : ∀ i, S i), AGT.profileProb (Function.update x p c) s =
      c (s p) * ∏ i ∈ univ.erase p, x i (s i) := by
    intro c s
    unfold AGT.profileProb
    exact prod_update_split x p c (fun i f => f (s i))
  have hx : AGT.expectedPayoff u x p = AGT.expectedPayoff u (Function.update x p (x p)) p := by
    rw [Function.update_eq_self]
  rw [hx]
  unfold DGPNash.NashMap.purePayoff AGT.expectedPayoff
  simp only [hP, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro s _
  have : ∑ j : S p, (if s p = j then (1:ℝ) else 0) * x p j = x p (s p) := by
    simp
  calc x p (s p) * (∏ i ∈ univ.erase p, x i (s i)) * u p s
      = (∑ j : S p, (if s p = j then (1:ℝ) else 0) * x p j) *
          (∏ i ∈ univ.erase p, x i (s i)) * u p s := by rw [this]
    _ = _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply sum_congr rfl
        intro j _
        ring

end DGPNash.WellSupported.Eq28Aux

open Finset in
open DGPNash.WellSupported in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (hu : ∀ p s, 0 ≤ u p s) (hr : 2 ≤ Fintype.card ι)
    (x : ∀ i, S i → ℝ) (ε : ℝ) (hx : IsEpsApproxNash u x ε) (p : ι) :
    ∑ j : S p, DGPNash.NashMap.purePayoff u x p j * x p j ≥ maxPurePayoff u x p - ε := by
  rw [← DGPNash.WellSupported.Eq28Aux.expected_eq_sum]
  have hne : Nonempty (S p) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := (hx.1 p).2
    simp at this
  have hle : ∀ j : S p, DGPNash.NashMap.purePayoff u x p j ≤ AGT.expectedPayoff u x p + ε := by
    intro j
    have hl : AGT.IsLottery (fun k : S p => if k = j then (1:ℝ) else 0) := by
      refine ⟨fun k => by dsimp only; split_ifs <;> norm_num, by simp⟩
    have := hx.2 p _ hl
    unfold DGPNash.NashMap.purePayoff
    linarith
  have : DGPNash.WellSupported.maxPurePayoff u x p ≤ AGT.expectedPayoff u x p + ε :=
    ciSup_le hle
  linarith
