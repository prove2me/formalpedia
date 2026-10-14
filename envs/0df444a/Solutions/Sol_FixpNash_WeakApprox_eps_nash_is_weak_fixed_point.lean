-- Prove2me | solution 1 for FixpNash.WeakApprox.eps_nash_is_weak_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:59:26.811975+00:00
-- url     : https://prove2.me/submissions/19d5747f-2539-41c0-aea1-44f87ff0af61

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

private lemma wa_card (i : ι) : (Fintype.card (S i) : ℝ) ≤ maxNumStrategies S := by
  exact_mod_cast (Finset.le_sup (f := fun i => Fintype.card (S i)) (Finset.mem_univ i))

private lemma wa_npos (i : ι) (j : S i) : (1 : ℝ) ≤ maxNumStrategies S := by
  letI : Nonempty (S i) := ⟨j⟩
  have h : (1 : ℝ) ≤ Fintype.card (S i) := by exact_mod_cast Fintype.card_pos
  exact h.trans (wa_card i)

private lemma wa_residual (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ) (i : ι) (j : S i) :
    (nashFunction u x i j - x i j) * (1+∑ k : S i, max 0 (gain u x i k)) =
      max 0 (gain u x i j) - x i j * ∑ k : S i, max 0 (gain u x i k) := by
  have h0 : 0 ≤ ∑ k : S i, max 0 (gain u x i k) := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hd : 1 + ∑ k : S i, max 0 (gain u x i k) ≠ 0 := by positivity
  unfold nashFunction
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

private lemma wa_forward (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (x : ∀ i, S i → ℝ)
    (hx : DGPNash.WellSupported.IsEpsApproxNash u x (ε / ((maxNumStrategies S : ℝ)+1))) :
    IsWeakApproxFixedPoint u x ε := by
  have h := (wa_pure u x _).mp hx
  refine ⟨h.1, ?_⟩
  intro i j
  let N : ℝ := maxNumStrategies S
  let a := ε/(N+1)
  let G := ∑ k : S i, max 0 (gain u x i k)
  have hN : 1 ≤ N := wa_npos i j
  have ha : 0 < a := div_pos hε (by linarith)
  have hae : a*(N+1)=ε := div_mul_cancel₀ _ (by linarith)
  have hg (k : S i) : max 0 (gain u x i k) ≤ a := by
    apply max_le ha.le
    have hk := h.2 i k
    unfold gain
    dsimp [a, N]
    linarith
  have hG : G ≤ N*a := by
    calc
      G ≤ ∑ _ : S i, a := Finset.sum_le_sum (fun k _ => hg k)
      _ = (Fintype.card (S i) : ℝ)*a := by simp
      _ ≤ N*a := mul_le_mul_of_nonneg_right (wa_card i) ha.le
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hx0 := (h.1 i).1 j
  have hx1 : x i j ≤ 1 := by
    have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => (h.1 i).1 k) (Finset.mem_univ j)
    rwa [(h.1 i).2] at hh
  have he := wa_residual u x i j
  change (nashFunction u x i j-x i j)*(1+G)=max 0 (gain u x i j)-x i j*G at he
  have hp := hg j
  have hp0 : 0 ≤ max 0 (gain u x i j) := le_max_left _ _
  have hxG := mul_le_mul_of_nonneg_right hx1 hG0
  have hxG0 := mul_nonneg hx0 hG0
  have hεG := mul_nonneg hε.le hG0
  have hGa : G < ε := by nlinarith only [hae, hG, ha]
  have haε : a < ε := by nlinarith only [hae, hN, ha]
  apply abs_lt.mpr
  constructor
  · apply (mul_lt_mul_iff_left₀ (by positivity : 0 < 1+G)).mp
    nlinarith only [he, hp0, hxG, hGa, hεG]
  · apply (mul_lt_mul_iff_left₀ (by positivity : 0 < 1+G)).mp
    nlinarith only [he, hp, hxG0, haε, hεG]


 theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (ε' : ℝ) (hε' : 0 < ε') (x : ∀ i, S i → ℝ)
    (hx : DGPNash.WellSupported.IsEpsApproxNash u x (ε' / ((maxNumStrategies S : ℝ) + 1))) :
    IsWeakApproxFixedPoint u x ε' := by
  exact wa_forward u ε' hε' x hx
#print axioms solution
