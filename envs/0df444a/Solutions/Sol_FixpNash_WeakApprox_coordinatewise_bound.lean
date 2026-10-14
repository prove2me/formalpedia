-- Prove2me | solution 1 for FixpNash.WeakApprox.coordinatewise_bound
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:59:38.534584+00:00
-- url     : https://prove2.me/submissions/3649ce19-31f7-4955-91d0-086c35196306

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

private lemma wa_weights (x : ∀ i, S i → ℝ) (hx : IsMixedProfile x) :
    (∀ s, 0 ≤ profileProb x s) ∧ (∑ s, profileProb x s) = 1 := by
  classical
  constructor
  · intro s
    exact Finset.prod_nonneg (fun i _ => (hx i).1 (s i))
  · unfold profileProb
    rw [← Fintype.prod_sum]
    simp_rw [fun i => (hx i).2]
    simp

private lemma wa_expected_bounds (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ)
    (hx : IsMixedProfile x) (i : ι) :
    (⨅ s : (∀ k, S k), u i s) ≤ expectedPayoff u x i ∧
      expectedPayoff u x i ≤ (⨆ s : (∀ k, S k), u i s) := by
  classical
  have hw := wa_weights x hx
  constructor
  · calc
      _ = ∑ s, profileProb x s * (⨅ s : (∀ k, S k), u i s) := by rw [← Finset.sum_mul, hw.2, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
        (ciInf_le (Set.finite_range _).bddBelow s) (hw.1 s))
  · calc
      _ ≤ ∑ s, profileProb x s * (⨆ s : (∀ k, S k), u i s) := Finset.sum_le_sum
        (fun s _ => mul_le_mul_of_nonneg_left (le_ciSup (Set.finite_range _).bddAbove s) (hw.1 s))
      _ = _ := by rw [← Finset.sum_mul, hw.2, one_mul]

private lemma wa_update (x : ∀ i, S i → ℝ) (hx : IsMixedProfile x) (i : ι) (j : S i) :
    IsMixedProfile (Function.update x i (fun k => if k=j then 1 else 0)) := by
  classical
  intro k
  by_cases hk : k=i
  · subst k
    simp only [Function.update_self]
    constructor
    · intro a; dsimp; split_ifs <;> norm_num
    · simp
  · simpa only [Function.update_of_ne hk] using hx k

private lemma wa_constants (u : ι → (∀ i, S i) → ℝ) (x : ∀ i, S i → ℝ)
    (hx : IsMixedProfile x) (i : ι) : 1 ≤ cConst u ∧ ∀ j, |gain u x i j| < cConst u := by
  classical
  have he := wa_expected_bounds u x hx i
  have hs : (⨆ s : (∀ k, S k), u i s) - (⨅ s : (∀ k, S k), u i s) ≤ payoffSpread u :=
    le_ciSup (f := fun k => (⨆ s : (∀ l, S l), u k s) - (⨅ s : (∀ l, S l), u k s))
      (Set.finite_range _).bddAbove i
  constructor
  · unfold cConst
    linarith [he.1, he.2]
  · intro j
    have hp := wa_expected_bounds u _ (wa_update x hx i j) i
    change (⨅ s : (∀ k, S k), u i s) ≤ purePayoff u x i j ∧
      purePayoff u x i j ≤ (⨆ s : (∀ k, S k), u i s) at hp
    rw [abs_lt]
    unfold gain cConst
    constructor <;> linarith [he.1, he.2, hp.1, hp.2]

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

private lemma wa_coord (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (x : ∀ i, S i → ℝ)
    (hx : IsWeakApproxFixedPoint u x (ε^2/(4*cConst u^2*(maxNumStrategies S : ℝ)^3))) (i : ι) (j : S i) :
    |max 0 (gain u x i j) - x i j * ∑ k : S i, max 0 (gain u x i k)| <
      ε^2/(4*cConst u^2*(maxNumStrategies S : ℝ)^3) * (1+∑ k : S i, max 0 (gain u x i k)) ∧
    ε^2/(4*cConst u^2*(maxNumStrategies S : ℝ)^3) * (1+∑ k : S i, max 0 (gain u x i k)) <
      ε^2/(2*cConst u*(maxNumStrategies S : ℝ)^2) := by
  classical
  let c := cConst u
  let N : ℝ := maxNumStrategies S
  let G := ∑ k : S i, max 0 (gain u x i k)
  have hc : 1 ≤ c := (wa_constants u x hx.1 i).1
  have hN : 1 ≤ N := wa_npos i j
  have hc0 : 0 < c := by linarith
  have hN0 : 0 < N := by linarith
  have hG0 : 0 ≤ G := Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have hG : G < N*c := by
    have hk (k : S i) : max 0 (gain u x i k) < c :=
      max_lt hc0 ((le_abs_self _).trans_lt ((wa_constants u x hx.1 i).2 k))
    have hh : G < ∑ _ : S i, c := Finset.sum_lt_sum (fun k _ => (hk k).le)
      ⟨j, Finset.mem_univ j, hk j⟩
    have hcard : (Fintype.card (S i) : ℝ)*c ≤ N*c := mul_le_mul_of_nonneg_right (wa_card i) hc0.le
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
    linarith
  have hNc : 1 ≤ N*c := by nlinarith
  have hd : 0 < 1+G := by positivity
  constructor
  · rw [← wa_residual, abs_mul, abs_of_pos hd]
    exact mul_lt_mul_of_pos_right (hx.2 i j) hd
  · change ε^2/(4*c^2*N^3)*(1+G) < ε^2/(2*c*N^2)
    have he : ε^2/(4*c^2*N^3)*(2*c*N) = ε^2/(2*c*N^2) := by
      field_simp [ne_of_gt hc0, ne_of_gt hN0]
      <;> ring
    rw [← he]
    apply mul_lt_mul_of_pos_left (by nlinarith : 1+G < 2*c*N)
    positivity


 theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : ∀ i, S i → ℝ)
    (hx : IsWeakApproxFixedPoint u x
      (ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3))) :
    ∀ (i : ι) (j : S i),
      |max 0 (gain u x i j) - x i j * ∑ l : S i, max 0 (gain u x i l)| <
          ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3) *
            (1 + ∑ l : S i, max 0 (gain u x i l)) ∧
        ε ^ 2 / (4 * cConst u ^ 2 * (maxNumStrategies S : ℝ) ^ 3) *
            (1 + ∑ l : S i, max 0 (gain u x i l)) <
          ε ^ 2 / (2 * cConst u * (maxNumStrategies S : ℝ) ^ 2) := by
  exact wa_coord u ε hε x hx
#print axioms solution
