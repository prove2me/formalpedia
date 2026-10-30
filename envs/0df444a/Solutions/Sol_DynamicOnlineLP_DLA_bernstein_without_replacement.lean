-- Prove2me | solution 1 for DynamicOnlineLP.DLA.bernstein_without_replacement
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-29T06:24:33.655988+00:00
-- url     : https://prove2.me/submissions/7e18c816-a4de-4e51-afec-315b27cb82ae

import Definitions.Def_DynamicOnlineLP_DLA_Instance
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

open Finset

namespace TCSShortlist.Bernstein

private noncomputable def elementary {ι : Type*} (s : Finset ι) (x : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ t ∈ s.powersetCard r, ∏ i ∈ t, x i

private theorem elementary_eq_esymm {ι : Type*} (s : Finset ι) (x : ι → ℝ) (r : ℕ) :
    elementary s x r = (s.val.map x).esymm r := (Finset.esymm_map_val x s r).symm

private theorem esymm_cons (s : Multiset ℝ) (a : ℝ) (r : ℕ) :
    (a ::ₘ s).esymm (r + 1) = s.esymm (r + 1) + a * s.esymm r := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map,
    Multiset.sum_map_mul_left]

private theorem elementary_insert {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (i : ι) (hi : i ∉ s) (r : ℕ) :
    elementary (insert i s) x (r + 1) =
      elementary s x (r + 1) + x i * elementary s x r := by
  simp only [elementary_eq_esymm, insert_val_of_notMem hi, Multiset.map_cons, esymm_cons]

private theorem elementary_congr {ι : Type*} (s : Finset ι) (x y : ι → ℝ)
    (h : ∀ i ∈ s, x i = y i) (r : ℕ) : elementary s x r = elementary s y r := by
  apply sum_congr rfl
  intro t ht
  apply prod_congr rfl
  intro i hi
  exact h i ((mem_powersetCard.mp ht).1 hi)

private theorem elementary_nonneg {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) (r : ℕ) : 0 ≤ elementary s x r := by
  apply sum_nonneg
  intro t ht
  exact prod_nonneg fun i hi ↦ hx i ((mem_powersetCard.mp ht).1 hi)

private theorem elementary_pair {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℝ) (i j : ι) (hij : i ≠ j)
    (hi : i ∉ s) (hj : j ∉ s) (r : ℕ) :
    elementary (insert i (insert j s)) x (r + 2) =
      elementary s x (r + 2) + (x i + x j) * elementary s x (r + 1) +
        x i * x j * elementary s x r := by
  rw [elementary_insert _ _ i (by simp [hij, hi]), elementary_insert _ _ j hj,
    elementary_insert _ _ j hj]
  ring

private theorem insert_pair_erase {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    insert i (insert j ((univ.erase i).erase j)) = univ := by
  rw [insert_erase (by simp [hij.symm]), insert_erase (mem_univ i)]

private theorem sum_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    ∑ k, f k = f i + f j + ∑ k ∈ (univ.erase i).erase j, f k := by
  conv_lhs => rw [← insert_pair_erase i j hij]
  rw [sum_insert (by simp [hij]), sum_insert (by simp)]
  ring

private theorem elementary_univ_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (i j : ι) (hij : i ≠ j) (r : ℕ) :
    elementary univ x (r + 2) =
      elementary ((univ.erase i).erase j) x (r + 2) +
        (x i + x j) * elementary ((univ.erase i).erase j) x (r + 1) +
        x i * x j * elementary ((univ.erase i).erase j) x r := by
  conv_lhs => rw [← insert_pair_erase i j hij]
  exact elementary_pair _ _ i j hij (by simp) (by simp) r

private theorem pair_average {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (i j : ι) (hij : i ≠ j) (r : ℕ) :
    let m := (x i + x j) / 2
    let y := Function.update (Function.update x i m) j m
    (∀ k, 0 ≤ y k) ∧ (∑ k, y k) = (∑ k, x k) ∧
      elementary univ x (r + 2) ≤ elementary univ y (r + 2) ∧
      (∑ k, (y k) ^ 2) = (∑ k, (x k) ^ 2) - (x i - x j) ^ 2 / 2 := by
  dsimp only
  let m := (x i + x j) / 2
  let y := Function.update (Function.update x i m) j m
  have hxi := hx i
  have hxj := hx j
  have hmi : y i = m := by simp [y, hij]
  have hmj : y j = m := by simp [y]
  have hout (k : ι) (hk : k ∈ (univ.erase i).erase j) : y k = x k := by
    have hki : k ≠ i := (mem_erase.mp (mem_erase.mp hk).2).1
    have hkj : k ≠ j := (mem_erase.mp hk).1
    simp [y, hki, hkj]
  have hsum : ∑ k ∈ (univ.erase i).erase j, y k =
      ∑ k ∈ (univ.erase i).erase j, x k := sum_congr rfl hout
  have hsq : ∑ k ∈ (univ.erase i).erase j, (y k) ^ 2 =
      ∑ k ∈ (univ.erase i).erase j, (x k) ^ 2 := by
    apply sum_congr rfl
    intro k hk
    rw [hout k hk]
  have he (n : ℕ) : elementary ((univ.erase i).erase j) y n =
      elementary ((univ.erase i).erase j) x n := elementary_congr _ _ _ hout n
  change (∀ k, 0 ≤ y k) ∧ (∑ k, y k) = (∑ k, x k) ∧
    elementary univ x (r + 2) ≤ elementary univ y (r + 2) ∧
    (∑ k, (y k) ^ 2) = (∑ k, (x k) ^ 2) - (x i - x j) ^ 2 / 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      rw [hmi]
      dsimp [m]
      positivity
    by_cases hkj : k = j
    · subst k
      rw [hmj]
      dsimp [m]
      positivity
    simpa [y, hki, hkj] using hx k
  · rw [sum_pair y i j hij, sum_pair x i j hij, hmi, hmj, hsum]
    dsimp [m]
    ring
  · rw [elementary_univ_pair x i j hij, elementary_univ_pair y i j hij,
      hmi, hmj, he, he, he]
    have hC := elementary_nonneg ((univ.erase i).erase j) x (fun k _ ↦ hx k) r
    have havg : x i * x j ≤ m * m := by
      dsimp [m]
      nlinarith only [sq_nonneg (x i - x j)]
    have hp := mul_le_mul_of_nonneg_right havg hC
    dsimp [m] at *
    nlinarith only [hp]
  · rw [sum_pair (fun k ↦ (y k) ^ 2) i j hij,
      sum_pair (fun k ↦ (x k) ^ 2) i j hij, hmi, hmj, hsq]
    dsimp [m]
    ring

private theorem continuous_elementary {ι : Type*} [Fintype ι] (r : ℕ) :
    Continuous (fun x : ι → ℝ ↦ elementary univ x r) := by
  unfold elementary
  fun_prop

private theorem elementary_constant (R r : ℕ) (a : ℝ) :
    elementary (univ : Finset (Fin R)) (fun _ ↦ a) r = (R.choose r : ℝ) * a ^ r := by
  unfold elementary
  calc
    (∑ t ∈ (univ : Finset (Fin R)).powersetCard r, ∏ _i ∈ t, a) =
        ∑ _t ∈ (univ : Finset (Fin R)).powersetCard r, a ^ r := by
      apply sum_congr rfl
      intro t ht
      simp [(mem_powersetCard.mp ht).2]
    _ = _ := by simp

private theorem elementary_bound_succ_succ (R r : ℕ) (hR : 0 < R)
    (x : Fin R → ℝ) (hx : ∀ i, 0 ≤ x i) :
    elementary univ x (r + 2) ≤
      (R.choose (r + 2) : ℝ) * ((∑ i, x i) / (R : ℝ)) ^ (r + 2) := by
  classical
  let S := ∑ i, x i
  let K : Set (Fin R → ℝ) :=
    Set.Icc (fun _ ↦ 0) (fun _ ↦ S) ∩ {y | ∑ i, y i = S}
  have hK (y : Fin R → ℝ) : y ∈ K ↔ (∀ i, 0 ≤ y i) ∧ ∑ i, y i = S := by
    constructor
    · intro hy
      exact ⟨hy.1.1, hy.2⟩
    · rintro ⟨hy, hsum⟩
      refine ⟨⟨hy, ?_⟩, hsum⟩
      intro i
      calc
        y i ≤ ∑ j, y j := single_le_sum (fun j _ ↦ hy j) (mem_univ i)
        _ = S := hsum
  have hKcompact : IsCompact K := by
    apply isCompact_Icc.inter_right
    exact isClosed_eq (by fun_prop) continuous_const
  have hxK : x ∈ K := (hK x).mpr ⟨hx, rfl⟩
  obtain ⟨z, hzK, hzmax⟩ := hKcompact.exists_isMaxOn ⟨x, hxK⟩
    (continuous_elementary (r + 2)).continuousOn
  let M : Set (Fin R → ℝ) := K ∩ {y | elementary univ y (r + 2) =
    elementary univ z (r + 2)}
  have hMcompact : IsCompact M := hKcompact.inter_right
    (isClosed_eq (continuous_elementary (r + 2)) continuous_const)
  obtain ⟨y, hyM, hymin⟩ := hMcompact.exists_isMinOn ⟨z, hzK, rfl⟩
    (show Continuous (fun y : Fin R → ℝ ↦ ∑ i, (y i) ^ 2) by fun_prop).continuousOn
  have hy0 : ∀ i, 0 ≤ y i := ((hK y).mp hyM.1).1
  have hyS : ∑ i, y i = S := ((hK y).mp hyM.1).2
  have hconstant (i j : Fin R) : y i = y j := by
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨hw0, hwsum, hwe, hwsq⟩ := pair_average y hy0 i j hij r
    let w := Function.update (Function.update y i ((y i + y j) / 2)) j ((y i + y j) / 2)
    have hwK : w ∈ K := (hK w).mpr ⟨hw0, hwsum.trans hyS⟩
    have hwM : w ∈ M := by
      refine ⟨hwK, le_antisymm (isMaxOn_iff.mp hzmax w hwK) ?_⟩
      exact hyM.2.symm.trans_le hwe
    have hmin := isMinOn_iff.mp hymin w hwM
    have hdiff : (y i - y j) ^ 2 = 0 := by
      nlinarith only [hmin, hwsq, sq_nonneg (y i - y j)]
    nlinarith only [hdiff]
  have hn : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hmean (i : Fin R) : y i = S / (R : ℝ) := by
    apply (eq_div_iff hn).mpr
    calc
      y i * (R : ℝ) = ∑ j, y j := by
        conv_rhs => arg 2; ext j; rw [hconstant j i]
        simp [mul_comm]
      _ = S := hyS
  have heq : elementary univ y (r + 2) =
      (R.choose (r + 2) : ℝ) * (S / (R : ℝ)) ^ (r + 2) := by
    rw [elementary_congr univ y (fun _ ↦ S / (R : ℝ)) (fun i _ ↦ hmean i),
      elementary_constant]
  calc
    elementary univ x (r + 2) ≤ elementary univ z (r + 2) := isMaxOn_iff.mp hzmax x hxK
    _ = elementary univ y (r + 2) := hyM.2.symm
    _ = _ := heq

/-- The normalized elementary symmetric mean is bounded by the arithmetic mean power. -/
theorem elementary_symmetric_mean_le {R r : ℕ} (hR : 0 < R) (_hr : r ≤ R)
    (x : Fin R → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (∑ t ∈ (univ : Finset (Fin R)).powersetCard r, ∏ i ∈ t, x i) ≤
      (R.choose r : ℝ) * ((∑ i, x i) / (R : ℝ)) ^ r := by
  classical
  change elementary univ x r ≤ _
  rcases r with _ | (_ | r)
  · simp [elementary]
  · have hn : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    simp [elementary, powersetCard_one, mul_div_cancel₀ (∑ i, x i) hn]
  · exact elementary_bound_succ_succ R r hR x hx

end TCSShortlist.Bernstein

open Finset

namespace TCSShortlist.Bernstein

private theorem sum_powersetCard_prod_perm {α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (x : α → ℝ) (σ : Equiv.Perm α) :
    (∑ T ∈ (univ : Finset α).powersetCard r, ∏ j ∈ T, x (σ j)) =
      ∑ T ∈ (univ : Finset α).powersetCard r, ∏ j ∈ T, x j := by
  apply Finset.sum_equiv σ.finsetCongr
  · intro T
    simp
  · intro T _
    simp

/-- Uniform permutation images of a fixed finite subset give its normalized symmetric mean. -/
theorem average_perm_prod_eq_symmetric_mean {R : ℕ} (S : Finset (Fin R)) (x : Fin R → ℝ) :
    (∑ σ : Equiv.Perm (Fin R), ∏ k ∈ S, x (σ k)) /
        (Fintype.card (Equiv.Perm (Fin R)) : ℝ) =
      (∑ T ∈ (univ : Finset (Fin R)).powersetCard S.card, ∏ j ∈ T, x j) /
        (Nat.choose R S.card : ℝ) := by
  classical
  let f (T : Finset (Fin R)) : ℝ := ∑ σ : Equiv.Perm (Fin R), ∏ k ∈ T, x (σ k)
  let P := (univ : Finset (Fin R)).powersetCard S.card
  have hsame (T : Finset (Fin R)) (hT : T ∈ P) : f T = f S := by
    have hcard : S.card = T.card := (Finset.mem_powersetCard.mp hT).2.symm
    obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_map_finset_eq S T hcard
    dsimp [f]
    rw [← hτ]
    simp only [Finset.prod_map, Equiv.coe_toEmbedding]
    change (∑ σ : Equiv.Perm (Fin R), ∏ k ∈ S, x ((σ * τ) k)) = _
    exact Equiv.sum_comp (Equiv.mulRight τ) (fun σ : Equiv.Perm (Fin R) ↦
      ∏ k ∈ S, x (σ k))
  have htotal : (Nat.choose R S.card : ℝ) * f S =
      (Fintype.card (Equiv.Perm (Fin R)) : ℝ) *
        (∑ T ∈ P, ∏ j ∈ T, x j) := by
    calc
      (Nat.choose R S.card : ℝ) * f S = ∑ T ∈ P, f S := by
        simp [P]
      _ = ∑ T ∈ P, f T := Finset.sum_congr rfl (fun T hT ↦ (hsame T hT).symm)
      _ = ∑ σ : Equiv.Perm (Fin R), ∑ T ∈ P, ∏ k ∈ T, x (σ k) := by
        dsimp [f]
        rw [Finset.sum_comm]
      _ = ∑ _σ : Equiv.Perm (Fin R), ∑ T ∈ P, ∏ k ∈ T, x k := by
        apply Finset.sum_congr rfl
        intro σ _
        exact sum_powersetCard_prod_perm S.card x σ
      _ = _ := by simp
  have hperm : (Fintype.card (Equiv.Perm (Fin R)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsize : S.card ≤ R := by simpa using S.card_le_univ
  have hchoose : (Nat.choose R S.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hsize).ne'
  change f S / _ = (∑ T ∈ P, ∏ j ∈ T, x j) / _
  apply (div_eq_div_iff hperm hchoose).2
  simpa only [mul_comm] using htotal

end TCSShortlist.Bernstein

open Finset

namespace TCSShortlist.Bernstein

/-- A quadratic exponential bound retaining the denominator needed for Bernstein's inequality. -/
theorem exp_le_one_add_add_sq_div (x L : ℝ) (_hL : 0 ≤ L) (hL2 : L < 2)
    (hx : |x| ≤ L) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 - L) := by
  have hd : 0 < 2 - L := by linarith
  have hdx : 0 < 2 - |x| := by linarith
  have hrem : |Real.exp x - 1 - x| ≤ Real.exp |x| - 1 - |x| := by
    have h := Complex.norm_exp_sub_sum_le_exp_norm_sub_sum (x : ℂ) 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_one, pow_zero, pow_one, div_one, zero_add] at h
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sub_add_eq_sub_sub] using h
  have hpad : Real.exp |x| - 1 - |x| ≤ |x| ^ 2 / (2 - |x|) := by
    have hp := Real.exp_le_two_add_div_two_sub (abs_nonneg x) (by linarith : |x| < 2)
    calc
      Real.exp |x| - 1 - |x| ≤ (2 + |x|) / (2 - |x|) - 1 - |x| := by
        linarith only [hp]
      _ = |x| ^ 2 / (2 - |x|) := by
        field_simp
        ring
  have hratio : |x| ^ 2 / (2 - |x|) ≤ x ^ 2 / (2 - L) := by
    rw [sq_abs]
    exact div_le_div_of_nonneg_left (sq_nonneg x) hd (by linarith)
  linarith only [le_abs_self (Real.exp x - 1 - x), hrem, hpad, hratio]

/-- The finite population MGF bound for centered values with a common absolute bound. -/
theorem average_exp_le_of_centered {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → ℝ) (Δ lam : ℝ) (hΔ : 0 ≤ Δ) (hlam : 0 ≤ lam)
    (hbound : ∀ i, |X i| ≤ Δ) (hcenter : ∑ i, X i = 0)
    (hlamΔ : lam * Δ < 2) :
    (∑ i, Real.exp (lam * X i)) / (Fintype.card ι : ℝ) ≤
      Real.exp (lam ^ 2 * ((∑ i, (X i) ^ 2) / (Fintype.card ι : ℝ)) /
        (2 - lam * Δ)) := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hd : 0 < 2 - lam * Δ := by linarith
  have hpoint (i : ι) :
      Real.exp (lam * X i) ≤ 1 + lam * X i + lam ^ 2 * (X i) ^ 2 / (2 - lam * Δ) := by
    have hscaled : |lam * X i| ≤ lam * Δ := by
      rw [abs_mul, abs_of_nonneg hlam]
      exact mul_le_mul_of_nonneg_left (hbound i) hlam
    simpa only [mul_pow] using
      exp_le_one_add_add_sq_div (lam * X i) (lam * Δ) (mul_nonneg hlam hΔ) hlamΔ hscaled
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) ↦ hpoint i)
  calc
    (∑ i, Real.exp (lam * X i)) / (Fintype.card ι : ℝ) ≤
        (∑ i, (1 + lam * X i + lam ^ 2 * (X i) ^ 2 / (2 - lam * Δ))) /
          (Fintype.card ι : ℝ) :=
      div_le_div_of_nonneg_right hsum hn.le
    _ = 1 + lam ^ 2 * ((∑ i, (X i) ^ 2) / (Fintype.card ι : ℝ)) /
          (2 - lam * Δ) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcenter,
        mul_zero, add_zero]
      field_simp
    _ ≤ Real.exp (lam ^ 2 * ((∑ i, (X i) ^ 2) / (Fintype.card ι : ℝ)) /
          (2 - lam * Δ)) := by
      simpa only [add_comm] using Real.add_one_le_exp
        (lam ^ 2 * ((∑ i, (X i) ^ 2) / (Fintype.card ι : ℝ)) / (2 - lam * Δ))

/-- Centering a finite population at its actual average gives the variance-sensitive MGF bound. -/
theorem average_exp_sub_mean_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (Δ lam : ℝ) (hΔ : 0 ≤ Δ) (hlam : 0 ≤ lam)
    (hbound : ∀ i, |c i - (∑ j, c j) / (Fintype.card ι : ℝ)| ≤ Δ)
    (hlamΔ : lam * Δ < 2) :
    (∑ i, Real.exp (lam * (c i - (∑ j, c j) / (Fintype.card ι : ℝ)))) /
        (Fintype.card ι : ℝ) ≤
      Real.exp (lam ^ 2 *
        ((∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
          (Fintype.card ι : ℝ)) / (2 - lam * Δ)) := by
  apply average_exp_le_of_centered _ Δ lam hΔ hlam hbound
  · have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  · exact hlamΔ

end TCSShortlist.Bernstein

open Finset

namespace TCSShortlist.Bernstein

/-- Sampling a fixed set of positions without replacement has no larger exponential
moment than independent sampling from the same finite population. -/
theorem average_exp_perm_sum_le {R : ℕ} (hR : 0 < R) (X : Fin R → ℝ)
    (S : Finset (Fin R)) (lam : ℝ) :
    (∑ σ : Equiv.Perm (Fin R), Real.exp (lam * ∑ k ∈ S, X (σ k))) /
        (Fintype.card (Equiv.Perm (Fin R)) : ℝ) ≤
      ((∑ j, Real.exp (lam * X j)) / (R : ℝ)) ^ S.card := by
  classical
  simp_rw [Finset.mul_sum, Real.exp_sum]
  rw [average_perm_prod_eq_symmetric_mean S (fun j ↦ Real.exp (lam * X j))]
  have hcard : S.card ≤ R := by simpa using S.card_le_univ
  have hchoose : 0 < (R.choose S.card : ℝ) := by
    exact_mod_cast Nat.choose_pos hcard
  calc
    _ ≤ ((R.choose S.card : ℝ) *
        ((∑ j, Real.exp (lam * X j)) / (R : ℝ)) ^ S.card) /
          (R.choose S.card : ℝ) :=
      div_le_div_of_nonneg_right
        (elementary_symmetric_mean_le hR hcard (fun j ↦ Real.exp (lam * X j))
          (fun j ↦ (Real.exp_pos _).le)) hchoose.le
    _ = _ := by rw [mul_div_cancel_left₀ _ hchoose.ne']

/-- The variance-sensitive exponential moment for a centered finite population
sampled at a fixed set of distinct positions. -/
theorem average_exp_perm_sum_le_of_centered {R : ℕ} (hR : 0 < R)
    (X : Fin R → ℝ) (S : Finset (Fin R)) (Δ lam : ℝ)
    (hΔ : 0 ≤ Δ) (hlam : 0 ≤ lam) (hbound : ∀ j, |X j| ≤ Δ)
    (hcenter : ∑ j, X j = 0) (hlamΔ : lam * Δ < 2) :
    (∑ σ : Equiv.Perm (Fin R), Real.exp (lam * ∑ k ∈ S, X (σ k))) /
        (Fintype.card (Equiv.Perm (Fin R)) : ℝ) ≤
      Real.exp (lam ^ 2 * ((S.card : ℝ) * ((∑ j, (X j) ^ 2) / (R : ℝ))) /
        (2 - lam * Δ)) := by
  have : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  have hscalar := average_exp_le_of_centered X Δ lam hΔ hlam hbound hcenter hlamΔ
  simp only [Fintype.card_fin] at hscalar
  have hnonneg : 0 ≤ (∑ j, Real.exp (lam * X j)) / (R : ℝ) := by positivity
  calc
    _ ≤ ((∑ j, Real.exp (lam * X j)) / (R : ℝ)) ^ S.card :=
      average_exp_perm_sum_le hR X S lam
    _ ≤ (Real.exp (lam ^ 2 * ((∑ j, (X j) ^ 2) / (R : ℝ)) /
        (2 - lam * Δ))) ^ S.card := pow_le_pow_left₀ hnonneg hscalar _
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end TCSShortlist.Bernstein

/-!
Finite population moments used by the exact without-replacement Bernstein bound.
All quantities use the population mean and variance with denominator the population size.
-/

open Finset

namespace TCSShortlist.Bernstein

theorem mean_mem_extrema {ι : Type*} [Fintype ι] [Nonempty ι] (c : ι → ℝ) :
    (⨅ i, c i) ≤ (∑ i, c i) / (Fintype.card ι : ℝ) ∧
      (∑ i, c i) / (Fintype.card ι : ℝ) ≤ ⨆ i, c i := by
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  constructor
  · apply (le_div_iff₀ hn).mpr
    calc
      (⨅ i, c i) * (Fintype.card ι : ℝ) = ∑ _i : ι, ⨅ i, c i := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i, c i := sum_le_sum fun i _ ↦ ciInf_le (Set.finite_range c).bddBelow i
  · apply (div_le_iff₀ hn).mpr
    calc
      (∑ i, c i) ≤ ∑ _i : ι, ⨆ i, c i :=
        sum_le_sum fun i _ ↦ le_ciSup (Set.finite_range c).bddAbove i
      _ = (⨆ i, c i) * (Fintype.card ι : ℝ) := by
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_comm]

theorem population_range_nonneg {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) : 0 ≤ (⨆ i, c i) - (⨅ i, c i) := by
  exact sub_nonneg.mpr (ciInf_le_ciSup (Set.finite_range c).bddBelow
    (Set.finite_range c).bddAbove)

theorem abs_sub_mean_le_range {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) (j : ι) :
    |c j - (∑ i, c i) / (Fintype.card ι : ℝ)| ≤ (⨆ i, c i) - (⨅ i, c i) := by
  obtain ⟨hlo, hhi⟩ := mean_mem_extrema c
  have hjlo := ciInf_le (Set.finite_range c).bddBelow j
  have hjhi := le_ciSup (Set.finite_range c).bddAbove j
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem population_variance_nonneg {ι : Type*} [Fintype ι] (c : ι → ℝ) :
    0 ≤ (∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
      (Fintype.card ι : ℝ) := by
  exact div_nonneg (sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

theorem population_variance_eq_zero_iff {ι : Type*} [Fintype ι] [Nonempty ι]
    (c : ι → ℝ) :
    (∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
        (Fintype.card ι : ℝ) = 0 ↔
      ∀ i, c i = (∑ j, c j) / (Fintype.card ι : ℝ) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro h i
    have hs := (div_eq_zero_iff.mp h).resolve_right hn
    have hi := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ sq_nonneg
      (c j - (∑ k, c k) / (Fintype.card ι : ℝ)))).mp hs i (mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · intro h
    apply div_eq_zero_iff.mpr
    left
    apply sum_eq_zero
    intro i _
    rw [show c i - (∑ j, c j) / (Fintype.card ι : ℝ) = 0 from sub_eq_zero.mpr (h i)]
    norm_num

theorem population_range_eq_zero_of_variance_eq_zero {ι : Type*}
    [Fintype ι] [Nonempty ι] (c : ι → ℝ)
    (h : (∑ i, (c i - (∑ j, c j) / (Fintype.card ι : ℝ)) ^ 2) /
      (Fintype.card ι : ℝ) = 0) : (⨆ i, c i) - (⨅ i, c i) = 0 := by
  have hc := (population_variance_eq_zero_iff c).mp h
  have hsup : (⨆ i, c i) = (∑ j, c j) / (Fintype.card ι : ℝ) := by
    simpa only [ciSup_const] using
      congrArg (fun f : ι → ℝ ↦ ⨆ i, f i) (funext hc)
  have hinf : (⨅ i, c i) = (∑ j, c j) / (Fintype.card ι : ℝ) := by
    simpa only [ciInf_const] using
      congrArg (fun f : ι → ℝ ↦ ⨅ i, f i) (funext hc)
  rw [hsup, hinf, sub_self]

theorem firstTimes_card_eq {R r : ℕ} (hr : r ≤ R) :
    (DynamicOnlineLP.DLA.firstTimes R r).card = r := by
  classical
  let e : ↥(DynamicOnlineLP.DLA.firstTimes R r) ≃ Fin r := {
    toFun := fun t ↦ ⟨t.val.val, by
      simpa [DynamicOnlineLP.DLA.firstTimes] using t.property⟩
    invFun := fun t ↦ ⟨⟨t.val, lt_of_lt_of_le t.isLt hr⟩,
      by simp [DynamicOnlineLP.DLA.firstTimes, t.isLt]⟩
    left_inv := by intro t; apply Subtype.ext; apply Fin.ext; rfl
    right_inv := by intro t; apply Fin.ext; rfl }
  simpa using Fintype.card_congr e

theorem sum_firstTimes_centered {R r : ℕ} (hr : r ≤ R) (c : Fin R → ℝ)
    (σ : Equiv.Perm (Fin R)) :
    (∑ k ∈ DynamicOnlineLP.DLA.firstTimes R r,
        (c (σ k) - (∑ j, c j) / (R : ℝ))) =
      (∑ k ∈ DynamicOnlineLP.DLA.firstTimes R r, c (σ k)) -
        (r : ℝ) * ((∑ j, c j) / (R : ℝ)) := by
  rw [sum_sub_distrib]
  simp only [sum_const, firstTimes_card_eq hr, nsmul_eq_mul]

theorem probPerm_le_one {R : ℕ} (P : Equiv.Perm (Fin R) → Prop) :
    DynamicOnlineLP.DLA.probPerm P ≤ 1 := by
  classical
  have hn : 0 < (Fintype.card (Equiv.Perm (Fin R)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  unfold DynamicOnlineLP.DLA.probPerm
  apply (div_le_one hn).mpr
  exact_mod_cast (card_filter_le (univ : Finset (Equiv.Perm (Fin R))) P)

end TCSShortlist.Bernstein

open Finset

namespace TCSShortlist.Bernstein

/-- Exponential Markov inequality for the uniform average on a finite nonempty space. -/
theorem finite_exp_chernoff {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (lam t B : ℝ) (hlam : 0 ≤ lam)
    (hmgf : (∑ ω, Real.exp (lam * Z ω)) / (Fintype.card Ω : ℝ) ≤ Real.exp B) :
    ((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) / (Fintype.card Ω : ℝ) ≤
      Real.exp (-lam * t + B) := by
  classical
  have hn : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : ((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) *
      Real.exp (lam * t) ≤ ∑ ω, Real.exp (lam * Z ω) := by
    calc
      _ = ∑ ω ∈ Finset.univ.filter (fun ω ↦ t ≤ Z ω), Real.exp (lam * t) := by
        simp
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω ↦ t ≤ Z ω), Real.exp (lam * Z ω) := by
        apply Finset.sum_le_sum
        intro ω hω
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hω).2 hlam)
      _ ≤ ∑ ω, Real.exp (lam * Z ω) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ ↦ (Real.exp_pos _).le)
  calc
    _ ≤ Real.exp B / Real.exp (lam * t) := by
      apply (le_div_iff₀ (Real.exp_pos _)).mpr
      calc
        _ = (((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) *
            Real.exp (lam * t)) / (Fintype.card Ω : ℝ) := by ring
        _ ≤ (∑ ω, Real.exp (lam * Z ω)) / (Fintype.card Ω : ℝ) :=
          div_le_div_of_nonneg_right hsum hn.le
        _ ≤ Real.exp B := hmgf
    _ = Real.exp (-lam * t + B) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- The exact one-sided Bernstein tail obtained from the Bernstein MGF premise. -/
theorem finite_bernstein_upper_of_mgf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (v Δ t : ℝ) (hv : 0 < v) (hΔ : 0 ≤ Δ) (ht : 0 < t)
    (hmgf : ∀ lam : ℝ, 0 ≤ lam → lam * Δ < 2 →
      (∑ ω, Real.exp (lam * Z ω)) / (Fintype.card Ω : ℝ) ≤
        Real.exp (lam ^ 2 * v / (2 - lam * Δ))) :
    ((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) / (Fintype.card Ω : ℝ) ≤
      Real.exp (-(t ^ 2) / (2 * v + t * Δ)) := by
  have hD : 0 < v + t * Δ / 2 := by positivity
  have hlam : 0 ≤ t / (v + t * Δ / 2) := (div_pos ht hD).le
  have hlamΔ : t / (v + t * Δ / 2) * Δ < 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith
  have hd : 0 < 2 - t / (v + t * Δ / 2) * Δ := by linarith
  have hden : 0 < 2 * v + t * Δ := by positivity
  have hexponent : -(t / (v + t * Δ / 2)) * t +
      (t / (v + t * Δ / 2)) ^ 2 * v / (2 - t / (v + t * Δ / 2) * Δ) =
      -(t ^ 2) / (2 * v + t * Δ) := by
    field_simp
    ring
  have h := finite_exp_chernoff Z (t / (v + t * Δ / 2)) t
    ((t / (v + t * Δ / 2)) ^ 2 * v / (2 - t / (v + t * Δ / 2) * Δ))
    hlam (hmgf _ hlam hlamΔ)
  simpa only [hexponent] using h

/-- The exact two-sided Bernstein tail from upper and lower MGF estimates. -/
theorem finite_bernstein_two_sided_of_mgf {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (Z : Ω → ℝ) (v Δ t : ℝ) (hv : 0 < v) (hΔ : 0 ≤ Δ) (ht : 0 < t)
    (hmgf : ∀ lam : ℝ, 0 ≤ lam → lam * Δ < 2 →
      ((∑ ω, Real.exp (lam * Z ω)) / (Fintype.card Ω : ℝ) ≤
        Real.exp (lam ^ 2 * v / (2 - lam * Δ))) ∧
      ((∑ ω, Real.exp (lam * (-Z ω))) / (Fintype.card Ω : ℝ) ≤
        Real.exp (lam ^ 2 * v / (2 - lam * Δ)))) :
    ((Finset.univ.filter (fun ω ↦ t ≤ |Z ω|)).card : ℝ) / (Fintype.card Ω : ℝ) ≤
      2 * Real.exp (-(t ^ 2) / (2 * v + t * Δ)) := by
  classical
  have hn : 0 < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hupper := finite_bernstein_upper_of_mgf Z v Δ t hv hΔ ht
    (fun lam hlam hlt ↦ (hmgf lam hlam hlt).1)
  have hlower := finite_bernstein_upper_of_mgf (fun ω ↦ -Z ω) v Δ t hv hΔ ht
    (fun lam hlam hlt ↦ (hmgf lam hlam hlt).2)
  have hcard : (Finset.univ.filter (fun ω ↦ t ≤ |Z ω|)).card ≤
      (Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card +
        (Finset.univ.filter (fun ω ↦ t ≤ -Z ω)).card := by
    calc
      _ ≤ ((Finset.univ.filter (fun ω ↦ t ≤ Z ω)) ∪
          (Finset.univ.filter (fun ω ↦ t ≤ -Z ω))).card := by
        apply Finset.card_le_card
        intro ω hω
        have hw := (Finset.mem_filter.mp hω).2
        by_cases hz : 0 ≤ Z ω
        · apply Finset.mem_union.mpr
          left
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            by simpa only [abs_of_nonneg hz] using hw⟩
        · apply Finset.mem_union.mpr
          right
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            by simpa only [abs_of_neg (lt_of_not_ge hz)] using hw⟩
      _ ≤ _ := Finset.card_union_le _ _
  have hcard_real : ((Finset.univ.filter (fun ω ↦ t ≤ |Z ω|)).card : ℝ) ≤
      ((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) +
        ((Finset.univ.filter (fun ω ↦ t ≤ -Z ω)).card : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ (((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) +
        ((Finset.univ.filter (fun ω ↦ t ≤ -Z ω)).card : ℝ)) /
          (Fintype.card Ω : ℝ) := div_le_div_of_nonneg_right hcard_real hn.le
    _ = ((Finset.univ.filter (fun ω ↦ t ≤ Z ω)).card : ℝ) / (Fintype.card Ω : ℝ) +
        ((Finset.univ.filter (fun ω ↦ t ≤ -Z ω)).card : ℝ) / (Fintype.card Ω : ℝ) :=
      add_div _ _ _
    _ ≤ Real.exp (-(t ^ 2) / (2 * v + t * Δ)) +
        Real.exp (-(t ^ 2) / (2 * v + t * Δ)) := add_le_add hupper hlower
    _ = 2 * Real.exp (-(t ^ 2) / (2 * v + t * Δ)) := by ring

end TCSShortlist.Bernstein

open Finset DynamicOnlineLP.DLA TCSShortlist.Bernstein

theorem solution {R : ℕ} (hR : 0 < R) (c : Fin R → ℝ) (r : ℕ)
    (hr : r ≤ R) (t : ℝ) (ht : 0 < t) :
    let cbar : ℝ := (∑ j : Fin R, c j) / (R : ℝ)
    let σR2 : ℝ := (∑ j : Fin R, (c j - cbar) ^ 2) / (R : ℝ)
    let ΔR : ℝ := (⨆ j : Fin R, c j) - (⨅ j : Fin R, c j)
    probPerm (fun σ : Equiv.Perm (Fin R) =>
        t ≤ |∑ k ∈ firstTimes R r, c (σ k) - (r : ℝ) * cbar|) ≤
      2 * Real.exp (-(t ^ 2) / (2 * (r : ℝ) * σR2 + t * ΔR)) := by
  classical
  have : Nonempty (Fin R) := ⟨⟨0, hR⟩⟩
  let μ : ℝ := (∑ j, c j) / (R : ℝ)
  let V : ℝ := (∑ j, (c j - μ) ^ 2) / (R : ℝ)
  let D : ℝ := (⨆ j, c j) - (⨅ j, c j)
  let X : Fin R → ℝ := fun j ↦ c j - μ
  let Z : Equiv.Perm (Fin R) → ℝ := fun σ ↦
    (∑ k ∈ firstTimes R r, c (σ k)) - (r : ℝ) * μ
  change probPerm (fun σ ↦ t ≤ |Z σ|) ≤
    2 * Real.exp (-(t ^ 2) / (2 * (r : ℝ) * V + t * D))
  have hV : 0 ≤ V := by
    simpa only [Fintype.card_fin] using population_variance_nonneg c
  have hD : 0 ≤ D := population_range_nonneg c
  have hsum (σ : Equiv.Perm (Fin R)) : (∑ k ∈ firstTimes R r, X (σ k)) = Z σ :=
    sum_firstTimes_centered hr c σ
  have hzero_event (hz : ∀ σ, Z σ = 0) : probPerm (fun σ ↦ t ≤ |Z σ|) = 0 := by
    unfold probPerm
    simp only [hz, abs_zero, not_le.mpr ht, filter_false, card_empty, Nat.cast_zero, zero_div]
  by_cases hr0 : r = 0
  · have hz : ∀ σ, Z σ = 0 := by
      intro σ
      dsimp [Z]
      simp [hr0, firstTimes]
    rw [hzero_event hz]
    positivity
  by_cases hV0 : V = 0
  · have hc : ∀ j, c j = μ := by
      have hiff := population_variance_eq_zero_iff c
      simp only [Fintype.card_fin] at hiff
      exact hiff.mp hV0
    have hz : ∀ σ, Z σ = 0 := by
      intro σ
      rw [← hsum σ]
      apply sum_eq_zero
      intro k _
      exact sub_eq_zero.mpr (hc (σ k))
    rw [hzero_event hz]
    positivity
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr0
  have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hV0)
  have hn : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hcenter : ∑ j, X j = 0 := by
    dsimp [X, μ]
    simp only [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hbound (j : Fin R) : |X j| ≤ D := by
    simpa only [Fintype.card_fin] using abs_sub_mean_le_range c j
  have hmgf (lam : ℝ) (hlam : 0 ≤ lam) (hlamD : lam * D < 2) :
      ((∑ σ : Equiv.Perm (Fin R), Real.exp (lam * Z σ)) /
          (Fintype.card (Equiv.Perm (Fin R)) : ℝ) ≤
        Real.exp (lam ^ 2 * ((r : ℝ) * V) / (2 - lam * D))) ∧
      ((∑ σ : Equiv.Perm (Fin R), Real.exp (lam * (-Z σ))) /
          (Fintype.card (Equiv.Perm (Fin R)) : ℝ) ≤
        Real.exp (lam ^ 2 * ((r : ℝ) * V) / (2 - lam * D))) := by
    constructor
    · have h := average_exp_perm_sum_le_of_centered hR X (firstTimes R r) D lam
        hD hlam hbound hcenter hlamD
      simpa only [hsum, firstTimes_card_eq hr] using h
    · have hcenterNeg : ∑ j, -X j = 0 := by rw [sum_neg_distrib, hcenter, neg_zero]
      have hboundNeg (j : Fin R) : |-X j| ≤ D := by rw [abs_neg]; exact hbound j
      have h := average_exp_perm_sum_le_of_centered hR (fun j ↦ -X j)
        (firstTimes R r) D lam hD hlam hboundNeg hcenterNeg hlamD
      simpa only [sum_neg_distrib, hsum, neg_sq, firstTimes_card_eq hr] using h
  have h := finite_bernstein_two_sided_of_mgf Z ((r : ℝ) * V) D t
    (mul_pos hrpos hVpos) hD ht hmgf
  simpa only [probPerm, mul_assoc] using h
