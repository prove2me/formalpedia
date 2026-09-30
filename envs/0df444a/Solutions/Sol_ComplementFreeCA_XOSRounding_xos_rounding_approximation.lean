-- Prove2me | solution 1 for ComplementFreeCA.XOSRounding.xos_rounding_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:05:41.80314+00:00
-- url     : https://prove2.me/submissions/f0a8b89c-188e-44a1-b9f5-74e6d97ccf1d

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Definitions.Def_ComplementFreeCA_XOSRounding_Model
import Definitions.Def_ComplementFreeCA_XOSRounding_Rounding
import Definitions.Def_ComplementFreeCA_XOSRounding_Algorithm
open Finset

private theorem amgm_pow (d : ℕ) (hd : 0 < d) (Z : Fin d → ℝ) (hZ : ∀ i, 0 ≤ Z i) :
    ∏ i, Z i ≤ ((∑ i, Z i)/(d:ℝ)) ^ d := by
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have h := Real.geom_mean_le_arith_mean univ (fun _ : Fin d => (1:ℝ)) Z
    (by intro i hi; norm_num) (by simpa using hdR) (fun i hi => hZ i)
  simp only [Real.rpow_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_mul] at h
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (prod_nonneg (fun i hi => hZ i)) _) h (show (0:ℝ) ≤ d by positivity)
  rw [← Real.rpow_mul (prod_nonneg (fun i hi => hZ i)), inv_mul_cancel₀ (ne_of_gt hdR),
    Real.rpow_one, Real.rpow_natCast] at hp
  exact hp

private theorem failure_mono_step (a : ℕ) (ha : 1 ≤ a) :
    (1-1/(a:ℝ))^a ≤ (1-1/((a+1:ℕ):ℝ))^(a+1) := by
  have haR : (1:ℝ) ≤ a := by exact_mod_cast ha
  have hap : (0:ℝ) < a := by linarith
  have hbase : 0 ≤ 1-1/(a:ℝ) := by rw [sub_nonneg, div_le_one hap]; exact haR
  let Z : Fin (a+1) → ℝ := fun i => if i = Fin.last a then 1 else 1-1/(a:ℝ)
  have hz : ∀ i, 0 ≤ Z i := by intro i; dsimp [Z]; split_ifs <;> positivity
  have h := amgm_pow (a+1) (by omega) Z hz
  have hp : ∏ i, Z i = (1-1/(a:ℝ))^a := by simp [Z, Fin.prod_univ_castSucc]
  have hs : (∑ i, Z i) / ((a+1:ℕ):ℝ) = 1-1/((a+1:ℕ):ℝ) := by
    simp [Z, Fin.sum_univ_castSucc]
    field_simp
    ring
  rwa [hp,hs] at h

private theorem product_bound (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (X : Fin k → ℝ)
    (hX0 : ∀ i, 0 ≤ X i) (hX1 : ∀ i, X i ≤ 1) (hsum : ∑ i, X i ≤ 1) :
    1 - (1 - (∑ i, X i) / (k : ℝ)) ^ k ≤ 1 - ∏ i, (1 - X i) ∧
    (1 - (1 - 1 / (k : ℝ)) ^ k) * ∑ i, X i ≤ 1 - (1 - (∑ i, X i) / (k : ℝ)) ^ k ∧
    (1 - (1 - 1 / (n : ℝ)) ^ n) * ∑ i, X i ≤ (1 - (1 - 1 / (k : ℝ)) ^ k) * ∑ i, X i := by
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0:ℝ) < k := by linarith
  have hS : (0:ℝ) ≤ ∑ i, X i := sum_nonneg (fun i hi => hX0 i)
  refine ⟨?_, ?_, ?_⟩
  · have h := amgm_pow k (by omega) (fun i => 1-X i) (fun i => sub_nonneg.mpr (hX1 i))
    have he : (∑ i, (1-X i))/(k:ℝ) = 1-(∑ i, X i)/(k:ℝ) := by
      rw [sum_sub_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      rw [sub_div, div_self (ne_of_gt hkp)]
    rw [he] at h
    linarith
  · have hbase : 0 ≤ 1-1/(k:ℝ) := by rw [sub_nonneg, div_le_one hkp]; exact hkR
    have h := (convexOn_pow (𝕜 := ℝ) k).2 (show 1-1/(k:ℝ) ∈ Set.Ici 0 from hbase)
      (show (1:ℝ) ∈ Set.Ici 0 by norm_num) hS (sub_nonneg.mpr hsum) (by ring : (∑ i, X i)+(1-∑ i,X i)=1)
    simp only [smul_eq_mul, one_pow, mul_one] at h
    have he : (∑ i, X i)*(1-1/(k:ℝ))+(1-∑ i,X i) = 1-(∑ i,X i)/(k:ℝ) := by ring
    rw [he] at h
    nlinarith
  · have hm : (1-1/(k:ℝ))^k ≤ (1-1/(n:ℝ))^n := by
      induction n, hkn using Nat.le_induction with
      | base => exact le_rfl
      | succ t hkt ih => exact ih.trans (failure_mono_step t (hk.trans hkt))
    exact mul_le_mul_of_nonneg_right (by linarith) hS

open MeasureTheory Set ComplementFreeCA.XOSRounding

private noncomputable def tail (z t : ℝ) : ℝ := (Set.Ioc 0 z).indicator (fun _ => 1) t

private theorem tail_integrable (z : ℝ) : Integrable (tail z) := by
  apply (integrable_indicator_iff measurableSet_Ioc).mpr
  exact integrableOn_const (by simp)

private theorem tail_integral (z : ℝ) (hz : 0 ≤ z) : (∫ t, tail z t) = z := by
  unfold tail
  rw [integral_indicator_const (1:ℝ) measurableSet_Ioc]
  simp [Measure.real, Real.volume_Ioc, hz]

private theorem tail_nonneg (z t : ℝ) : 0 ≤ tail z t := by
  unfold tail
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

private theorem tail_of_pos (z t : ℝ) (ht : 0 < t) : tail z t = if t ≤ z then 1 else 0 := by
  simp [tail, Set.indicator, ht]

private theorem tail_of_nonpos (z t : ℝ) (ht : t ≤ 0) : tail z t = 0 := by
  simp [tail, Set.indicator, not_lt.mpr ht]

private theorem sum_tail_integrable {α : Type*} [Fintype α] (w z : α → ℝ) :
    Integrable (fun t => ∑ a, w a * tail (z a) t) := by
  apply integrable_finset_sum
  intro a ha
  exact (tail_integrable (z a)).const_mul (w a)

private theorem sum_tail_integral {α : Type*} [Fintype α] (w z : α → ℝ) (hz : ∀ a, 0 ≤ z a) :
    (∫ t, ∑ a, w a * tail (z a) t) = ∑ a, w a * z a := by
  rw [integral_finset_sum Finset.univ (fun a ha => (tail_integrable (z a)).const_mul (w a))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_const_mul, tail_integral _ (hz a)]

private theorem independent_union {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (p : ι → α → ℝ) (hp : ∀ i, ∑ a, p i a = 1) (B : ι → α → Prop) [∀ i, DecidablePred (B i)] :
    (∑ σ : ι → α, (∏ i, p i (σ i)) * (if ∃ i, B i (σ i) then 1 else 0)) =
      1 - ∏ i, (1 - ∑ a, if B i a then p i a else 0) := by
  classical
  have hmass : (∑ σ : ι → α, ∏ i, p i (σ i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hp]
  have hcomp : (∑ σ : ι → α, (∏ i, p i (σ i)) * (if ∃ i, B i (σ i) then 0 else 1)) =
      ∏ i, (1 - ∑ a, if B i a then p i a else 0) := by
    have hpcomp : ∀ i, (∑ a, if B i a then 0 else p i a) = 1 - ∑ a, if B i a then p i a else 0 := by
      intro i
      rw [← hp i, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> ring
    rw [← Finset.prod_congr rfl (fun i hi => hpcomp i), Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases h : ∃ i, B i (σ i)
    · rw [if_pos h, mul_zero]
      symm
      obtain ⟨i,hi⟩ := h
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    · have hi : ∀ i, ¬ B i (σ i) := by simpa using h
      simp [hi,h]
  have hadd : (∑ σ : ι → α, (∏ i, p i (σ i)) * (if ∃ i, B i (σ i) then 1 else 0)) +
      (∑ σ : ι → α, (∏ i, p i (σ i)) * (if ∃ i, B i (σ i) then 0 else 1)) = 1 := by
    calc
      _ = ∑ σ : ι → α, ∏ i, p i (σ i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro σ hσ
        split_ifs <;> ring
      _ = 1 := hmass
  linarith

private theorem expected_max {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPFeasible x) (j : Fin m) :
    (1 - (1 - 1 / (n : ℝ)) ^ n) *
        ∑ i, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S * cl i S j ≤
      roundingExpectation x (fun σ => maxClauseEntry hn cl σ j) := by
  classical
  let p := roundingLaw x
  let Q := fun σ => maxClauseEntry hn cl σ j
  let α : ℝ := 1-(1-1/(n:ℝ))^n
  let w := fun (i : Fin n) (S : Finset (Fin m)) => if j ∈ S then x i S else 0
  let L := fun t => ∑ i, ∑ S, w i S * tail (cl i S j) t
  let R := fun t => ∑ σ, profileProb x σ * tail (Q σ) t
  have hp0 : ∀ i S, 0 ≤ p i S := by
    intro i S
    dsimp [p, roundingLaw]
    split_ifs
    · have h1 := hx.2.1 i
      have h2 := hx.2.2 i S
      linarith
    · simpa using hx.2.2 i S
  have hp1 : ∀ i, ∑ S, p i S = 1 := by
    intro i
    simp [p, roundingLaw, Finset.sum_add_distrib]
  have hpeq : ∀ i S, j ∈ S → p i S = x i S := by
    intro i S hj
    have he : S ≠ ∅ := by intro he; simpa [he] using hj
    simp [p, roundingLaw, he]
  have hc0 : ∀ i S, 0 ≤ cl i S j := by
    intro i S
    exact (hv i).1.2 _ (hcl i S).1 j
  have hQ : ∀ σ i, cl i (σ i) j ≤ Q σ := by
    intro σ i
    exact Finset.le_sup' (f := fun i => cl i (σ i) j) (Finset.mem_univ i)
  have hQ0 : ∀ σ, 0 ≤ Q σ := by
    intro σ
    exact (hc0 ⟨0,hn⟩ _).trans (hQ σ ⟨0,hn⟩)
  have hRint : Integrable R := sum_tail_integrable (profileProb x) Q
  have hLint : Integrable L := by
    apply integrable_finset_sum
    intro i hi
    exact sum_tail_integrable (w i) (fun S => cl i S j)
  have hpoint : ∀ t, α*L t ≤ R t := by
    intro t
    by_cases ht : 0 < t
    · let B := fun (i : Fin n) (S : Finset (Fin m)) => j ∈ S ∧ t ≤ cl i S j
      let q := fun i => ∑ S, if B i S then p i S else 0
      have hq0 : ∀ i, 0 ≤ q i := by
        intro i
        apply Finset.sum_nonneg
        intro S hS
        split_ifs
        · exact hp0 i S
        · exact le_rfl
      have hq1 : ∀ i, q i ≤ 1 := by
        intro i
        rw [← hp1 i]
        apply Finset.sum_le_sum
        intro S hS
        split_ifs
        · exact le_rfl
        · exact hp0 i S
      have hqitem : ∀ i, q i ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S := by
        intro i
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro S hS
        by_cases hj : j ∈ S
        · by_cases hct : t ≤ cl i S j
          · simp [q, B, hj, hct, hpeq i S hj]
          · simp [B,hj,hct,hx.2.2 i S]
        · simp [B,hj]
      have hqsum : (∑ i, q i) ≤ 1 := (Finset.sum_le_sum (fun i hi => hqitem i)).trans (hx.1 j)
      have hpbound := product_bound n n (by omega) le_rfl q hq0 hq1 hqsum
      have hqL : (∑ i, q i) = L t := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro S hS
        by_cases hj : j ∈ S
        · by_cases hct : t ≤ cl i S j
          · simp [B, hj, hct, w, tail_of_pos _ _ ht, hpeq i S hj]
          · simp [B, hj, hct, w, tail_of_pos _ _ ht]
        · simp [B, hj, w]
      have htail : 1-∏ i, (1-q i) ≤ R t := by
        rw [← independent_union p hp1 B]
        apply Finset.sum_le_sum
        intro σ hσ
        have hpr : 0 ≤ ∏ i, p i (σ i) := Finset.prod_nonneg (fun i hi => hp0 i _)
        by_cases he : ∃ i, B i (σ i)
        · obtain ⟨i,hi⟩ := he
          have htQ : t ≤ Q σ := hi.2.trans (hQ σ i)
          simp [show ∃ i, B i (σ i) from ⟨i,hi⟩, tail_of_pos _ _ ht, htQ, profileProb, p]
        · simp only [if_neg he, mul_zero]
          exact mul_nonneg hpr (tail_nonneg _ _)
      rw [← hqL]
      exact (hpbound.2.1.trans hpbound.1).trans htail
    · have ht' : t ≤ 0 := le_of_not_gt ht
      simp [L,R,tail_of_nonpos _ _ ht']
  have hi := integral_mono (hLint.const_mul α) hRint hpoint
  rw [integral_const_mul] at hi
  have hleft : (∫ t, L t) = ∑ i, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S * cl i S j := by
    rw [integral_finset_sum Finset.univ (fun i hi => sum_tail_integrable (w i) (fun S => cl i S j))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sum_tail_integral (w i) (fun S => cl i S j) (hc0 i), Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro S hS
    simp [w, ite_mul]
  have hright : (∫ t, R t) = roundingExpectation x (fun σ => maxClauseEntry hn cl σ j) := by
    exact sum_tail_integral (profileProb x) Q hQ0
  rw [hleft,hright] at hi
  exact hi

private theorem alg_ge_max {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (hwin : IsHighestClauseRule cl win)
    (σ : Fin n → Finset (Fin m)) :
    ∑ j, maxClauseEntry hn cl σ j ≤ algWelfare v win σ := by
  have hmax : ∀ j, maxClauseEntry hn cl σ j = cl (win σ j) (σ (win σ j)) j := by
    intro j
    apply le_antisymm
    · apply sup'_le
      intro i hi
      exact hwin σ j i
    · exact le_sup' (f := fun i => cl i (σ i) j) (mem_univ (win σ j))
  simp_rw [hmax]
  have he : (∑ j, cl (win σ j) (σ (win σ j)) j) =
      ∑ i, ∑ j ∈ algAllocation win σ i, cl i (σ i) j := by
    simp only [algAllocation, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    simp [eq_comm]
  rw [he]
  apply sum_le_sum
  intro i hi
  exact (hv i).2 _ |>.2 _ (hcl i (σ i)).1

private theorem expected_alg {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (hwin : IsHighestClauseRule cl win)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPFeasible x) :
    (1 - (1 - 1 / (n : ℝ)) ^ n) * lpValue v x ≤
      roundingExpectation x (algWelfare v win) := by
  classical
  have hprob : ∀ σ, 0 ≤ profileProb x σ := by
    intro σ
    apply Finset.prod_nonneg
    intro i hi
    unfold roundingLaw
    split_ifs
    · have h1 := hx.2.1 i
      have h2 := hx.2.2 i (σ i)
      linarith
    · simpa using hx.2.2 i (σ i)
  have hLP : (∑ j, ∑ i, ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin m) => j ∈ S), x i S * cl i S j) = lpValue v x := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hS
    calc
      (∑ j, if j ∈ S then x i S * cl i S j else 0) = x i S * ∑ j ∈ S, cl i S j := by
        rw [Finset.mul_sum]
        simp
      _ = x i S * v i S := by rw [(hcl i S).2]
  have hitem := Finset.sum_le_sum (s := Finset.univ) (fun j hj => expected_max hn W v hv cl hcl x hx j)
  rw [← Finset.mul_sum, hLP] at hitem
  have hlinear : (∑ j, roundingExpectation x (fun σ => maxClauseEntry hn cl σ j)) =
      roundingExpectation x (fun σ => ∑ j, maxClauseEntry hn cl σ j) := by
    unfold roundingExpectation
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [hlinear] at hitem
  refine hitem.trans ?_
  apply Finset.sum_le_sum
  intro σ hσ
  exact mul_le_mul_of_nonneg_left (alg_ge_max hn W v hv cl hcl win hwin σ) (hprob σ)

private theorem lp_bound {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPOptimal v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare v O ≤ lpValue v x := by
  classical
  let y : Fin n → Finset (Fin m) → ℝ := fun i S => if S = O i then 1 else 0
  have hy : IsLPFeasible y := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      simp only [y, sum_ite_eq', mem_filter, mem_univ, true_and]
      by_cases he : ∃ i, j ∈ O i
      · obtain ⟨i, hi⟩ := he
        have hother : ∀ i' ≠ i, j ∉ O i' := by
          intro i' hne hj
          exact disjoint_left.mp (hO hne) hj hi
        rw [sum_eq_single i]
        · simp [hi]
        · intro i' hi' hne
          simp [hother i' hne]
        · simp
      · simp only [not_exists] at he
        simp [he]
    · intro i
      simp [y]
    · intro i S
      simp only [y]
      split_ifs <;> norm_num
  have heq : lpValue v y = welfare v O := by
    simp [lpValue, welfare, y, ite_mul]
  rw [← heq]
  exact hx.2 y hy

theorem solution {n m : ℕ} (hn : 0 < n)
    (W : Fin n → Finset (Fin m → ℝ)) (v : Fin n → Finset (Fin m) → ℝ)
    (hv : ∀ i, IsXOSWith (v i) (W i))
    (cl : Fin n → Finset (Fin m) → Fin m → ℝ) (hcl : ∀ i, IsXOSOracle (v i) (W i) (cl i))
    (win : (Fin n → Finset (Fin m)) → Fin m → Fin n) (hwin : IsHighestClauseRule cl win)
    (x : Fin n → Finset (Fin m) → ℝ) (hx : IsLPOptimal v x)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    (1 - (1 - 1 / (n : ℝ)) ^ n) * welfare v O ≤
      roundingExpectation x (algWelfare v win) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hbase : 0 ≤ 1-1/(n:ℝ) := by
    rw [sub_nonneg, div_le_one hnR]
    exact_mod_cast (show 1 ≤ n by omega)
  have hupper : 1-1/(n:ℝ) ≤ 1 := by
    have h : (0:ℝ) ≤ 1/n := by positivity
    linarith
  have halpha : 0 ≤ 1-(1-1/(n:ℝ))^n := sub_nonneg.mpr (pow_le_one₀ hbase hupper)
  exact (mul_le_mul_of_nonneg_left (lp_bound v x hx O hO) halpha).trans
    (expected_alg hn W v hv cl hcl win hwin x hx.1)
