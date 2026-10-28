-- Prove2me | solution 1 for CrossSell.Pricing.optimal_price
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:44:09.340532+00:00
-- url     : https://prove2.me/submissions/c763b9ce-153a-404c-bee6-cf4029e2e9ec

import Mathlib
import Definitions.Def_CrossSell_Pricing_Model

namespace CrossSell.Pricing
open Finset

section Aux
variable {ι κ : Type*}

lemma key_le (a x b : ℝ) : Real.exp (a - x) * (x - b) ≤ Real.exp (a - b - 1) := by
  have h := Real.add_one_le_exp (x - b - 1)
  have h2 : Real.exp (a - x) * Real.exp (x - b - 1) = Real.exp (a - b - 1) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (a - x) * (x - b) ≤ Real.exp (a - x) * Real.exp (x - b - 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith
    _ = _ := h2

lemma key_lt (a x b : ℝ) (hx : x ≠ b + 1) :
    Real.exp (a - x) * (x - b) < Real.exp (a - b - 1) := by
  have h := Real.add_one_lt_exp (show x - b - 1 ≠ 0 from fun h => hx (by linarith))
  have h2 : Real.exp (a - x) * Real.exp (x - b - 1) = Real.exp (a - b - 1) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp (a - x) * (x - b) < Real.exp (a - x) * Real.exp (x - b - 1) := by
        apply mul_lt_mul_of_pos_left _ (Real.exp_pos _)
        linarith
    _ = _ := h2

lemma key_eq (a x b : ℝ) (hx : x = b + 1) :
    Real.exp (a - x) * (x - b) = Real.exp (a - b - 1) := by
  rw [hx]
  have : b + 1 - b = 1 := by ring
  rw [this, mul_one]; congr 1; ring

lemma secProfit_mul_den (T : Option ι → Finset κ) (s : κ → ℝ) (v : Option ι → κ → ℝ)
    (r : κ → ℝ) (i : Option ι) :
    secProfit T s v r i * (1 + ∑ k ∈ T i, Real.exp (v i k - r k)) =
      ∑ l ∈ T i, (r l - s l) * Real.exp (v i l - r l) := by
  have hD : 0 < 1 + ∑ k ∈ T i, Real.exp (v i k - r k) := by positivity
  unfold secProfit secProb
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  field_simp

lemma secProfit_sub_le (T : Option ι → Finset κ) (s : κ → ℝ) (v : Option ι → κ → ℝ)
    (r : κ → ℝ) (i : Option ι) (lam : ℝ) :
    (secProfit T s v r i - lam) * (1 + ∑ k ∈ T i, Real.exp (v i k - r k)) ≤
      ∑ l ∈ T i, Real.exp (v i l - s l - lam - 1) - lam := by
  have h := secProfit_mul_den T s v r i
  have e : (secProfit T s v r i - lam) * (1 + ∑ k ∈ T i, Real.exp (v i k - r k)) =
      ∑ l ∈ T i, Real.exp (v i l - r l) * (r l - (s l + lam)) - lam := by
    rw [sub_mul, h]
    have : ∑ l ∈ T i, Real.exp (v i l - r l) * (r l - (s l + lam)) =
        ∑ l ∈ T i, (r l - s l) * Real.exp (v i l - r l) - lam * ∑ l ∈ T i, Real.exp (v i l - r l) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro l _; ring
    rw [this]; ring
  rw [e]
  have : ∑ l ∈ T i, Real.exp (v i l - r l) * (r l - (s l + lam)) ≤
      ∑ l ∈ T i, Real.exp (v i l - s l - lam - 1) := by
    apply Finset.sum_le_sum; intro l _
    have := key_le (v i l) (r l) (s l + lam)
    have e2 : v i l - (s l + lam) - 1 = v i l - s l - lam - 1 := by ring
    rw [e2] at this; exact this
  linarith

lemma secProfit_bound (T : Option ι → Finset κ) (s : κ → ℝ) (v : Option ι → κ → ℝ)
    (i : Option ι) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (∀ r : κ → ℝ, secProfit T s v r i ≤ lam) ∧
      ∃ r0 : κ → ℝ, secProfit T s v r0 i = lam := by
  set W : ℝ := ∑ l ∈ T i, Real.exp (v i l - s l - 1) with hW
  have hW0 : 0 ≤ W := by positivity
  let φ : ℝ → ℝ := fun x => x - ∑ l ∈ T i, Real.exp (v i l - s l - x - 1)
  have hφc : Continuous φ := by fun_prop
  have hφ0 : φ 0 ≤ 0 := by
    simp only [φ]
    have : 0 ≤ ∑ l ∈ T i, Real.exp (v i l - s l - 0 - 1) := by positivity
    linarith
  have hφW : 0 ≤ φ W := by
    simp only [φ]
    have : ∑ l ∈ T i, Real.exp (v i l - s l - W - 1) ≤ W := by
      rw [hW]
      apply Finset.sum_le_sum; intro l _
      apply Real.exp_le_exp.mpr
      linarith
    linarith
  obtain ⟨lam, hlam, hφl⟩ := intermediate_value_Icc hW0 hφc.continuousOn ⟨hφ0, hφW⟩
  have hl0 : 0 ≤ lam := hlam.1
  have hsum : ∑ l ∈ T i, Real.exp (v i l - s l - lam - 1) = lam := by
    simp only [φ] at hφl; linarith
  refine ⟨lam, hl0, ?_, ?_⟩
  · intro r
    have h := secProfit_sub_le T s v r i lam
    have hD : 0 < 1 + ∑ k ∈ T i, Real.exp (v i k - r k) := by positivity
    rw [hsum, sub_self] at h
    by_contra hc
    push_neg at hc
    have : 0 < (secProfit T s v r i - lam) * (1 + ∑ k ∈ T i, Real.exp (v i k - r k)) :=
      mul_pos (by linarith) hD
    linarith
  · refine ⟨fun l => s l + 1 + lam, ?_⟩
    have hE : ∀ l, Real.exp (v i l - (s l + 1 + lam)) = Real.exp (v i l - s l - lam - 1) := by
      intro l; congr 1; ring
    have hD : 1 + ∑ k ∈ T i, Real.exp (v i k - (s k + 1 + lam)) = 1 + lam := by
      simp only [hE]; rw [hsum]
    have h := secProfit_mul_den T s v (fun l => s l + 1 + lam) i
    simp only [hE] at h
    have h3 : ∑ l ∈ T i, (s l + 1 + lam - s l) * Real.exp (v i l - s l - lam - 1) = (1 + lam) * lam := by
      have : ∀ l, (s l + 1 + lam - s l) * Real.exp (v i l - s l - lam - 1) =
          (1 + lam) * Real.exp (v i l - s l - lam - 1) := by intro l; ring
      simp only [this]; rw [← Finset.mul_sum, hsum]
    have hD' : (1 + ∑ k ∈ T i, Real.exp (v i k - (s k + 1 + lam))) = 1 + lam := hD
    simp only [hE] at hD'
    rw [hD', h3] at h
    have : (1 + lam) ≠ 0 := by linarith
    have := mul_right_cancel₀ this (by linarith : secProfit T s v (fun l => s l + 1 + lam) i * (1 + lam) = lam * (1 + lam))
    exact this

end Aux

section Main
variable {ι κ : Type*}

lemma profit_sub (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) (z : ℝ) :
    profit S T u c s v p r - z =
      ((∑ i ∈ S, Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i) - z)) +
        secProfit T s v r none - z) / (1 + ∑ j ∈ S, Real.exp (u j - p j)) := by
  have hD : 0 < 1 + ∑ j ∈ S, Real.exp (u j - p j) := by positivity
  unfold profit
  rw [Finset.sum_insertNone]
  have h1 : ∀ i : Option ι, ∑ l ∈ T i, (r l - s l) * mainProb S u p i * secProb T v r i l
      = mainProb S u p i * secProfit T s v r i := by
    intro i; unfold secProfit; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  simp only [h1]
  rw [eq_div_iff hD.ne']
  have h2 : ∀ i : ι, (p i - c i) * mainProb S u p (some i) +
      mainProb S u p (some i) * secProfit T s v r (some i) =
      Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i)) /
        (1 + ∑ j ∈ S, Real.exp (u j - p j)) := by
    intro i; simp only [mainProb, mainDenom]; ring
  have h3 : (∑ i ∈ S, (p i - c i) * mainProb S u p (some i)) +
      (mainProb S u p none * secProfit T s v r none +
        ∑ i ∈ S, mainProb S u p (some i) * secProfit T s v r (some i)) =
      (∑ i ∈ S, Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i)) /
        (1 + ∑ j ∈ S, Real.exp (u j - p j))) +
        secProfit T s v r none / (1 + ∑ j ∈ S, Real.exp (u j - p j)) := by
    have : (∑ i ∈ S, (p i - c i) * mainProb S u p (some i)) +
        ∑ i ∈ S, mainProb S u p (some i) * secProfit T s v r (some i) =
        ∑ i ∈ S, Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i)) /
          (1 + ∑ j ∈ S, Real.exp (u j - p j)) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun i _ => h2 i)
    simp only [mainProb, mainDenom]
    simp only [mainProb, mainDenom] at this
    linarith [this, show 1 / (1 + ∑ j ∈ S, Real.exp (u j - p j)) * secProfit T s v r none =
      secProfit T s v r none / (1 + ∑ j ∈ S, Real.exp (u j - p j)) by ring]
  have h4 : (∑ i ∈ S, Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i) - z)) =
      (∑ i ∈ S, Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i))) -
        z * ∑ i ∈ S, Real.exp (u i - p i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [h4, h3, ← Finset.sum_div]
  field_simp
  ring

lemma num_le (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) (z : ℝ) :
    (∑ i ∈ S, Real.exp (u i - p i) * (p i - c i + secProfit T s v r (some i) - z)) ≤
      ∑ i ∈ S, Real.exp ((u i - c i - 1 - z) + secProfit T s v r (some i)) := by
  apply Finset.sum_le_sum; intro i _
  have := key_le (u i) (p i) (c i - secProfit T s v r (some i) + z)
  have e1 : p i - c i + secProfit T s v r (some i) - z =
      p i - (c i - secProfit T s v r (some i) + z) := by ring
  have e2 : u i - (c i - secProfit T s v r (some i) + z) - 1 =
      (u i - c i - 1 - z) + secProfit T s v r (some i) := by ring
  rw [e1]; rw [e2] at this; exact this

lemma profit_le_aux (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ) (z : ℝ) :
    profit S T u c s v p r - z ≤
      (Hr S T u c s v r z - z) / (1 + ∑ j ∈ S, Real.exp (u j - p j)) := by
  have hD : 0 < 1 + ∑ j ∈ S, Real.exp (u j - p j) := by positivity
  rw [profit_sub]
  apply div_le_div_of_nonneg_right _ hD.le
  unfold Hr
  linarith [num_le S T u c s v p r z]

lemma profit_at_opt (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (r : κ → ℝ) (z : ℝ) :
    profit S T u c s v (fun i => z + c i - secProfit T s v r (some i) + 1) r - z =
      (Hr S T u c s v r z - z) /
        (1 + ∑ j ∈ S, Real.exp (u j - (z + c j - secProfit T s v r (some j) + 1))) := by
  rw [profit_sub]
  congr 1
  unfold Hr
  congr 2
  apply Finset.sum_congr rfl; intro i _
  have := key_eq (u i) (z + c i - secProfit T s v r (some i) + 1)
    (c i - secProfit T s v r (some i) + z) (by ring)
  have e1 : z + c i - secProfit T s v r (some i) + 1 - c i + secProfit T s v r (some i) - z = 1 := by ring
  have e2 : u i - (c i - secProfit T s v r (some i) + z) - 1 =
      (u i - c i - 1 - z) + secProfit T s v r (some i) := by ring
  rw [e2] at this
  have e3 : z + c i - secProfit T s v r (some i) + 1 - (c i - secProfit T s v r (some i) + z) = 1 := by ring
  rw [e3, mul_one] at this
  rw [e1, mul_one]; exact this

lemma optimal_price' [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (zstar : ℝ) (rstar : κ → ℝ)
    (hz : zstar = Hmax S T u c s v zstar)
    (hr : ∀ r : κ → ℝ, Hr S T u c s v r zstar ≤ Hr S T u c s v rstar zstar) :
    profit S T u c s v (fun i => zstar + c i - secProfit T s v rstar (some i) + 1) rstar = zstar ∧
    ∀ (p : ι → ℝ) (r : κ → ℝ), profit S T u c s v p r ≤ zstar := by
  have hmax : Hmax S T u c s v zstar = Hr S T u c s v rstar zstar := by
    unfold Hmax
    exact le_antisymm (ciSup_le hr) (le_ciSup ⟨Hr S T u c s v rstar zstar, by
      rintro _ ⟨r, rfl⟩; exact hr r⟩ rstar)
  have hH : Hr S T u c s v rstar zstar = zstar := by rw [← hmax]; exact hz.symm
  constructor
  · have := profit_at_opt S T u c s v rstar zstar
    rw [hH, sub_self, zero_div] at this
    linarith
  · intro p r
    have h1 := profit_le_aux S T u c s v p r zstar
    have hD : 0 < 1 + ∑ j ∈ S, Real.exp (u j - p j) := by positivity
    have h2 : (Hr S T u c s v r zstar - zstar) / (1 + ∑ j ∈ S, Real.exp (u j - p j)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith [hr r]) hD.le
    linarith

lemma theorem_1a' (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (p : ι → ℝ) (r : κ → ℝ)
    (hopt : ∀ (p' : ι → ℝ) (r' : κ → ℝ), profit S T u c s v p' r' ≤ profit S T u c s v p r) :
    ∀ i ∈ S, ∀ j ∈ S, aggMarkup T c s v p r i = aggMarkup T c s v p r j := by
  classical
  have key : ∀ i ∈ S, aggMarkup T c s v p r i = profit S T u c s v p r + 1 := by
    intro i hi
    by_contra hne
    set P := profit S T u c s v p r with hP
    set t := secProfit T s v r (some i) with ht
    set p' : ι → ℝ := Function.update p i (P + c i - t + 1) with hp'
    have hp'i : p' i = P + c i - t + 1 := by simp [hp']
    have hp'j : ∀ j, j ≠ i → p' j = p j := fun j hj => by simp [hp', hj]
    have hopt' := hopt p' r
    have h0 := profit_sub S T u c s v p r P
    rw [← hP, sub_self] at h0
    have hD : 0 < 1 + ∑ j ∈ S, Real.exp (u j - p j) := by positivity
    have hD' : 0 < 1 + ∑ j ∈ S, Real.exp (u j - p' j) := by positivity
    have hN : (∑ j ∈ S, Real.exp (u j - p j) * (p j - c j + secProfit T s v r (some j) - P)) +
        secProfit T s v r none - P = 0 := by
      have := h0.symm
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · exact h
      · exact absurd h hD.ne'
    have h1 := profit_sub S T u c s v p' r P
    have hsplit : ∀ q : ι → ℝ, (∑ j ∈ S, Real.exp (u j - q j) *
          (q j - c j + secProfit T s v r (some j) - P)) =
        Real.exp (u i - q i) * (q i - c i + t - P) +
          ∑ j ∈ S.erase i, Real.exp (u j - q j) * (q j - c j + secProfit T s v r (some j) - P) := by
      intro q; rw [← Finset.add_sum_erase S _ hi]
    have herase : ∑ j ∈ S.erase i, Real.exp (u j - p' j) *
          (p' j - c j + secProfit T s v r (some j) - P) =
        ∑ j ∈ S.erase i, Real.exp (u j - p j) * (p j - c j + secProfit T s v r (some j) - P) := by
      apply Finset.sum_congr rfl; intro j hj
      rw [hp'j j (Finset.ne_of_mem_erase hj)]
    have hlt : Real.exp (u i - p i) * (p i - c i + t - P) <
        Real.exp (u i - (c i - t + P) - 1) := by
      have := key_lt (u i) (p i) (c i - t + P) (by
        intro h; apply hne; unfold aggMarkup; linarith)
      have e : u i - (c i - t + P) - 1 = u i - (c i - t + P) - 1 := rfl
      have e1 : p i - c i + t - P = p i - (c i - t + P) := by ring
      rw [e1]; exact this
    have heq : Real.exp (u i - p' i) * (p' i - c i + t - P) =
        Real.exp (u i - (c i - t + P) - 1) := by
      have := key_eq (u i) (p' i) (c i - t + P) (by rw [hp'i]; ring)
      have e1 : p' i - c i + t - P = p' i - (c i - t + P) := by ring
      rw [e1]; exact this
    have hN' : 0 < (∑ j ∈ S, Real.exp (u j - p' j) *
          (p' j - c j + secProfit T s v r (some j) - P)) + secProfit T s v r none - P := by
      rw [hsplit p', herase, heq]
      rw [hsplit p] at hN
      linarith
    have : 0 < profit S T u c s v p' r - P := by
      rw [h1]; exact div_pos hN' hD'
    linarith
  intro i hi j hj
  rw [key i hi, key j hj]

end Main

section Fixed
variable {ι κ : Type*}

lemma Hr_eq (S : Finset ι) (T : Option ι → Finset κ) (u c : ι → ℝ) (s : κ → ℝ)
    (v : Option ι → κ → ℝ) (r : κ → ℝ) (z : ℝ) :
    Hr S T u c s v r z = Real.exp (-z) *
      (∑ i ∈ S, Real.exp (u i - c i - 1 + secProfit T s v r (some i))) +
        secProfit T s v r none := by
  unfold Hr; rw [Finset.mul_sum]; congr 1
  apply Finset.sum_congr rfl; intro i _
  rw [← Real.exp_add]; congr 1; ring

lemma H_fixed_point' (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) :
    (∀ z : ℝ, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z)) ∧
    (∃! z : ℝ, z = Hmax S T u c s v z) ∧
    (S.Nonempty → StrictAnti (Hmax S T u c s v)) := by
  classical
  choose lam hlam0 hlamle hlamatt using fun i : Option ι => secProfit_bound T s v i
  set Abar : ℝ := ∑ i ∈ S, Real.exp (u i - c i - 1 + lam (some i)) with hAbar
  have hAbar0 : 0 ≤ Abar := by positivity
  set A : (κ → ℝ) → ℝ :=
    fun r => ∑ i ∈ S, Real.exp (u i - c i - 1 + secProfit T s v r (some i)) with hA
  have hA0 : ∀ r, 0 ≤ A r := fun r => by simp only [hA]; positivity
  have hAle : ∀ r, A r ≤ Abar := by
    intro r
    apply Finset.sum_le_sum; intro i _
    apply Real.exp_le_exp.mpr
    linarith [hlamle (some i) r]
  have hHr : ∀ r z, Hr S T u c s v r z = Real.exp (-z) * A r + secProfit T s v r none :=
    fun r z => Hr_eq S T u c s v r z
  have hHr_le : ∀ r z, Hr S T u c s v r z ≤ Real.exp (-z) * Abar + lam none := by
    intro r z
    rw [hHr]
    have := mul_le_mul_of_nonneg_left (hAle r) (Real.exp_pos (-z)).le
    linarith [hlamle none r]
  have hbdd : ∀ z, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z) :=
    fun z => ⟨_, by rintro _ ⟨r, rfl⟩; exact hHr_le r z⟩
  have hle : ∀ r z, Hr S T u c s v r z ≤ Hmax S T u c s v z :=
    fun r z => le_ciSup (hbdd z) r
  have hHmax_le : ∀ z, Hmax S T u c s v z ≤ Real.exp (-z) * Abar + lam none :=
    fun z => ciSup_le (fun r => hHr_le r z)
  have hanti : Antitone (Hmax S T u c s v) := by
    intro z1 z2 h
    apply ciSup_mono (hbdd z1)
    intro r
    rw [hHr, hHr]
    have := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h)) (hA0 r)
    linarith
  have hge : ∀ r z, secProfit T s v r none ≤ Hr S T u c s v r z := by
    intro r z; rw [hHr]
    have := mul_nonneg (Real.exp_pos (-z)).le (hA0 r)
    linarith
  have hlip : ∀ z1 z2, Hmax S T u c s v z1 ≤
      Hmax S T u c s v z2 + Abar * |Real.exp (-z1) - Real.exp (-z2)| := by
    intro z1 z2
    apply ciSup_le; intro r
    have h1 : Hr S T u c s v r z1 = Hr S T u c s v r z2 +
        (Real.exp (-z1) - Real.exp (-z2)) * A r := by
      rw [hHr, hHr]; ring
    have h2 : (Real.exp (-z1) - Real.exp (-z2)) * A r ≤
        |Real.exp (-z1) - Real.exp (-z2)| * A r :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (hA0 r)
    have h3 : |Real.exp (-z1) - Real.exp (-z2)| * A r ≤
        |Real.exp (-z1) - Real.exp (-z2)| * Abar :=
      mul_le_mul_of_nonneg_left (hAle r) (abs_nonneg _)
    have := hle r z2
    linarith
  have hcont : Continuous (Hmax S T u c s v) := by
    rw [continuous_iff_continuousAt]; intro z0
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
    apply squeeze_zero_norm (a := fun z => Abar * |Real.exp (-z) - Real.exp (-z0)|)
    · intro z
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := hlip z0 z
        rw [abs_sub_comm] at this
        linarith
      · have := hlip z z0
        linarith
    · have hc : Continuous fun z : ℝ => Abar * |Real.exp (-z) - Real.exp (-z0)| := by fun_prop
      have := hc.tendsto z0
      simpa using this
  have huniq : ∀ z z' : ℝ, z = Hmax S T u c s v z → z' = Hmax S T u c s v z' → z ≤ z' := by
    intro z z' h h'
    by_contra hlt
    push_neg at hlt
    have := hanti hlt.le
    linarith
  obtain ⟨r0, hr0⟩ := hlamatt none
  have hex : ∃ z : ℝ, z = Hmax S T u c s v z := by
    have hga : 0 < Hmax S T u c s v (lam none - 1) - (lam none - 1) := by
      have := hle r0 (lam none - 1)
      have := hge r0 (lam none - 1)
      linarith
    have hgb : Hmax S T u c s v (Abar + lam none + 1) - (Abar + lam none + 1) < 0 := by
      have h1 := hHmax_le (Abar + lam none + 1)
      have h2 : Real.exp (-(Abar + lam none + 1)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr; linarith [hlam0 none]
      have := mul_le_mul_of_nonneg_right h2 hAbar0
      linarith
    have hab : lam none - 1 ≤ Abar + lam none + 1 := by linarith
    have hgc : ContinuousOn (fun z => Hmax S T u c s v z - z) (Set.Icc (lam none - 1) (Abar + lam none + 1)) :=
      (hcont.sub continuous_id).continuousOn
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc' hab hgc
      (show (0:ℝ) ∈ Set.Icc (Hmax S T u c s v (Abar + lam none + 1) - (Abar + lam none + 1))
        (Hmax S T u c s v (lam none - 1) - (lam none - 1)) from ⟨hgb.le, hga.le⟩)
    exact ⟨z, by simp only at hz; linarith⟩
  refine ⟨hbdd, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hex
    exact ⟨z, hz, fun y hy => le_antisymm (huniq y z hy hz) (huniq z y hz hy)⟩
  · intro hne z1 z2 hlt
    have hAr0 : 0 < A r0 := by
      simp only [hA]; exact Finset.sum_pos (fun i _ => Real.exp_pos _) hne
    have hG : lam none < Hmax S T u c s v z2 := by
      have h1 := hle r0 z2
      rw [hHr, hr0] at h1
      have := mul_pos (Real.exp_pos (-z2)) hAr0
      linarith
    set G := Hmax S T u c s v z2 with hGdef
    set eta := G - lam none with heta
    have heta0 : 0 < eta := by linarith
    set q := Real.exp (z2 - z1) - 1 with hq
    have hq0 : 0 < q := by
      have : 1 < Real.exp (z2 - z1) := by
        rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
      linarith
    have hexp : Real.exp (-z1) = Real.exp (z2 - z1) * Real.exp (-z2) := by
      rw [← Real.exp_add]; congr 1; ring
    set theta := min (eta / 2) (q * eta / 2) with htheta
    have htheta0 : 0 < theta := lt_min (by linarith) (by positivity)
    have hth1 : theta ≤ eta / 2 := min_le_left _ _
    have hth2 : theta ≤ q * eta / 2 := min_le_right _ _
    obtain ⟨r, hr⟩ := exists_lt_of_lt_ciSup (show G - theta < Hmax S T u c s v z2 by linarith)
    have hX : eta / 2 ≤ Real.exp (-z2) * A r := by
      have := hr
      rw [hHr] at this
      have := hlamle none r
      linarith
    have hqX : q * (eta / 2) ≤ q * (Real.exp (-z2) * A r) :=
      mul_le_mul_of_nonneg_left hX hq0.le
    have h1 : Hr S T u c s v r z1 = Hr S T u c s v r z2 + q * (Real.exp (-z2) * A r) := by
      rw [hHr, hHr, hexp, hq]; ring
    have := hle r z1
    linarith

end Fixed

section Goal
variable {ι κ : Type*}

lemma theorem_1' (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) :
    (∀ (p : ι → ℝ) (r : κ → ℝ),
        (∀ (p' : ι → ℝ) (r' : κ → ℝ), profit S T u c s v p' r' ≤ profit S T u c s v p r) →
        ∀ i ∈ S, ∀ j ∈ S, aggMarkup T c s v p r i = aggMarkup T c s v p r j) ∧
    (∀ z : ℝ, BddAbove (Set.range fun r : κ → ℝ => Hr S T u c s v r z)) ∧
    (∃ zstar : ℝ, zstar = Hmax S T u c s v zstar ∧
        (∀ z : ℝ, z = Hmax S T u c s v z → z = zstar) ∧
        IsLUB (Set.range fun pr : (ι → ℝ) × (κ → ℝ) => profit S T u c s v pr.1 pr.2) zstar) ∧
    (S.Nonempty → StrictAnti (Hmax S T u c s v)) := by
  obtain ⟨hb, ⟨zs, hzs, huniq⟩, hsa⟩ := H_fixed_point' S T u c s v
  refine ⟨fun p r hopt => theorem_1a' S T u c s v p r hopt, hb,
    ⟨zs, hzs, fun z hz => huniq z hz, ?_⟩, hsa⟩
  constructor
  · rintro _ ⟨⟨p, r⟩, rfl⟩
    have h1 := profit_le_aux S T u c s v p r zs
    have hD : 0 < 1 + ∑ j ∈ S, Real.exp (u j - p j) :=
      add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
    have h0 : Hr S T u c s v r zs ≤ zs := by
      have := le_ciSup (hb zs) r
      have e : Hmax S T u c s v zs = ⨆ r : κ → ℝ, Hr S T u c s v r zs := rfl
      rw [← e] at this; linarith
    have h2 : (Hr S T u c s v r zs - zs) / (1 + ∑ j ∈ S, Real.exp (u j - p j)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hD.le
    simp only
    linarith
  · intro b hbd
    by_contra hlt
    push_neg at hlt
    have hlt' : b < ⨆ r : κ → ℝ, Hr S T u c s v r zs := by
      have e : Hmax S T u c s v zs = ⨆ r : κ → ℝ, Hr S T u c s v r zs := rfl
      rw [← e]; linarith
    obtain ⟨r, hr⟩ := exists_lt_of_lt_ciSup hlt'
    have h0 : Hr S T u c s v r zs ≤ zs := by
      have := le_ciSup (hb zs) r
      have e : Hmax S T u c s v zs = ⨆ r : κ → ℝ, Hr S T u c s v r zs := rfl
      rw [← e] at this; linarith
    set p : ι → ℝ := fun i => zs + c i - secProfit T s v r (some i) + 1 with hp
    have h1 := profit_at_opt S T u c s v r zs
    have hD1 : 1 ≤ 1 + ∑ j ∈ S, Real.exp (u j - (zs + c j - secProfit T s v r (some j) + 1)) := by
      have : 0 ≤ ∑ j ∈ S, Real.exp (u j - (zs + c j - secProfit T s v r (some j) + 1)) := by
        exact Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
      linarith
    set D := 1 + ∑ j ∈ S, Real.exp (u j - (zs + c j - secProfit T s v r (some j) + 1)) with hD
    have hD0 : 0 < D := by linarith
    have hx : Hr S T u c s v r zs - zs ≤ (Hr S T u c s v r zs - zs) / D := by
      rw [le_div_iff₀ hD0]
      nlinarith [mul_nonneg (by linarith : 0 ≤ -(Hr S T u c s v r zs - zs)) (by linarith : 0 ≤ D - 1)]
    have hmem := hbd ⟨(p, r), rfl⟩
    simp only [hp] at hmem
    linarith

end Goal

end CrossSell.Pricing

open CrossSell.Pricing

theorem solution {ι κ : Type*} [Fintype κ] (S : Finset ι) (T : Option ι → Finset κ)
    (u c : ι → ℝ) (s : κ → ℝ) (v : Option ι → κ → ℝ) (zstar : ℝ) (rstar : κ → ℝ)
    (hz : zstar = Hmax S T u c s v zstar)
    (hr : ∀ r : κ → ℝ, Hr S T u c s v r zstar ≤ Hr S T u c s v rstar zstar) :
    profit S T u c s v (fun i => zstar + c i - secProfit T s v rstar (some i) + 1) rstar = zstar ∧
    ∀ (p : ι → ℝ) (r : κ → ℝ), profit S T u c s v p r ≤ zstar :=
  optimal_price' S T u c s v zstar rstar hz hr
