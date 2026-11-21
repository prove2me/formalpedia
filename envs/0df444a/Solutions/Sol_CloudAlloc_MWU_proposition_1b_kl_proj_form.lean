-- Prove2me | solution 1 for CloudAlloc.MWU.proposition_1b_kl_proj_form
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:49:19.381752+00:00
-- url     : https://prove2.me/submissions/5d7e6b41-dced-49d1-a121-42f5b4cf2d78

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsKLProj

namespace Aux_CloudKL

theorem conv (u v Y : ℝ) (hu : 0 < u) (hv : 0 < v) (hY : 0 < Y) :
    v * Real.log (v / Y) - u * Real.log (u / Y) ≤ (v - u) * (Real.log (v / Y) + 1) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hv hu)
  rw [Real.log_div hv.ne' hu.ne'] at h
  rw [Real.log_div hv.ne' hY.ne', Real.log_div hu.ne' hY.ne']
  have key : u * (Real.log v - Real.log u) ≤ v - u := by
    have h2 := mul_le_mul_of_nonneg_left h hu.le
    have e : u * (v / u - 1) = v - u := by
      rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ v hu.ne', mul_one]
    linarith
  nlinarith [key]

end Aux_CloudKL

open CloudAlloc.MWU Aux_CloudKL in
theorem solution {N : ℕ} (hN : 2 ≤ N) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {y x : Fin N → ℝ} (hy : ∀ i, 0 < y i) (hx : IsKLProj N ε y x) :
    let S := Finset.univ.filter (fun i => x i = ε / N)
    ∃ μ : Fin N → ℝ, (∀ i, 0 ≤ μ i) ∧ (∀ i ∉ S, μ i = 0) ∧
      ∀ i, x i = y i * Real.exp (μ i) * ((1 - ε / N * S.card) / ∑ j ∈ Sᶜ, y j) := by
  intro S
  have hSdef : S = Finset.univ.filter (fun i => x i = ε / N) := rfl
  have hx' : (∑ k, x k = 1 ∧ ∀ k, ε / N ≤ x k) ∧
      ∀ z ∈ truncSimplex N ε, klDiv x y ≤ klDiv z y := hx
  obtain ⟨⟨hsum, hge⟩, hopt⟩ := hx'
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha : 0 < ε / N := div_pos hε hN0
  have hxpos : ∀ k, 0 < x k := fun k => lt_of_lt_of_le ha (hge k)
  -- first-order optimality via two-coordinate mass shifts
  have kkt : ∀ i j, ε / N < x i → x i / y i ≤ x j / y j := by
    intro i j hi
    by_contra hlt
    push_neg at hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    have hcross : x j * y i < x i * y j := (div_lt_div_iff₀ (hy j) (hy i)).1 hlt
    have hg : 0 < x i * y j - x j * y i := by linarith
    have hyy : 0 < y i + y j := by linarith [hy i, hy j]
    obtain ⟨t, ht⟩ : ∃ t : ℝ,
        t = min (x i - ε / N) ((x i * y j - x j * y i) / (2 * (y i + y j))) := ⟨_, rfl⟩
    have ht1 : t ≤ x i - ε / N := by rw [ht]; exact min_le_left _ _
    have ht2 : t ≤ (x i * y j - x j * y i) / (2 * (y i + y j)) := by
      rw [ht]; exact min_le_right _ _
    have htpos : 0 < t := by
      rw [ht]
      exact lt_min (by linarith) (div_pos hg (by linarith))
    have ht3 : t * (y i + y j) < x i * y j - x j * y i := by
      have h4 := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * (y i + y j))).1 ht2
      nlinarith
    obtain ⟨z, hz⟩ : ∃ z : Fin N → ℝ, ∀ k,
        z k = x k + t * ((if k = j then (1 : ℝ) else 0) - (if k = i then 1 else 0)) :=
      ⟨_, fun _ => rfl⟩
    have hzj : z j = x j + t := by
      rw [hz, if_pos rfl, if_neg hij.symm]; ring
    have hzi : z i = x i - t := by
      rw [hz, if_neg hij, if_pos rfl]; ring
    have hzk : ∀ k, k ≠ i → k ≠ j → z k = x k := fun k h1 h2 => by
      rw [hz, if_neg h2, if_neg h1]; ring
    have hzge : ∀ k, ε / N ≤ z k := by
      intro k
      by_cases hki : k = i
      · rw [hki, hzi]; linarith
      · by_cases hkj : k = j
        · rw [hkj, hzj]; linarith [hge j]
        · rw [hzk k hki hkj]; exact hge k
    have hzmem : z ∈ truncSimplex N ε := by
      show ∑ k, z k = 1 ∧ ∀ k, ε / N ≤ z k
      refine ⟨?_, hzge⟩
      rw [Finset.sum_congr rfl (fun k _ => hz k), Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
        if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _), hsum]
      ring
    have hzpos : ∀ k, 0 < z k := fun k => lt_of_lt_of_le ha (hzge k)
    have hdiff : klDiv z y - klDiv x y ≤
        t * (Real.log (z j / y j) + 1) - t * (Real.log (z i / y i) + 1) := by
      have e : klDiv z y - klDiv x y =
          ∑ k, (z k * Real.log (z k / y k) - x k * Real.log (x k / y k)) := by
        unfold klDiv
        rw [Finset.sum_sub_distrib]
      rw [e]
      calc ∑ k, (z k * Real.log (z k / y k) - x k * Real.log (x k / y k))
          ≤ ∑ k, (z k - x k) * (Real.log (z k / y k) + 1) :=
            Finset.sum_le_sum (fun k _ => conv (x k) (z k) (y k) (hxpos k) (hzpos k) (hy k))
        _ = ∑ k, ((if k = j then t * (Real.log (z k / y k) + 1) else 0) -
              (if k = i then t * (Real.log (z k / y k) + 1) else 0)) := by
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [hz k]
            split_ifs <;> ring
        _ = t * (Real.log (z j / y j) + 1) - t * (Real.log (z i / y i) + 1) := by
            rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq',
              if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
    have hlog : Real.log (z j / y j) < Real.log (z i / y i) := by
      rw [hzj, hzi]
      apply Real.log_lt_log (div_pos (by linarith [hxpos j]) (hy j))
      rw [div_lt_div_iff₀ (hy j) (hy i)]
      nlinarith
    have hm := mul_pos htpos (sub_pos.2 hlog)
    have := hopt z hzmem
    nlinarith
  -- a free coordinate exists
  obtain ⟨i0, hi0⟩ : ∃ i0, ε / N < x i0 := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ k, x k = ε / N := fun k => le_antisymm (hcon k) (hge k)
    have h1 : ∑ k, x k = N * (ε / N) := by
      rw [Finset.sum_congr rfl (fun k _ => hall k), Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    rw [hsum, mul_div_assoc', mul_div_cancel_left₀ ε hN0.ne'] at h1
    linarith
  obtain ⟨C, hCdef⟩ : ∃ C, C = x i0 / y i0 := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; exact div_pos (hxpos i0) (hy i0)
  have hCle : ∀ k, C ≤ x k / y k := fun k => by rw [hCdef]; exact kkt i0 k hi0
  have hfree : ∀ k, k ∉ S → x k = C * y k := by
    intro k hk
    rw [hSdef, Finset.mem_filter] at hk
    have hne : x k ≠ ε / N := fun h => hk ⟨Finset.mem_univ _, h⟩
    have hlt : ε / N < x k := lt_of_le_of_ne (hge k) (Ne.symm hne)
    have h1 : x k / y k ≤ C := by rw [hCdef]; exact kkt k i0 hlt
    have h2 := hCle k
    have h3 : x k / y k = C := le_antisymm h1 h2
    rw [div_eq_iff (hy k).ne'] at h3
    exact h3
  have hi0S : i0 ∈ Sᶜ := by
    rw [Finset.mem_compl, hSdef, Finset.mem_filter]
    exact fun h => absurd h.2 (ne_of_gt hi0)
  have hpos : 0 < ∑ k ∈ Sᶜ, y k := Finset.sum_pos (fun k _ => hy k) ⟨i0, hi0S⟩
  have hsplit : ∑ k ∈ S, x k + ∑ k ∈ Sᶜ, x k = ∑ k, x k := Finset.sum_add_sum_compl S x
  have hS : ∑ k ∈ S, x k = ε / N * (S.card : ℝ) := by
    have : ∀ k ∈ S, x k = ε / N := by
      intro k hk
      rw [hSdef, Finset.mem_filter] at hk
      exact hk.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hSc : ∑ k ∈ Sᶜ, x k = C * ∑ k ∈ Sᶜ, y k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k hk => hfree k (Finset.mem_compl.1 hk))
  have hC : (1 - ε / N * (S.card : ℝ)) / ∑ j ∈ Sᶜ, y j = C := by
    rw [div_eq_iff hpos.ne']
    linarith
  refine ⟨fun k => Real.log (x k / (y k * C)), ?_, ?_, ?_⟩
  · intro k
    apply Real.log_nonneg
    rw [le_div_iff₀ (mul_pos (hy k) hCpos), one_mul]
    have := (le_div_iff₀ (hy k)).1 (hCle k)
    linarith
  · intro k hk
    show Real.log (x k / (y k * C)) = 0
    rw [hfree k hk, mul_comm (y k) C, div_self (mul_pos hCpos (hy k)).ne', Real.log_one]
  · intro k
    rw [hC]
    show x k = y k * Real.exp (Real.log (x k / (y k * C))) * C
    rw [Real.exp_log (div_pos (hxpos k) (mul_pos (hy k) hCpos))]
    have hyC : y k * C ≠ 0 := (mul_pos (hy k) hCpos).ne'
    calc x k = (y k * C) * (x k / (y k * C)) := by
          rw [mul_div_assoc', mul_div_cancel_left₀ (x k) hyC]
      _ = y k * (x k / (y k * C)) * C := by ring
