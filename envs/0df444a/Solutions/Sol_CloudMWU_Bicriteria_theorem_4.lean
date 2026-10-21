-- Prove2me | solution 1 for CloudMWU.Bicriteria.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:26:03.264384+00:00
-- url     : https://prove2.me/submissions/8dfba56c-8cca-47c1-8061-06873c56e926

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Model
import Theorems.Thm_CloudMWU_Bicriteria_lemma_1
import Theorems.Thm_CloudMWU_Bicriteria_lemma_2_strict

open Finset CloudMWU.Bicriteria

theorem cmw_t4_cons (a ℓ : ℕ → ℝ) (u : ℕ) :
    cumWork a ℓ u = cumLoad ℓ u - queue a ℓ u := by
  induction u with
  | zero => simp [cumWork, cumLoad, queue]
  | succ u ih =>
    have hw : work a ℓ u = ℓ u + queue a ℓ u - queue a ℓ (u + 1) := by
      simp only [work, queue]
      rcases le_total (a u) (ℓ u + queue a ℓ u) with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; ring
      · rw [min_eq_right h, max_eq_left (by linarith)]; ring
    unfold cumWork cumLoad at *
    rw [sum_range_succ, sum_range_succ, ih, hw]; ring

theorem cmw_t4_q0 (a ℓ : ℕ → ℝ) (u : ℕ) : 0 ≤ queue a ℓ u := by
  cases u with
  | zero => simp [queue]
  | succ u => simp only [queue]; exact le_max_left _ _

/-- growth of a continuously active user: either it reaches `(1 - εc) β(i)` or it has grown
geometrically at rate `1 + c'`. -/
theorem cmw_t4_growth (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j)
    (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (i : Fin N) (s : ℕ) :
    ∀ n : ℕ, (∀ τ, s ≤ τ → τ < s + n → 0 < runQueue h L τ i) →
      (1 - ε * cLem1 N ε η) * β i ≤ h (s + n) i ∨
        h s i * (1 + cLem2 N ε η) ^ n ≤ h (s + n) i := by
  have hc0 : 0 ≤ cLem1 N ε η := by
    unfold cLem1; have : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  have hc'0 : 0 ≤ cLem2 N ε η := by
    unfold cLem2 lam; have : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    positivity
  have hεc : ε * cLem1 N ε η ≤ 1 := by
    unfold cLem1
    have : (2:ℝ) ≤ N := by exact_mod_cast hN
    rw [mul_div_assoc', div_le_one (by positivity)]
    have h1 : ε * η ≤ 1 := by nlinarith
    have h2 : ε * (ε * η) ≤ 1 := by nlinarith
    linarith
  intro n
  induction n with
  | zero => intro _; right; simp
  | succ n ih =>
    intro hact
    have ih' := ih (fun τ h1 h2 => hact τ h1 (by omega))
    have hτ : 0 < runQueue h L (s + n) i := hact (s + n) (by omega) (by omega)
    have hiA : i ∈ active h L (s + n) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩
    have hl1 := (lemma_1 N hN ε η hε hε' hη hη' β L hL h hrun (s + n)).2
    have e : s + (n + 1) = s + n + 1 := by omega
    rw [e]
    have hβi : 0 ≤ β i := by
      have := hβ i
      have : 0 ≤ Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) := by
        have : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
        positivity
      linarith
    by_cases hb : h (s + n) i < β i
    · have hup := hl1.1 i hiA hb
      have hup2 := lemma_2_strict N hN ε η hε hε' hη hη' β hβ hβsum L hL h hrun (s + n) i hiA hb
      rcases ih' with h1 | h1
      · left; linarith
      · right
        rw [pow_succ]
        have : h s i * (1 + cLem2 N ε η) ^ n * (1 + cLem2 N ε η)
            ≤ h (s + n) i * (1 + cLem2 N ε η) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
        linarith
    · push_neg at hb
      have hdown := hl1.2 i hiA hb
      left
      have : (1 - ε * cLem1 N ε η) * β i ≤ (1 - ε * cLem1 N ε η) * h (s + n) i :=
        mul_le_mul_of_nonneg_left hb (by linarith)
      linarith

set_option maxHeartbeats 1000000 in
theorem solution (N : ℕ) (hN : 2 ≤ N) (ε η : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    (β : Fin N → ℝ) (hβ : ∀ j, Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) < β j)
    (hβsum : ∑ j, β j ≤ 1)
    (L : ℕ → Fin N → ℝ) (hL : ∀ t i, 0 ≤ L t i)
    (h : ℕ → Fin N → ℝ) (hrun : IsAlg1Run ε η β L h) (i : Fin N) (t : ℕ) :
    cumWork (fun _ => (1 - 2 * ε) * β i) (fun τ => L τ i) t
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) (t + ⌈pTilde N ε η⌉₊) ∧
    cumWork (fun _ => (1 - 2 * ε) * β i) (fun τ => L τ i) t - β i * pTilde N ε η
        ≤ cumWork (fun τ => h τ i) (fun τ => L τ i) t := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hεN : 0 < ε / (N : ℝ) := by positivity
  have hsimp : ∀ τ, h τ ∈ truncSimplex N ε := by
    intro τ
    cases τ with
    | zero => exact hrun.1
    | succ τ => exact (hrun.2 τ).2.1
  have hpos : ∀ τ j, 0 ≤ h τ j := fun τ j => le_trans hεN.le ((hsimp τ).2 j)
  have hle1 : ∀ τ j, h τ j ≤ 1 := by
    intro τ j
    have := Finset.single_le_sum (f := h τ) (fun k _ => hpos τ k) (Finset.mem_univ j)
    rw [(hsimp τ).1] at this; exact this
  have hβi : 0 < β i := by
    have := hβ i
    have : 0 ≤ Real.exp (η * (1 + lam N ε)) * ε / (N : ℝ) := by positivity
    linarith
  set a' : ℝ := (1 - 2 * ε) * β i with ha'
  have ha'0 : 0 ≤ a' := by rw [ha']; apply mul_nonneg (by linarith) hβi.le
  set ℓ : ℕ → ℝ := fun τ => L τ i with hℓ
  have hℓ0 : ∀ τ, 0 ≤ ℓ τ := fun τ => hL τ i
  set C : ℕ → ℝ := fun u => cumWork (fun τ => h τ i) ℓ u with hC
  set C' : ℕ → ℝ := fun u => cumWork (fun _ => a') ℓ u with hC'
  set Λ : ℕ → ℝ := fun u => cumLoad ℓ u with hΛ
  have hCle : ∀ u, C u ≤ Λ u := by
    intro u; simp only [hC, hΛ]; rw [cmw_t4_cons]; linarith [cmw_t4_q0 (fun τ => h τ i) ℓ u]
  have hC'le : ∀ u, C' u ≤ Λ u := by
    intro u; simp only [hC', hΛ]; rw [cmw_t4_cons]; linarith [cmw_t4_q0 (fun _ => a') ℓ u]
  have hΛmono : ∀ u v, u ≤ v → Λ u ≤ Λ v := by
    intro u v huv
    simp only [hΛ, cumLoad]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr huv)
      (fun τ _ _ => hℓ0 τ)
  have hwork0 : ∀ τ, 0 ≤ work (fun τ => h τ i) ℓ τ := fun τ =>
    le_min (hpos τ i) (add_nonneg (hℓ0 τ) (cmw_t4_q0 _ _ _))
  have hCmono : ∀ u v, u ≤ v → C u ≤ C v := by
    intro u v huv
    simp only [hC, cumWork]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr huv)
      (fun τ _ _ => hwork0 τ)
  have hw'le : ∀ τ, work (fun _ => a') ℓ τ ≤ a' := fun τ => min_le_left _ _
  have hw'0 : ∀ τ, 0 ≤ work (fun _ => a') ℓ τ := fun τ =>
    le_min ha'0 (add_nonneg (hℓ0 τ) (cmw_t4_q0 _ _ _))
  have hC0 : ∀ u, 0 ≤ C u := fun u => Finset.sum_nonneg (fun τ _ => hwork0 τ)
  -- constants
  set c := cLem1 N ε η with hc
  set c' := cLem2 N ε η with hc'
  have hc'eq : c' = ε ^ 3 * η / (16 * (N : ℝ) ^ 2) := by
    rw [hc']; unfold cLem2 lam; field_simp; ring
  have hc'pos : 0 < c' := by rw [hc'eq]; positivity
  have hc'small : c' ≤ 1 / 100 := by
    rw [hc'eq, div_le_iff₀ (by positivity)]
    have : ε ^ 3 ≤ 1 / 1000 := by
      have := pow_le_pow_left₀ hε.le hε' 3; norm_num at this; linarith
    nlinarith
  have hlog1 : 1 ≤ Real.log ((N : ℝ) / ε) := by
    have h20 : (20 : ℝ) ≤ (N : ℝ) / ε := by
      rw [le_div_iff₀ hε]; nlinarith
    have he : Real.exp 1 ≤ (N : ℝ) / ε := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) he
  have hpT : pTilde N ε η = 2 * Real.log ((N : ℝ) / ε) / c' := by
    rw [hc'eq]; unfold pTilde; field_simp; ring
  set P := ⌈pTilde N ε η⌉₊ with hP
  have hP1 : pTilde N ε η ≤ (P : ℝ) := Nat.le_ceil _
  have hpTpos : 0 < pTilde N ε η := by rw [hpT]; positivity
  have hP2 : (P : ℝ) < pTilde N ε η + 1 := Nat.ceil_lt_add_one hpTpos.le
  have hpTbig : 200 ≤ pTilde N ε η := by
    rw [hpT, le_div_iff₀ hc'pos]; nlinarith
  have hPpos : 1 ≤ P := by
    have : (1 : ℝ) ≤ P := by linarith
    exact_mod_cast this
  -- εc ≤ 2ε
  have hεc : ε * c ≤ 2 * ε := by
    have : c ≤ 2 := by
      rw [hc]; unfold cLem1; rw [div_le_iff₀ (by positivity)]; nlinarith
    nlinarith
  -- key: after P - 1 steps of activity the allocation is at least (1 - 2ε) β(i)
  have hkey : ∀ s, (∀ τ, s ≤ τ → τ < s + (P - 1) → 0 < runQueue h L τ i) →
      a' ≤ h (s + (P - 1)) i := by
    intro s hact
    rcases cmw_t4_growth N hN ε η hε hε' hη hη' β hβ hβsum L hL h hrun i s (P - 1) hact
      with h1 | h1
    · have : a' ≤ (1 - ε * c) * β i := by
        rw [ha']; apply mul_le_mul_of_nonneg_right (by linarith) hβi.le
      linarith
    · exfalso
      -- (ε/N) (1+c')^(P-1) > 1
      have hlog' : c' / (1 + c') ≤ Real.log (1 + c') := by
        have h1' := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 / (1 + c'))
        rw [one_div, Real.log_inv] at h1'
        have : (1 + c')⁻¹ - 1 = -(c' / (1 + c')) := by field_simp; ring
        linarith
      have hn : ((P - 1 : ℕ) : ℝ) ≥ pTilde N ε η - 1 := by
        rw [Nat.cast_sub hPpos]; push_cast; linarith
      have hexpo : Real.log ((N : ℝ) / ε) < ((P - 1 : ℕ) : ℝ) * Real.log (1 + c') := by
        have hlpos : 0 < c' / (1 + c') := by positivity
        have h2 : (pTilde N ε η - 1) * (c' / (1 + c')) ≤ ((P - 1 : ℕ) : ℝ) * Real.log (1 + c') := by
          apply mul_le_mul hn hlog' hlpos.le (by positivity)
        have h3 : Real.log ((N : ℝ) / ε) < (pTilde N ε η - 1) * (c' / (1 + c')) := by
          rw [hpT]
          have e : (2 * Real.log ((N : ℝ) / ε) / c' - 1) * (c' / (1 + c'))
              = (2 * Real.log ((N : ℝ) / ε) - c') / (1 + c') := by field_simp
          rw [e, lt_div_iff₀ (by positivity)]
          nlinarith
        linarith
      have hpow : (N : ℝ) / ε < (1 + c') ^ (P - 1) := by
        rw [← Real.exp_log (by positivity : (0:ℝ) < (N : ℝ) / ε),
          ← Real.exp_log (by positivity : (0:ℝ) < 1 + c'), ← Real.exp_nat_mul]
        exact Real.exp_lt_exp.mpr hexpo
      have hhs : ε / (N : ℝ) ≤ h s i := (hsimp s).2 i
      have : 1 < h s i * (1 + c') ^ (P - 1) := by
        have h4 : ε / (N : ℝ) * ((N : ℝ) / ε) = 1 := by field_simp
        have h5 : ε / (N : ℝ) * ((N : ℝ) / ε) < ε / (N : ℝ) * (1 + c') ^ (P - 1) :=
          mul_lt_mul_of_pos_left hpow hεN
        have h6 : ε / (N : ℝ) * (1 + c') ^ (P - 1) ≤ h s i * (1 + c') ^ (P - 1) :=
          mul_le_mul_of_nonneg_right hhs (by positivity)
        linarith
      linarith [hle1 (s + (P - 1)) i]
  -- part (a) by induction
  have hA : ∀ u, C' u ≤ C (u + P) := by
    intro u
    induction u with
    | zero =>
      simp only [hC', cumWork, Finset.range_zero, Finset.sum_empty]; exact hC0 _
    | succ u ih =>
      by_cases hex : ∃ r', u + 1 ≤ r' ∧ r' ≤ u + 1 + P ∧
          queue (fun τ => h τ i) ℓ r' = 0
      · obtain ⟨r', h1, h2, h3⟩ := hex
        have hCr : C r' = Λ r' := by
          simp only [hC, hΛ]; rw [cmw_t4_cons, h3, sub_zero]
        have := hCmono r' (u + 1 + P) h2
        have := hΛmono (u + 1) r' h1
        have := hC'le (u + 1)
        have e : u + 1 + P = u + 1 + P := rfl
        linarith
      · push_neg at hex
        have hbusy : ∀ r', u + 1 ≤ r' → r' ≤ u + 1 + P → 0 < queue (fun τ => h τ i) ℓ r' :=
          fun r' h1 h2 => lt_of_le_of_ne (cmw_t4_q0 _ _ _) (Ne.symm (hex r' h1 h2))
        -- allocation at time u + P is at least a'
        have hact : ∀ τ, u + 1 ≤ τ → τ < u + 1 + (P - 1) → 0 < runQueue h L τ i := by
          intro τ h1 h2
          exact hbusy τ h1 (by omega)
        have hal := hkey (u + 1) hact
        have e1 : u + 1 + (P - 1) = u + P := by omega
        rw [e1] at hal
        -- work at time u + P equals allocation
        have hq : 0 < queue (fun τ => h τ i) ℓ (u + P + 1) := hbusy _ (by omega) (by omega)
        have hwfull : work (fun τ => h τ i) ℓ (u + P) = h (u + P) i := by
          simp only [queue] at hq
          have : 0 < ℓ (u + P) + queue (fun τ => h τ i) ℓ (u + P) - h (u + P) i := by
            by_contra hcon; push_neg at hcon
            rw [max_eq_left hcon] at hq; exact lt_irrefl _ hq
          unfold work; exact min_eq_left (by linarith)
        have hCs : C (u + 1 + P) = C (u + P) + h (u + P) i := by
          have e2 : u + 1 + P = u + P + 1 := by omega
          simp only [hC]
          rw [e2]; unfold cumWork; rw [Finset.sum_range_succ, hwfull]
        have hC's : C' (u + 1) = C' u + work (fun _ => a') ℓ u := by
          simp only [hC']; unfold cumWork; rw [Finset.sum_range_succ]
        have := hw'le u
        linarith
  refine ⟨hA t, ?_⟩
  -- part (b)
  have hc'ε : c' ≤ ε := by
    rw [hc'eq, div_le_iff₀ (by positivity)]
    have h1 : ε ^ 2 * η ≤ 1 := by nlinarith
    have h2 : ε ^ 3 * η = ε * (ε ^ 2 * η) := by ring
    rw [h2]; apply mul_le_mul_of_nonneg_left _ hε.le
    have h3 : (1:ℝ) ≤ 16 * (N : ℝ) ^ 2 := by nlinarith
    linarith
  have hpTε : 1 ≤ ε * pTilde N ε η := by
    rw [hpT, mul_div_assoc', le_div_iff₀ hc'pos]
    nlinarith
  have hPa : (P : ℝ) * a' ≤ β i * pTilde N ε η := by
    rw [ha']
    have : (P : ℝ) * (1 - 2 * ε) ≤ pTilde N ε η := by
      have h1 : (P : ℝ) * (1 - 2 * ε) ≤ (pTilde N ε η + 1) * (1 - 2 * ε) :=
        mul_le_mul_of_nonneg_right hP2.le (by linarith)
      nlinarith
    nlinarith
  have hC'diff : ∀ u v, u ≤ v → C' v - C' u ≤ ((v : ℝ) - u) * a' := by
    intro u v huv
    simp only [hC', cumWork]
    rw [← Finset.sum_range_add_sum_Ico _ huv]
    have := Finset.sum_le_card_nsmul (Ico u v) (fun τ => work (fun _ => a') ℓ τ) a'
      (fun τ _ => hw'le τ)
    rw [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub huv] at this
    linarith
  by_cases htP : P ≤ t
  · have h1 := hA (t - P)
    have e : t - P + P = t := by omega
    rw [e] at h1
    have h2 := hC'diff (t - P) t (by omega)
    have h3 : ((t : ℝ) - ((t - P : ℕ) : ℝ)) = P := by
      rw [Nat.cast_sub htP]; ring
    rw [h3] at h2
    show C' t - β i * pTilde N ε η ≤ C t
    linarith
  · push_neg at htP
    have h2 := hC'diff 0 t (by omega)
    have h0 : C' 0 = 0 := by simp [hC', cumWork]
    have h3 : ((t : ℝ) - ((0 : ℕ) : ℝ)) * a' ≤ (P : ℝ) * a' := by
      apply mul_le_mul_of_nonneg_right _ ha'0
      have : (t : ℝ) ≤ P := by exact_mod_cast htP.le
      simp; linarith
    show C' t - β i * pTilde N ε η ≤ C t
    linarith [hC0 t]
