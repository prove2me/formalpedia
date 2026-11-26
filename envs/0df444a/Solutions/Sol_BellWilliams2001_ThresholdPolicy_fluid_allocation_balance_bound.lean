-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.fluid_allocation_balance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:29:14.457896+00:00
-- url     : https://prove2.me/submissions/0f470e86-66cd-42ae-84e8-ea539ae9dddd

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open BellWilliams2001.ThresholdPolicy
open Set

set_option maxHeartbeats 1150000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (T : Allocation Ω) (hT : M.IsAdmissible n T)
      (ω : Ω) (t e : ℝ), 0 ≤ t → 0 ≤ e →
      (∀ k, |M.Abar n ω t k-M.lam k*t| ≤ e) →
      (∀ j, |M.Sbar n ω (M.Tbar n T ω t j) j-M.mu j*M.Tbar n T ω t j| ≤ e) →
      (∀ k, |M.Qbar n T ω t k| ≤ e) →
      (∑ j, |M.Tbar n T ω t j-M.fluidAllocation t j|) + (∑ k, |M.Ibar n T ω t k|) ≤ C*e := by
  let a := (M.lam 0-M.mu 0)/M.mu 1
  let b := M.lam 1/M.mu 2
  have hab : a+b=1 := by dsimp [a,b]; linarith [M.a31_ii]
  have hm0 := M.mu_pos 0
  have hm1 := M.mu_pos 1
  have hm2 := M.mu_pos 2
  let K0 := (4+M.mu 1*(3/M.mu 2))/M.mu 0
  let K1 := 4/M.mu 1+3/M.mu 2
  let K2 := 3/M.mu 2
  have hk0 : 0 < K0 := by dsimp [K0]; positivity
  have hk1 : 0 < K1 := by dsimp [K1]; positivity
  have hk2 : 0 < K2 := by dsimp [K2]; positivity
  refine ⟨2*(K0+K1+K2),by positivity,?_⟩
  intro n T hT ω t e ht he ha hs hq
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  let A := M.Abar n ω t
  let S (j : Fin 3) := M.Sbar n ω (M.Tbar n T ω t j) j
  let U := M.Tbar n T ω t
  let Q := M.Qbar n T ω t
  let I := M.Ibar n T ω t
  have hComp j : R*(T ω j (R*t)/R) = T ω j (R*t) := mul_div_cancel₀ _ hR.ne'
  have hQ0 : Q 0 = A 0-S 0-S 1 := by
    simp only [Q,A,S,U,R,SystemSequence.Qbar,SystemSequence.Abar,SystemSequence.Sbar,SystemSequence.Tbar,
      SystemSequence.queue,if_true,sub_div]
    simp [← show R = M.r n^2 from rfl,hComp]
  have hQ1 : Q 1 = A 1-S 2 := by
    simp only [Q,A,S,U,R,SystemSequence.Qbar,SystemSequence.Abar,SystemSequence.Sbar,SystemSequence.Tbar,
      SystemSequence.queue,show (1:Fin 2) ≠ 0 by decide,if_false,sub_div]
    simp [← show R = M.r n^2 from rfl,hComp]
  have hI0 : I 0 = t-U 0 := by
    simp only [I,U,SystemSequence.Ibar,SystemSequence.Tbar,SystemSequence.idle,if_true,sub_div,
      ← show R = M.r n^2 from rfl, mul_div_cancel_left₀ _ hR.ne']
  have hI1 : I 1 = t-U 1-U 2 := by
    simp only [I,U,SystemSequence.Ibar,SystemSequence.Tbar,SystemSequence.idle,show (1:Fin 2) ≠ 0 by decide,
      if_false,sub_div,← show R = M.r n^2 from rfl,mul_div_cancel_left₀ _ hR.ne']
  have hIN (k : Fin 2) : 0 ≤ I k := by
    have ht' : R*t ∈ Ici (0:ℝ) := mul_nonneg hR.le ht
    have hh := hT.idle_mono ω k (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) ht' ht'
    rw [hT.idle_zero] at hh
    exact div_nonneg hh hR.le
  let d₀ := U 0-t
  let d₁ := U 1-a*t
  let d₂ := U 2-b*t
  have h₀ : d₀ ≤ 0 := by dsimp [d₀]; linarith [hIN 0]
  have h₁ : d₁+d₂ ≤ 0 := by
    have hd : d₁+d₂ = -I 1 := by dsimp [d₁,d₂]; rw [hI1]; linear_combination -t*hab
    rw [hd]
    exact neg_nonpos.mpr (hIN 1)
  have hn₀ (k : Fin 2) : -(e) ≤ A k-M.lam k*t ∧ A k-M.lam k*t ≤ e := abs_le.1 (ha k)
  have hn₁ (j : Fin 3) : -(e) ≤ S j-M.mu j*U j ∧ S j-M.mu j*U j ≤ e := abs_le.1 (hs j)
  have hn₂ (k : Fin 2) : -(e) ≤ Q k ∧ Q k ≤ e := abs_le.1 (hq k)
  have hb' : M.mu 2*b = M.lam 1 := by dsimp [b]; field_simp
  have ha' : M.mu 1*a = M.lam 0-M.mu 0 := by dsimp [a]; field_simp
  have hLinear : -(4*e) ≤ M.mu 0*d₀+M.mu 1*d₁ ∧ M.mu 0*d₀+M.mu 1*d₁ ≤ 4*e := by
    have hh : M.mu 0*d₀+M.mu 1*d₁ = M.mu 0*U 0+M.mu 1*U 1-M.lam 0*t := by
      dsimp [d₀,d₁]
      linear_combination -t*ha'
    rw [hh]
    exact ⟨by linarith [(hn₀ 0).1,(hn₁ 0).2,(hn₁ 1).2,(hn₂ 0).2],
      by linarith [(hn₀ 0).2,(hn₁ 0).1,(hn₁ 1).1,(hn₂ 0).1]⟩
  have hLast : |d₂| ≤ K2*e := by
    have h : M.mu 2*d₂ = M.mu 2*U 2-M.lam 1*t := by dsimp [d₂]; linear_combination -t*hb'
    have hd : -(3*e) ≤ M.mu 2*d₂ ∧ M.mu 2*d₂ ≤ 3*e := by
      rw [h]
      exact ⟨by linarith [(hn₀ 1).1,(hn₁ 2).2,(hn₂ 1).2],
        by linarith [(hn₀ 1).2,(hn₁ 2).1,(hn₂ 1).1]⟩
    have hEq : K2*e*M.mu 2 = 3*e := by dsimp [K2]; field_simp
    apply abs_le.2
    exact ⟨le_of_mul_le_mul_right (by linarith [hd.1,hEq]) hm2,
      le_of_mul_le_mul_right (by linarith [hd.2,hEq]) hm2⟩
  have hMidU : d₁ ≤ K2*e := by linarith [(abs_le.1 hLast).1]
  have hMidL : -(4/M.mu 1 * e) ≤ d₁ := by
    have h0' := mul_nonpos_of_nonneg_of_nonpos hm0.le h₀
    have hEq : (4/M.mu 1)*e*M.mu 1 = 4*e := by field_simp
    exact le_of_mul_le_mul_right (by linarith [hLinear.1,h0',hEq]) hm1
  have hMid : |d₁| ≤ K1*e := by
    have hA : 0 ≤ (4/M.mu 1)*e := by positivity
    have hB : 0 ≤ K2*e := mul_nonneg hk2.le he
    apply abs_le.2
    dsimp only [K1,K2] at *
    constructor <;> linarith only [hMidL,hMidU,hA,hB]
  have hFirst : |d₀| ≤ K0*e := by
    have hB := mul_le_mul_of_nonneg_left hMidU hm1.le
    have hEq : K0*e*M.mu 0 = 4*e+M.mu 1*(K2*e) := by
      dsimp [K0,K2]
      field_simp
      <;> ring
    rw [abs_of_nonpos h₀]
    exact le_of_mul_le_mul_right (by linarith [hLinear.1,hB,hEq]) hm0
  have hI0' : |I 0| ≤ K0*e := by
    have heq : I 0 = -d₀ := by rw [hI0]; dsimp [d₀]; ring
    rw [heq,abs_neg]
    exact hFirst
  have hI1' : |I 1| ≤ (K1+K2)*e := by
    have heq : I 1 = -(d₁+d₂) := by dsimp [d₁,d₂]; rw [hI1]; linear_combination -t*hab
    rw [heq,abs_neg,add_mul]
    exact (abs_add_le _ _).trans (add_le_add hMid hLast)
  rw [Fin.sum_univ_three,Fin.sum_univ_two]
  have hEq0 : M.Tbar n T ω t 0-M.fluidAllocation t 0=d₀ := rfl
  have hEq1 : M.Tbar n T ω t 1-M.fluidAllocation t 1=d₁ := rfl
  have hEq2 : M.Tbar n T ω t 2-M.fluidAllocation t 2=d₂ := rfl
  rw [hEq0,hEq1,hEq2]
  change |d₀|+|d₁|+|d₂|+(|I 0|+|I 1|) ≤ _
  linarith only [hFirst,hMid,hLast,hI0',hI1']
