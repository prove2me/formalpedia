-- Prove2me | solution 1 for BranchSpectral.base_nonnegative_by_logical_chain
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:22:41.297006+00:00
-- url     : https://prove2.me/submissions/9ca5c504-200f-4e7e-8fcc-23d8d58afb35

import Mathlib
open MeasureTheory Set Filter Topology


namespace BrAux

lemma atom_abs (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)| ≤ Real.exp (t/4) * Real.exp (-g^2*t) := by
  rw [abs_mul, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  calc Real.exp (-(g ^ 2 - e ^ 2) * t) * |Real.cos (2 * e * g * t)|
      ≤ Real.exp (-(g ^ 2 - e ^ 2) * t) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
    _ ≤ Real.exp (t / 4 + -g ^ 2 * t) := by
        rw [mul_one]
        apply Real.exp_le_exp.2
        have : e ^ 2 ≤ 1 / 4 := by
          have h0 : 0 ≤ |e| := abs_nonneg e
          have : |e| ^ 2 ≤ (1/2) ^ 2 := pow_le_pow_left₀ h0 he 2
          rw [sq_abs] at this; linarith
        nlinarith

lemma atom_near (g e t : ℝ) (hg : 0 < g) (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t) := by
  apply mul_nonneg (Real.exp_pos _).le
  have hgt : g * t ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hnear ht.le
    rwa [inv_mul_cancel₀ ht.ne'] at this
  have hgt0 : 0 ≤ g * t := by positivity
  have habs : |2 * e * g * t| ≤ 1 := by
    rw [show 2 * e * g * t = (2 * e) * (g * t) by ring, abs_mul, abs_of_nonneg hgt0, abs_mul]
    have : |(2:ℝ)| * |e| ≤ 1 := by rw [abs_two]; linarith
    calc |2| * |e| * (g * t) ≤ 1 * 1 := by
          apply mul_le_mul this hgt hgt0 (by norm_num)
      _ = 1 := by norm_num
  apply Real.cos_nonneg_of_mem_Icc
  rw [abs_le] at habs
  constructor <;> linarith [Real.pi_gt_three]

/-- generic lower bound: if every term with `gamma j ≤ L` is nonnegative, then the kernel is at least
the anchor term minus `exp(t/4)` times the Gaussian tail beyond `L`. -/
lemma lower (gamma eps : ℕ → ℝ) (gamma_pos : ∀ j, 0 < gamma j) (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (t : ℝ) (ht : 0 < t) (hsum : Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (L : ℝ) (hL : 100 ≤ L)
    (hnn : ∀ j, gamma j ≤ L → 0 ≤ Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) :
    Real.exp (-10000*t) - Real.exp (t/4) * (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by
  classical
  set f : ℕ → ℝ := fun j => Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)) with hf
  set tl : ℕ → ℝ := fun j => if L < gamma j then Real.exp (-(gamma j)^2*t) else 0 with htl
  have htl_s : Summable tl := by
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hsum
    · simp only [htl]; split_ifs <;> positivity
    · simp only [htl]; split_ifs <;> [exact le_rfl; exact (Real.exp_pos _).le]
  have hf_s : Summable f := by
    refine Summable.of_norm_bounded (hsum.mul_left (Real.exp (t/4))) (fun j => ?_)
    rw [Real.norm_eq_abs]; exact atom_abs _ _ t (strip j) ht
  set g : ℕ → ℝ := fun j => (if j = anchor then Real.exp (-10000*t) else 0) - Real.exp (t/4) * tl j with hg
  have hg_s : Summable g := by
    have h1 : Summable (fun j : ℕ => if j = anchor then Real.exp (-10000*t) else 0) :=
      summable_of_ne_finset_zero (s := {anchor}) (fun j hj => by simp at hj; simp [hj])
    exact h1.sub (htl_s.mul_left _)
  have hle : ∀ j, g j ≤ f j := by
    intro j
    simp only [hg, htl, hf]
    by_cases hj : j = anchor
    · subst hj
      have hnL : ¬ L < gamma j := by linarith
      have he0 : eps j = 0 := verified j (by linarith)
      simp only [if_true, hnL, if_false, mul_zero, sub_zero, he0]
      simp only [zero_mul, Real.cos_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, sub_zero]
      apply Real.exp_le_exp.2
      have : gamma j ^ 2 ≤ 10000 := by
        have h0 : gamma j ≤ 100 := anchor_low
        nlinarith [gamma_pos j]
      nlinarith
    · simp only [hj, if_false, zero_sub]
      split_ifs with hL'
      · have := atom_abs (gamma j) (eps j) t (strip j) ht
        rw [abs_le] at this
        linarith [this.1]
      · push Not at hL'
        simpa using hnn j hL'
  have := hg_s.tsum_le_tsum hle hf_s
  calc Real.exp (-10000*t) - Real.exp (t/4) * (∑' j, tl j)
      = ∑' j, g j := by
        rw [hg, Summable.tsum_sub _ (htl_s.mul_left _), tsum_ite_eq, tsum_mul_left]
        exact summable_of_ne_finset_zero (s := {anchor}) (fun j hj => by simp at hj; simp [hj])
    _ ≤ ∑' j, f j := this

lemma small_ratio (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
    (fun (t : ℝ) => ((t⁻¹)^2+t⁻¹)*Real.exp (-t⁻¹+(10000+1/4)*t)) t < 1/2 := by
  simp only
  set s := t⁻¹ with hs
  have hs1 : 10000 ≤ s := by
    rw [hs, le_inv_comm₀ (by norm_num) ht]; linarith
  have hb : (10000+1/4)*t ≤ 2 := by nlinarith
  have he2 : Real.exp ((10000+1/4)*t) ≤ Real.exp 2 := Real.exp_le_exp.2 hb
  have hE2 : Real.exp 2 < 8 := by
    have := Real.exp_one_lt_d9
    rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
  have h3 : s ^ 3 / (Nat.factorial 3) ≤ Real.exp s := Real.pow_div_factorial_le_exp (x := s) (by linarith) 3
  norm_num [Nat.factorial] at h3
  rw [Real.exp_add, Real.exp_neg]
  have hpos : 0 < Real.exp s := Real.exp_pos _
  have hpos2 : 0 < Real.exp ((10000+1/4)*t) := Real.exp_pos _
  rw [show (s ^ 2 + s) * ((Real.exp s)⁻¹ * Real.exp ((10000 + 1 / 4) * t)) =
      (s ^ 2 + s) * Real.exp ((10000 + 1 / 4) * t) / Real.exp s by field_simp]
  rw [div_lt_iff₀ hpos]
  have : (s ^ 2 + s) * Real.exp ((10000 + 1 / 4) * t) ≤ (s ^ 2 + s) * 8 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  nlinarith

lemma large_ratio (t : ℝ) (ht : 1/10000 ≤ t) :
    (fun (t : ℝ) => (1000000+t⁻¹)*Real.exp (-(1000000-10000-1/4)*t)) t < 1/2 := by
  simp only
  have ht0 : 0 < t := by linarith
  have hinv : t⁻¹ ≤ 10000 := by
    rw [inv_le_comm₀ ht0 (by norm_num)]; linarith
  have hx : (98:ℝ) ≤ (1000000-10000-1/4)*t := by nlinarith
  have hexp : Real.exp 98 ≤ Real.exp ((1000000-10000-1/4)*t) := Real.exp_le_exp.2 hx
  have h4 : (98:ℝ) ^ 4 / (Nat.factorial 4) ≤ Real.exp 98 := Real.pow_div_factorial_le_exp (x := 98) (by norm_num) 4
  norm_num [Nat.factorial] at h4
  rw [show -(1000000-10000-1/4)*t = -((1000000-10000-1/4)*t) by ring, Real.exp_neg]
  have hpos : 0 < Real.exp ((1000000-10000-1/4)*t) := Real.exp_pos _
  rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
  nlinarith

lemma large_bound (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (t : ℝ) (ht : 0 < t) :
    Real.exp (-10000*t)*(1-((1000000+(t)⁻¹)*Real.exp (-(1000000-10000-1/4)*(t)))) ≤ (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by
  have hlow := lower gamma eps gamma_pos strip verified anchor anchor_low t ht (gauss_sum t ht) 1000
    (by norm_num) (fun j hj => by
      rw [verified j hj]; simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
      positivity)
  have htail := gauss_tail t ht 1000 (by norm_num)
  have hE : Real.exp (t/4) * ((1000^2 + t⁻¹) * Real.exp (-1000^2*t)) =
      Real.exp (-10000*t) * ((1000000+(t)⁻¹)*Real.exp (-(1000000-10000-1/4)*(t))) := by
    have : Real.exp (t/4) * Real.exp (-1000^2*t) =
        Real.exp (-10000*t) * Real.exp (-(1000000-10000-1/4)*(t)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    calc Real.exp (t/4) * ((1000^2 + t⁻¹) * Real.exp (-1000^2*t))
        = (1000^2 + t⁻¹) * (Real.exp (t/4) * Real.exp (-1000^2*t)) := by ring
      _ = _ := by rw [this]; ring
  have h4 := mul_le_mul_of_nonneg_left htail (Real.exp_pos (t/4)).le
  nlinarith

lemma small_bound (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (t : ℝ) (ht : 0 < t)
    (hc : t ≤ 1/10000) :
    Real.exp (-10000*t)*(1-((((t)⁻¹)^2+(t)⁻¹)*Real.exp (-(t)⁻¹+(10000+1/4)*(t)))) ≤ (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by
  have hinv : 10000 ≤ t⁻¹ := by rw [le_inv_comm₀ (by norm_num) ht]; linarith
  have hlow := lower gamma eps gamma_pos strip verified anchor anchor_low t ht (gauss_sum t ht) t⁻¹
    (by linarith) (fun j hj => by
      by_cases h1 : gamma j ≤ 1000
      · rw [verified j h1]; simp only [mul_zero, zero_mul, Real.cos_zero, mul_one]
        positivity
      · exact atom_near (gamma j) (eps j) t (gamma_pos j) (strip j) ht hj)
  have htail := gauss_tail t ht t⁻¹ (by linarith)
  have hE : Real.exp (t/4) * (((t⁻¹)^2 + t⁻¹) * Real.exp (-(t⁻¹)^2*t)) =
      Real.exp (-10000*t) * ((((t)⁻¹)^2+(t)⁻¹)*Real.exp (-(t)⁻¹+(10000+1/4)*(t))) := by
    have : Real.exp (t/4) * Real.exp (-(t⁻¹)^2*t) =
        Real.exp (-10000*t) * Real.exp (-(t)⁻¹+(10000+1/4)*(t)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; field_simp; ring
    calc Real.exp (t/4) * (((t⁻¹)^2 + t⁻¹) * Real.exp (-(t⁻¹)^2*t))
        = ((t⁻¹)^2 + t⁻¹) * (Real.exp (t/4) * Real.exp (-(t⁻¹)^2*t)) := by ring
      _ = _ := by rw [this]; ring
  have h4 := mul_le_mul_of_nonneg_left htail (Real.exp_pos (t/4)).le
  nlinarith

lemma kernel_lower (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by
  intro t ht
  have hE := Real.exp_pos (-10000*t)
  rcases le_total t (1/10000) with h | h
  · have := small_bound gamma eps gamma_pos strip verified anchor anchor_low gauss_sum gauss_tail t ht h
    have hr := small_ratio t ht h
    simp only at hr
    nlinarith
  · have := large_bound gamma eps gamma_pos strip verified anchor anchor_low gauss_sum gauss_tail t ht
    have hr := large_ratio t h
    simp only at hr
    nlinarith

end BrAux


namespace BrAux
lemma qnonneg (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (Q : ℕ → ℝ → ℝ)
    (representation : ∀ n ≥ 1, ∀ u > 0,
      Q n u = 2^n*u^(2*n-1)*(∫ t in Ioi (0 : ℝ),
        t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))))) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by
  intro n hn u hu
  rw [representation n hn u hu]
  apply mul_nonneg (by positivity)
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht' : 0 < t := Set.mem_Ioi.1 ht
  have := kernel_lower gamma eps gamma_pos strip verified anchor anchor_low gauss_sum gauss_tail t ht'
  apply mul_nonneg (mul_nonneg (pow_nonneg ht'.le _) (Real.exp_pos _).le)
  linarith [Real.exp_pos (-10000*t)]
end BrAux

theorem BranchSpectral.base_nonnegative_by_logical_chain (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (Q : ℕ → ℝ → ℝ)
    (representation : ∀ n ≥ 1, ∀ u > 0,
      Q n u = 2^n*u^(2*n-1)*(∫ t in Ioi (0 : ℝ),
        t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)))))
    (integrable : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)))) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by
  exact BrAux.qnonneg gamma eps gamma_pos strip verified anchor anchor_low gauss_sum gauss_tail Q representation

theorem solution (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (Q : ℕ → ℝ → ℝ)
    (representation : ∀ n ≥ 1, ∀ u > 0,
      Q n u = 2^n*u^(2*n-1)*(∫ t in Ioi (0 : ℝ),
        t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)))))
    (integrable : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)))) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by
  exact BrAux.qnonneg gamma eps gamma_pos strip verified anchor anchor_low gauss_sum gauss_tail Q representation
