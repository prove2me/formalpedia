-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.proposition_5_1_a
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:23:32.887903+00:00
-- url     : https://prove2.me/submissions/4aee0898-eae8-449d-8dec-7b0a346445f1

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting



namespace BeckTeboulleMD.EMDA

lemma h63_logmono : MonotoneOn (fun t : ℝ => Real.log t - 2 * (t - 1) / (t + 1)) (Set.Ioi 0) := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t : ℝ => Real.log t - 2 * (t - 1) / (t + 1))
      (t⁻¹ - 4 / (t + 1) ^ 2) t := by
    intro t ht
    have h1 := Real.hasDerivAt_log ht.ne'
    have h2 : HasDerivAt (fun t : ℝ => 2 * (t - 1)) 2 t := by
      simpa using ((hasDerivAt_id t).sub_const 1).const_mul 2
    have h3 : HasDerivAt (fun t : ℝ => t + 1) 1 t := (hasDerivAt_id t).add_const 1
    have h4 := h2.div h3 (by positivity)
    refine (h1.sub h4).congr_deriv ?_
    field_simp
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
  · intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact (hd t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    have ht' : (0:ℝ) < t := ht
    rw [(hd t ht').deriv]
    have : t⁻¹ - 4 / (t + 1) ^ 2 = (t - 1) ^ 2 / (t * (t + 1) ^ 2) := by
      field_simp
      ring
    rw [this]
    positivity

lemma h63_pt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a = 0 ↔ b = 0) :
    2 * (a - b) ^ 2 / (a + b) ≤ (a - b) * Real.log (a / b) := by
  by_cases h0 : a = 0
  · have : b = 0 := hab.1 h0
    subst h0; subst this; simp
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm h0)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm (fun h => h0 (hab.2 h)))
  have ht : 0 < a / b := div_pos hapos hbpos
  have hm := h63_logmono
  have key : 2 * (a / b - 1) / (a / b + 1) = 2 * (a - b) / (a + b) := by
    field_simp
  have h1 : (fun t : ℝ => Real.log t - 2 * (t - 1) / (t + 1)) 1 = 0 := by simp
  rcases le_or_gt b a with hba | hba
  · have h1t : (1:ℝ) ≤ a / b := by rw [le_div_iff₀ hbpos]; linarith
    have := hm (show (1:ℝ) ∈ Set.Ioi 0 from by norm_num) ht h1t
    simp only [h1, key] at this
    have h5 : 2 * (a - b) / (a + b) ≤ Real.log (a / b) := by linarith
    have h6 : (a - b) * (2 * (a - b) / (a + b)) ≤ (a - b) * Real.log (a / b) :=
      mul_le_mul_of_nonneg_left h5 (by linarith)
    calc 2 * (a - b) ^ 2 / (a + b) = (a - b) * (2 * (a - b) / (a + b)) := by ring
      _ ≤ _ := h6
  · have h1t : a / b ≤ 1 := by rw [div_le_iff₀ hbpos]; linarith
    have := hm ht (show (1:ℝ) ∈ Set.Ioi 0 from by norm_num) h1t
    simp only [h1, key] at this
    have h5 : Real.log (a / b) ≤ 2 * (a - b) / (a + b) := by linarith
    have h6 : (a - b) * (2 * (a - b) / (a + b)) ≤ (a - b) * Real.log (a / b) :=
      mul_le_mul_of_nonpos_left h5 (by linarith)
    calc 2 * (a - b) ^ 2 / (a + b) = (a - b) * (2 * (a - b) / (a + b)) := by ring
      _ ≤ _ := h6

lemma h63_sym {n : ℕ} {x y : Fin n → ℝ} (hx : x ∈ stdSimplex ℝ (Fin n))
    (hy : y ∈ stdSimplex ℝ (Fin n)) (hs : ∀ j, x j = 0 ↔ y j = 0) :
    (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j) := by
  have hx0 := hx.1
  have hy0 := hy.1
  have hxs : ∑ j, x j = 1 := hx.2
  have hys : ∑ j, y j = 1 := hy.2
  have step1 : ∑ j, 2 * (x j - y j) ^ 2 / (x j + y j) ≤ ∑ j, (x j - y j) * Real.log (x j / y j) :=
    Finset.sum_le_sum (fun j _ => h63_pt (hx0 j) (hy0 j) (hs j))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => |x j - y j| / Real.sqrt (x j + y j)) (fun j => Real.sqrt (x j + y j))
  have e1 : ∀ j, |x j - y j| / Real.sqrt (x j + y j) * Real.sqrt (x j + y j) = |x j - y j| := by
    intro j
    by_cases h : x j + y j = 0
    · have h1 : x j = 0 := by linarith [hx0 j, hy0 j]
      have h2 : y j = 0 := by linarith [hx0 j, hy0 j]
      simp [h1, h2]
    · have : Real.sqrt (x j + y j) ≠ 0 := by
        rw [Real.sqrt_ne_zero']; exact lt_of_le_of_ne (add_nonneg (hx0 j) (hy0 j)) (Ne.symm h)
      field_simp
  have e2 : ∀ j, (|x j - y j| / Real.sqrt (x j + y j)) ^ 2 = (x j - y j) ^ 2 / (x j + y j) := by
    intro j
    rw [div_pow, Real.sq_sqrt (add_nonneg (hx0 j) (hy0 j)), sq_abs]
  have e3 : ∀ j, (Real.sqrt (x j + y j)) ^ 2 = x j + y j := fun j =>
    Real.sq_sqrt (add_nonneg (hx0 j) (hy0 j))
  simp only [e1, e2, e3] at hcs
  rw [Finset.sum_add_distrib, hxs, hys] at hcs
  have e4 : ∑ j, 2 * (x j - y j) ^ 2 / (x j + y j) = 2 * ∑ j, (x j - y j) ^ 2 / (x j + y j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  rw [e4] at step1
  nlinarith [hcs]


lemma h63_z_mem {n : ℕ} {x y : Fin n → ℝ} (hx : x ∈ stdSimplex ℝ (Fin n))
    (hy : y ∈ stdSimplex ℝ (Fin n)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (fun j => s * x j + (1 - s) * y j) ∈ stdSimplex ℝ (Fin n) := by
  refine ⟨fun j => ?_, ?_⟩
  · have := hx.1 j; have := hy.1 j
    have : 0 ≤ 1 - s := by linarith
    positivity
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx.2, hy.2]; ring

lemma h63_strong {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (y : Fin n → ℝ) (hy : y ∈ stdSimplex ℝ (Fin n)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2) := by
  have hb' : b = 1 - a := by linarith
  subst hb'
  have ha1 : a ≤ 1 := by linarith
  set c : ℝ := (∑ j, |x j - y j|) ^ 2 with hc
  let z : ℝ → Fin n → ℝ := fun s j => s * x j + (1 - s) * y j
  let h : ℝ → ℝ := fun s => ∑ j, z s j * Real.log (z s j)
  let g : ℝ → ℝ := fun s => h s - 1 / 2 * c * s ^ 2
  let D : ℝ → ℝ := fun s => ∑ j, (x j - y j) * (Real.log (z s j) + 1)
  have hzpos : ∀ s, 0 < s → s < 1 → ∀ j, (z s j = 0 ↔ x j = 0 ∧ y j = 0) := by
    intro s hs0 hs1 j
    have := hx.1 j; have := hy.1 j
    have h1 : 0 < 1 - s := by linarith
    constructor
    · intro h0
      have e : s * x j + (1 - s) * y j = 0 := h0
      constructor
      · by_contra hne
        have : 0 < x j := lt_of_le_of_ne (hx.1 j) (Ne.symm hne)
        have : 0 < s * x j := by positivity
        nlinarith [mul_nonneg h1.le (hy.1 j)]
      · by_contra hne
        have : 0 < y j := lt_of_le_of_ne (hy.1 j) (Ne.symm hne)
        have : 0 < (1 - s) * y j := by positivity
        nlinarith [mul_nonneg hs0.le (hx.1 j)]
    · rintro ⟨h1, h2⟩
      show s * x j + (1 - s) * y j = 0
      rw [h1, h2]; ring
  have hcont : Continuous h := by
    apply continuous_finsetSum
    intro j _
    have : Continuous (z · j) := by fun_prop
    exact Real.continuous_mul_log.comp this
  have hterm : ∀ s ∈ Set.Ioo (0:ℝ) 1, ∀ j : Fin n, HasDerivAt (fun s => z s j * Real.log (z s j))
      ((x j - y j) * (Real.log (z s j) + 1)) s := by
    intro s hs j
    by_cases hj : x j = 0 ∧ y j = 0
    · have hf : (fun s => z s j * Real.log (z s j)) = fun _ => 0 := by
        funext s; simp [z, hj.1, hj.2]
      rw [hf]
      have : (x j - y j) * (Real.log (z s j) + 1) = 0 := by simp [hj.1, hj.2]
      rw [this]
      exact hasDerivAt_const s 0
    · have hne : z s j ≠ 0 := fun h0 => hj ((hzpos s hs.1 hs.2 j).1 h0)
      have h1 : HasDerivAt (fun s => z s j) (x j - y j) s := by
        have h0 := ((hasDerivAt_id s).mul_const (x j)).add (((hasDerivAt_id s).const_sub 1).mul_const (y j))
        have h0' : HasDerivAt (fun s : ℝ => s * x j + (1 - s) * y j) _ s := h0
        refine h0'.congr_deriv ?_
        simp
        ring
      have := (Real.hasDerivAt_mul_log hne).comp s h1
      refine this.congr_deriv ?_
      ring
  have hderiv : ∀ s ∈ Set.Ioo (0:ℝ) 1, HasDerivAt h (D s) s := by
    intro s hs
    have hsum : HasDerivAt (∑ j ∈ (Finset.univ : Finset (Fin n)), fun s => z s j * Real.log (z s j))
        (∑ j ∈ (Finset.univ : Finset (Fin n)), (x j - y j) * (Real.log (z s j) + 1)) s := by
      apply HasDerivAt.sum
      intro j _
      exact hterm s hs j
    have e : h = ∑ j ∈ (Finset.univ : Finset (Fin n)), fun s => z s j * Real.log (z s j) := by
      funext s; simp [h, Finset.sum_apply]
    rw [e]; exact hsum
  have hg_conv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) g := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
    · exact (hcont.sub (by fun_prop)).continuousOn
    · rw [interior_Icc]
      intro s hs
      exact ((hderiv s hs).sub ((hasDerivAt_pow 2 s).const_mul (1 / 2 * c))).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      have hdg : ∀ s ∈ Set.Ioo (0:ℝ) 1, deriv g s = D s - c * s := by
        intro s hs
        have : HasDerivAt g (D s - 1 / 2 * c * ((2:ℕ) * s ^ (2 - 1))) s :=
          (hderiv s hs).sub ((hasDerivAt_pow 2 s).const_mul (1 / 2 * c))
        rw [this.deriv]
        simp only [Nat.cast_ofNat]
        ring
      intro r hr s hs hrs
      rw [hdg r hr, hdg s hs]
      rcases eq_or_lt_of_le hrs with heq | hlt
      · rw [heq]
      · have hzr := h63_z_mem hx hy hr.1.le hr.2.le
        have hzs := h63_z_mem hx hy hs.1.le hs.2.le
        have hsame : ∀ j, (z s j = 0 ↔ z r j = 0) := by
          intro j
          rw [hzpos s hs.1 hs.2 j, hzpos r hr.1 hr.2 j]
        have hP : (∑ j, |z s j - z r j|) ^ 2 ≤ ∑ j, (z s j - z r j) * Real.log (z s j / z r j) :=
          h63_sym hzs hzr hsame
        have hterm : ∀ j, (z s j - z r j) * Real.log (z s j / z r j)
            = (s - r) * ((x j - y j) * (Real.log (z s j) - Real.log (z r j))) := by
          intro j
          by_cases hj : x j = 0 ∧ y j = 0
          · simp [z, hj.1, hj.2]
          · have h1 : z s j ≠ 0 := fun h0 => hj ((hzpos s hs.1 hs.2 j).1 h0)
            have h2 : z r j ≠ 0 := fun h0 => hj ((hzpos r hr.1 hr.2 j).1 h0)
            rw [Real.log_div h1 h2]
            simp only [z]
            ring
        have habs : ∑ j, |z s j - z r j| = (s - r) * ∑ j, |x j - y j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          have : z s j - z r j = (s - r) * (x j - y j) := by simp only [z]; ring
          rw [this, abs_mul, abs_of_pos (sub_pos.2 hlt)]
        simp only [hterm, habs] at hP
        rw [← Finset.mul_sum, mul_pow] at hP
        have hDsr : D s - D r = ∑ j, (x j - y j) * (Real.log (z s j) - Real.log (z r j)) := by
          simp only [D, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro j _; ring
        have hsr : 0 < s - r := sub_pos.2 hlt
        have : c * (s - r) ≤ D s - D r := by
          rw [hDsr]
          have : (s - r) * (c * (s - r)) ≤ (s - r) * ∑ j, (x j - y j) * (Real.log (z s j) - Real.log (z r j)) := by
            nlinarith [hP]
          exact le_of_mul_le_mul_left this hsr
        nlinarith
  have hmem0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hmem1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have key := hg_conv.2 hmem1 hmem0 ha (show 0 ≤ 1 - a by linarith) (by ring)
  simp only [smul_eq_mul, mul_one, mul_zero, add_zero] at key
  have e1 : h 1 = entropy x := by
    simp [h, z, entropy]
  have e0 : h 0 = entropy y := by
    simp [h, z, entropy]
  have ea : h a = entropy (a • x + (1 - a) • y) := by
    simp only [h, z, entropy]
    apply Finset.sum_congr rfl; intro j _
    simp
  simp only [g, e1, e0, ea] at key
  nlinarith [key]


lemma h63_fderiv {n : ℕ} {x : Fin n → ℝ} (hx : ∀ j, 0 < x j) (v : Fin n → ℝ) :
    fderiv ℝ (entropy (n := n)) x v = ∑ j, (Real.log (x j) + 1) * v j := by
  have hd : HasFDerivAt (entropy (n := n))
      (∑ j : Fin n, (Real.log (x j) + 1) • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    have : entropy (n := n) = ∑ j : Fin n, fun x : Fin n → ℝ => x j * Real.log (x j) := by
      funext x; simp [entropy, Finset.sum_apply]
    rw [this]
    apply HasFDerivAt.sum
    intro j _
    have h1 := (Real.hasDerivAt_mul_log (hx j).ne').comp_hasFDerivAt x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j).hasFDerivAt
    exact h1
  rw [hd.fderiv]
  simp

theorem h63_prop_a {n : ℕ} :
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (fderiv ℝ (entropy (n := n)) x - fderiv ℝ (entropy (n := n)) y) (x - y)
        = ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) := by
  have hmem : ∀ x ∈ relIntSimplex n, x ∈ stdSimplex ℝ (Fin n) := fun x hx =>
    ⟨fun j => (hx.1 j).le, hx.2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy
    rw [ContinuousLinearMap.sub_apply, h63_fderiv hx.1, h63_fderiv hy.1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Real.log_div (hx.1 j).ne' (hy.1 j).ne']
    simp only [Pi.sub_apply]
    ring
  · intro x hx y hy
    exact h63_sym (hmem x hx) (hmem y hy) (fun j => ⟨fun h => absurd h (hx.1 j).ne',
      fun h => absurd h (hy.1 j).ne'⟩)
  · intro x hx y hy a b ha hb hab
    exact h63_strong x (hmem x hx) y (hmem y hy) a b ha hb hab

theorem h63_remark {n : ℕ} :
    (∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), (∀ j, x j = 0 ↔ y j = 0) →
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ stdSimplex ℝ (Fin n), ∀ y ∈ stdSimplex ℝ (Fin n), ∀ a b : ℝ,
      0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) :=
  ⟨fun x hx y hy hs => h63_sym hx hy hs, fun x hx y hy a b ha hb hab => h63_strong x hx y hy a b ha hb hab⟩

end BeckTeboulleMD.EMDA

open BeckTeboulleMD.EMDA


theorem solution {n : ℕ} :
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (fderiv ℝ (entropy (n := n)) x - fderiv ℝ (entropy (n := n)) y) (x - y)
        = ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n,
      (∑ j, |x j - y j|) ^ 2 ≤ ∑ j, (x j - y j) * Real.log (x j / y j)) ∧
    (∀ x ∈ relIntSimplex n, ∀ y ∈ relIntSimplex n, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      entropy (a • x + b • y)
        ≤ a * entropy x + b * entropy y - a * b * (1 / 2 * (∑ j, |x j - y j|) ^ 2)) := by
  exact h63_prop_a
