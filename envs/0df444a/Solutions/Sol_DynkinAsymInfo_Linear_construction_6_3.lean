-- Prove2me | solution 1 for DynkinAsymInfo.Linear.construction_6_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T10:05:15.403879+00:00
-- url     : https://prove2.me/submissions/84365266-8cbc-4548-adee-b90e6424d778

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal


namespace DynkinEulerAux

lemma exists_const_Ioo {F : ℝ → ℝ} {A B : ℝ}
    (h : ∀ x ∈ Set.Ioo A B, HasDerivAt F 0 x) : ∃ k, ∀ x ∈ Set.Ioo A B, F x = k :=
  isOpen_Ioo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (h x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (h x hx).deriv)

/-- A `C²` solution of an Euler equation `a x² y'' + b x y' + c y = 0` on `(A,B)`, `0<A`,
whose indicial polynomial has two distinct real roots, is a combination of two powers
on `[A,B]`. -/
theorem euler_rep {a b c r1 r2 A B : ℝ} (ha : a ≠ 0) (hA : 0 < A) (hAB : A < B)
    (hr1 : a * r1 * (r1 - 1) + b * r1 + c = 0) (hr2 : a * r2 * (r2 - 1) + b * r2 + c = 0)
    (hne : r1 ≠ r2) (y : ℝ → ℝ) (hC : ContDiffOn ℝ 2 y (Set.Icc A B))
    (hODE : ∀ x ∈ Set.Ioo A B,
      a * x ^ 2 * deriv (deriv y) x + b * x * deriv y x + c * y x = 0) :
    ∃ c1 c2 : ℝ, ∀ x ∈ Set.Icc A B, y x = c1 * x ^ r1 + c2 * x ^ r2 := by
  have hsum : a * (1 - r1 - r2) = b := by
    have h : (r1 - r2) * (a * (r1 + r2) - a + b) = 0 := by linear_combination hr1 - hr2
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  have hprod : a * (r1 * r2) = c := by linear_combination -hr1 - r1 * hsum
  have hCo : ContDiffOn ℝ 2 y (Set.Ioo A B) := hC.mono Set.Ioo_subset_Icc_self
  have hy1 : ∀ x ∈ Set.Ioo A B, HasDerivAt y (deriv y x) x := fun x hx =>
    ((hCo.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hCd : ContDiffOn ℝ 1 (deriv y) (Set.Ioo A B) :=
    hCo.deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hy2 : ∀ x ∈ Set.Ioo A B, HasDerivAt (deriv y) (deriv (deriv y) x) x := fun x hx =>
    ((hCd.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have key : ∀ x ∈ Set.Ioo A B, x ^ 2 * deriv (deriv y) x +
      (1 - r1 - r2) * x * deriv y x + r1 * r2 * y x = 0 := by
    intro x hx
    have h := hODE x hx
    have : a * (x ^ 2 * deriv (deriv y) x + (1 - r1 - r2) * x * deriv y x
        + r1 * r2 * y x) = 0 := by
      rw [← hsum, ← hprod] at h; linear_combination h
    exact (mul_eq_zero.mp this).resolve_left ha
  -- first integral
  obtain ⟨K, hK⟩ : ∃ K, ∀ x ∈ Set.Ioo A B,
      (x * deriv y x - r2 * y x) * x ^ (-r1) = K := by
    apply exists_const_Ioo
    intro x hx
    have hx0 : 0 < x := lt_trans hA hx.1
    have hw : HasDerivAt (fun x => x * deriv y x - r2 * y x)
        (1 * deriv y x + x * deriv (deriv y) x - r2 * deriv y x) x :=
      ((hasDerivAt_id x).mul (hy2 x hx)).sub ((hy1 x hx).const_mul r2)
    have hp : HasDerivAt (fun x : ℝ => x ^ (-r1)) (-r1 * x ^ (-r1 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    refine (hw.mul hp).congr_deriv ?_
    have hxx : x ^ (-r1) = x * x ^ (-r1 - 1) := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    rw [hxx]
    have := key x hx
    linear_combination (x ^ (-r1 - 1)) * this
  obtain ⟨K', hK'⟩ : ∃ K', ∀ x ∈ Set.Ioo A B,
      y x * x ^ (-r2) - K / (r1 - r2) * x ^ (r1 - r2) = K' := by
    apply exists_const_Ioo
    intro x hx
    have hx0 : 0 < x := lt_trans hA hx.1
    have hp : HasDerivAt (fun x : ℝ => x ^ (-r2)) (-r2 * x ^ (-r2 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    have hq : HasDerivAt (fun x : ℝ => x ^ (r1 - r2)) ((r1 - r2) * x ^ (r1 - r2 - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    refine (((hy1 x hx).mul hp).sub (hq.const_mul (K / (r1 - r2)))).congr_deriv ?_
    have hKx := hK x hx
    have hsub : r1 - r2 ≠ 0 := sub_ne_zero.mpr hne
    have e1 : x ^ (-r2) = x * x ^ (-r2 - 1) := by
      rw [Real.rpow_sub_one hx0.ne']; field_simp
    have e2 : x ^ (r1 - r2 - 1) = x ^ r1 * x ^ (-r2 - 1) := by
      rw [← Real.rpow_add hx0]; ring_nf
    have e3 : x ^ (-r1) * x ^ r1 = 1 := by
      rw [← Real.rpow_add hx0]; simp
    have hKr : K * x ^ r1 = x * deriv y x - r2 * y x := by
      rw [← hKx, mul_assoc, e3, mul_one]
    have e5 : K / (r1 - r2) * ((r1 - r2) * (x ^ r1 * x ^ (-r2 - 1))) =
        K * x ^ r1 * x ^ (-r2 - 1) := by
      field_simp
    rw [e2, e1, e5]
    linear_combination (-(x ^ (-r2 - 1))) * hKr
  refine ⟨K / (r1 - r2), K', ?_⟩
  have hIoo : Set.EqOn y (fun x => K / (r1 - r2) * x ^ r1 + K' * x ^ r2) (Set.Ioo A B) := by
    intro x hx
    have hx0 : 0 < x := lt_trans hA hx.1
    have h := hK' x hx
    have e1 : x ^ (-r2) * x ^ r2 = 1 := by rw [← Real.rpow_add hx0]; simp
    have e2 : x ^ (r1 - r2) * x ^ r2 = x ^ r1 := by rw [← Real.rpow_add hx0]; ring_nf
    simp only
    have : y x = (y x * x ^ (-r2)) * x ^ r2 := by rw [mul_assoc, e1, mul_one]
    rw [this, show y x * x ^ (-r2) = K' + K / (r1 - r2) * x ^ (r1 - r2) by linarith]
    rw [add_mul, mul_assoc, e2]; ring
  have hcont2 : ContinuousOn (fun x : ℝ => K / (r1 - r2) * x ^ r1 + K' * x ^ r2)
      (Set.Icc A B) := by
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (lt_of_lt_of_le hA hx.1).ne')
    · apply ContinuousOn.mul continuousOn_const
      exact ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (lt_of_lt_of_le hA hx.1).ne')
  have := hIoo.of_subset_closure hC.continuousOn hcont2 Set.Ioo_subset_Icc_self
    (by rw [closure_Ioo hAB.ne])
  intro x hx
  exact this hx

/-- two-power function and its derivative -/
lemma hasDerivAt_pow2 (c1 c2 r1 r2 x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2)
      (c1 * (r1 * x ^ (r1 - 1)) + c2 * (r2 * x ^ (r2 - 1))) x := by
  have h1 := Real.hasDerivAt_rpow_const (x := x) (p := r1) (Or.inl hx.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := x) (p := r2) (Or.inl hx.ne')
  exact (h1.const_mul c1).add (h2.const_mul c2)

/-- transfer of derivatives from the representation -/
lemma derivWithin_eq_of_rep {y : ℝ → ℝ} {c1 c2 r1 r2 A B : ℝ} (hA : 0 < A) (hAB : A < B)
    (hrep : ∀ x ∈ Set.Icc A B, y x = c1 * x ^ r1 + c2 * x ^ r2) (x : ℝ)
    (hx : x ∈ Set.Icc A B) :
    derivWithin y (Set.Icc A B) x = c1 * (r1 * x ^ (r1 - 1)) + c2 * (r2 * x ^ (r2 - 1)) := by
  have hx0 : 0 < x := lt_of_lt_of_le hA hx.1
  rw [derivWithin_congr (f := fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2)
    (fun z hz => hrep z hz) (hrep x hx)]
  exact (hasDerivAt_pow2 c1 c2 r1 r2 x hx0).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc hAB x hx)

lemma deriv_eq_of_rep {y : ℝ → ℝ} {c1 c2 r1 r2 A B : ℝ} (hA : 0 < A)
    (hrep : ∀ x ∈ Set.Icc A B, y x = c1 * x ^ r1 + c2 * x ^ r2) (x : ℝ)
    (hx : x ∈ Set.Ioo A B) :
    deriv y x = c1 * (r1 * x ^ (r1 - 1)) + c2 * (r2 * x ^ (r2 - 1)) := by
  have hx0 : 0 < x := lt_trans hA hx.1
  have hev : y =ᶠ[nhds x] (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2) := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with z hz using hrep z hz
  rw [hev.deriv_eq]
  exact (hasDerivAt_pow2 c1 c2 r1 r2 x hx0).deriv

end DynkinEulerAux



namespace DynkinEulerAux
open DynkinAsymInfo.Linear

lemma mvt {f f' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) :
    ∃ ξ ∈ Set.Ioo a b, f b - f a = f' ξ * (b - a) := by
  obtain ⟨ξ, hξ, h⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (fun x hx => hd x (Set.Ioo_subset_Icc_self hx))
  refine ⟨ξ, hξ, ?_⟩
  rw [h]; field_simp [sub_ne_zero.mpr hab.ne']

lemma omega_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < signalNoise p := by
  unfold signalNoise
  exact div_pos (by linarith) p.sigma_pos

lemma sigma_omega (p : Params) : p.sigma * signalNoise p = p.mu1 - p.mu0 := by
  unfold signalNoise
  field_simp [p.sigma_pos.ne']

lemma quadA_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < quadA p := by
  unfold quadA
  have := omega_pos p h62
  positivity

lemma discr_gt (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : quadB p ^ 2 < discr p := by
  unfold discr
  have := quadA_pos p h62
  nlinarith [h62.1]

lemma abs_lt_sqrt (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) :
    |quadB p| < Real.sqrt (discr p) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (discr_gt p h62)

lemma beta1_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < beta1 p := by
  unfold beta1
  have h1 := abs_lt_sqrt p h62
  have h2 := quadA_pos p h62
  have h3 := neg_abs_le (quadB p)
  have h4 := le_abs_self (quadB p)
  apply div_pos _ (by linarith)
  linarith

lemma beta1_lt_one (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : beta1 p < 1 := by
  unfold beta1
  have h2 := quadA_pos p h62
  have hs : 0 < 2 * quadA p + quadB p := by
    unfold quadA quadB
    have := omega_pos p h62
    have := p.sigma_pos
    have : 0 < p.sigma * signalNoise p := by positivity
    nlinarith
  have hD : discr p < (2 * quadA p + quadB p) ^ 2 := by
    have hsum : quadA p + quadB p + p.mu0 = p.mu1 := by
      unfold quadA quadB; have := sigma_omega p; linarith
    unfold discr
    nlinarith [h62.2]
  have hsq : Real.sqrt (discr p) < 2 * quadA p + quadB p := by
    rw [Real.sqrt_lt' hs]; exact hD
  rw [div_lt_one (by linarith)]
  linarith

lemma beta2_neg (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : beta2 p < 0 := by
  unfold beta2
  have h1 := abs_lt_sqrt p h62
  have h2 := quadA_pos p h62
  have h3 := neg_abs_le (quadB p)
  apply div_neg_of_neg_of_pos _ (by linarith)
  linarith

/-- both betas are roots of `ω²/2 β(β-1) + σωβ + μ0 = 0`. -/
lemma beta_root (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (β : ℝ)
    (hβ : β = beta1 p ∨ β = beta2 p) :
    signalNoise p ^ 2 / 2 * β * (β - 1) + p.sigma * signalNoise p * β + p.mu0 = 0 := by
  have hqa := quadA_pos p h62
  have hD : 0 ≤ discr p := le_trans (sq_nonneg _) (discr_gt p h62).le
  have hs : Real.sqrt (discr p) ^ 2 = quadB p ^ 2 - 4 * quadA p * p.mu0 := by
    rw [Real.sq_sqrt hD]; rfl
  have hq : quadA p * β ^ 2 + quadB p * β + p.mu0 = 0 := by
    rcases hβ with rfl | rfl
    · unfold beta1
      field_simp
      linear_combination hs
    · unfold beta2
      field_simp
      linear_combination hs
  unfold quadA quadB at hq
  linear_combination hq

end DynkinEulerAux

namespace DynkinEulerAux
open DynkinAsymInfo.Linear

/-- Core of Lemma 6.7 / Corollary 6.8. -/
theorem core67 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) (A B : ℝ) (hAB : 0 < A ∧ A < B)
    (v : ℝ → ℝ) (hC2 : ContDiffOn ℝ 2 v (Set.Icc A B))
    (hODE : ∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv v) phi +
      p.sigma * signalNoise p * phi * deriv v phi + p.mu0 * v phi = 0)
    (hleft : ∀ phi, 0 < phi → phi ≤ A → v phi = 1 + phi)
    (hA : derivWithin v (Set.Icc A B) A = 1)
    (hB : derivWithin v (Set.Icc A B) B = 1 + eps) :
    (∀ phi ∈ Set.Ioo A B, 1 + phi < v phi ∧ 1 < deriv v phi) ∧
    A ≤ -p.mu0 / p.mu1 := by
  obtain ⟨hA0, hAB⟩ := hAB
  set b1 := beta1 p with hb1def
  set b2 := beta2 p with hb2def
  have hb1 : 0 < b1 := beta1_pos p h62
  have hb1' : b1 < 1 := beta1_lt_one p h62
  have hb2 : b2 < 0 := beta2_neg p h62
  have hw := omega_pos p h62
  have hr1 := beta_root p h62 b1 (Or.inl rfl)
  have hr2 := beta_root p h62 b2 (Or.inr rfl)
  obtain ⟨D1, D2, hrep⟩ := euler_rep (a := signalNoise p ^ 2 / 2) (b := p.sigma * signalNoise p)
    (c := p.mu0) (r1 := b1) (r2 := b2) (by positivity) hA0 hAB
    (by linear_combination hr1) (by linear_combination hr2) (by linarith) v hC2
    (fun x hx => by linear_combination hODE x hx)
  have hAI : A ∈ Set.Icc A B := ⟨le_rfl, hAB.le⟩
  have hBI : B ∈ Set.Icc A B := ⟨hAB.le, le_rfl⟩
  set F : ℝ → ℝ := fun x => D1 * x ^ b1 + D2 * x ^ b2 with hF
  set f : ℝ → ℝ := fun x => D1 * b1 * x ^ (b1 - 1) + D2 * b2 * x ^ (b2 - 1) with hf
  set k : ℝ → ℝ := fun x => D1 * b1 * (b1 - 1) * x ^ (b1 - b2) + D2 * b2 * (b2 - 1) with hk
  have hFd : ∀ x, 0 < x → HasDerivAt F (f x) x := by
    intro x hx
    refine (hasDerivAt_pow2 D1 D2 b1 b2 x hx).congr_deriv ?_
    simp only [hf]; ring
  have hfd : ∀ x, 0 < x → HasDerivAt f (x ^ (b2 - 1 - 1) * k x) x := by
    intro x hx
    refine (hasDerivAt_pow2 (D1 * b1) (D2 * b2) (b1 - 1) (b2 - 1) x hx).congr_deriv ?_
    have e : x ^ (b1 - 1 - 1) = x ^ (b1 - b2) * x ^ (b2 - 1 - 1) := by
      rw [← Real.rpow_add hx]; ring_nf
    simp only [hk]; rw [e]; ring
  have hFA : F A = 1 + A := by show D1 * A ^ b1 + D2 * A ^ b2 = 1 + A; rw [← hrep A hAI]; exact hleft A hA0 le_rfl
  have hfA : f A = 1 := by
    rw [← hA, derivWithin_eq_of_rep hA0 hAB hrep A hAI]; simp only [hf]; ring
  have hfB : f B = 1 + eps := by
    rw [← hB, derivWithin_eq_of_rep hA0 hAB hrep B hBI]; simp only [hf]; ring
  -- D1 > 0
  have hD1 : 0 < D1 := by
    have hApos : 0 < A ^ b1 := Real.rpow_pos_of_pos hA0 _
    have e1 : A ^ (b1 - 1) = A ^ b1 / A := Real.rpow_sub_one hA0.ne' _
    have e2 : A ^ (b2 - 1) = A ^ b2 / A := Real.rpow_sub_one hA0.ne' _
    have h1 : D1 * A ^ b1 + D2 * A ^ b2 = 1 + A := hFA
    have h2 : b1 * (D1 * A ^ b1) + b2 * (D2 * A ^ b2) = A := by
      have := hfA; simp only [hf] at this; rw [e1, e2] at this
      field_simp at this; linear_combination this
    have h3 : (b1 - b2) * (D1 * A ^ b1) = A - b2 * (1 + A) := by
      linear_combination h2 - b2 * h1
    have h4 : 0 < D1 * A ^ b1 := by
      have : 0 < (b1 - b2) * (D1 * A ^ b1) := by rw [h3]; nlinarith
      exact pos_of_mul_pos_right this (by linarith)
    exact pos_of_mul_pos_left h4 hApos.le
  have hk_anti : ∀ x y, 0 < x → x < y → k y < k x := by
    intro x y hx hxy
    simp only [hk]
    have : x ^ (b1 - b2) < y ^ (b1 - b2) := Real.rpow_lt_rpow hx.le hxy (by linarith)
    have hc : D1 * b1 * (b1 - 1) < 0 := by
      have : 0 < D1 * b1 := mul_pos hD1 hb1
      nlinarith
    nlinarith
  have hpowpos : ∀ x : ℝ, 0 < x → 0 < x ^ (b2 - 1 - 1) := fun x hx => Real.rpow_pos_of_pos hx _
  -- f > 1 inside
  have hv : ∀ x ∈ Set.Ioo A B, 1 < f x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    obtain ⟨ξ1, hξ1, h1⟩ := mvt (f := f) hx.1
      (fun t ht => hfd t (lt_of_lt_of_le hA0 ht.1))
    obtain ⟨ξ2, hξ2, h2⟩ := mvt (f := f) hx.2
      (fun t ht => hfd t (lt_of_lt_of_le (lt_trans hA0 hx.1) ht.1))
    have hξ1pos : 0 < ξ1 := lt_trans hA0 hξ1.1
    have hξ2pos : 0 < ξ2 := lt_trans (lt_trans hA0 hx.1) hξ2.1
    have hk1 : k ξ1 ≤ 0 := by
      have : ξ1 ^ (b2 - 1 - 1) * k ξ1 * (x - A) ≤ 0 := by rw [← h1, hfA]; linarith
      have hxA : 0 < x - A := by linarith [hx.1]
      by_contra hh; push Not at hh
      have := mul_pos (mul_pos (hpowpos ξ1 hξ1pos) hh) hxA
      linarith
    have hk2 : 0 < k ξ2 := by
      have hBx : 0 < B - x := by linarith [hx.2]
      have : 0 < ξ2 ^ (b2 - 1 - 1) * k ξ2 * (B - x) := by rw [← h2, hfB]; linarith
      have := pos_of_mul_pos_left this hBx.le
      exact pos_of_mul_pos_right this (hpowpos ξ2 hξ2pos).le
    have := hk_anti ξ1 ξ2 hξ1pos (lt_trans hξ1.2 hξ2.1)
    linarith
  refine ⟨?_, ?_⟩
  · intro x hx
    have hx0 : 0 < x := lt_trans hA0 hx.1
    refine ⟨?_, ?_⟩
    · rw [hrep x (Set.Ioo_subset_Icc_self hx)]
      obtain ⟨ξ, hξ, h⟩ := mvt (f := F) hx.1
        (fun t ht => hFd t (lt_of_lt_of_le hA0 ht.1))
      have hξI : ξ ∈ Set.Ioo A B := ⟨hξ.1, lt_trans hξ.2 hx.2⟩
      have := hv ξ hξI
      have hxA : 0 < x - A := by linarith [hx.1]
      have : x - A < f ξ * (x - A) := by nlinarith
      show 1 + x < F x
      linarith
    · rw [deriv_eq_of_rep hA0 hrep x hx]
      have := hv x hx
      simp only [hf] at this
      linarith
  · -- Corollary 6.8
    have hkA : 0 ≤ k A := by
      by_contra hcon
      push Not at hcon
      obtain ⟨ξ, hξ, h⟩ := mvt (f := f) hAB
        (fun t ht => hfd t (lt_of_lt_of_le hA0 ht.1))
      have hξpos : 0 < ξ := lt_trans hA0 hξ.1
      have hkξ : k ξ < 0 := lt_trans (hk_anti A ξ hA0 hξ.1) hcon
      have : ξ ^ (b2 - 1 - 1) * k ξ * (B - A) < 0 := by
        have := mul_neg_of_pos_of_neg (hpowpos ξ hξpos) hkξ
        exact mul_neg_of_neg_of_pos this (by linarith)
      rw [← h, hfB, hfA] at this
      linarith
    have hf'A : 0 ≤ A ^ (b2 - 1 - 1) * k A := mul_nonneg (hpowpos A hA0).le hkA
    -- ODE identity at A
    have hid : signalNoise p ^ 2 / 2 * A ^ 2 * (A ^ (b2 - 1 - 1) * k A) +
        p.sigma * signalNoise p * A * f A + p.mu0 * F A = 0 := by
      have e1 : A ^ 2 * A ^ (b2 - 1 - 1) = A ^ b2 := by
        rw [show A ^ 2 = A ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hA0]; ring_nf
      have e2 : A ^ (b1 - b2) * A ^ b2 = A ^ b1 := by
        rw [← Real.rpow_add hA0]; ring_nf
      have e3 : A * A ^ (b1 - 1) = A ^ b1 := by
        rw [Real.rpow_sub_one hA0.ne']; field_simp
      have e4 : A * A ^ (b2 - 1) = A ^ b2 := by
        rw [Real.rpow_sub_one hA0.ne']; field_simp
      simp only [hk, hf, hF]
      have : signalNoise p ^ 2 / 2 * A ^ 2 * (A ^ (b2 - 1 - 1) *
          (D1 * b1 * (b1 - 1) * A ^ (b1 - b2) + D2 * b2 * (b2 - 1))) +
          p.sigma * signalNoise p * A * (D1 * b1 * A ^ (b1 - 1) + D2 * b2 * A ^ (b2 - 1)) +
          p.mu0 * (D1 * A ^ b1 + D2 * A ^ b2) =
          signalNoise p ^ 2 / 2 * (D1 * b1 * (b1 - 1)) * ((A ^ 2 * A ^ (b2 - 1 - 1)) * A ^ (b1 - b2))
          + signalNoise p ^ 2 / 2 * (D2 * b2 * (b2 - 1)) * (A ^ 2 * A ^ (b2 - 1 - 1))
          + p.sigma * signalNoise p * (D1 * b1) * (A * A ^ (b1 - 1))
          + p.sigma * signalNoise p * (D2 * b2) * (A * A ^ (b2 - 1))
          + p.mu0 * (D1 * A ^ b1 + D2 * A ^ b2) := by ring
      rw [this, e1, mul_comm (A ^ b2) (A ^ (b1 - b2)), e2, e3, e4]
      linear_combination D1 * A ^ b1 * hr1 + D2 * A ^ b2 * hr2
    rw [hfA, hFA] at hid
    have hso := sigma_omega p
    have h0 : 0 ≤ signalNoise p ^ 2 / 2 * A ^ 2 * (A ^ (b2 - 1 - 1) * k A) := by positivity
    rw [le_div_iff₀ h62.2]
    rw [hso] at hid
    nlinarith

end DynkinEulerAux

namespace DynkinEulerAux
open DynkinAsymInfo.Linear

theorem core66 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) (A B : ℝ) (hAB : 0 < A ∧ A < B)
    (v1 : ℝ → ℝ) (hC2 : ContDiffOn ℝ 2 v1 (Set.Icc A B))
    (hODE : ∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv v1) phi +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * phi * deriv v1 phi +
      p.mu1 * v1 phi = 0)
    (hleft : ∀ phi, 0 < phi → phi ≤ A → v1 phi = 1)
    (hright : ∀ phi, B ≤ phi → v1 phi = 1 + eps)
    (hB : derivWithin v1 (Set.Icc A B) B = 0) :
    (∀ phi ∈ Set.Icc A B, 0 ≤ derivWithin v1 (Set.Icc A B) phi) ∧
    (∀ phi ∈ Set.Icc A B, 1 ≤ v1 phi) ∧
    (∀ phi ∈ Set.Ico A B, v1 phi < 1 + eps) := by
  obtain ⟨hA0, hAB⟩ := hAB
  set r1 := beta1 p - 1 with hr1def
  set r2 := beta2 p - 1 with hr2def
  have hb1 : 0 < beta1 p := beta1_pos p h62
  have hb2 : beta2 p < 0 := beta2_neg p h62
  have hw := omega_pos p h62
  have hso := sigma_omega p
  have hr1 : signalNoise p ^ 2 / 2 * r1 * (r1 - 1) +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * r1 + p.mu1 = 0 := by
    have := beta_root p h62 (beta1 p) (Or.inl rfl)
    rw [hr1def]; linear_combination this - hso
  have hr2 : signalNoise p ^ 2 / 2 * r2 * (r2 - 1) +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * r2 + p.mu1 = 0 := by
    have := beta_root p h62 (beta2 p) (Or.inr rfl)
    rw [hr2def]; linear_combination this - hso
  obtain ⟨C1, C2, hrep⟩ := euler_rep (a := signalNoise p ^ 2 / 2)
    (b := signalNoise p ^ 2 + p.sigma * signalNoise p)
    (c := p.mu1) (r1 := r1) (r2 := r2) (by positivity) hA0 hAB
    hr1 hr2 (by rw [hr1def, hr2def]; intro h; linarith) v1 hC2
    (fun x hx => by linear_combination hODE x hx)
  have hAI : A ∈ Set.Icc A B := ⟨le_rfl, hAB.le⟩
  have hBI : B ∈ Set.Icc A B := ⟨hAB.le, le_rfl⟩
  set F : ℝ → ℝ := fun x => C1 * x ^ r1 + C2 * x ^ r2 with hF
  set f : ℝ → ℝ := fun x => C1 * (r1 * x ^ (r1 - 1)) + C2 * (r2 * x ^ (r2 - 1)) with hf
  set k : ℝ → ℝ := fun x => C1 * r1 * x ^ (r1 - r2) + C2 * r2 with hk
  have hFd : ∀ x, 0 < x → HasDerivAt F (f x) x := fun x hx => hasDerivAt_pow2 C1 C2 r1 r2 x hx
  have hfk : ∀ x : ℝ, 0 < x → f x = x ^ (r2 - 1) * k x := by
    intro x hx
    have e : x ^ (r1 - 1) = x ^ (r1 - r2) * x ^ (r2 - 1) := by
      rw [← Real.rpow_add hx]; ring_nf
    simp only [hf, hk]; rw [e]; ring
  have hFA : F A = 1 := by show C1 * A ^ r1 + C2 * A ^ r2 = 1; rw [← hrep A hAI]; exact hleft A hA0 le_rfl
  have hFB : F B = 1 + eps := by
    show C1 * B ^ r1 + C2 * B ^ r2 = 1 + eps; rw [← hrep B hBI]; exact hright B le_rfl
  have hdw : ∀ x ∈ Set.Icc A B, derivWithin v1 (Set.Icc A B) x = f x :=
    fun x hx => derivWithin_eq_of_rep hA0 hAB hrep x hx
  have hfB : f B = 0 := by rw [← hdw B hBI]; exact hB
  have hB0 : 0 < B := lt_trans hA0 hAB
  have hkB : k B = 0 := by
    have := hfk B hB0
    rw [hfB] at this
    have hp : 0 < B ^ (r2 - 1) := Real.rpow_pos_of_pos hB0 _
    rcases mul_eq_zero.mp this.symm with h | h
    · linarith
    · exact h
  have hgap : 0 < r1 - r2 := by rw [hr1def, hr2def]; linarith
  have hfpos : ∀ x ∈ Set.Ico A B, 0 < f x := by
    rcases lt_or_ge (C1 * r1) 0 with hc | hc
    · intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hA0 hx.1
      have hlt : x ^ (r1 - r2) < B ^ (r1 - r2) := Real.rpow_lt_rpow hx0.le hx.2 hgap
      have : 0 < k x := by
        have : k B < k x := by simp only [hk]; nlinarith
        linarith
      rw [hfk x hx0]
      exact mul_pos (Real.rpow_pos_of_pos hx0 _) this
    · exfalso
      have hfle : ∀ x ∈ Set.Icc A B, f x ≤ 0 := by
        intro x hx
        have hx0 : 0 < x := lt_of_lt_of_le hA0 hx.1
        have hle : x ^ (r1 - r2) ≤ B ^ (r1 - r2) := Real.rpow_le_rpow hx0.le hx.2 hgap.le
        have : k x ≤ k B := by simp only [hk]; nlinarith
        rw [hfk x hx0]
        exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_pos_of_pos hx0 _).le (by linarith)
      obtain ⟨ξ, hξ, h⟩ := mvt (f := F) hAB (fun t ht => hFd t (lt_of_lt_of_le hA0 ht.1))
      have := hfle ξ (Set.Ioo_subset_Icc_self hξ)
      rw [hFA, hFB] at h
      have : f ξ * (B - A) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg this (by linarith)
      linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hdw x hx]
    rcases eq_or_lt_of_le hx.2 with h | h
    · rw [h, hfB]
    · exact (hfpos x ⟨hx.1, h⟩).le
  · intro x hx
    rw [hrep x hx]
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; exact hFA.ge
    · obtain ⟨ξ, hξ, hm⟩ := mvt (f := F) h (fun t ht => hFd t (lt_of_lt_of_le hA0 ht.1))
      have := hfpos ξ ⟨hξ.1.le, lt_of_lt_of_le hξ.2 hx.2⟩
      have : 0 < f ξ * (x - A) := mul_pos this (by linarith)
      show 1 ≤ F x
      linarith
  · intro x hx
    rw [hrep x ⟨hx.1, hx.2.le⟩]
    have hx0 : 0 < x := lt_of_lt_of_le hA0 hx.1
    obtain ⟨ξ, hξ, hm⟩ := mvt (f := F) hx.2 (fun t ht => hFd t (lt_of_lt_of_le hx0 ht.1))
    have := hfpos ξ ⟨le_trans hx.1 hξ.1.le, hξ.2⟩
    have : 0 < f ξ * (B - x) := mul_pos this (by linarith [hx.2])
    show F x < 1 + eps
    linarith

end DynkinEulerAux



namespace DynkinAsymInfo.Linear.L69

open DynkinAsymInfo.Linear

lemma omega_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < signalNoise p := by
  unfold signalNoise
  exact div_pos (by linarith) p.sigma_pos

lemma sigma_omega (p : Params) : p.sigma * signalNoise p = p.mu1 - p.mu0 := by
  unfold signalNoise
  field_simp [p.sigma_pos.ne']

lemma quadA_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < quadA p := by
  unfold quadA
  have := omega_pos p h62
  positivity

lemma discr_gt (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : quadB p ^ 2 < discr p := by
  unfold discr
  have := quadA_pos p h62
  nlinarith [h62.1]

lemma abs_lt_sqrt (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) :
    |quadB p| < Real.sqrt (discr p) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (discr_gt p h62)

lemma beta1_pos (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : 0 < beta1 p := by
  unfold beta1
  have h1 := abs_lt_sqrt p h62
  have h2 := quadA_pos p h62
  have h3 := neg_abs_le (quadB p)
  have h4 := le_abs_self (quadB p)
  apply div_pos _ (by linarith)
  linarith

lemma beta1_lt_one (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : beta1 p < 1 := by
  unfold beta1
  have h2 := quadA_pos p h62
  have hs : 0 < 2 * quadA p + quadB p := by
    unfold quadA quadB
    have := omega_pos p h62
    have := p.sigma_pos
    have : 0 < p.sigma * signalNoise p := by positivity
    nlinarith
  have hD : discr p < (2 * quadA p + quadB p) ^ 2 := by
    have hsum : quadA p + quadB p + p.mu0 = p.mu1 := by
      unfold quadA quadB; have := sigma_omega p; linarith
    unfold discr
    nlinarith [h62.2]
  have hsq : Real.sqrt (discr p) < 2 * quadA p + quadB p := by
    rw [Real.sqrt_lt' hs]; exact hD
  rw [div_lt_one (by linarith)]
  linarith

lemma beta2_neg (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) : beta2 p < 0 := by
  unfold beta2
  have h1 := abs_lt_sqrt p h62
  have h2 := quadA_pos p h62
  have h3 := neg_abs_le (quadB p)
  apply div_neg_of_neg_of_pos _ (by linarith)
  linarith

/-- the derivative of `rootEq` -/
lemma hasDerivAt_rootEq (p : Params) (eps z : ℝ) (hz : 0 < z) :
    HasDerivAt (fun z => rootEq p eps z)
      ((1 - beta2 p) * ((beta1 p - 1) * z ^ (beta1 p - 1 - 1)) +
        (beta1 p - 1) * ((beta2 p - 1) * z ^ (beta2 p - 1 - 1))) z := by
  unfold rootEq
  have h1 := Real.hasDerivAt_rpow_const (x := z) (p := beta1 p - 1) (Or.inl hz.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := z) (p := beta2 p - 1) (Or.inl hz.ne')
  have := ((h1.const_mul (1 - beta2 p)).add (h2.const_mul (beta1 p - 1))).sub_const
    ((beta1 p - beta2 p) / (1 + eps))
  exact this

lemma rootEq_strictMonoOn (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) :
    StrictMonoOn (fun z => rootEq p eps z) (Set.Ioc 0 1) := by
  have hb1 := beta1_lt_one p h62
  have hb1p := beta1_pos p h62
  have hb2 := beta2_neg p h62
  apply strictMonoOn_of_deriv_pos (convex_Ioc 0 1)
  · intro z hz
    exact (hasDerivAt_rootEq p eps z hz.1).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioc] at hz
    rw [(hasDerivAt_rootEq p eps z hz.1).deriv]
    have hlt : z ^ (beta1 p - 1 - 1) < z ^ (beta2 p - 1 - 1) :=
      Real.rpow_lt_rpow_of_exponent_gt hz.1 hz.2 (by linarith)
    have hneg : (1 - beta2 p) * (beta1 p - 1) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (by linarith)
    have : (1 - beta2 p) * ((beta1 p - 1) * z ^ (beta1 p - 1 - 1)) +
        (beta1 p - 1) * ((beta2 p - 1) * z ^ (beta2 p - 1 - 1)) =
        ((1 - beta2 p) * (beta1 p - 1)) * (z ^ (beta1 p - 1 - 1) - z ^ (beta2 p - 1 - 1)) := by
      ring
    rw [this]
    exact mul_pos_of_neg_of_neg hneg (by linarith)

lemma rootEq_one (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) (heps : 0 < eps) :
    0 < rootEq p eps 1 := by
  unfold rootEq
  simp only [Real.one_rpow]
  have hb1 := beta1_pos p h62
  have hb2 := beta2_neg p h62
  have hd : 0 < beta1 p - beta2 p := by linarith
  have : (beta1 p - beta2 p) / (1 + eps) < beta1 p - beta2 p := by
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  linarith

lemma exists_neg (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) (heps : 0 < eps) :
    ∃ z ∈ Set.Ioo (0 : ℝ) 1, rootEq p eps z < 0 := by
  have hb1 := beta1_pos p h62
  have hb1' := beta1_lt_one p h62
  have hb2 := beta2_neg p h62
  set e := beta1 p - beta2 p with he
  have hepos : 0 < e := by linarith
  set c := (1 - beta1 p) / (2 * (1 - beta2 p)) with hc
  have hcpos : 0 < c := div_pos (by linarith) (by linarith)
  have hclt : c < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine ⟨c ^ e⁻¹, ⟨Real.rpow_pos_of_pos hcpos _, ?_⟩, ?_⟩
  · exact Real.rpow_lt_one hcpos.le hclt (inv_pos.mpr hepos)
  · set z := c ^ e⁻¹ with hz
    have hzpos : 0 < z := Real.rpow_pos_of_pos hcpos _
    have hze : z ^ e = c := Real.rpow_inv_rpow hcpos.le hepos.ne'
    have hsplit : z ^ (beta1 p - 1) = z ^ e * z ^ (beta2 p - 1) := by
      rw [← Real.rpow_add hzpos]; congr 1; rw [he]; ring
    unfold rootEq
    rw [hsplit, hze]
    have hzq : 0 < z ^ (beta2 p - 1) := Real.rpow_pos_of_pos hzpos _
    have hcc : (1 - beta2 p) * c = (1 - beta1 p) / 2 := by
      have : (1 - beta2 p) ≠ 0 := by linarith
      rw [hc]; field_simp
    have hdiv : 0 < (beta1 p - beta2 p) / (1 + eps) := div_pos (by linarith) (by linarith)
    have : (1 - beta2 p) * (c * z ^ (beta2 p - 1)) + (beta1 p - 1) * z ^ (beta2 p - 1) =
        ((1 - beta2 p) * c + (beta1 p - 1)) * z ^ (beta2 p - 1) := by ring
    rw [this, hcc]
    have : ((1 - beta1 p) / 2 + (beta1 p - 1)) * z ^ (beta2 p - 1) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hzq
    linarith

end DynkinAsymInfo.Linear.L69

open DynkinAsymInfo.Linear in
theorem lemma69_main (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) :
    beta1 p ∈ Set.Ioo 0 1 ∧ beta2 p < 0 ∧
      ∃! z : ℝ, z ∈ Set.Ioo 0 1 ∧ rootEq p eps z = 0 := by
  refine ⟨⟨L69.beta1_pos p h62, L69.beta1_lt_one p h62⟩, L69.beta2_neg p h62, ?_⟩
  obtain ⟨z0, hz0, hneg⟩ := L69.exists_neg p h62 eps heps
  have hcont : ContinuousOn (fun z => rootEq p eps z) (Set.Icc z0 1) := by
    intro z hz
    exact (L69.hasDerivAt_rootEq p eps z (lt_of_lt_of_le hz0.1 hz.1)).continuousAt.continuousWithinAt
  have hmem : (0 : ℝ) ∈ Set.Icc (rootEq p eps z0) (rootEq p eps 1) :=
    ⟨hneg.le, (L69.rootEq_one p h62 eps heps).le⟩
  obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc hz0.2.le hcont hmem
  have hr1 : r ≠ 1 := by
    rintro rfl; have := L69.rootEq_one p h62 eps heps; simp only at hr0; linarith
  refine ⟨r, ⟨⟨lt_of_lt_of_le hz0.1 hr.1, lt_of_le_of_ne hr.2 hr1⟩, hr0⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  have hmono := L69.rootEq_strictMonoOn p h62 eps
  have hrI : r ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_lt_of_le hz0.1 hr.1, hr.2⟩
  have hyI : y ∈ Set.Ioc (0 : ℝ) 1 := ⟨hy.1, hy.2.le⟩
  exact hmono.injOn hyI hrI (by simp only at hr0 ⊢; rw [hy0, hr0])



namespace DynkinEulerAux
open DynkinAsymInfo.Linear

lemma deriv2_pow2 (c1 c2 r1 r2 x : ℝ) (hx : 0 < x) :
    deriv (deriv (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2)) x =
      c1 * (r1 * ((r1 - 1) * x ^ (r1 - 1 - 1))) + c2 * (r2 * ((r2 - 1) * x ^ (r2 - 1 - 1))) := by
  have hev : deriv (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2) =ᶠ[nhds x]
      (fun x : ℝ => (c1 * r1) * x ^ (r1 - 1) + (c2 * r2) * x ^ (r2 - 1)) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    rw [(hasDerivAt_pow2 c1 c2 r1 r2 z hz).deriv]; ring
  rw [hev.deriv_eq, (hasDerivAt_pow2 (c1 * r1) (c2 * r2) (r1 - 1) (r2 - 1) x hx).deriv]
  ring

lemma pow2_ode {a b c r1 r2 : ℝ} (c1 c2 : ℝ)
    (hr1 : a * r1 * (r1 - 1) + b * r1 + c = 0) (hr2 : a * r2 * (r2 - 1) + b * r2 + c = 0)
    (x : ℝ) (hx : 0 < x) :
    a * x ^ 2 * deriv (deriv (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2)) x +
      b * x * deriv (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2) x +
      c * (c1 * x ^ r1 + c2 * x ^ r2) = 0 := by
  rw [deriv2_pow2 c1 c2 r1 r2 x hx, (hasDerivAt_pow2 c1 c2 r1 r2 x hx).deriv]
  have e1 : ∀ r : ℝ, x ^ 2 * x ^ (r - 1 - 1) = x ^ r := by
    intro r
    rw [show x ^ 2 = x ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hx]; ring_nf
  have e2 : ∀ r : ℝ, x * x ^ (r - 1) = x ^ r := by
    intro r; rw [Real.rpow_sub_one hx.ne']; field_simp
  have : a * x ^ 2 * (c1 * (r1 * ((r1 - 1) * x ^ (r1 - 1 - 1))) +
      c2 * (r2 * ((r2 - 1) * x ^ (r2 - 1 - 1)))) +
      b * x * (c1 * (r1 * x ^ (r1 - 1)) + c2 * (r2 * x ^ (r2 - 1))) +
      c * (c1 * x ^ r1 + c2 * x ^ r2) =
      a * c1 * r1 * (r1 - 1) * (x ^ 2 * x ^ (r1 - 1 - 1)) +
      a * c2 * r2 * (r2 - 1) * (x ^ 2 * x ^ (r2 - 1 - 1)) +
      b * c1 * r1 * (x * x ^ (r1 - 1)) + b * c2 * r2 * (x * x ^ (r2 - 1)) +
      c * (c1 * x ^ r1 + c2 * x ^ r2) := by ring
  rw [this, e1, e1, e2, e2]
  linear_combination c1 * x ^ r1 * hr1 + c2 * x ^ r2 * hr2

lemma contDiffOn_pow2 (c1 c2 r1 r2 A B : ℝ) (hA : 0 < A) :
    ContDiffOn ℝ 2 (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2) (Set.Icc A B) := by
  intro x hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le hA hx.1).ne'
  apply ContDiffAt.contDiffWithinAt
  apply ContDiffAt.add
  · exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hx0)
  · exact contDiffAt_const.mul (Real.contDiffAt_rpow_const_of_ne hx0)

/-- transfer the ODE from a representation on `[A,B]` -/
lemma ode_of_rep {y : ℝ → ℝ} {c1 c2 r1 r2 A B : ℝ} (hA : 0 < A)
    (hrep : ∀ x ∈ Set.Icc A B, y x = c1 * x ^ r1 + c2 * x ^ r2) (x : ℝ)
    (hx : x ∈ Set.Ioo A B) :
    deriv y x = deriv (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2) x ∧
    deriv (deriv y) x = deriv (deriv (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2)) x := by
  have hev : y =ᶠ[nhds x] (fun x : ℝ => c1 * x ^ r1 + c2 * x ^ r2) := by
    filter_upwards [Icc_mem_nhds hx.1 hx.2] with z hz using hrep z hz
  exact ⟨hev.deriv_eq, hev.deriv.deriv_eq⟩

end DynkinEulerAux

namespace DynkinEulerAux
open DynkinAsymInfo.Linear

lemma delta_spec (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) (heps : 0 < eps) :
    delta p eps ∈ Set.Ioo 0 1 ∧ rootEq p eps (delta p eps) = 0 := by
  obtain ⟨_, _, r, hr, huniq⟩ := lemma69_main p h62 eps heps
  have hS : {z : ℝ | z ∈ Set.Ioo 0 1 ∧ rootEq p eps z = 0} = {r} := by
    ext z; constructor
    · intro hz; exact huniq z hz
    · intro hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hr
  have : delta p eps = r := by unfold delta; rw [hS, csInf_singleton]
  rw [this]; exact hr

theorem core63 (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) :
    let A := Ab p eps
    let B := Bb p eps
    0 < A ∧ A < B ∧
    ContDiffOn ℝ 2 (V1 p eps) (Set.Icc A B) ∧
    (∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv (V1 p eps)) phi +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * phi * deriv (V1 p eps) phi +
      p.mu1 * V1 p eps phi = 0) ∧
    (∀ phi, 0 < phi → phi ≤ A → V1 p eps phi = 1) ∧
    (∀ phi, B ≤ phi → V1 p eps phi = 1 + eps) ∧
    derivWithin (V1 p eps) (Set.Icc A B) B = 0 ∧
    ContDiffOn ℝ 2 (V p eps) (Set.Icc A B) ∧
    (∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv (V p eps)) phi +
      p.sigma * signalNoise p * phi * deriv (V p eps) phi +
      p.mu0 * V p eps phi = 0) ∧
    (∀ phi, 0 < phi → phi ≤ A → V p eps phi = 1 + phi) ∧
    derivWithin (V p eps) (Set.Icc A B) A = 1 ∧
    derivWithin (V p eps) (Set.Icc A B) B = 1 + eps ∧
    (∀ phi, B ≤ phi → deriv (V p eps) phi = 1 + eps) := by
  intro A B
  have hb1 : 0 < beta1 p := beta1_pos p h62
  have hb1' : beta1 p < 1 := beta1_lt_one p h62
  have hb2 : beta2 p < 0 := beta2_neg p h62
  have hw := omega_pos p h62
  have hso := sigma_omega p
  obtain ⟨hd, hroot⟩ := delta_spec p h62 eps heps
  set d := delta p eps with hddef
  set b1 := beta1 p with hb1def
  set b2 := beta2 p with hb2def
  have hd0 := hd.1
  have hd1 := hd.2
  -- the root equation
  have h90 : (1 - b2) * d ^ (b1 - 1) + (b1 - 1) * d ^ (b2 - 1) = (b1 - b2) / (1 + eps) := by
    unfold rootEq at hroot; rw [← hb1def, ← hb2def] at hroot; linarith
  -- positivity of the denominator of (93)
  set u := d ^ (b1 - 1) with hu
  set w := d ^ (b2 - 1) with hw'
  have hu0 : 0 < u := Real.rpow_pos_of_pos hd0 _
  have huw : u < w := Real.rpow_lt_rpow_of_exponent_gt hd0 hd1 (by linarith)
  have hu' : d ^ (1 - b1) = u⁻¹ := by
    rw [hu, ← Real.rpow_neg hd0.le]; ring_nf
  have hw'' : d ^ (1 - b2) = w⁻¹ := by
    rw [hw', ← Real.rpow_neg hd0.le]; ring_nf
  set Den := (1 + eps) * (b1 - b2) - b2 * (b1 - 1) * d ^ (1 - b2) +
      b1 * (b2 - 1) * d ^ (1 - b1) with hDen
  have hDenpos : 0 < Den := by
    have hh : 0 < (1 - b2) * u + (b1 - 1) * w := by
      rw [h90]; exact div_pos (by linarith) (by linarith)
    have hw0 : 0 < w := lt_trans hu0 huw
    have key : Den * ((1 - b2) * u + (b1 - 1) * w) =
        (1 - b2) * (1 - b1) * ((-b2) * (w - u) / w + b1 * (w - u) / u) := by
      have e : (1 + eps) * ((1 - b2) * u + (b1 - 1) * w) = b1 - b2 := by
        rw [h90]; field_simp
      rw [hDen, hu', hw'']
      field_simp
      linear_combination (b1 - b2) * u * w * e
    have : 0 < (1 - b2) * (1 - b1) * ((-b2) * (w - u) / w + b1 * (w - u) / u) := by
      apply mul_pos (mul_pos (by linarith) (by linarith))
      apply add_pos
      · exact div_pos (mul_pos (by linarith) (by linarith)) hw0
      · exact div_pos (mul_pos hb1 (by linarith)) hu0
    rw [← key] at this
    exact pos_of_mul_pos_left this hh.le
  have hnum : 0 < b1 * b2 * (d ^ (-b2) - d ^ (-b1)) := by
    have h1 : d ^ (-b2) < 1 := Real.rpow_lt_one hd0.le hd1 (by linarith)
    have h2 : 1 < d ^ (-b1) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hd0 hd1 (by linarith)
    have : b1 * b2 < 0 := mul_neg_of_pos_of_neg hb1 hb2
    nlinarith
  have hBdef : B = b1 * b2 * (d ^ (-b2) - d ^ (-b1)) / Den := by
    show Bb p eps = _; unfold Bb; rfl
  have hB0 : 0 < B := by rw [hBdef]; exact div_pos hnum hDenpos
  have hAdef : A = d * B := rfl
  have hA0 : 0 < A := mul_pos hd0 hB0
  have hAB : A < B := by rw [hAdef]; nlinarith
  have hBeq : B * Den = b1 * b2 * (d ^ (-b2) - d ^ (-b1)) := by
    rw [hBdef]; field_simp
  refine ⟨hA0, hAB, ?_⟩
  have hAI : A ∈ Set.Icc A B := ⟨le_rfl, hAB.le⟩
  have hBI : B ∈ Set.Icc A B := ⟨hAB.le, le_rfl⟩
  have hbb : b1 - b2 ≠ 0 := by intro h; linarith
  -- useful power identities
  have hpowA : ∀ r : ℝ, A ^ r = d ^ r * B ^ r := fun r => Real.mul_rpow hd0.le hB0.le
  have hBinv : ∀ r : ℝ, B ^ (-r) * B ^ r = 1 := by
    intro r; rw [← Real.rpow_add hB0]; simp
  ------------------------------------------------------------------
  -- V1
  set C1' := C1 p eps with hC1
  set C2' := C2 p eps with hC2
  have hC1def : C1' = (1 - b2) * (1 + eps) / (b1 - b2) * B ^ (1 - b1) := rfl
  have hC2def : C2' = (b1 - 1) * (1 + eps) / (b1 - b2) * B ^ (1 - b2) := rfl
  have hV1rep : ∀ x ∈ Set.Icc A B, V1 p eps x = C1' * x ^ (b1 - 1) + C2' * x ^ (b2 - 1) := by
    intro x hx
    have hBB : C1' * B ^ (b1 - 1) + C2' * B ^ (b2 - 1) = 1 + eps := by
      rw [hC1def, hC2def]
      have e1 : B ^ (1 - b1) * B ^ (b1 - 1) = 1 := by rw [← Real.rpow_add hB0]; simp
      have e2 : B ^ (1 - b2) * B ^ (b2 - 1) = 1 := by rw [← Real.rpow_add hB0]; simp
      have : (1 - b2) * (1 + eps) / (b1 - b2) * B ^ (1 - b1) * B ^ (b1 - 1) +
          (b1 - 1) * (1 + eps) / (b1 - b2) * B ^ (1 - b2) * B ^ (b2 - 1) =
          (1 - b2) * (1 + eps) / (b1 - b2) * (B ^ (1 - b1) * B ^ (b1 - 1)) +
          (b1 - 1) * (1 + eps) / (b1 - b2) * (B ^ (1 - b2) * B ^ (b2 - 1)) := by ring
      rw [this, e1, e2]; field_simp; ring
    have hAA : C1' * A ^ (b1 - 1) + C2' * A ^ (b2 - 1) = 1 := by
      rw [hC1def, hC2def, hpowA, hpowA]
      have e1 : B ^ (1 - b1) * B ^ (b1 - 1) = 1 := by rw [← Real.rpow_add hB0]; simp
      have e2 : B ^ (1 - b2) * B ^ (b2 - 1) = 1 := by rw [← Real.rpow_add hB0]; simp
      have : (1 - b2) * (1 + eps) / (b1 - b2) * B ^ (1 - b1) * (d ^ (b1 - 1) * B ^ (b1 - 1)) +
          (b1 - 1) * (1 + eps) / (b1 - b2) * B ^ (1 - b2) * (d ^ (b2 - 1) * B ^ (b2 - 1)) =
          (1 + eps) / (b1 - b2) * ((1 - b2) * d ^ (b1 - 1) * (B ^ (1 - b1) * B ^ (b1 - 1)) +
          (b1 - 1) * d ^ (b2 - 1) * (B ^ (1 - b2) * B ^ (b2 - 1))) := by ring
      rw [this, e1, e2, mul_one, mul_one, h90]; field_simp
    unfold V1
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [if_pos le_rfl]; exact hAA.symm
    · rw [if_neg (not_le.mpr h)]
      rcases eq_or_lt_of_le hx.2 with h' | h'
      · rw [h', if_pos le_rfl]; exact hBB.symm
      · rw [if_neg (not_le.mpr h')]
  have hr1 : signalNoise p ^ 2 / 2 * (b1 - 1) * (b1 - 1 - 1) +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * (b1 - 1) + p.mu1 = 0 := by
    have := beta_root p h62 b1 (Or.inl rfl)
    linear_combination this - hso
  have hr2 : signalNoise p ^ 2 / 2 * (b2 - 1) * (b2 - 1 - 1) +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * (b2 - 1) + p.mu1 = 0 := by
    have := beta_root p h62 b2 (Or.inr rfl)
    linear_combination this - hso
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiffOn_pow2 C1' C2' (b1 - 1) (b2 - 1) A B hA0).congr hV1rep
  · intro x hx
    obtain ⟨e1, e2⟩ := ode_of_rep hA0 hV1rep x hx
    rw [e1, e2, hV1rep x (Set.Ioo_subset_Icc_self hx)]
    have := pow2_ode C1' C2' hr1 hr2 x (lt_trans hA0 hx.1)
    linear_combination this
  · intro x _ hx
    unfold V1; rw [if_pos hx]
  · intro x hx
    unfold V1; rw [if_neg (by intro h; linarith), if_pos hx]
  · rw [derivWithin_eq_of_rep hA0 hAB hV1rep B hBI, hC1def, hC2def]
    have e1 : B ^ (1 - b1) * B ^ (b1 - 1 - 1) = B⁻¹ := by
      rw [← Real.rpow_add hB0, ← Real.rpow_neg_one]; ring_nf
    have e2 : B ^ (1 - b2) * B ^ (b2 - 1 - 1) = B⁻¹ := by
      rw [← Real.rpow_add hB0, ← Real.rpow_neg_one]; ring_nf
    have : (1 - b2) * (1 + eps) / (b1 - b2) * B ^ (1 - b1) * ((b1 - 1) * B ^ (b1 - 1 - 1)) +
        (b1 - 1) * (1 + eps) / (b1 - b2) * B ^ (1 - b2) * ((b2 - 1) * B ^ (b2 - 1 - 1)) =
        (1 - b2) * (1 + eps) / (b1 - b2) * (b1 - 1) * (B ^ (1 - b1) * B ^ (b1 - 1 - 1)) +
        (b1 - 1) * (1 + eps) / (b1 - b2) * (b2 - 1) * (B ^ (1 - b2) * B ^ (b2 - 1 - 1)) := by
      ring
    rw [this, e1, e2]; ring
  ------------------------------------------------------------------
  -- V
  set D1' := D1 p eps with hD1
  set D2' := D2 p eps with hD2
  have hD1def : D1' = A ^ (-b1) / (b1 - b2) * (-b2 + (1 - b2) * A) := rfl
  have hD2def : D2' = A ^ (-b2) / (b1 - b2) * (b1 + (b1 - 1) * A) := rfl
  have eA1 : A ^ (-b1) * A ^ b1 = 1 := by rw [← Real.rpow_add hA0]; simp
  have eA2 : A ^ (-b2) * A ^ b2 = 1 := by rw [← Real.rpow_add hA0]; simp
  have hGA : D1' * A ^ b1 + D2' * A ^ b2 = 1 + A := by
    rw [hD1def, hD2def]
    have : A ^ (-b1) / (b1 - b2) * (-b2 + (1 - b2) * A) * A ^ b1 +
        A ^ (-b2) / (b1 - b2) * (b1 + (b1 - 1) * A) * A ^ b2 =
        (A ^ (-b1) * A ^ b1) * (-b2 + (1 - b2) * A) / (b1 - b2) +
        (A ^ (-b2) * A ^ b2) * (b1 + (b1 - 1) * A) / (b1 - b2) := by ring
    rw [this, eA1, eA2]; field_simp; ring
  have hVrep : ∀ x ∈ Set.Icc A B, V p eps x = D1' * x ^ b1 + D2' * x ^ b2 := by
    intro x hx
    unfold V
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h; rw [if_pos le_rfl]; exact hGA.symm
    · rw [if_neg (not_le.mpr h)]
      rcases eq_or_lt_of_le hx.2 with h' | h'
      · rw [h', if_pos le_rfl]; ring
      · rw [if_neg (not_le.mpr h')]
  have hq1 := beta_root p h62 b1 (Or.inl rfl)
  have hq2 := beta_root p h62 b2 (Or.inr rfl)
  have hq1' : signalNoise p ^ 2 / 2 * b1 * (b1 - 1) + p.sigma * signalNoise p * b1 + p.mu0 = 0 :=
    hq1
  have hq2' : signalNoise p ^ 2 / 2 * b2 * (b2 - 1) + p.sigma * signalNoise p * b2 + p.mu0 = 0 :=
    hq2
  -- derivative at B
  have hGB' : D1' * (b1 * B ^ (b1 - 1)) + D2' * (b2 * B ^ (b2 - 1)) = 1 + eps := by
    rw [hD1def, hD2def]
    have hA' : A = d * B := rfl
    have f1 : A ^ (-b1) * B ^ (b1 - 1) = d ^ (-b1) * B⁻¹ := by
      rw [hpowA, mul_assoc, ← Real.rpow_add hB0, ← Real.rpow_neg_one]; ring_nf
    have f2 : A ^ (-b2) * B ^ (b2 - 1) = d ^ (-b2) * B⁻¹ := by
      rw [hpowA, mul_assoc, ← Real.rpow_add hB0, ← Real.rpow_neg_one]; ring_nf
    have g1 : d * d ^ (-b1) = d ^ (1 - b1) := by
      rw [show (1 - b1) = 1 + (-b1) by ring, Real.rpow_add hd0, Real.rpow_one]
    have g2 : d * d ^ (-b2) = d ^ (1 - b2) := by
      rw [show (1 - b2) = 1 + (-b2) by ring, Real.rpow_add hd0, Real.rpow_one]
    have : A ^ (-b1) / (b1 - b2) * (-b2 + (1 - b2) * A) * (b1 * B ^ (b1 - 1)) +
        A ^ (-b2) / (b1 - b2) * (b1 + (b1 - 1) * A) * (b2 * B ^ (b2 - 1)) =
        (A ^ (-b1) * B ^ (b1 - 1)) * b1 * (-b2 + (1 - b2) * A) / (b1 - b2) +
        (A ^ (-b2) * B ^ (b2 - 1)) * b2 * (b1 + (b1 - 1) * A) / (b1 - b2) := by ring
    rw [this, f1, f2, hA']
    have hBne : B ≠ 0 := hB0.ne'
    field_simp
    rw [hDen] at hBeq
    linear_combination -hBeq + b1 * (1 - b2) * B * g1 + b2 * (b1 - 1) * B * g2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (contDiffOn_pow2 D1' D2' b1 b2 A B hA0).congr hVrep
  · intro x hx
    obtain ⟨e1, e2⟩ := ode_of_rep hA0 hVrep x hx
    rw [e1, e2, hVrep x (Set.Ioo_subset_Icc_self hx)]
    have := pow2_ode D1' D2' hq1' hq2' x (lt_trans hA0 hx.1)
    linear_combination this
  · intro x _ hx
    unfold V; rw [if_pos hx]
  · rw [derivWithin_eq_of_rep hA0 hAB hVrep A hAI, hD1def, hD2def]
    have f1 : A ^ (-b1) * A ^ (b1 - 1) = A⁻¹ := by
      rw [← Real.rpow_add hA0, ← Real.rpow_neg_one]; ring_nf
    have f2 : A ^ (-b2) * A ^ (b2 - 1) = A⁻¹ := by
      rw [← Real.rpow_add hA0, ← Real.rpow_neg_one]; ring_nf
    have : A ^ (-b1) / (b1 - b2) * (-b2 + (1 - b2) * A) * (b1 * A ^ (b1 - 1)) +
        A ^ (-b2) / (b1 - b2) * (b1 + (b1 - 1) * A) * (b2 * A ^ (b2 - 1)) =
        (A ^ (-b1) * A ^ (b1 - 1)) * b1 * (-b2 + (1 - b2) * A) / (b1 - b2) +
        (A ^ (-b2) * A ^ (b2 - 1)) * b2 * (b1 + (b1 - 1) * A) / (b1 - b2) := by ring
    rw [this, f1, f2]
    field_simp
    ring
  · rw [derivWithin_eq_of_rep hA0 hAB hVrep B hBI]; exact hGB'
  · intro x hx
    -- right linear piece
    set L : ℝ → ℝ := fun x => D1' * B ^ b1 + D2' * B ^ b2 + (1 + eps) * (x - B) with hL
    have hVL : ∀ z, B ≤ z → V p eps z = L z := by
      intro z hz
      unfold V; rw [if_neg (by intro h; linarith), if_pos hz]
    have hLd : ∀ z, HasDerivAt L (1 + eps) z := by
      intro z
      exact ((((hasDerivAt_id z).sub_const B).const_mul (1 + eps)).const_add
        (D1' * B ^ b1 + D2' * B ^ b2)).congr_deriv (by ring)
    rcases eq_or_lt_of_le hx with h | h
    · subst h
      have hright : HasDerivWithinAt (V p eps) (1 + eps) (Set.Ici B) B :=
        (hLd B).hasDerivWithinAt.congr (fun z hz => hVL z hz) (hVL B le_rfl)
      have hleft0 : HasDerivWithinAt (V p eps) (1 + eps) (Set.Icc A B) B := by
        have := (hasDerivAt_pow2 D1' D2' b1 b2 B hB0).hasDerivWithinAt (s := Set.Icc A B)
        rw [hGB'] at this
        exact this.congr (fun z hz => hVrep z hz) (hVrep B hBI)
      have hleft : HasDerivWithinAt (V p eps) (1 + eps) (Set.Iic B) B :=
        hleft0.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hAB)
      have := hleft.union hright
      rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
      exact this.deriv
    · have hev : V p eps =ᶠ[nhds x] L := by
        filter_upwards [Ioi_mem_nhds h] with z hz using hVL z hz.le
      rw [hev.deriv_eq]; exact (hLd x).deriv

end DynkinEulerAux


open DynkinAsymInfo.Linear in
theorem solution (p : Params) (h62 : p.mu0 < 0 ∧ 0 < p.mu1)
    (eps : ℝ) (heps : 0 < eps) :
    let A := Ab p eps
    let B := Bb p eps
    0 < A ∧ A < B ∧
    ContDiffOn ℝ 2 (V1 p eps) (Set.Icc A B) ∧
    (∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv (V1 p eps)) phi +
      (signalNoise p ^ 2 + p.sigma * signalNoise p) * phi * deriv (V1 p eps) phi +
      p.mu1 * V1 p eps phi = 0) ∧
    (∀ phi, 0 < phi → phi ≤ A → V1 p eps phi = 1) ∧
    (∀ phi, B ≤ phi → V1 p eps phi = 1 + eps) ∧
    derivWithin (V1 p eps) (Set.Icc A B) B = 0 ∧
    ContDiffOn ℝ 2 (V p eps) (Set.Icc A B) ∧
    (∀ phi ∈ Set.Ioo A B,
      signalNoise p ^ 2 * phi ^ 2 / 2 * deriv (deriv (V p eps)) phi +
      p.sigma * signalNoise p * phi * deriv (V p eps) phi +
      p.mu0 * V p eps phi = 0) ∧
    (∀ phi, 0 < phi → phi ≤ A → V p eps phi = 1 + phi) ∧
    derivWithin (V p eps) (Set.Icc A B) A = 1 ∧
    derivWithin (V p eps) (Set.Icc A B) B = 1 + eps ∧
    (∀ phi, B ≤ phi → deriv (V p eps) phi = 1 + eps) :=
  DynkinEulerAux.core63 p h62 eps heps
