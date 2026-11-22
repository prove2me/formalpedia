-- Prove2me | solution 1 for CubicSurface27.smooth_implies_transverse
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T04:54:16.694055+00:00
-- url     : https://prove2.me/submissions/05c5a9e9-29b7-4559-a678-db5fd6d0dc6b

import Definitions.Def_cubic_surface_27_layer
import Definitions.Def_cubic_surface_transverse

open MvPolynomial

namespace SmoothTransverseAux

open CubicSurface27

/-! ### Degree-3 monomials are products of three variables -/

lemma exists_single_add {n : ℕ} (m : Fin 4 →₀ ℕ) (hm : m.degree = n + 1) :
    ∃ i m', m = m' + Finsupp.single i 1 ∧ m'.degree = n := by
  have hne : m ≠ 0 := by
    rintro rfl; simp at hm
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hle : Finsupp.single i 1 ≤ m := by
    rw [Finsupp.single_le_iff]; simp at hi; omega
  refine ⟨i, m - Finsupp.single i 1, (tsub_add_cancel_of_le hle).symm, ?_⟩
  have h := congrArg Finsupp.degree (tsub_add_cancel_of_le hle)
  rw [map_add, Finsupp.degree_single, hm] at h
  omega

lemma monomial_deg3 (m : Fin 4 →₀ ℕ) (hm : m.degree = 3) :
    ∃ a b c : Fin 4, monomial m (1 : ℂ) = X a * X b * X c := by
  obtain ⟨c, m1, rfl, h1⟩ := exists_single_add (n := 2) m hm
  obtain ⟨b, m2, rfl, h2⟩ := exists_single_add (n := 1) m1 h1
  obtain ⟨a, m3, rfl, h3⟩ := exists_single_add (n := 0) m2 h2
  rw [Finsupp.degree_eq_zero_iff] at h3
  subst h3
  refine ⟨a, b, c, ?_⟩
  simp [X, monomial_mul]

/-- Induction principle for homogeneous cubics. -/
lemma cubic_induction (P : MvPolynomial (Fin 4) ℂ → Prop)
    (h0 : P 0) (hadd : ∀ F G, P F → P G → P (F + G))
    (hsmul : ∀ (r : ℂ) F, P F → P (r • F))
    (hX : ∀ a b c : Fin 4, P (X a * X b * X c))
    (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) : P F := by
  rw [F.as_sum]
  refine Finset.sum_induction _ P hadd h0 ?_
  intro m hm
  have hdeg : m.degree = 3 := by
    have := hF (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_weight_one]
    exact this
  obtain ⟨a, b, c, habc⟩ := monomial_deg3 m hdeg
  have : monomial m (coeff m F) = coeff m F • monomial m (1 : ℂ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, habc]
  exact hsmul _ _ (hX a b c)

/-! ### Polarization identities -/

lemma polar3_zero (x y z : Fin 4 → ℂ) : polar3 0 x y z = 0 := by
  simp [polar3]

lemma polar3_add (F G : MvPolynomial (Fin 4) ℂ) (x y z : Fin 4 → ℂ) :
    polar3 (F + G) x y z = polar3 F x y z + polar3 G x y z := by
  simp only [polar3, map_add]; ring

lemma polar3_smul (r : ℂ) (F : MvPolynomial (Fin 4) ℂ) (x y z : Fin 4 → ℂ) :
    polar3 (r • F) x y z = r * polar3 F x y z := by
  simp only [polar3, smul_eval]; ring

lemma polar3_expand (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (u v0 v1 : Fin 4 → ℂ) (s t : ℂ) :
    polar3 F u (s • v0 + t • v1) (s • v0 + t • v1) =
      s ^ 2 * polar3 F u v0 v0 + 2 * s * t * polar3 F u v0 v1 + t ^ 2 * polar3 F u v1 v1 := by
  refine cubic_induction (fun F => polar3 F u (s • v0 + t • v1) (s • v0 + t • v1) =
      s ^ 2 * polar3 F u v0 v0 + 2 * s * t * polar3 F u v0 v1 + t ^ 2 * polar3 F u v1 v1)
    ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, hF]; ring
  · intro a b c; simp [polar3]; ring

lemma polar3_grad (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u x : Fin 4 → ℂ) :
    3 * polar3 F u x x = ∑ i, u i * eval x (pderiv i F) := by
  refine cubic_induction (fun F => 3 * polar3 F u x x = ∑ i, u i * eval x (pderiv i F))
    ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG
    simp only [polar3_add, map_add, mul_add, Finset.sum_add_distrib, ← hF, ← hG]
  · intro r F hF
    simp only [polar3_smul, Derivation.map_smul, smul_eval]
    have : ∑ i, u i * (r * eval x (pderiv i F)) = r * ∑ i, u i * eval x (pderiv i F) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, ← hF]; ring
  · intro a b c
    simp [polar3, Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite (eval x), mul_ite, Finset.sum_ite_eq]
    ring

/-! ### The Sylvester determinant of two binary quadratics -/

/-- The resultant of `a s² + b s t + c t²` and `d s² + e s t + f t²`. -/
def res2 (a b c d e f : ℂ) : ℂ := (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e)

lemma sylvester_det (a b c d e f : ℂ) :
    (!![a, d, 0, 0; b, e, a, d; c, f, b, e; 0, 0, c, f] : Matrix (Fin 4) (Fin 4) ℂ).det =
      -res2 a b c d e f := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, res2]
  ring

lemma res2_root_aux (a b c d e f : ℂ) (ha : a ≠ 0) (h : res2 a b c d e f = 0) :
    ∃ r : ℂ, a * r ^ 2 + b * r + c = 0 ∧ d * r ^ 2 + e * r + f = 0 := by
  obtain ⟨σ, hσ⟩ := IsAlgClosed.exists_eq_mul_self (discrim a b c)
  obtain ⟨r1, hr1⟩ := exists_quadratic_eq_zero ha ⟨σ, hσ⟩
  set r2 := -b / a - r1 with hr2
  have hdiv : a * (b / a) = b := mul_div_cancel₀ b ha
  have hb : b = -a * (r1 + r2) := by rw [hr2]; linear_combination -hdiv
  have hc : c = a * r1 * r2 := by rw [hr2]; linear_combination hr1 + r1 * hdiv
  clear_value r2
  subst hb hc
  have key : res2 (a) (-a * (r1 + r2)) (a * r1 * r2) d e f =
      a ^ 2 * (d * r1 ^ 2 + e * r1 + f) * (d * r2 ^ 2 + e * r2 + f) := by
    unfold res2; ring
  rw [key] at h
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) ha
    · exact ⟨r1, by ring, h⟩
  · exact ⟨r2, by ring, h⟩

lemma sylvester_root (a b c d e f : ℂ)
    (h : (!![a, d, 0, 0; b, e, a, d; c, f, b, e; 0, 0, c, f] : Matrix (Fin 4) (Fin 4) ℂ).det = 0) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧ a * s ^ 2 + b * s * t + c * t ^ 2 = 0 ∧
      d * s ^ 2 + e * s * t + f * t ^ 2 = 0 := by
  rw [sylvester_det, neg_eq_zero] at h
  by_cases ha : a = 0
  · by_cases hd : d = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [ha], by simp [hd]⟩
    · have h' : res2 d e f a b c = 0 := by rw [← h]; unfold res2; ring
      obtain ⟨r, h1, h2⟩ := res2_root_aux d e f a b c hd h'
      exact ⟨r, 1, Or.inr one_ne_zero, by linear_combination h2, by linear_combination h1⟩
  · obtain ⟨r, h1, h2⟩ := res2_root_aux a b c d e f ha h
    exact ⟨r, 1, Or.inr one_ne_zero, by linear_combination h1, by linear_combination h2⟩

end SmoothTransverseAux

open CubicSurface27 SmoothTransverseAux in
theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) :
    HasTransverseZeroes F := by
  intro W hW v0 v1 p q hv0 hv1 hli hdet
  obtain ⟨_, hWF⟩ := hW
  set B := polar3 F
  obtain ⟨s, t, hst, hα, hβ⟩ := sylvester_root (B p v0 v0) (2 * B p v0 v1) (B p v1 v1)
    (B q v0 v0) (2 * B q v0 v1) (B q v1 v1) (by simpa [polarJacDet, B] using hdet)
  set x : Fin 4 → ℂ := s • v0 + t • v1 with hxdef
  have hxW : x ∈ W := W.add_mem (W.smul_mem s hv0) (W.smul_mem t hv1)
  have hx0 : x ≠ 0 := by
    intro hx
    have := Fintype.linearIndependent_iff.mp hli ![s, t, 0, 0]
      (by simpa [Fin.sum_univ_four, hxdef] using hx)
    rcases hst with h | h
    · exact h (this 0)
    · exact h (this 1)
  have hFx : eval x F = 0 := hWF x hxW
  -- the differential of `F` at `x`, as a linear functional
  let g : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := ∑ i, (eval x (pderiv i F)) • LinearMap.proj i
  have hg : ∀ u, g u = 3 * B u x x := by
    intro u
    rw [polar3_grad F hF u x]
    simp [g, mul_comm]
  -- `B v x x = 0` whenever `v ∈ W`, since every evaluation point lies in `W`
  have hBW : ∀ v ∈ W, B v x x = 0 := by
    intro v hv
    have h1 := hWF _ (W.add_mem (W.add_mem hv hxW) hxW)
    have h2 := hWF _ (W.add_mem hv hxW)
    have h3 := hWF _ (W.add_mem hxW hxW)
    have h4 := hWF _ (W.add_mem hxW hv)
    have h5 := hWF _ hv
    simp only [B, polar3, h1, h2, h3, h4, h5, hFx]
    ring
  have hgp : g p = 0 := by
    rw [hg]
    show 3 * polar3 F p (s • v0 + t • v1) (s • v0 + t • v1) = 0
    have hα' : polar3 F p v0 v0 * s ^ 2 + 2 * polar3 F p v0 v1 * s * t
        + polar3 F p v1 v1 * t ^ 2 = 0 := hα
    rw [polar3_expand F hF]
    linear_combination 3 * hα'
  have hgq : g q = 0 := by
    rw [hg]
    show 3 * polar3 F q (s • v0 + t • v1) (s • v0 + t • v1) = 0
    have hβ' : polar3 F q v0 v0 * s ^ 2 + 2 * polar3 F q v0 v1 * s * t
        + polar3 F q v1 v1 * t ^ 2 = 0 := hβ
    rw [polar3_expand F hF]
    linear_combination 3 * hβ'
  have hspan : Submodule.span ℂ (Set.range ![v0, v1, p, q]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hg0 : g = 0 := by
    have hle : Submodule.span ℂ (Set.range ![v0, v1, p, q]) ≤ LinearMap.ker g := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · simp [hg, hBW v0 hv0]
      · simp [hg, hBW v1 hv1]
      · simpa using hgp
      · simpa using hgq
    rw [hspan, top_le_iff, LinearMap.ker_eq_top] at hle
    exact hle
  obtain ⟨i, hi⟩ := hsm x hx0 hFx
  apply hi
  have := LinearMap.congr_fun hg0 (Pi.single i 1)
  simpa [g, Pi.single_apply] using this
