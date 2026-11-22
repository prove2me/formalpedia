-- Prove2me | solution 1 for CubicSurface27.linesOf_finite
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T05:41:51.822235+00:00
-- url     : https://prove2.me/submissions/6e374ba8-04d5-4609-84ab-f9063dd3a7bf

import Definitions.Def_cubic_surface_27_layer
import Definitions.Def_cubic_surface_transverse

/-!
Direct proof of `CubicSurface27.linesOf_finite` (no imports of platform theorems).

Route: every line of the smooth cubic surface is a transverse zero of the section `s_F`
(the argument of `smooth_implies_transverse`, inlined).  In each of finitely many affine
charts of `Gr(2,4)` (normalised so that the chart coordinates lie in the closed unit
polydisc), lines of `X` are zeros of a polynomial map `Φ : ℂ⁴ → ℂ⁴` whose derivative at
each zero is injective.  Hence the zeros are isolated, and a compact discrete set is finite.
-/

open MvPolynomial

namespace LFAux

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

lemma polar3_comm12 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x y z : Fin 4 → ℂ) :
    polar3 F x y z = polar3 F y x z := by
  refine cubic_induction (fun F => polar3 F x y z = polar3 F y x z) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]
  · intro r F hF; simp only [polar3_smul, hF]
  · intro a b c; simp [polar3]; ring

lemma polar3_comm13 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x y z : Fin 4 → ℂ) :
    polar3 F x y z = polar3 F z y x := by
  refine cubic_induction (fun F => polar3 F x y z = polar3 F z y x) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]
  · intro r F hF; simp only [polar3_smul, hF]
  · intro a b c; simp [polar3]; ring

/-- `F(u + ε d)` as a cubic in `ε`. -/
lemma expF (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u d : Fin 4 → ℂ) (ε : ℂ) :
    eval (u + ε • d) F = eval u F + ε * (3 * polar3 F d u u) + ε ^ 2 * (3 * polar3 F d d u)
      + ε ^ 3 * eval d F := by
  refine cubic_induction (fun F => eval (u + ε • d) F = eval u F + ε * (3 * polar3 F d u u)
      + ε ^ 2 * (3 * polar3 F d d u) + ε ^ 3 * eval d F) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, map_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, smul_eval, hF]; ring
  · intro a b c; simp [polar3]; ring

/-- `B(u+εd, u+εd, w+εe)` as a cubic in `ε`. -/
lemma expB (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u d w e : Fin 4 → ℂ) (ε : ℂ) :
    polar3 F (u + ε • d) (u + ε • d) (w + ε • e) = polar3 F u u w
      + ε * (2 * polar3 F d u w + polar3 F u u e)
      + ε ^ 2 * (polar3 F d d w + 2 * polar3 F d u e) + ε ^ 3 * polar3 F d d e := by
  refine cubic_induction (fun F => polar3 F (u + ε • d) (u + ε • d) (w + ε • e) = polar3 F u u w
      + ε * (2 * polar3 F d u w + polar3 F u u e)
      + ε ^ 2 * (polar3 F d d w + 2 * polar3 F d u e) + ε ^ 3 * polar3 F d d e)
    ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, hF]; ring
  · intro a b c; simp [polar3]; ring

/-- `F(s u + t w)` as a binary cubic. -/
lemma expST (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (u w : Fin 4 → ℂ) (s t : ℂ) :
    eval (s • u + t • w) F = s ^ 3 * eval u F + 3 * s ^ 2 * t * polar3 F u u w
      + 3 * s * t ^ 2 * polar3 F w w u + t ^ 3 * eval w F := by
  refine cubic_induction (fun F => eval (s • u + t • w) F = s ^ 3 * eval u F
      + 3 * s ^ 2 * t * polar3 F u u w + 3 * s * t ^ 2 * polar3 F w w u + t ^ 3 * eval w F)
    ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, map_add, hF, hG]; ring
  · intro r F hF; simp only [polar3_smul, smul_eval, hF]; ring
  · intro a b c; simp [polar3]; ring

/-! ### Differentiability of polynomial evaluation -/

@[fun_prop]
lemma differentiable_eval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : E → Fin 4 → ℂ) (hg : Differentiable ℂ g) (P : MvPolynomial (Fin 4) ℂ) :
    Differentiable ℂ (fun a => eval (g a) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p n hp =>
    simp only [eval_mul, eval_X]
    exact hp.mul (differentiable_pi.mp hg n)

lemma polar3_comm23 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x y z : Fin 4 → ℂ) :
    polar3 F x y z = polar3 F x z y := by
  refine cubic_induction (fun F => polar3 F x y z = polar3 F x z y) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]
  · intro r F hF; simp only [polar3_smul, hF]
  · intro a b c; simp [polar3]; ring

lemma polar3_lin1 (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (r s : ℂ)
    (x y z w : Fin 4 → ℂ) :
    polar3 F (r • x + s • y) z w = r * polar3 F x z w + s * polar3 F y z w := by
  refine cubic_induction (fun F => polar3 F (r • x + s • y) z w
      = r * polar3 F x z w + s * polar3 F y z w) ?_ ?_ ?_ ?_ F hF
  · simp [polar3_zero]
  · intro F G hF hG; simp only [polar3_add, hF, hG]; ring
  · intro r' F hF; simp only [polar3_smul, hF]; ring
  · intro a b c; simp [polar3]; ring

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

/-! ### The Sylvester determinant of two binary quadratics (from `smooth_implies_transverse`) -/

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

/-- The transversality argument of `smooth_implies_transverse`, stated for a pair of vectors
spanning a line on the surface. -/
lemma jac_ne_zero (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (v0 v1 p q : Fin 4 → ℂ) (hli : LinearIndependent ℂ ![v0, v1, p, q])
    (hst0 : ∀ s t : ℂ, eval (s • v0 + t • v1) F = 0) :
    polarJacDet F v0 v1 p q ≠ 0 := by
  intro hdet
  set W := Submodule.span ℂ {v0, v1}
  have hWF : ∀ x ∈ W, eval x F = 0 := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    exact hst0 a b
  have hv0 : v0 ∈ W := Submodule.subset_span (by simp)
  have hv1 : v1 ∈ W := Submodule.subset_span (by simp)
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
  let g : (Fin 4 → ℂ) →ₗ[ℂ] ℂ := ∑ i, (eval x (pderiv i F)) • LinearMap.proj i
  have hg : ∀ u, g u = 3 * B u x x := by
    intro u
    rw [polar3_grad F hF u x]
    simp [g, mul_comm]
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

/-! ### The chart map -/

/-- Chart coordinates `a ∈ ℂ⁴` give the line spanned by `chu0 a` and `chu1 a`. -/
def chu0 (v0 p q a : Fin 4 → ℂ) : Fin 4 → ℂ := v0 + a 0 • p + a 1 • q
def chu1 (v1 p q a : Fin 4 → ℂ) : Fin 4 → ℂ := v1 + a 2 • p + a 3 • q

/-- The four coefficients of the binary cubic `F(s u₀ + t u₁)` (up to the factors 3). -/
noncomputable def Φ (F : MvPolynomial (Fin 4) ℂ) (v0 v1 p q : Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    Fin 4 → ℂ :=
  ![eval (chu0 v0 p q a) F,
    polar3 F (chu0 v0 p q a) (chu0 v0 p q a) (chu1 v1 p q a),
    polar3 F (chu1 v1 p q a) (chu1 v1 p q a) (chu0 v0 p q a),
    eval (chu1 v1 p q a) F]

lemma hasDerivAt_cubic (c0 c1 c2 c3 : ℂ) :
    HasDerivAt (fun ε : ℂ => c0 + ε * c1 + ε ^ 2 * c2 + ε ^ 3 * c3) c1 0 := by
  have h := ((((hasDerivAt_id (0:ℂ)).mul_const c1).const_add c0).add
    ((hasDerivAt_pow 2 (0:ℂ)).mul_const c2)).add ((hasDerivAt_pow 3 (0:ℂ)).mul_const c3)
  exact h.congr_deriv (by simp)

lemma chu0_shift (v0 p q a h : Fin 4 → ℂ) (ε : ℂ) :
    chu0 v0 p q (a + ε • h) = chu0 v0 p q a + ε • (h 0 • p + h 1 • q) := by
  ext i; simp [chu0]; ring

lemma chu1_shift (v1 p q a h : Fin 4 → ℂ) (ε : ℂ) :
    chu1 v1 p q (a + ε • h) = chu1 v1 p q a + ε • (h 2 • p + h 3 • q) := by
  ext i; simp [chu1]; ring

/-- The derivative of `Φ` along `h`. -/
noncomputable def dΦ (F : MvPolynomial (Fin 4) ℂ) (v0 v1 p q a h : Fin 4 → ℂ) : Fin 4 → ℂ :=
  let x := chu0 v0 p q a
  let y := chu1 v1 p q a
  let d0 := h 0 • p + h 1 • q
  let d1 := h 2 • p + h 3 • q
  ![3 * polar3 F d0 x x, 2 * polar3 F d0 x y + polar3 F x x d1,
    2 * polar3 F d1 y x + polar3 F y y d0, 3 * polar3 F d1 y y]

lemma hasDerivAt_Φ (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (v0 v1 p q a h : Fin 4 → ℂ) :
    HasDerivAt (fun ε : ℂ => Φ F v0 v1 p q (a + ε • h)) (dΦ F v0 v1 p q a h) 0 := by
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · simp only [Φ, chu0_shift, dΦ]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    simp_rw [expF F hF]
    exact hasDerivAt_cubic _ _ _ _
  · simp only [Φ, chu0_shift, chu1_shift, dΦ]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    simp_rw [expB F hF]
    exact hasDerivAt_cubic _ _ _ _
  · simp only [Φ, chu0_shift, chu1_shift, dΦ]
    try simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp_rw [expB F hF]
    exact hasDerivAt_cubic _ _ _ _
  · simp only [Φ, chu1_shift, dΦ]
    try simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
    simp_rw [expF F hF]
    exact hasDerivAt_cubic _ _ _ _

lemma differentiable_Φ (F : MvPolynomial (Fin 4) ℂ) (v0 v1 p q : Fin 4 → ℂ) :
    Differentiable ℂ (Φ F v0 v1 p q) := by
  have h0 : Differentiable ℂ (chu0 v0 p q) := by unfold chu0; fun_prop
  have h1 : Differentiable ℂ (chu1 v1 p q) := by unfold chu1; fun_prop
  rw [differentiable_pi]
  intro i
  fin_cases i <;> simp [Φ, polar3] <;> fun_prop

lemma li_chart (v0 v1 p q : Fin 4 → ℂ) (hli : LinearIndependent ℂ ![v0, v1, p, q])
    (a : Fin 4 → ℂ) : LinearIndependent ℂ ![chu0 v0 p q a, chu1 v1 p q a, p, q] := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro g hg
  have := hli ![g 0, g 1, g 0 * a 0 + g 1 * a 2 + g 2, g 0 * a 1 + g 1 * a 3 + g 3] (by
    rw [← hg]; ext n; simp [Fin.sum_univ_four, chu0, chu1]; ring)
  have e0 : g 0 = 0 := by simpa using this 0
  have e1 : g 1 = 0 := by simpa using this 1
  have e2 : g 2 = 0 := by simpa [e0, e1] using this 2
  have e3 : g 3 = 0 := by simpa [e0, e1] using this 3
  intro i; fin_cases i <;> assumption

lemma dΦ_inj (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (v0 v1 p q : Fin 4 → ℂ) (hli : LinearIndependent ℂ ![v0, v1, p, q])
    (a : Fin 4 → ℂ) (ha : Φ F v0 v1 p q a = 0) (h : Fin 4 → ℂ)
    (hd : dΦ F v0 v1 p q a h = 0) : h = 0 := by
  have hli' := li_chart v0 v1 p q hli a
  have e0 := congrFun ha 0
  have e1 := congrFun ha 1
  have e2 := congrFun ha 2
  have e3 := congrFun ha 3
  have d0 := congrFun hd 0
  have d1 := congrFun hd 1
  have d2 := congrFun hd 2
  have d3 := congrFun hd 3
  simp only [Φ, dΦ] at e0 e1 e2 e3 d0 d1 d2 d3
  simp at e0 e1 e2 e3 d0 d1 d2 d3
  generalize chu0 v0 p q a = x at *
  generalize chu1 v1 p q a = y at *
  have hst : ∀ s t : ℂ, eval (s • x + t • y) F = 0 := by
    intro s t; rw [expST F hF]; simp [e0, e1, e2, e3]
  have hdet := jac_ne_zero F hF hsm x y p q hli' hst
  simp only [polarJacDet] at hdet
  rw [polar3_comm13 F hF x x, polar3_comm13 F hF y y] at *
  simp only [polar3_lin1 F hF] at d0 d1 d2 d3
  rw [polar3_comm23 F hF p y x, polar3_comm23 F hF q y x] at d2
  refine Matrix.eq_zero_of_mulVec_eq_zero hdet ?_
  ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  · linear_combination d0
  · linear_combination d1
  · linear_combination d2
  · linear_combination d3

/-- In one chart (the closed unit polydisc), there are finitely many zeros of `Φ`. -/
lemma chart_finite (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (hsm : IsSmoothCubic F)
    (v0 v1 p q : Fin 4 → ℂ) (hli : LinearIndependent ℂ ![v0, v1, p, q]) :
    {a : Fin 4 → ℂ | Φ F v0 v1 p q a = 0 ∧ ‖a‖ ≤ 1}.Finite := by
  have hdiff := differentiable_Φ F v0 v1 p q
  apply IsCompact.finite
  · have : {a : Fin 4 → ℂ | Φ F v0 v1 p q a = 0 ∧ ‖a‖ ≤ 1}
        = Φ F v0 v1 p q ⁻¹' {0} ∩ Metric.closedBall 0 1 := by
      ext a; simp
    rw [this]
    exact (isCompact_closedBall 0 1).inter_left (isClosed_singleton.preimage hdiff.continuous)
  · rw [isDiscrete_iff_nhdsNE]
    rintro a ⟨ha, -⟩
    rw [Filter.inf_principal_eq_bot]
    have hf := (hdiff a).hasFDerivAt
    have hinj : Function.Injective (fderiv ℂ (Φ F v0 v1 p q) a) := by
      rw [injective_iff_map_eq_zero]
      intro h hh
      have hline : HasDerivAt (fun ε : ℂ => a + ε • h) h 0 := by
        simpa using ((hasDerivAt_id (0:ℂ)).smul_const h).const_add a
      have h1 := hf.comp_hasDerivAt_of_eq (0:ℂ) hline (by simp)
      have h2 := hasDerivAt_Φ F hF v0 v1 p q a h
      have := h2.unique h1
      exact dΦ_inj F hF hsm v0 v1 p q hli a ha h (by rw [this]; exact hh)
    obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz
      (fderiv ℂ (Φ F v0 v1 p q) a : (Fin 4 → ℂ) →ₗ[ℂ] (Fin 4 → ℂ))).mp hinj
    have hev := hf.eventually_ne (c := 0) ⟨K, hK⟩
    filter_upwards [hev] with z hz
    simp [hz]

/-! ### Every plane is in a normalised chart -/

/-- Standard basis vector. -/
noncomputable abbrev e (i : Fin 4) : Fin 4 → ℂ := Pi.single i 1

lemma exists_compl (i j : Fin 4) (hij : i ≠ j) :
    ∃ k l : Fin 4, i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by
  revert i j; decide

lemma fin4_cases (i j k l n : Fin 4) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : i ≠ l) (h4 : j ≠ k)
    (h5 : j ≠ l) (h6 : k ≠ l) : n = i ∨ n = j ∨ n = k ∨ n = l := by
  revert i j k l n; decide

lemma cover (W : Submodule ℂ (Fin 4 → ℂ)) (hW : Module.finrank ℂ W = 2) :
    ∃ i j k l : Fin 4, (i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l) ∧
      ∃ a : Fin 4 → ℂ, ‖a‖ ≤ 1 ∧ chu0 (e i) (e k) (e l) a ∈ W ∧ chu1 (e j) (e k) (e l) a ∈ W ∧
        W = Submodule.span ℂ (Set.range ![chu0 (e i) (e k) (e l) a, chu1 (e j) (e k) (e l) a]) := by
  let b := Module.finBasisOfFinrankEq ℂ W hW
  set w0 : Fin 4 → ℂ := (b 0 : Fin 4 → ℂ) with hw0
  set w1 : Fin 4 → ℂ := (b 1 : Fin 4 → ℂ) with hw1
  have hw0W : w0 ∈ W := (b 0).2
  have hw1W : w1 ∈ W := (b 1).2
  have hli : LinearIndependent ℂ ![w0, w1] := by
    have hb : LinearIndependent ℂ ![b 0, b 1] := by
      convert b.linearIndependent using 1; funext n; fin_cases n <;> rfl
    rw [LinearIndependent.pair_iff] at hb ⊢
    intro s t hst
    exact hb s t (Subtype.ext (by simpa [hw0, hw1] using hst))
  let m : Fin 4 → Fin 4 → ℂ := fun i j => w0 i * w1 j - w0 j * w1 i
  have hex : ∃ i j, m i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hw0ne : w0 ≠ 0 := hli.ne_zero 0
    obtain ⟨i, hi⟩ : ∃ i, w0 i ≠ 0 := by
      by_contra h; push Not at h; exact hw0ne (funext h)
    have := LinearIndependent.pair_iff.mp hli (-w1 i) (w0 i) (by
      ext n; have := hcon i n; simp [m] at this ⊢; linear_combination this)
    exact hi this.2
  obtain ⟨⟨i, j⟩, -, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun ij : Fin 4 × Fin 4 => ‖m ij.1 ij.2‖) Finset.univ_nonempty
  simp only [Finset.mem_univ, true_implies, Prod.forall] at hmax
  set μ := m i j with hμ
  have hμ0 : μ ≠ 0 := by
    obtain ⟨i', j', h'⟩ := hex
    intro h0
    have := hmax i' j'
    rw [h0, norm_zero] at this
    exact h' (norm_le_zero_iff.mp this)
  have hij : i ≠ j := by rintro rfl; apply hμ0; simp [hμ, m]
  obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := exists_compl i j hij
  set u0 : Fin 4 → ℂ := μ⁻¹ • (w1 j • w0 - w0 j • w1) with hu0
  set u1 : Fin 4 → ℂ := μ⁻¹ • (w0 i • w1 - w1 i • w0) with hu1
  have hu0n : ∀ n, u0 n = μ⁻¹ * m n j := by intro n; simp only [hu0, m, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hu1n : ∀ n, u1 n = μ⁻¹ * m i n := by intro n; simp only [hu1, m, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hu0W : u0 ∈ W := W.smul_mem _ (W.sub_mem (W.smul_mem _ hw0W) (W.smul_mem _ hw1W))
  have hu1W : u1 ∈ W := W.smul_mem _ (W.sub_mem (W.smul_mem _ hw1W) (W.smul_mem _ hw0W))
  have hmm : ∀ n, m n n = 0 := by intro n; simp only [m]; ring
  have hanti : ∀ n n', m n n' = - m n' n := by intro n n'; simp only [m]; ring
  have hμμ : μ⁻¹ * μ = 1 := inv_mul_cancel₀ hμ0
  have hμμ' : μ⁻¹ * m i j = 1 := hμμ
  let a : Fin 4 → ℂ := ![u0 k, u0 l, u1 k, u1 l]
  have hc0 : chu0 (e i) (e k) (e l) a = u0 := by
    ext n
    rcases fin4_cases i j k l n hij hik hil hjk hjl hkl with h | h | h | h <;> rw [h]
    · simp [chu0, a, Pi.single_apply, hik.symm, hil.symm, hu0n, hμμ']
    · simp [chu0, a, Pi.single_apply, hij.symm, hjk, hjl, hu0n, hmm]
    · simp [chu0, a, Pi.single_apply, hik, hkl]
    · simp [chu0, a, Pi.single_apply, hil, hkl.symm]
  have hc1 : chu1 (e j) (e k) (e l) a = u1 := by
    ext n
    rcases fin4_cases i j k l n hij hik hil hjk hjl hkl with h | h | h | h <;> rw [h]
    · simp [chu1, a, Pi.single_apply, hij, hik.symm, hil.symm, hu1n, hmm]
    · simp [chu1, a, Pi.single_apply, hjk.symm, hjl.symm, hu1n, hμμ']
    · simp [chu1, a, Pi.single_apply, hjk, hkl]
    · simp [chu1, a, Pi.single_apply, hjl, hkl.symm]
  have hbd : ∀ n n', ‖μ⁻¹ * m n n'‖ ≤ 1 := by
    intro n n'
    rw [norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hμ0), mul_one]
    exact hmax n n'
  refine ⟨i, j, k, l, ⟨hij, hik, hil, hjk, hjl, hkl⟩, a, ?_, ?_, ?_, ?_⟩
  · rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro n; fin_cases n
    · show ‖u0 k‖ ≤ 1; rw [hu0n]; exact hbd _ _
    · show ‖u0 l‖ ≤ 1; rw [hu0n]; exact hbd _ _
    · show ‖u1 k‖ ≤ 1; rw [hu1n]; exact hbd _ _
    · show ‖u1 l‖ ≤ 1; rw [hu1n]; exact hbd _ _
  · rw [hc0]; exact hu0W
  · rw [hc1]; exact hu1W
  · rw [hc0, hc1]
    have hli2 : LinearIndependent ℂ ![u0, u1] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrFun hst i
      have h2 := congrFun hst j
      simp [hu0n, hu1n, hmm, hμμ'] at h1 h2
      exact ⟨h1, h2⟩
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨n, rfl⟩
      fin_cases n
      · exact hu0W
      · exact hu1W
    · rw [finrank_span_eq_card hli2, hW]; simp

lemma polar3_of_mem (F : MvPolynomial (Fin 4) ℂ) (W : Submodule ℂ (Fin 4 → ℂ))
    (hWF : ∀ x ∈ W, eval x F = 0) (x y z : Fin 4 → ℂ) (hx : x ∈ W) (hy : y ∈ W) (hz : z ∈ W) :
    polar3 F x y z = 0 := by
  simp only [polar3]
  rw [hWF _ (W.add_mem (W.add_mem hx hy) hz), hWF _ (W.add_mem hx hy), hWF _ (W.add_mem hy hz),
    hWF _ (W.add_mem hz hx), hWF _ hx, hWF _ hy, hWF _ hz]
  ring

lemma li_std (i j k l : Fin 4) (h1 : i ≠ j) (h2 : i ≠ k) (h3 : i ≠ l) (h4 : j ≠ k)
    (h5 : j ≠ l) (h6 : k ≠ l) : LinearIndependent ℂ ![e i, e j, e k, e l] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hi := congrFun hg i
  have hj := congrFun hg j
  have hk := congrFun hg k
  have hl := congrFun hg l
  simp [Fin.sum_univ_four, Pi.single_apply, h1, h2, h3, h4, h5, h6, h1.symm, h2.symm, h3.symm,
    h4.symm, h5.symm, h6.symm] at hi hj hk hl
  intro n; fin_cases n <;> assumption

end LFAux

open CubicSurface27 LFAux in
theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (hsm : IsSmoothCubic F) :
    (linesOf F).Finite := by
  let S : Set (Fin 4 × Fin 4 × Fin 4 × Fin 4) := {c | c.1 ≠ c.2.1 ∧ c.1 ≠ c.2.2.1 ∧
    c.1 ≠ c.2.2.2 ∧ c.2.1 ≠ c.2.2.1 ∧ c.2.1 ≠ c.2.2.2 ∧ c.2.2.1 ≠ c.2.2.2}
  let img : (Fin 4 × Fin 4 × Fin 4 × Fin 4) → Set (Submodule ℂ (Fin 4 → ℂ)) := fun c =>
    (fun a => Submodule.span ℂ (Set.range ![chu0 (e c.1) (e c.2.2.1) (e c.2.2.2) a,
      chu1 (e c.2.1) (e c.2.2.1) (e c.2.2.2) a])) ''
      {a | Φ F (e c.1) (e c.2.1) (e c.2.2.1) (e c.2.2.2) a = 0 ∧ ‖a‖ ≤ 1}
  have hfin : (⋃ c ∈ S, img c).Finite := by
    refine (Set.toFinite S).biUnion (fun c hc => ?_)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hc
    exact (chart_finite F hF hsm _ _ _ _ (li_std _ _ _ _ h1 h2 h3 h4 h5 h6)).image _
  refine hfin.subset ?_
  intro W hW
  obtain ⟨i, j, k, l, hd, a, ha, h0, h1, hWeq⟩ := cover W hW.1
  refine Set.mem_biUnion (x := (i, j, k, l)) hd ⟨a, ⟨?_, ha⟩, hWeq.symm⟩
  have hWF := hW.2
  ext n; fin_cases n
  · exact hWF _ h0
  · exact polar3_of_mem F W hWF _ _ _ h0 h0 h1
  · exact polar3_of_mem F W hWF _ _ _ h1 h1 h0
  · exact hWF _ h1
