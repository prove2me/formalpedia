-- Prove2me | solution 1 for CubicSurface27.singular_point_on_line
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T10:10:30.217168+00:00
-- url     : https://prove2.me/submissions/ede7cb63-15bc-4750-a642-da9c67053d77

import Definitions.Def_cubic_surface_27_layer

open MvPolynomial

namespace SPAux

open CubicSurface27

/-! ### Degree-3 monomials are products of three variables
(copied from the accepted proof of `smooth_implies_transverse`) -/

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

/-! ### The quadric of directions at `x` -/

/-- `qs F x y = ∑ xᵢ ∂ᵢF(y)`: for a cubic `F` this is a quadratic form in `y`. -/
noncomputable def qs (F : MvPolynomial (Fin 4) ℂ) (x y : Fin 4 → ℂ) : ℂ :=
  ∑ i, x i * eval y (pderiv i F)

lemma qs_add (F G : MvPolynomial (Fin 4) ℂ) (x y : Fin 4 → ℂ) :
    qs (F + G) x y = qs F x y + qs G x y := by
  simp [qs, map_add, mul_add, Finset.sum_add_distrib]

lemma qs_smul (r : ℂ) (F : MvPolynomial (Fin 4) ℂ) (x y : Fin 4 → ℂ) :
    qs (r • F) x y = r * qs F x y := by
  simp only [qs, Derivation.map_smul, smul_eval, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma qs_eq_eval (F : MvPolynomial (Fin 4) ℂ) (x y : Fin 4 → ℂ) :
    qs F x y = eval y (∑ i, C (x i) * pderiv i F) := by
  simp [qs, map_sum]

/-- Expansion of a cubic along the plane spanned by `x` and `y`. -/
lemma expand_line (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x y : Fin 4 → ℂ)
    (s t : ℂ) :
    eval (s • x + t • y) F = s ^ 3 * eval x F + s ^ 2 * t * qs F y x
      + s * t ^ 2 * qs F x y + t ^ 3 * eval y F := by
  refine cubic_induction (fun F => eval (s • x + t • y) F = s ^ 3 * eval x F
      + s ^ 2 * t * qs F y x + s * t ^ 2 * qs F x y + t ^ 3 * eval y F) ?_ ?_ ?_ ?_ F hF
  · simp [qs]
  · intro F G hF hG
    simp only [map_add, qs_add, hF, hG]; ring
  · intro r F hF
    simp only [smul_eval, qs_smul, hF]; ring
  · intro a b c
    simp [qs, Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite (eval x), apply_ite (eval y), mul_ite,
      Finset.sum_ite_eq]
    ring

/-- `y ↦ qs F x y` is a quadratic form: its expansion on a plane. -/
lemma qs_expand (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x p d : Fin 4 → ℂ)
    (α β : ℂ) :
    qs F x (α • p + β • d) = α ^ 2 * qs F x p
      + α * β * (qs F x (p + d) - qs F x p - qs F x d) + β ^ 2 * qs F x d := by
  refine cubic_induction (fun F => qs F x (α • p + β • d) = α ^ 2 * qs F x p
      + α * β * (qs F x (p + d) - qs F x p - qs F x d) + β ^ 2 * qs F x d)
    ?_ ?_ ?_ ?_ F hF
  · simp [qs]
  · intro F G hF hG
    simp only [qs_add, hF, hG]; ring
  · intro r F hF
    simp only [qs_smul, hF]; ring
  · intro a b c
    simp [qs, Derivation.leibniz, pderiv_X, Pi.single_apply, mul_add, add_mul,
      Finset.sum_add_distrib, apply_ite (eval (α • p + β • d)), apply_ite (eval p),
      apply_ite (eval d), apply_ite (eval (p + d)), mul_ite, Finset.sum_ite_eq]
    ring

lemma qs_hom (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (x d : Fin 4 → ℂ) (l : ℂ) :
    qs F x (l • d) = l ^ 2 * qs F x d := by
  have := qs_expand F hF x 0 d 0 l
  simpa using this

lemma eval_hom (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F) (y : Fin 4 → ℂ) (l : ℂ) :
    eval (l • y) F = l ^ 3 * eval y F := by
  have := expand_line F hF 0 y 0 l
  simpa using this

/-! ### Polynomial functions of one variable -/

def PF (φ : ℂ → ℂ) : Prop := ∃ P : Polynomial ℂ, ∀ u, φ u = P.eval u

lemma PF.const (c : ℂ) : PF (fun _ => c) := ⟨Polynomial.C c, by simp⟩

lemma PF.id : PF (fun u => u) := ⟨Polynomial.X, by simp⟩

lemma PF.add {f g : ℂ → ℂ} (hf : PF f) (hg : PF g) : PF (fun u => f u + g u) := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, by simp [hP, hQ]⟩

lemma PF.sub {f g : ℂ → ℂ} (hf : PF f) (hg : PF g) : PF (fun u => f u - g u) := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  exact ⟨P - Q, by simp [hP, hQ]⟩

lemma PF.mul {f g : ℂ → ℂ} (hf : PF f) (hg : PF g) : PF (fun u => f u * g u) := by
  obtain ⟨P, hP⟩ := hf; obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, by simp [hP, hQ]⟩

lemma PF.congr {f g : ℂ → ℂ} (hf : PF f) (h : ∀ u, f u = g u) : PF g := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨P, fun u => by rw [← h, hP]⟩

lemma pf_eval (P : MvPolynomial (Fin 4) ℂ) (v : ℂ → Fin 4 → ℂ)
    (hv : ∀ i, PF fun u => v u i) : PF fun u => eval (v u) P := by
  induction P using MvPolynomial.induction_on
  · rename_i a; exact (PF.const a).congr (by simp)
  · rename_i p q hp hq; exact (hp.add hq).congr (by simp)
  · rename_i p i hp; exact (hp.mul (hv i)).congr (by simp)

lemma pf_affine (a b : Fin 4 → ℂ) (i : Fin 4) : PF fun u => (u • a + b) i :=
  ((PF.id.mul (PF.const (a i))).add (PF.const (b i))).congr (by simp)

lemma pf_eval_affine (P : MvPolynomial (Fin 4) ℂ) (a b : Fin 4 → ℂ) :
    PF fun u => eval (u • a + b) P :=
  pf_eval P _ (pf_affine a b)

/-- A polynomial function on `ℂ` without zeros is constant. -/
lemma pf_const_of_ne {f : ℂ → ℂ} (hf : PF f) (hne : ∀ u, f u ≠ 0) (u : ℂ) : f u = f 0 := by
  obtain ⟨P, hP⟩ := hf
  have hdeg : P.degree = 0 := by
    by_contra hd
    obtain ⟨r, hr⟩ := IsAlgClosed.exists_root P hd
    exact hne r (by rw [hP]; exact hr)
  rw [hP, hP, Polynomial.eq_C_of_degree_eq_zero hdeg]
  simp

/-- A homogeneous function of degree `n ≥ 1` on `ℂ²`, polynomial in both affine charts,
has a nontrivial zero. -/
lemma binary_root (n : ℕ) (hn : n ≠ 0) (φ : ℂ → ℂ → ℂ)
    (hhom : ∀ l s t, φ (l * s) (l * t) = l ^ n * φ s t)
    (h1 : PF fun u => φ u 1) (h2 : PF fun u => φ 1 u) :
    ∃ s t, (s ≠ 0 ∨ t ≠ 0) ∧ φ s t = 0 := by
  by_contra H
  push Not at H
  have c1 := pf_const_of_ne h1 (fun u => H u 1 (Or.inr one_ne_zero))
  have c2 := pf_const_of_ne h2 (fun u => H 1 u (Or.inl one_ne_zero))
  have e1 : φ 1 0 = φ 0 1 := by rw [← c2 1, c1 1]
  have e2 : φ 1 0 = 2 ^ n * φ 0 1 := by
    rw [← c2 2, ← c1 (1 / 2)]
    have := hhom 2 (1 / 2) 1
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, mul_one] at this
    exact this
  have hne : φ 0 1 ≠ 0 := H 0 1 (Or.inr one_ne_zero)
  have h2n : (2 : ℂ) ^ n = 1 := by
    have : (2 ^ n - 1) * φ 0 1 = 0 := by linear_combination -e2 + e1
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h hne
  have : (2 : ℕ) ^ n = 1 := by exact_mod_cast h2n
  rw [Nat.pow_eq_one] at this
  omega

/-! ### Linear algebra -/

lemma li_zero {x a b c : Fin 4 → ℂ} (h : LinearIndependent ℂ ![x, a, b, c]) {α β γ : ℂ}
    (hz : α • a + β • b + γ • c = 0) : α = 0 ∧ β = 0 ∧ γ = 0 := by
  have := Fintype.linearIndependent_iff.mp h ![0, α, β, γ]
    (by simpa [Fin.sum_univ_four, add_assoc] using hz)
  exact ⟨this 1, this 2, this 3⟩

lemma li_pair {x a b c : Fin 4 → ℂ} (h : LinearIndependent ℂ ![x, a, b, c]) {α β γ : ℂ}
    (hne : α • a + β • b + γ • c ≠ 0) : LinearIndependent ℂ ![x, α • a + β • b + γ • c] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := Fintype.linearIndependent_iff.mp h ![s, t * α, t * β, t * γ] (by
    rw [← hst]; simp [Fin.sum_univ_four, smul_add, mul_smul, add_assoc])
  refine ⟨this 0, ?_⟩
  by_contra ht
  apply hne
  have h1 : α = 0 := by simpa [ht] using this 1
  have h2 : β = 0 := by simpa [ht] using this 2
  have h3 : γ = 0 := by simpa [ht] using this 3
  simp [h1, h2, h3]

lemma exists_not_mem_span {n : ℕ} (hn : n < 4) (v : Fin n → (Fin 4 → ℂ)) :
    ∃ p, p ∉ Submodule.span ℂ (Set.range v) := by
  by_contra h
  push Not at h
  have htop : Submodule.span ℂ (Set.range v) = ⊤ := eq_top_iff.2 (fun p _ => h p)
  have h1 := finrank_range_le_card (R := ℂ) (b := v)
  unfold Set.finrank at h1
  rw [htop, finrank_top, Module.finrank_fin_fun] at h1
  simp at h1
  omega

lemma complete2 (x p : Fin 4 → ℂ) (h : LinearIndependent ℂ ![x, p]) :
    ∃ c d : Fin 4 → ℂ, LinearIndependent ℂ ![x, p, c, d] := by
  have hi2 : LinearIndependent ℂ (Fin.snoc ![x] p : Fin 2 → (Fin 4 → ℂ)) := by
    have heq : (Fin.snoc ![x] p : Fin 2 → (Fin 4 → ℂ)) = ![x, p] := by
      funext i; fin_cases i <;> simp [Fin.snoc]
    rw [heq]; exact h
  obtain ⟨c, hc⟩ := exists_not_mem_span (by norm_num) (Fin.snoc ![x] p : Fin 2 → (Fin 4 → ℂ))
  have hi3 := linearIndependent_finSnoc.2 ⟨hi2, hc⟩
  obtain ⟨d, hd⟩ := exists_not_mem_span (by norm_num)
    (Fin.snoc (Fin.snoc ![x] p : Fin 2 → (Fin 4 → ℂ)) c : Fin 3 → (Fin 4 → ℂ))
  have hi4 := linearIndependent_finSnoc.2 ⟨hi3, hd⟩
  refine ⟨c, d, ?_⟩
  have heq : ![x, p, c, d] =
      (Fin.snoc (Fin.snoc (Fin.snoc ![x] p : Fin 2 → (Fin 4 → ℂ)) c : Fin 3 → (Fin 4 → ℂ)) d :
        Fin 4 → (Fin 4 → ℂ)) := by
    funext i
    fin_cases i <;> simp [Fin.snoc]
  rw [heq]
  exact hi4

lemma complete1 (x : Fin 4 → ℂ) (hx : x ≠ 0) :
    ∃ a b c : Fin 4 → ℂ, LinearIndependent ℂ ![x, a, b, c] := by
  have hi1 : LinearIndependent ℂ ![x] := by
    rw [linearIndependent_unique_iff]
    simpa using hx
  obtain ⟨a, ha⟩ := exists_not_mem_span (by norm_num) ![x]
  have hi2 := linearIndependent_finSnoc.2 ⟨hi1, ha⟩
  have heq : (Fin.snoc ![x] a : Fin 2 → (Fin 4 → ℂ)) = ![x, a] := by
    funext i; fin_cases i <;> simp [Fin.snoc]
  rw [heq] at hi2
  obtain ⟨b, c, h⟩ := complete2 x a hi2
  exact ⟨a, b, c, h⟩

/-! ### The final step: a common zero of the quadric and the cubic gives a line -/

lemma line_of_zero (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (x : Fin 4 → ℂ) (hFx : eval x F = 0) (hsing : ∀ i : Fin 4, eval x (pderiv i F) = 0)
    (y : Fin 4 → ℂ) (hli : LinearIndependent ℂ ![x, y]) (hq : qs F x y = 0)
    (hc : eval y F = 0) : ∃ W ∈ linesOf F, x ∈ W := by
  refine ⟨Submodule.span ℂ (Set.range ![x, y]), ⟨?_, ?_⟩, ?_⟩
  · rw [finrank_span_eq_card hli]; simp
  · intro z hz
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hz
    have hq0 : qs F y x = 0 := by simp [qs, hsing]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [expand_line F hF, hFx, hq0, hq, hc]; ring
  · exact Submodule.subset_span ⟨0, rfl⟩

end SPAux

open CubicSurface27 SPAux in
theorem solution (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (x : Fin 4 → ℂ) (hx : x ≠ 0) (hFx : MvPolynomial.eval x F = 0)
    (hsing : ∀ i : Fin 4, MvPolynomial.eval x (MvPolynomial.pderiv i F) = 0) :
    ∃ W ∈ linesOf F, x ∈ W := by
  have hqP : ∀ y, qs F x y = eval y (∑ i, C (x i) * pderiv i F) := fun y => qs_eq_eval F x y
  -- Step 1: a nonzero direction `p` (independent of `x`) on the quadric.
  obtain ⟨a, b, c, habc⟩ := complete1 x hx
  obtain ⟨s, t, hst, hpq⟩ := binary_root 2 two_ne_zero (fun s t => qs F x (s • a + t • b))
    (by
      intro l s t
      simp only [mul_smul, ← smul_add]
      exact qs_hom F hF x _ l)
    ((pf_eval_affine (∑ i, C (x i) * pderiv i F) a b).congr (fun u => by simp [hqP]))
    ((pf_eval_affine (∑ i, C (x i) * pderiv i F) b a).congr (fun u => by simp [hqP, add_comm]))
  set p := s • a + t • b with hpdef
  have hp3 : p = s • a + t • b + (0 : ℂ) • c := by simp [hpdef]
  have hp0 : p ≠ 0 := by
    intro h0
    rw [hp3] at h0
    obtain ⟨h1, h2, -⟩ := li_zero habc h0
    rcases hst with h | h <;> contradiction
  have hxp : LinearIndependent ℂ ![x, p] := by
    rw [hp3] at hp0 ⊢; exact li_pair habc hp0
  -- Step 2: complete `x, p` to a basis and parametrize the conic from `p`.
  obtain ⟨d1, d2, hli⟩ := complete2 x p hxp
  let Y : (Fin 4 → ℂ) → (Fin 4 → ℂ) := fun d => qs F x d • p - (qs F x (p + d) - qs F x d) • d
  have hYhom : ∀ (l : ℂ) d, Y (l • d) = l ^ 2 • Y d := by
    intro l d
    have e1 : qs F x (l • d) = l ^ 2 * qs F x d := qs_hom F hF x d l
    have e2 : qs F x (p + l • d) = l * (qs F x (p + d) - qs F x d) + l ^ 2 * qs F x d := by
      have := qs_expand F hF x p d 1 l
      simp only [one_smul, one_pow, one_mul] at this
      rw [this]; rw [hpq]; ring
    simp only [Y, e1, e2]
    ext i; simp; ring
  have pfq : ∀ a b : Fin 4 → ℂ, PF fun u => qs F x (u • a + b) :=
    fun a b => (pf_eval_affine (∑ i, C (x i) * pderiv i F) a b).congr (fun u => by simp [hqP])
  have pfY : ∀ a b : Fin 4 → ℂ, PF fun u => eval (Y (u • a + b)) F := by
    intro a b
    refine pf_eval F _ (fun i => ?_)
    refine (((pfq a b).mul (PF.const (p i))).sub
      (((pfq a (p + b)).sub (pfq a b)).mul (pf_affine a b i))).congr (fun u => ?_)
    simp only [Y, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show p + (u • a + b) = u • a + (p + b) by abel]
  obtain ⟨s', t', hst', hY⟩ := binary_root 6 (by norm_num)
    (fun s t => eval (Y (s • d1 + t • d2)) F)
    (by
      intro l s t
      simp only [mul_smul, ← smul_add, hYhom, eval_hom F hF]
      ring)
    ((pfY d1 d2).congr (fun u => by simp))
    ((pfY d2 d1).congr (fun u => by simp [add_comm]))
  set d := s' • d1 + t' • d2 with hddef
  set cc := qs F x (p + d) - qs F x d with hcc
  have hYd : Y d = qs F x d • p + (-(cc * s')) • d1 + (-(cc * t')) • d2 := by
    simp only [Y, hddef, hcc]; ext i; simp; ring
  by_cases hY0 : Y d = 0
  · -- the line through `p` in direction `d` lies on the quadric
    rw [hYd] at hY0
    obtain ⟨hqd, h1, h2⟩ := li_zero hli hY0
    have hcc0 : cc = 0 := by
      rcases hst' with h | h
      · have : cc * s' = 0 := by simpa using h1
        exact (mul_eq_zero.mp this).resolve_right h
      · have : cc * t' = 0 := by simpa using h2
        exact (mul_eq_zero.mp this).resolve_right h
    obtain ⟨α, β, hαβ, hF0⟩ := binary_root 3 (by norm_num)
      (fun α β => eval (α • p + β • d) F)
      (by
        intro l α β
        simp only [mul_smul, ← smul_add, eval_hom F hF])
      ((pf_eval_affine F p d).congr (fun u => by simp))
      ((pf_eval_affine F d p).congr (fun u => by simp [add_comm]))
    have hy : α • p + β • d = α • p + (β * s') • d1 + (β * t') • d2 := by
      simp only [hddef]; ext i; simp; ring
    have hy0 : α • p + β • d ≠ 0 := by
      rw [hy]; intro h0
      obtain ⟨hα, h1', h2'⟩ := li_zero hli h0
      rcases hαβ with h | h
      · exact h hα
      · rcases hst' with h' | h'
        · exact h ((mul_eq_zero.mp h1').resolve_right h')
        · exact h ((mul_eq_zero.mp h2').resolve_right h')
    have hli2 : LinearIndependent ℂ ![x, α • p + β • d] := by
      rw [hy] at hy0 ⊢; exact li_pair hli hy0
    refine line_of_zero F hF x hFx hsing _ hli2 ?_ hF0
    have := qs_expand F hF x p d α β
    rw [this]
    rw [hpq, hqd]
    have : qs F x (p + d) = 0 := by rw [hcc, hqd] at hcc0; simpa using hcc0
    rw [this]; ring
  · -- the second intersection point `Y d` of the line with the conic
    have hli2 : LinearIndependent ℂ ![x, Y d] := by
      rw [hYd] at hY0 ⊢; exact li_pair hli hY0
    refine line_of_zero F hF x hFx hsing _ hli2 ?_ hY
    have hYd' : Y d = qs F x d • p + (-cc) • d := by
      simp only [Y, hcc, neg_smul, ← sub_eq_add_neg]
    rw [hYd']
    rw [qs_expand F hF x p d]
    rw [hpq, hcc]; ring
