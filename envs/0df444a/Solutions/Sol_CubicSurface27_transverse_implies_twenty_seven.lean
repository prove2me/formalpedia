-- Prove2me | solution 1 for CubicSurface27.transverse_implies_twenty_seven
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-22T10:16:34.15945+00:00
-- url     : https://prove2.me/submissions/50d04e33-6964-46bf-aed4-ea7f83be88f0

import Definitions.Def_cubic_surface_27_layer
import Definitions.Def_cubic_surface_transverse
import Theorems.Thm_CubicSurface27_singular_point_on_line
import Theorems.Thm_CubicSurface27_linesOf_finite
import Theorems.Thm_CubicSurface27_linesOf_finite_to_27

open MvPolynomial

namespace T27SmoothAux

open CubicSurface27

/-! ### Polarization (copied from the accepted proof of `smooth_implies_transverse`) -/

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

/-! ### Completing independent vectors -/

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

/-- A nonzero vector `x` of a 2-dimensional subspace `W` of `ℂ⁴` extends to a basis
`x, v₁, p, q` of `ℂ⁴` with `v₁ ∈ W`. -/
lemma exists_completion (W : Submodule ℂ (Fin 4 → ℂ)) (hW : Module.finrank ℂ W = 2)
    (x : Fin 4 → ℂ) (hxW : x ∈ W) (hx : x ≠ 0) :
    ∃ v1 p q : Fin 4 → ℂ, v1 ∈ W ∧ LinearIndependent ℂ ![x, v1, p, q] := by
  have hle : Submodule.span ℂ (Set.range ![x]) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    simpa using hxW
  have hlt : Submodule.span ℂ (Set.range ![x]) < W := by
    refine lt_of_le_of_ne hle fun h => ?_
    have h1 := finrank_range_le_card (R := ℂ) (b := ![x])
    unfold Set.finrank at h1
    rw [h, hW] at h1
    simp at h1
  obtain ⟨v1, hv1W, hv1⟩ := SetLike.exists_of_lt hlt
  have hi1 : LinearIndependent ℂ ![x] := by
    rw [linearIndependent_unique_iff]
    simpa using hx
  have hi2 : LinearIndependent ℂ (Fin.snoc ![x] v1 : Fin 2 → (Fin 4 → ℂ)) :=
    linearIndependent_finSnoc.2 ⟨hi1, hv1⟩
  obtain ⟨p, hp⟩ := exists_not_mem_span (by norm_num) (Fin.snoc ![x] v1 : Fin 2 → (Fin 4 → ℂ))
  have hi3 := linearIndependent_finSnoc.2 ⟨hi2, hp⟩
  obtain ⟨q, hq⟩ := exists_not_mem_span (by norm_num)
    (Fin.snoc (Fin.snoc ![x] v1 : Fin 2 → (Fin 4 → ℂ)) p : Fin 3 → (Fin 4 → ℂ))
  have hi4 := linearIndependent_finSnoc.2 ⟨hi3, hq⟩
  refine ⟨v1, p, q, hv1W, ?_⟩
  have heq : ![x, v1, p, q] =
      (Fin.snoc (Fin.snoc (Fin.snoc ![x] v1 : Fin 2 → (Fin 4 → ℂ)) p : Fin 3 → (Fin 4 → ℂ)) q :
        Fin 4 → (Fin 4 → ℂ)) := by
    funext i
    fin_cases i <;> simp [Fin.snoc]
  rw [heq]
  exact hi4

/-- Transversality at a line `W` forces `F` to be smooth at every nonzero point of `W`:
at a singular point `x ∈ W` the first row of the Jacobian matrix in the chart `(x, v₁, p, q)`
vanishes. -/
lemma transverse_smooth_on_line (F : MvPolynomial (Fin 4) ℂ) (hF : IsCubicForm F)
    (W : Submodule ℂ (Fin 4 → ℂ)) (hW : W ∈ linesOf F) (hT : IsTransverseZero F W)
    (x : Fin 4 → ℂ) (hxW : x ∈ W) (hx : x ≠ 0) :
    ∃ i : Fin 4, eval x (pderiv i F) ≠ 0 := by
  by_contra h
  push Not at h
  have hB : ∀ u, polar3 F u x x = 0 := by
    intro u
    have := polar3_grad F hF u x
    simp only [h, mul_zero, Finset.sum_const_zero] at this
    linear_combination this / 3
  obtain ⟨v1, p, q, hv1, hli⟩ := exists_completion W hW.1 x hxW hx
  apply hT x v1 p q hxW hv1 hli
  unfold polarJacDet
  simp only [hB]
  apply Matrix.det_eq_zero_of_row_eq_zero 0
  intro j
  fin_cases j <;> simp

end T27SmoothAux

open CubicSurface27

/-- Sketch for `transverse_implies_smooth`: a singular point lies on a line `W` of the surface
(child `singular_point_on_line`), but transversality at `W` makes `F` smooth along `W`. -/
theorem M27.transverse_implies_smooth (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (ht : HasTransverseZeroes F) :
    IsSmoothCubic F := by
  intro x hx hFx
  by_contra h
  push Not at h
  obtain ⟨W, hW, hxW⟩ := CubicSurface27.singular_point_on_line F hF x hx hFx h
  obtain ⟨i, hi⟩ := T27SmoothAux.transverse_smooth_on_line F hF W hW (ht W hW) x hxW hx
  exact hi (h i)

/-- Transversality forces smoothness (a singular point would lie on a line, along which
transversality makes `F` smooth); then `linesOf_finite` and `linesOf_finite_to_27` apply. -/
theorem solution (F : MvPolynomial (Fin 4) ℂ)
    (hF : IsCubicForm F) (ht : HasTransverseZeroes F) :
    (linesOf F).ncard = 27 := by
  have hsm := M27.transverse_implies_smooth F hF ht
  exact linesOf_finite_to_27 F hF hsm (linesOf_finite F hF hsm)
