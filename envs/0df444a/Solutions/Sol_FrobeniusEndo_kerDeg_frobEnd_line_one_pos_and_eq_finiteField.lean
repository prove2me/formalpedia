-- Prove2me | solution 1 for FrobeniusEndo.kerDeg_frobEnd_line_one_pos_and_eq_finiteField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/b3525e39-18a8-5b77-a80f-cb6bfdafe8e9

import Definitions.Def_EllipticCurve_FrobeniusEndo
import Theorems.Thm_WeierstrassCurve_Affine_Point_card_ker_eq_max_natDegree
import Theorems.Thm_WeierstrassCurve_Affine_Point_natDegree_parallelogram_law
import Theorems.Thm_FrobeniusEndo_exists_x_linePencil_frobEnd_mul_collision_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_zsmul_x_mul_psi_sq
import Theorems.Thm_WeierstrassCurve_Affine_Point_smul_some_eq_zero_iff
import Theorems.Thm_WeierstrassCurve_isCoprime_Phi_PsiSq
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_finiteField
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

p2m_open "Polynomial WeierstrassCurve~evalEval_ψ_sq~evalEval_φ WeierstrassCurve.Affine WeierstrassCurve.Affine.Point FrobeniusEndo"

open scoped Polynomial.Bivariate

namespace KerDegFrobLineFiniteField

section Wronskian

variable {k : Type*} [Field k]

theorem wronskian_ne_zero_of_natDegree_eq_succ {u v : k[X]} (hv : v ≠ 0)
    (hdeg : u.natDegree = v.natDegree + 1) :
    derivative u * v - u * derivative v ≠ 0 := by
  set e := v.natDegree with he
  have hu : u ≠ 0 := by
    intro h0
    rw [h0, natDegree_zero] at hdeg
    omega

  have h1 : (derivative u * v).coeff (e + e) = u.coeff (e + 1) * (e + 1) * v.coeff e := by
    have hdu : (derivative u).natDegree ≤ e := by
      have := natDegree_derivative_le u
      omega
    rw [coeff_mul_add_eq_of_natDegree_le hdu le_rfl, coeff_derivative]

  have h2 : (u * derivative v).coeff (e + e) = u.coeff (e + 1) * (v.coeff e * e) := by
    rcases Nat.eq_zero_or_pos e with he0 | hepos
    ·
      have h00 : v.natDegree = 0 := by rw [← he]; exact he0
      have hv' : derivative v = 0 := by
        rw [eq_C_of_natDegree_eq_zero h00, derivative_C]
      rw [hv', mul_zero, coeff_zero, he0, Nat.cast_zero, mul_zero, mul_zero]
    · obtain ⟨e', he'⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
      have hdv : (derivative v).natDegree ≤ e' := by
        have := natDegree_derivative_le v
        omega
      have hsplit : e + e = (e + 1) + e' := by omega
      rw [hsplit, coeff_mul_add_eq_of_natDegree_le (le_of_eq hdeg) hdv, coeff_derivative, ← he']
      rw [he']
      push_cast
      ring
  intro h0
  have h := congrArg (fun p : k[X] => p.coeff (e + e)) h0
  simp only [coeff_sub, coeff_zero, h1, h2] at h
  have hlead : u.coeff (e + 1) * v.coeff e = 0 := by linear_combination h
  rcases mul_eq_zero.mp hlead with hcu | hcv
  · exact (leadingCoeff_ne_zero.mpr hu) (by rw [leadingCoeff, hdeg]; exact hcu)
  · exact (leadingCoeff_ne_zero.mpr hv) hcv

end Wronskian

section Finiteness

variable {k : Type*} [Field k] {W : WeierstrassCurve k}

lemma finite_setOf_X_eq (x₀ : k) :
    {P : W.toAffine.Point | ∃ y : k, ∃ h : W.toAffine.Nonsingular x₀ y,
      P = Point.some x₀ y h}.Finite := by
  have hyfin : {y : k | W.toAffine.Nonsingular x₀ y}.Finite := by
    by_cases hne : ∃ b : k, W.toAffine.Nonsingular x₀ b
    · obtain ⟨b, hb⟩ := hne
      refine Set.Finite.subset
        ((Set.finite_singleton (W.toAffine.negY x₀ b)).insert b) (fun y hy => ?_)
      have hyns : W.toAffine.Nonsingular x₀ y := hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      exact Y_eq_of_X_eq hyns.left hb.left rfl
    · exact Set.Finite.subset Set.finite_empty (fun y hy => absurd ⟨y, hy⟩ hne)
  haveI : Finite {y : k | W.toAffine.Nonsingular x₀ y} := hyfin.to_subtype
  refine Set.Finite.subset (Set.finite_range
    (fun z : {y : k | W.toAffine.Nonsingular x₀ y} =>
      (Point.some x₀ z.1 z.2 : W.toAffine.Point))) ?_
  rintro P ⟨y, hns, rfl⟩
  exact ⟨⟨y, hns⟩, rfl⟩

lemma finite_setOf_X_mem {T : Set k} (hT : T.Finite) :
    {P : W.toAffine.Point | ∃ x ∈ T, ∃ y : k, ∃ h : W.toAffine.Nonsingular x y,
      P = Point.some x y h}.Finite := by
  refine Set.Finite.subset (hT.biUnion (fun x₀ _ => finite_setOf_X_eq (W := W) x₀)) ?_
  rintro P ⟨x, hxT, y, h, rfl⟩
  exact Set.mem_biUnion hxT ⟨y, h, rfl⟩

end Finiteness

section Reduced

variable {k : Type*} [Field k]

theorem exists_reduced_pair (p : k[X]) {q : k[X]} (hq : q ≠ 0) :
    ∃ g h : k[X], IsCoprime g h ∧ h ≠ 0 ∧ g * q = p * h ∧
      (p ≠ 0 → g ≠ 0 ∧ g.natDegree + q.natDegree = p.natDegree + h.natDegree) := by
  set r : RatFunc k := algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q with hr
  refine ⟨r.num, r.denom, RatFunc.isCoprime_num_denom r, RatFunc.denom_ne_zero r,
    (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hr, fun hp => ?_⟩
  have hid : r.num * q = p * r.denom := (RatFunc.num_mul_eq_mul_denom_iff hq).mpr hr
  have hr0 : r ≠ 0 := by
    rw [hr]
    exact div_ne_zero (RatFunc.algebraMap_ne_zero hp) (RatFunc.algebraMap_ne_zero hq)
  have hnum : r.num ≠ 0 := RatFunc.num_ne_zero hr0
  refine ⟨hnum, ?_⟩
  have h := congrArg Polynomial.natDegree hid
  rwa [natDegree_mul hnum hq, natDegree_mul hp (RatFunc.denom_ne_zero r)] at h

end Reduced

section Solver

theorem solver (d : ℤ → ℤ) (q a : ℤ) (good : ℤ → Prop) (h0 : d 0 = q) (h1 : d 1 = 1 - a + q)
    (hg0 : good 0) (hg1 : good 1) (hgood : ∀ n : ℤ, good n ∨ good (n - 1))
    (R1 : ∀ n : ℤ, good n → d (n + 1) + d (n - 1) = 2 * d n + 2)
    (R2 : ∀ n : ℤ, good n → d (n + 2) + d (n - 2) = 2 * d n + 8) :
    ∀ n : ℕ, d n = (n : ℤ) ^ 2 - a * n + q := by

  have hm1 : d (-1) = 1 + a + q := by
    have h := R1 0 hg0
    norm_num at h
    rw [h0, h1] at h
    linear_combination h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · simp [h0]
      · simp [h1]
    rcases Nat.lt_or_ge n 4 with hn4 | hn4
    · interval_cases n
      ·
        have h := R1 1 hg1
        have e0 := ih 0 (by norm_num)
        have e1 := ih 1 (by norm_num)
        norm_num at h e0 e1 ⊢
        linear_combination h + 2 * e1 - e0
      ·
        rcases hgood 2 with hg | hg
        · have h := R1 2 hg
          have e1 := ih 1 (by norm_num)
          have e2 := ih 2 (by norm_num)
          norm_num at h e1 e2 ⊢
          linear_combination h + 2 * e2 - e1
        · norm_num at hg
          have h := R2 1 hg
          have e1 := ih 1 (by norm_num)
          norm_num at h e1 ⊢
          rw [hm1] at h
          linear_combination h + 2 * e1
    ·
      have key : ∀ j : ℕ, j < n → d (j : ℤ) = (j : ℤ) ^ 2 - a * j + q := fun j hj => ih j hj
      rcases hgood ((n : ℤ) - 1) with hg | hg
      · have h := R1 ((n : ℤ) - 1) hg
        have e1 := key (n - 1) (by omega)
        have e2 := key (n - 2) (by omega)
        have c1 : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
        have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
        rw [c1] at e1
        rw [c2] at e2
        rw [show (n : ℤ) - 1 + 1 = n by ring, show (n : ℤ) - 1 - 1 = (n : ℤ) - 2 by ring] at h
        linear_combination h + 2 * e1 - e2
      · rw [show (n : ℤ) - 1 - 1 = (n : ℤ) - 2 by ring] at hg
        have h := R2 ((n : ℤ) - 2) hg
        have e2 := key (n - 2) (by omega)
        have e4 := key (n - 4) (by omega)
        have c2 : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
        have c4 : ((n - 4 : ℕ) : ℤ) = (n : ℤ) - 4 := by omega
        rw [c2] at e2
        rw [c4] at e4
        rw [show (n : ℤ) - 2 + 2 = n by ring, show (n : ℤ) - 2 - 2 = (n : ℤ) - 4 by ring] at h
        linear_combination h + 2 * e2 - e4

end Solver

section Curve

variable {k : Type*} [Field k] {W : WeierstrassCurve k}

lemma evalEval_eq_of_mk_eq {p p' : k[X][Y]}
    (hmk : Affine.CoordinateRing.mk W p = Affine.CoordinateRing.mk W p') {x y : k}
    (h : W.toAffine.Equation x y) : p.evalEval x y = p'.evalEval x y := by
  obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : W.toAffine.polynomial.evalEval x y = 0 := h
  have h1 : (p - p').evalEval x y = 0 := by
    rw [hr, evalEval_mul, h0, zero_mul]
  rwa [evalEval_sub, sub_eq_zero] at h1

lemma evalEval_ψ_sq {x y : k} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : Affine.CoordinateRing.mk W (W.ψ n ^ 2) = Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, Affine.CoordinateRing.mk_ψ, Affine.CoordinateRing.mk_Ψ_sq]
  have h1 := evalEval_eq_of_mk_eq hmk h
  rwa [evalEval_pow, evalEval_C] at h1

lemma evalEval_φ {x y : k} (h : W.toAffine.Equation x y) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have h1 := evalEval_eq_of_mk_eq (Affine.CoordinateRing.mk_φ (W := W) n) h
  rwa [evalEval_C] at h1

lemma exists_nonsingular [IsAlgClosed k] [W.IsElliptic] (x : k) :
    ∃ y : k, W.toAffine.Nonsingular x y := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (W.a₁ * x + W.a₃) * X +
      C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)))
    (natDegree_pos_iff_degree_pos.mp (by rw [natDegree_quadratic one_ne_zero]; norm_num)).ne'
  refine ⟨y, (equation_iff_nonsingular (W := W)).mp ((W.toAffine.equation_iff x y).mpr ?_)⟩
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X, one_mul] at hy
  linear_combination hy

lemma zsmul_x_mul_ΨSq [DecidableEq k] [W.IsElliptic] (n : ℤ) {x y : k}
    (h : W.toAffine.Nonsingular x y) {x' y' : k} (h' : W.toAffine.Nonsingular x' y')
    (hn : n • Point.some x y h = Point.some x' y' h') :
    x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  have key := WeierstrassCurve.Affine.Point.zsmul_x_mul_psi_sq W n h h' hn
  rwa [evalEval_ψ_sq h.left, evalEval_φ h.left] at key

lemma ΨSq_eval_eq_zero_of_zsmul_eq_zero [DecidableEq k] (n : ℤ) {x y : k}
    (h : W.toAffine.Nonsingular x y) (h0 : n • Point.some x y h = 0) :
    (W.ΨSq n).eval x = 0 := by
  rw [← evalEval_ψ_sq h.left n,
    (WeierstrassCurve.Affine.Point.smul_some_eq_zero_iff W h n).mp h0, zero_pow two_ne_zero]

end Curve

section Collision

variable {k : Type*} [Field k] (W : WeierstrassCurve k)

lemma ΨSq_ne_zero_of_isCoprime {n : ℤ} (hn : n ≠ 0) (hcop : IsCoprime (W.Φ n) (W.ΨSq n)) :
    W.ΨSq n ≠ 0 := by
  intro h0
  rw [h0, isCoprime_zero_right] at hcop
  have hdeg := natDegree_eq_zero_of_isUnit hcop
  rw [WeierstrassCurve.natDegree_Φ] at hdeg
  exact hn (Int.natAbs_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hdeg))

lemma collision_eq_zero_iff_aux {q : ℕ} {n : ℤ} (hcop : IsCoprime (W.Φ n) (W.ΨSq n))
    (h0 : W.Φ n - X ^ q * W.ΨSq n = 0) :
    n ≠ 0 ∧ (∃ c : k, c ≠ 0 ∧ W.ΨSq n = C c) ∧ n.natAbs ^ 2 = q := by
  rw [sub_eq_zero] at h0
  have hdvd : W.ΨSq n ∣ W.Φ n := ⟨X ^ q, by rw [h0, mul_comm]⟩
  have hunit : IsUnit (W.ΨSq n) := hcop.isUnit_of_dvd' hdvd (dvd_refl _)
  have hΨdeg : (W.ΨSq n).natDegree = 0 := natDegree_eq_zero_of_isUnit hunit
  have hdeg := congrArg Polynomial.natDegree h0
  rw [WeierstrassCurve.natDegree_Φ, natDegree_mul (pow_ne_zero _ X_ne_zero) hunit.ne_zero,
    natDegree_pow, natDegree_X, mul_one, hΨdeg, add_zero] at hdeg
  refine ⟨fun hn => ?_, ⟨(W.ΨSq n).coeff 0, fun hc => hunit.ne_zero ?_,
    eq_C_of_natDegree_eq_zero hΨdeg⟩, hdeg⟩
  · subst hn
    exact hunit.ne_zero (WeierstrassCurve.ΨSq_zero W)
  · rw [eq_C_of_natDegree_eq_zero hΨdeg, hc, C_0]

lemma natDegree_collision {q : ℕ} (hq : 2 ≤ q) {n : ℤ} (hnk : (n : k) ≠ 0) :
    (W.Φ n - X ^ q * W.ΨSq n).natDegree = q + n.natAbs ^ 2 - 1 := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact hnk (by simp)
  have hn1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
  have hΨ0 : W.ΨSq n ≠ 0 := WeierstrassCurve.ΨSq_ne_zero _ hnk
  have hdeg2 : (X ^ q * W.ΨSq n).natDegree = q + n.natAbs ^ 2 - 1 := by
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) hΨ0, natDegree_pow, natDegree_X, mul_one,
      WeierstrassCurve.natDegree_ΨSq _ hnk]
    omega
  have hlt : (W.Φ n).natDegree < (X ^ q * W.ΨSq n).natDegree := by
    rw [hdeg2, WeierstrassCurve.natDegree_Φ]
    omega
  rw [natDegree_sub_eq_right_of_natDegree_lt hlt, hdeg2]

end Collision

section Bad

variable {k : Type*} [Field k] (W : WeierstrassCurve k) (q : ℕ)

def bad (n : ℤ) : Set k :=
  {x | W.Ψ₂Sq.eval x = 0 ∨ (n ≠ 0 ∧ ((W.ΨSq n).eval x = 0 ∨ (W.Φ n - X ^ q * W.ΨSq n).eval x = 0))}

lemma not_mem_bad_iff {n : ℤ} {x : k} : x ∉ bad W q n ↔
    W.Ψ₂Sq.eval x ≠ 0 ∧ (n ≠ 0 → (W.ΨSq n).eval x ≠ 0 ∧ (W.Φ n - X ^ q * W.ΨSq n).eval x ≠ 0) := by
  simp only [bad, Set.mem_setOf_eq, not_or, not_and, ne_eq]

lemma finite_setOf_eval_eq_zero {p : k[X]} (hp : p ≠ 0) : {x : k | p.eval x = 0}.Finite :=
  Polynomial.finite_setOf_isRoot hp

lemma bad_finite [W.IsElliptic] (hC : ∀ n : ℤ, W.Φ n - X ^ q * W.ΨSq n ≠ 0)
    (hcop : ∀ n : ℤ, IsCoprime (W.Φ n) (W.ΨSq n))
    (n : ℤ) : (bad W q n).Finite := by
  have hΨ₂ : W.Ψ₂Sq ≠ 0 := by
    rw [← WeierstrassCurve.ΨSq_two]
    exact ΨSq_ne_zero_of_isCoprime W two_ne_zero (hcop 2)
  by_cases hn : n = 0
  · refine (finite_setOf_eval_eq_zero hΨ₂).subset ?_
    rintro x (hx | ⟨hn', _⟩)
    · exact hx
    · exact absurd hn hn'
  · refine (((finite_setOf_eval_eq_zero hΨ₂).union
      (finite_setOf_eval_eq_zero (ΨSq_ne_zero_of_isCoprime W hn (hcop n)))).union
      (finite_setOf_eval_eq_zero (hC n))).subset ?_
    rintro x (hx | ⟨_, hx | hx⟩)
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx

end Bad

section Cover

variable {A : Type*} [AddCommGroup A]

lemma forall_eq_zero_or_forall_eq_zero (f g : A →+ A) (h : ∀ P, f P = 0 ∨ g P = 0) :
    (∀ P, f P = 0) ∨ (∀ P, g P = 0) := by
  by_contra hcon
  rw [not_or, not_forall, not_forall] at hcon
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := hcon
  have hgP : g P = 0 := (h P).resolve_left hP
  have hfQ : f Q = 0 := (h Q).resolve_right hQ
  rcases h (P + Q) with hs | hs
  · rw [map_add, hfQ, add_zero] at hs
    exact hP hs
  · rw [map_add, hgP, zero_add] at hs
    exact hQ hs

end Cover

section Frobenius

variable {R : Type*} [CommRing R] {F : Type*} [Field F] {k : Type*} [Field k]
  [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k]
  (W : WeierstrassCurve R) (σ : k ≃ₐ[F] k)

lemma linePencil_frobEnd_apply (n : ℤ) (P : (W⁄k).Point) :
    linePencil (frobEnd W σ) n 1 P = n • P - σ • P := by
  rw [linePencil_apply, frobEnd_apply, one_zsmul]

lemma linePencil_frobEnd_add (n j : ℤ) (P : (W⁄k).Point) :
    linePencil (frobEnd W σ) (n + j) 1 P = linePencil (frobEnd W σ) n 1 P + j • P := by
  rw [linePencil_frobEnd_apply, linePencil_frobEnd_apply, add_zsmul]
  abel

lemma linePencil_frobEnd_sub (n j : ℤ) (P : (W⁄k).Point) :
    linePencil (frobEnd W σ) (n - j) 1 P = linePencil (frobEnd W σ) n 1 P - j • P := by
  rw [linePencil_frobEnd_apply, linePencil_frobEnd_apply, sub_zsmul]
  abel

variable [Fintype F]

lemma smul_some (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (x y : k) (h : (W⁄k).Nonsingular x y) :
    ∃ (x₁ y₁ : k) (h₁ : (W⁄k).Nonsingular x₁ y₁),
      σ • (Point.some x y h : (W⁄k).Point) = Point.some x₁ y₁ h₁ ∧ x₁ = x ^ Fintype.card F := by
  have e : σ • (Point.some x y h : (W⁄k).Point) = Point.map σ.toAlgHom (Point.some x y h) := rfl
  rw [Point.map_some] at e
  exact ⟨_, _, _, e, hσ x⟩

lemma two_le_card : 2 ≤ Fintype.card F := Fintype.one_lt_card

omit [DecidableEq k] in

lemma card_eq_zero : ((Fintype.card F : ℕ) : k) = 0 := by
  have h := congrArg (algebraMap F k) (FiniteField.cast_card_eq_zero F)
  rwa [map_natCast, _root_.map_zero] at h

structure IsMember (n : ℤ) (u v : k[X]) : Prop where
  cop : IsCoprime u v
  v_ne : v ≠ 0
  deg : (n : k) ≠ 0 → u.natDegree = v.natDegree + 1
  deg0 : n = 0 → u.natDegree = Fintype.card F ∧ v.natDegree = 0
  ident : ∀ {x y : k} (h : (W⁄k).Nonsingular x y), x ∉ bad (W⁄k) (Fintype.card F) n →
    ∃ (x' y' : k) (h' : (W⁄k).Nonsingular x' y'),
      linePencil (frobEnd W σ) n 1 (Point.some x y h) = Point.some x' y' h' ∧
        x' * v.eval x = u.eval x

lemma IsMember.u_ne {n : ℤ} {u v : k[X]} (hmem : IsMember W σ n u v)
    (hgood : (n : k) ≠ 0 ∨ n = 0) (hq : 2 ≤ Fintype.card F) : u ≠ 0 ∧ v.natDegree ≤ u.natDegree := by
  rcases hgood with hg | hg
  · have h := hmem.deg hg
    refine ⟨fun h0 => ?_, by omega⟩
    rw [h0, natDegree_zero] at h
    omega
  · obtain ⟨hu, hv⟩ := hmem.deg0 hg
    refine ⟨fun h0 => ?_, by omega⟩
    rw [h0, natDegree_zero] at hu
    omega

variable [IsAlgClosed k] [(W⁄k).IsElliptic]

theorem exists_isMember (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    (hC : ∀ n : ℤ, (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n ≠ 0) (n : ℤ) :
    ∃ u v : k[X], IsMember W σ n u v := by
  have hcop : ∀ n : ℤ, IsCoprime ((W⁄k).Φ n) ((W⁄k).ΨSq n) :=
    fun n => WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄k) n
  by_cases hn : n = 0
  ·
    subst hn
    refine ⟨X ^ Fintype.card F, 1, isCoprime_one_right, one_ne_zero, fun h => (h (by simp)).elim,
      fun _ => ⟨natDegree_X_pow _, natDegree_one⟩, ?_⟩
    · intro x y h _
      obtain ⟨x₁, y₁, h₁, hsm, hx₁⟩ := smul_some W σ hσ x y h
      have hA : linePencil (frobEnd W σ) 0 1 (Point.some x y h) = -(σ • Point.some x y h) := by
        rw [linePencil_frobEnd_apply, zero_zsmul, zero_sub]
      rw [hsm, Affine.Point.neg_some] at hA
      exact ⟨_, _, _, hA, by rw [eval_one, mul_one, eval_pow, eval_X, hx₁]⟩
  ·
    have hq2 : 2 ≤ Fintype.card F := two_le_card
    have hΨn : (W⁄k).ΨSq n ≠ 0 := ΨSq_ne_zero_of_isCoprime (W⁄k) hn (hcop n)
    have hCn : (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n ≠ 0 := hC n

    have hfin : {x : k | ∃ (y : k) (h : (W⁄k).Nonsingular x y), n • Point.some x y h = 0}.Finite := by
      refine (finite_setOf_eval_eq_zero hΨn).subset ?_
      rintro x ⟨y, h, h0⟩
      exact ΨSq_eval_eq_zero_of_zsmul_eq_zero n h h0
    obtain ⟨U, hUdeg, hU⟩ :=
      FrobeniusEndo.exists_x_linePencil_frobEnd_mul_collision_sq W σ hσ n hfin
    obtain ⟨u, v, hcopuv, hv0, hid, hdeg⟩ := exists_reduced_pair U (pow_ne_zero 2 hCn)
    refine ⟨u, v, hcopuv, hv0, fun hnk => ?_, fun h0 => absurd h0 hn, ?_⟩
    ·
      have hUd := hUdeg hnk
      have hn1 : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hn)
      have hU0 : U ≠ 0 := fun h0 => by
        rw [h0, natDegree_zero] at hUd
        omega
      have h := (hdeg hU0).2
      rw [natDegree_pow, natDegree_collision (W⁄k) hq2 hnk, hUd] at h
      omega
    · intro x y h hx
      rw [not_mem_bad_iff] at hx
      obtain ⟨hΨ₂x, hx2⟩ := hx
      obtain ⟨hΨx, hCx⟩ := hx2 hn

      have hnP : n • (Point.some x y h : (W⁄k).Point) ≠ 0 := fun h0 =>
        hΨx (ΨSq_eval_eq_zero_of_zsmul_eq_zero n h h0)
      rcases hnP_eq : n • (Point.some x y h : (W⁄k).Point) with _ | ⟨x₁, y₁, h₁⟩
      · exact absurd hnP_eq hnP
      obtain ⟨hA0, hAx⟩ := hU h h₁ hnP_eq hΨx hCx hΨ₂x
      rcases hA_eq : linePencil (frobEnd W σ) n 1 (Point.some x y h) with _ | ⟨x', y', h'⟩
      · exact absurd hA_eq hA0
      refine ⟨x', y', h', rfl, ?_⟩
      have hAx' := hAx h' hA_eq
      have hidx := congrArg (Polynomial.eval x) hid
      simp only [eval_mul, eval_pow] at hidx
      have key : (x' * v.eval x) * ((W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n).eval x ^ 2
          = u.eval x * ((W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n).eval x ^ 2 := by
        linear_combination (v.eval x) * hAx' - hidx
      exact mul_right_cancel₀ (pow_ne_zero 2 hCx) key

theorem step (hC : ∀ n : ℤ, (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n ≠ 0)
    (u v : ℤ → k[X]) (hmem : ∀ n, IsMember W σ n (u n) (v n))
    {n j : ℤ} (hj : j ≠ 0) (hgood : (n : k) ≠ 0 ∨ n = 0) :
    (u (n + j)).natDegree + (u (n - j)).natDegree = 2 * ((u n).natDegree + j.natAbs ^ 2) := by
  have hcop : ∀ n : ℤ, IsCoprime ((W⁄k).Φ n) ((W⁄k).ΨSq n) :=
    fun n => WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄k) n
  have hq2 : 2 ≤ Fintype.card F := two_le_card
  obtain ⟨hu0, hvu⟩ := IsMember.u_ne W σ (hmem n) hgood hq2
  have hΨj : (W⁄k).ΨSq j ≠ 0 := ΨSq_ne_zero_of_isCoprime (W⁄k) hj (hcop j)
  have hts : ((W⁄k).ΨSq j).natDegree < ((W⁄k).Φ j).natDegree := by
    have h1 := WeierstrassCurve.natDegree_ΨSq_le (W⁄k) j
    have h2 : 1 ≤ j.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hj)
    rw [WeierstrassCurve.natDegree_Φ]
    omega

  set S : Set k := ((bad (W⁄k) (Fintype.card F) n ∪ bad (W⁄k) (Fintype.card F) (n + j)) ∪
      bad (W⁄k) (Fintype.card F) (n - j)) ∪ {x | ((W⁄k).ΨSq j).eval x = 0} with hS
  have hSfin : S.Finite :=
    (((bad_finite (W⁄k) _ hC hcop n).union (bad_finite (W⁄k) _ hC hcop (n + j))).union
      (bad_finite (W⁄k) _ hC hcop (n - j))).union (finite_setOf_eval_eq_zero hΨj)
  obtain ⟨-, -, hdeg, -⟩ := WeierstrassCurve.Affine.Point.natDegree_parallelogram_law (W⁄k) hSfin
    (hmem n).cop (hcop j) (hmem (n + j)).cop (hmem (n - j)).cop hu0 (hmem n).v_ne hΨj
    (hmem (n + j)).v_ne (hmem (n - j)).v_ne hvu hts (fun x hxS => by
      simp only [hS, Set.mem_union, Set.mem_setOf_eq, not_or] at hxS
      obtain ⟨⟨⟨hxn, hxp⟩, hxm⟩, hΨjx⟩ := hxS
      obtain ⟨y, h⟩ := exists_nonsingular (W := W⁄k) x

      obtain ⟨xa, ya, ha, hAeq, hAid⟩ := (hmem n).ident h hxn

      have hjP : j • (Point.some x y h : (W⁄k).Point) ≠ 0 := fun h0 =>
        hΨjx (ΨSq_eval_eq_zero_of_zsmul_eq_zero j h h0)
      rcases hB : j • (Point.some x y h : (W⁄k).Point) with _ | ⟨xb, yb, hb⟩
      · exact absurd hB hjP
      have hBid : xb * ((W⁄k).ΨSq j).eval x = ((W⁄k).Φ j).eval x := zsmul_x_mul_ΨSq j h hb hB

      obtain ⟨xp, yp, hp, hPeq, hPid⟩ := (hmem (n + j)).ident h hxp
      obtain ⟨xm, ym, hm, hMeq, hMid⟩ := (hmem (n - j)).ident h hxm
      refine ⟨xa, ya, xb, yb, xp, yp, xm, ym, ha, hb, hp, hm, ?_, ?_, hAid, hBid, hPid, hMid⟩
      · rw [← hAeq, ← hB, ← hPeq, linePencil_frobEnd_add]
      · rw [← hAeq, ← hB, ← hMeq, linePencil_frobEnd_sub])
  rw [WeierstrassCurve.natDegree_Φ] at hdeg
  exact hdeg

theorem card_ker_eq (hC : ∀ n : ℤ, (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n ≠ 0)
    {m : ℤ} (hmk : (m : k) ≠ 0) {u v : k[X]} (hmem : IsMember W σ m u v) :
    Nat.card (linePencil (frobEnd W σ) m 1).ker = u.natDegree := by
  have hcop : ∀ n : ℤ, IsCoprime ((W⁄k).Φ n) ((W⁄k).ΨSq n) :=
    fun n => WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄k) n
  have hdeg := hmem.deg hmk

  set B : Set (W⁄k).Point := {P | ∃ x ∈ bad (W⁄k) (Fintype.card F) m, ∃ y : k,
    ∃ h : (W⁄k).Nonsingular x y, P = Point.some x y h} with hB
  have hBfin : B.Finite := finite_setOf_X_mem (W := W⁄k) (bad_finite (W⁄k) _ hC hcop m)
  have key := WeierstrassCurve.Affine.Point.card_ker_eq_max_natDegree (W⁄k)
    (linePencil (frobEnd W σ) m 1) hBfin hmem.cop
    (wronskian_ne_zero_of_natDegree_eq_succ hmem.v_ne hdeg)
    (fun {x y} hP hPB _ => by
      have hx : x ∉ bad (W⁄k) (Fintype.card F) m := fun hx => hPB ⟨x, hx, y, hP, rfl⟩
      obtain ⟨x', y', h', hAeq, -⟩ := hmem.ident hP hx
      rw [hAeq]
      exact Point.some_ne_zero _)
    (fun {x y} hP {x' y'} hP' hPB heq => by
      have hx : x ∉ bad (W⁄k) (Fintype.card F) m := fun hx => hPB ⟨x, hx, y, hP, rfl⟩
      obtain ⟨x'', y'', h'', hAeq, hid⟩ := hmem.ident hP hx
      rw [hAeq] at heq
      rw [← (Point.some.inj heq).1]
      exact hid)
  rw [key, hdeg]
  exact max_eq_left (Nat.le_succ _)

theorem main_generic (hσ : ∀ x : k, σ x = x ^ Fintype.card F)
    (hC : ∀ n : ℤ, (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n ≠ 0) (m : ℕ)
    (hmk : (m : k) ≠ 0) :
    0 < kerDeg (frobEnd W σ) m 1 ∧
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ)
        = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m
          + Fintype.card F := by
  choose u v hmem using exists_isMember W σ hσ hC

  set d : ℤ → ℤ := fun n => ((u n).natDegree : ℤ) with hd
  set good : ℤ → Prop := fun n => (n : k) ≠ 0 ∨ n = 0 with hgood_def
  have hgood : ∀ n : ℤ, good n ∨ good (n - 1) := by
    intro n
    by_cases h : (n : k) = 0
    · right
      left
      rw [Int.cast_sub, Int.cast_one, h, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    · exact Or.inl (Or.inl h)
  have R1 : ∀ n : ℤ, good n → d (n + 1) + d (n - 1) = 2 * d n + 2 := by
    intro n hg
    have h := step W σ hC u v hmem one_ne_zero hg
    simp only [hd]
    norm_num at h
    exact_mod_cast (by omega : (u (n + 1)).natDegree + (u (n - 1)).natDegree
      = 2 * (u n).natDegree + 2)
  have R2 : ∀ n : ℤ, good n → d (n + 2) + d (n - 2) = 2 * d n + 8 := by
    intro n hg
    have h := step W σ hC u v hmem two_ne_zero hg
    simp only [hd]
    norm_num at h
    exact_mod_cast (by omega : (u (n + 2)).natDegree + (u (n - 2)).natDegree
      = 2 * (u n).natDegree + 8)
  have h0 : d 0 = Fintype.card F := by
    simp only [hd]
    exact_mod_cast ((hmem 0).deg0 rfl).1

  have hE1 : kerDeg (frobEnd W σ) 1 1 = (u 1).natDegree := by
    rw [kerDeg_def]
    exact card_ker_eq W σ hC (by simp) (hmem 1)
  have h1 : d 1 = 1 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) + Fintype.card F := by
    simp only [hd, hE1]
    ring
  have hsol := solver d (Fintype.card F) _ good h0 h1 (Or.inr rfl) (Or.inl (by simp)) hgood R1 R2 m

  have hmk' : ((m : ℤ) : k) ≠ 0 := by rwa [Int.cast_natCast]
  have hEm : kerDeg (frobEnd W σ) m 1 = (u m).natDegree := by
    rw [kerDeg_def]
    exact card_ker_eq W σ hC hmk' (hmem m)
  refine ⟨?_, ?_⟩
  · rw [hEm, (hmem m).deg hmk']
    exact Nat.succ_pos _
  · rw [hEm]
    simpa only [hd] using hsol

omit [IsAlgClosed k] in

theorem exists_frob_eq_zsmul (hσ : ∀ x : k, σ x = x ^ Fintype.card F) {n : ℤ}
    (hCn : (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n = 0) :
    ∃ s : ℤ, s.natAbs ^ 2 = Fintype.card F ∧ ∀ P : (W⁄k).Point, σ • P = s • P := by
  obtain ⟨hn, ⟨c, hc, hΨc⟩, hnq⟩ :=
    collision_eq_zero_iff_aux (W⁄k) (WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄k) n) hCn
  have hΦ : (W⁄k).Φ n = X ^ Fintype.card F * (W⁄k).ΨSq n := sub_eq_zero.mp hCn

  have hpt : ∀ P : (W⁄k).Point,
      linePencil (frobEnd W σ) n 1 P = 0 ∨ linePencil (frobEnd W σ) n (-1) P = 0 := by
    rintro (_ | ⟨x, y, h⟩)
    · exact Or.inl (map_zero _)
    ·
      have hnP : n • (Point.some x y h : (W⁄k).Point) ≠ 0 := fun h0 => by
        have := ΨSq_eval_eq_zero_of_zsmul_eq_zero n h h0
        rw [hΨc, eval_C] at this
        exact hc this
      rcases hnP_eq : n • (Point.some x y h : (W⁄k).Point) with _ | ⟨x₁, y₁, h₁⟩
      · exact absurd hnP_eq hnP
      have hx₁ : x₁ = x ^ Fintype.card F := by
        have key := zsmul_x_mul_ΨSq n h h₁ hnP_eq
        rw [hΦ, eval_mul, eval_pow, eval_X, hΨc, eval_C] at key
        exact mul_right_cancel₀ hc key

      obtain ⟨x₂, y₂, h₂, hsm, hx₂⟩ := smul_some W σ hσ x y h

      rcases Y_eq_of_X_eq h₁.left h₂.left (hx₁.trans hx₂.symm) with hy | hy
      · left
        rw [linePencil_apply, frobEnd_apply, one_zsmul, hnP_eq, hsm, sub_eq_zero]
        subst hx₁; subst hx₂; subst hy
        rfl
      · right
        rw [linePencil_apply, frobEnd_apply, neg_zsmul, one_zsmul, sub_neg_eq_add, hnP_eq, hsm,
          add_eq_zero_iff_eq_neg, Affine.Point.neg_some]
        subst hx₁; subst hx₂; subst hy
        rfl
  rcases forall_eq_zero_or_forall_eq_zero _ _ hpt with hall | hall
  · refine ⟨n, hnq, fun P => ?_⟩
    have h := hall P
    rwa [linePencil_apply, frobEnd_apply, one_zsmul, sub_eq_zero, eq_comm] at h
  · refine ⟨-n, by rwa [Int.natAbs_neg], fun P => ?_⟩
    have h := hall P
    rwa [linePencil_apply, frobEnd_apply, neg_zsmul, one_zsmul, sub_neg_eq_add,
      add_eq_zero_iff_neg_eq, ← neg_zsmul, eq_comm] at h

theorem card_ker_of_eq_zsmul {j : ℤ} (hjk : (j : k) ≠ 0) (ψ : (W⁄k).Point →+ (W⁄k).Point)
    (hψ : ∀ P, ψ P = j • P) : Nat.card ψ.ker = j.natAbs ^ 2 := by
  have hj : j ≠ 0 := by
    rintro rfl
    exact hjk (by simp)
  have hΨ0 : (W⁄k).ΨSq j ≠ 0 := WeierstrassCurve.ΨSq_ne_zero _ hjk
  have hj1 : 1 ≤ j.natAbs ^ 2 := Nat.one_le_pow _ _ (Int.natAbs_pos.mpr hj)
  have hdegΨ : ((W⁄k).ΨSq j).natDegree = j.natAbs ^ 2 - 1 := WeierstrassCurve.natDegree_ΨSq _ hjk
  have hdeg : ((W⁄k).Φ j).natDegree = ((W⁄k).ΨSq j).natDegree + 1 := by
    rw [WeierstrassCurve.natDegree_Φ, hdegΨ]
    omega
  have key := WeierstrassCurve.Affine.Point.card_ker_eq_max_natDegree (W⁄k) ψ Set.finite_empty
    (WeierstrassCurve.isCoprime_Phi_PsiSq (W⁄k) j)
    (wronskian_ne_zero_of_natDegree_eq_succ hΨ0 hdeg)
    (fun {x y} hP _ hΨx h0 => by
      rw [hψ] at h0
      exact hΨx (ΨSq_eval_eq_zero_of_zsmul_eq_zero j hP h0))
    (fun {x y} hP {x' y'} hP' _ heq => by
      rw [hψ] at heq
      exact zsmul_x_mul_ΨSq j hP hP' heq)
  rw [key, hdeg, hdegΨ, max_eq_left (Nat.le_succ _)]
  omega

theorem main_degenerate {s : ℤ} (hsq : s.natAbs ^ 2 = Fintype.card F)
    (hs : ∀ P : (W⁄k).Point, σ • P = s • P) (m : ℕ) (hmk : (m : k) ≠ 0) :
    0 < kerDeg (frobEnd W σ) m 1 ∧
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ)
        = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m
          + Fintype.card F := by

  have hq : (Fintype.card F : ℤ) = s ^ 2 := by
    rw [← hsq, Nat.cast_pow, Int.natCast_natAbs, sq_abs]
  have hsk : (s : k) = 0 := by
    have h : ((s : k)) ^ 2 = 0 := by
      have h1 : ((s ^ 2 : ℤ) : k) = ((Fintype.card F : ℕ) : k) := by
        rw [← hq, Int.cast_natCast]
      rw [Int.cast_pow] at h1
      rw [h1]
      exact card_eq_zero
    exact pow_eq_zero_iff two_ne_zero |>.mp h

  have hpencil : ∀ (m' : ℤ) (P : (W⁄k).Point), linePencil (frobEnd W σ) m' 1 P = (m' - s) • P := by
    intro m' P
    rw [linePencil_apply, frobEnd_apply, one_zsmul, hs, sub_smul]
  have hker : ∀ m' : ℤ, (m' : k) ≠ 0 → kerDeg (frobEnd W σ) m' 1 = (m' - s).natAbs ^ 2 := by
    intro m' hm'
    rw [kerDeg_def]
    refine card_ker_of_eq_zsmul W (j := m' - s) ?_ _ (hpencil m')
    rwa [Int.cast_sub, hsk, sub_zero]
  have hmk' : ((m : ℤ) : k) ≠ 0 := by rwa [Int.cast_natCast]
  have hEm := hker m hmk'
  have hE1 := hker 1 (by simp)
  refine ⟨?_, ?_⟩
  · rw [hEm]
    refine pow_pos (Int.natAbs_pos.mpr ?_) 2
    intro h0
    apply hmk'
    have : (m : ℤ) = s := sub_eq_zero.mp h0
    rw [this, hsk]
  · rw [hEm, hE1, hq]
    push_cast
    rw [sq_abs, sq_abs]
    ring

theorem main (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (m : ℕ) (hmk : (m : k) ≠ 0) :
    0 < kerDeg (frobEnd W σ) m 1 ∧
      ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ)
        = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m
          + Fintype.card F := by
  by_cases hC : ∀ n : ℤ, (W⁄k).Φ n - X ^ Fintype.card F * (W⁄k).ΨSq n ≠ 0
  · exact main_generic W σ hσ hC m hmk
  · simp only [not_forall, not_not] at hC
    obtain ⟨n, hCn⟩ := hC
    obtain ⟨s, hsq, hs⟩ := exists_frob_eq_zsmul W σ hσ hCn
    exact main_degenerate W σ hsq hs m hmk

end Frobenius

end KerDegFrobLineFiniteField

theorem solution {R : Type*} [CommRing R] {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] [DecidableEq k] [Algebra R F] [Algebra R k] [Algebra F k] [IsScalarTower R F k] [IsAlgClosed k] (W : WeierstrassCurve R) [(W⁄k).IsElliptic] (σ : k ≃ₐ[F] k) (hσ : ∀ x : k, σ x = x ^ Fintype.card F) (m : ℕ) (hm : 1 ≤ m) (hmk : (m : k) ≠ 0) : 0 < kerDeg (frobEnd W σ) m 1 ∧ ((kerDeg (frobEnd W σ) m 1 : ℕ) : ℤ) = (m : ℤ) ^ 2 - ((Fintype.card F : ℤ) + 1 - kerDeg (frobEnd W σ) 1 1) * m + Fintype.card F :=
  KerDegFrobLineFiniteField.main W σ hσ m hmk

end S_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_finiteField
end P2MW
export P2MW.S_FrobeniusEndo_kerDeg_frobEnd_line_one_pos_and_eq_finiteField (solution)
