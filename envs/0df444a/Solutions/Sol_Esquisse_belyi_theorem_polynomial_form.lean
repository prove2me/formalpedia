-- Prove2me | solution 1 for Esquisse.belyi_theorem_polynomial_form
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T00:30:33.035668+00:00
-- url     : https://prove2.me/submissions/6ae2aee7-8c8f-435d-81f6-e94243243558

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Preimage

import Definitions.Def_esquisse_dessins_basic


/-
Local draft for the rational-point descent in Belyi's construction.
Source: Ilaria Seidel, A Proof of Belyi's Theorem, §2.1, p.3.
No verification or publication is claimed by this file.
-/
namespace BelyiConstruction
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

noncomputable def betaRaw (a b : ℕ) : K[X] := X ^ (a + 1) * (1 - X) ^ (b + 1)

def betaPoint (a b : ℕ) : K := ((a + 1 : ℕ) : K) / ((a + b + 2 : ℕ) : K)

noncomputable def beta (a b : ℕ) : K[X] :=
  C ((betaRaw a b).eval (betaPoint a b))⁻¹ * betaRaw a b

lemma betaRaw_derivative (a b : ℕ) :
    (betaRaw a b : K[X]).derivative =
      X ^ a * (1 - X) ^ b * (C ((a + 1 : ℕ) : K) - C ((a + b + 2 : ℕ) : K) * X) := by
  simp only [betaRaw, derivative_mul, derivative_pow_succ, derivative_X,
    derivative_sub, derivative_one, zero_sub, mul_one, C_eq_natCast]
  simp only [pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  simp only [C_add, C_1, C_eq_natCast]
  ring

lemma betaPoint_ne_zero (a b : ℕ) : (betaPoint a b : K) ≠ 0 := by
  unfold betaPoint
  exact div_ne_zero (Nat.cast_ne_zero.mpr (by omega))
    (Nat.cast_ne_zero.mpr (by omega))

lemma one_sub_betaPoint_ne_zero (a b : ℕ) : 1 - (betaPoint a b : K) ≠ 0 := by
  have hd : (a + b + 2 : K) ≠ 0 := by exact_mod_cast (show a + b + 2 ≠ 0 by omega)
  have hn : (b + 1 : K) ≠ 0 := by exact_mod_cast (show b + 1 ≠ 0 by omega)
  have he : 1 - (betaPoint a b : K) = (b + 1) / (a + b + 2) := by
    simp only [betaPoint, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    field_simp [hd]
    <;> ring
  rw [he]
  exact div_ne_zero hn hd

lemma betaRaw_at_point_ne_zero (a b : ℕ) :
    (betaRaw a b : K[X]).eval (betaPoint a b) ≠ 0 := by
  simp only [betaRaw, eval_mul, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_ne_zero (pow_ne_zero _ (betaPoint_ne_zero a b))
    (pow_ne_zero _ (one_sub_betaPoint_ne_zero a b))

@[simp] lemma beta_zero (a b : ℕ) : (beta a b : K[X]).eval 0 = 0 := by
  simp [beta, betaRaw]

@[simp] lemma beta_one (a b : ℕ) : (beta a b : K[X]).eval 1 = 0 := by
  simp [beta, betaRaw]

@[simp] lemma beta_at_point (a b : ℕ) :
    (beta a b : K[X]).eval (betaPoint a b) = 1 := by
  simp only [beta, eval_mul, eval_C]
  exact inv_mul_cancel₀ (betaRaw_at_point_ne_zero a b)

lemma beta_natDegree_pos (a b : ℕ) : 0 < (beta a b : K[X]).natDegree := by
  by_contra h
  have hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos h)
  have he : (beta a b : K[X]).eval 0 = (beta a b).eval (betaPoint a b) := by
    rw [hc]
    simp
  simpa using he

lemma beta_critical_value (a b : ℕ) (z : K)
    (hz : (beta a b : K[X]).derivative.eval z = 0) :
    (beta a b).eval z = 0 ∨ (beta a b).eval z = 1 := by
  have hraw : (betaRaw a b : K[X]).derivative.eval z = 0 := by
    have he : ((betaRaw a b : K[X]).eval (betaPoint a b))⁻¹ *
        (betaRaw a b).derivative.eval z = 0 := by
      simpa only [beta, derivative_mul, derivative_C, zero_mul, zero_add,
        eval_mul, eval_C] using hz
    exact (mul_eq_zero.mp he).resolve_left (inv_ne_zero (betaRaw_at_point_ne_zero a b))
  rw [betaRaw_derivative] at hraw
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one, eval_C] at hraw
  rcases mul_eq_zero.mp hraw with hpow | hlinear
  · rcases mul_eq_zero.mp hpow with hzero | hone
    · have he : z = 0 := eq_zero_of_pow_eq_zero hzero
      subst z
      exact Or.inl (beta_zero a b)
    · have he : 1 - z = 0 := eq_zero_of_pow_eq_zero hone
      have he' : z = 1 := (sub_eq_zero.mp he).symm
      subst z
      exact Or.inl (beta_one a b)
  · have hd : ((a + b + 2 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have he : z = betaPoint a b := by
      apply (eq_div_iff hd).mpr
      exact (mul_comm _ _).trans (sub_eq_zero.mp hlinear).symm
    rw [he]
    exact Or.inr (beta_at_point a b)

#print axioms beta_critical_value
#print axioms beta_natDegree_pos
end BelyiConstruction


/- Offline draft: not compiled or published.
Seidel, A Proof of Belyi's Theorem, §2.1, p.3.
We normalize by an affine map at each induction step. A dilation alone cannot
put arbitrary signed rational sets in [0,1]. No interval-invariance claim is used.
-/
namespace BelyiConstruction
open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- All finite critical values of a rational polynomial, after scalar extension,
lie in the two-point set. This makes the extension field explicit. -/
def GoodCrit (K : Type*) [Field K] [CharZero K] (f : ℚ[X]) : Prop :=
  ∀ z : K, (f.map (Rat.castHom K)).derivative.eval z = 0 →
    (f.map (Rat.castHom K)).eval z = 0 ∨
    (f.map (Rat.castHom K)).eval z = 1

lemma positive_degree_of_eval_ne {F : Type*} [Field F] {f : F[X]} {x y : F}
    (h : f.eval x ≠ f.eval y) : 0 < f.natDegree := by
  by_contra hn
  have hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hn)
  exact h (by rw [hc]; simp)

lemma goodCrit_comp {f g : ℚ[X]} (hf : GoodCrit K f) (hg : GoodCrit K g)
    (h0 : f.eval 0 = 0 ∨ f.eval 0 = 1)
    (h1 : f.eval 1 = 0 ∨ f.eval 1 = 1) : GoodCrit K (f.comp g) := by
  intro z hz
  rw [map_comp, derivative_comp, eval_mul, eval_comp] at hz
  rw [map_comp, eval_comp]
  rcases mul_eq_zero.mp hz with hgzero | hfzero
  · rcases hg z hgzero with he | he
    · rw [he]
      rcases h0 with h0 | h0
      · left
        simpa only [← Polynomial.eval_map_apply, map_zero, map_one] using
          congrArg (Rat.castHom K) h0
      · right
        simpa only [← Polynomial.eval_map_apply, map_zero, map_one] using
          congrArg (Rat.castHom K) h0
    · rw [he]
      rcases h1 with h1 | h1
      · left
        simpa only [← Polynomial.eval_map_apply, map_zero, map_one] using
          congrArg (Rat.castHom K) h1
      · right
        simpa only [← Polynomial.eval_map_apply, map_zero, map_one] using
          congrArg (Rat.castHom K) h1
  · exact hf _ hfzero

lemma map_beta (a b : ℕ) :
    (beta a b : ℚ[X]).map (Rat.castHom K) = (beta a b : K[X]) := by
  simp [beta, betaRaw, betaPoint]

lemma goodCrit_beta (a b : ℕ) : GoodCrit K (beta a b) := by
  intro z hz
  rw [map_beta] at hz ⊢
  exact beta_critical_value a b z hz

/-- An affine normalization has no finite critical points. -/
noncomputable def normalize (l r : ℚ) : ℚ[X] := C (r - l)⁻¹ * (X - C l)

@[simp] lemma normalize_left (l r : ℚ) : (normalize l r).eval l = 0 := by
  simp [normalize]

@[simp] lemma normalize_right {l r : ℚ} (hlr : l ≠ r) :
    (normalize l r).eval r = 1 := by
  simp [normalize, sub_ne_zero.mpr hlr.symm]

lemma normalize_degree {l r : ℚ} (hlr : l ≠ r) :
    0 < (normalize l r).natDegree := by
  apply positive_degree_of_eval_ne (x := l) (y := r)
  simp [normalize_right hlr]

lemma normalize_no_critical {l r : ℚ} (hlr : l ≠ r) (z : K) :
    ((normalize l r).map (Rat.castHom K)).derivative.eval z ≠ 0 := by
  have h : (r - l : ℚ) ≠ 0 := sub_ne_zero.mpr hlr.symm
  have hcast : ((r - l : ℚ) : K) ≠ 0 := by exact_mod_cast h
  simpa [normalize] using inv_ne_zero hcast

lemma goodCrit_normalize {l r : ℚ} (hlr : l ≠ r) : GoodCrit K (normalize l r) := by
  intro z hz
  exact (normalize_no_critical hlr z hz).elim

/-- Every interior rational point is the distinguished point of a beta polynomial. -/
lemma exists_betaPoint {x : ℚ} (hx : 0 < x) (hx1 : x < 1) :
    ∃ a b : ℕ, (betaPoint a b : ℚ) = x := by
  have hnum : 0 < x.num := Rat.num_pos.mpr hx
  have hnum0 : 0 ≤ x.num := le_of_lt hnum
  have hn : 0 < x.num.toNat := by omega
  have hcast : (x.num.toNat : ℚ) = (x.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hnum0
  have hrepr : x = (x.num.toNat : ℚ) / x.den := by
    rw [hcast]
    exact x.num_div_den.symm
  have hd : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have hnd : x.num.toNat < x.den := by
    have hq : (x.num.toNat : ℚ) < x.den := by
      apply (div_lt_one hd).mp
      rwa [← hrepr]
    exact_mod_cast hq
  refine ⟨x.num.toNat - 1, x.den - x.num.toNat - 1, ?_⟩
  have he1 : x.num.toNat - 1 + 1 = x.num.toNat := by omega
  have he2 : x.num.toNat - 1 + (x.den - x.num.toNat - 1) + 2 = x.den := by omega
  rw [betaPoint, he1, he2]
  exact hrepr.symm

/-- Rational finite-set descent, with critical values controlled in any fixed
characteristic-zero field. In particular take K = AlgebraicClosure ℚ. -/
theorem rational_descent (K : Type*) [Field K] [CharZero K] (S : Finset ℚ) :
    ∃ f : ℚ[X], 0 < f.natDegree ∧
      (∀ x ∈ S, f.eval x = 0 ∨ f.eval x = 1) ∧ GoodCrit K f := by
  classical
  have main : ∀ n : ℕ, ∀ S : Finset ℚ, S.card = n →
      ∃ f : ℚ[X], 0 < f.natDegree ∧
        (∀ x ∈ S, f.eval x = 0 ∨ f.eval x = 1) ∧ GoodCrit K f := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hc
      by_cases hone : S.card ≤ 1
      · obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hone
        refine ⟨X - C a, by simp, ?_, ?_⟩
        · intro x hx
          have hxa : x = a := Finset.mem_singleton.mp (ha hx)
          subst x
          simp
        · intro z hz
          simp at hz
      by_cases htwo : S.card = 2
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp htwo
        refine ⟨normalize a b, normalize_degree hab, ?_, goodCrit_normalize hab⟩
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact Or.inl (normalize_left a b)
        · rw [hx]
          exact Or.inr (normalize_right hab)
      have hcard : 2 < S.card := by omega
      have hS : S.Nonempty := Finset.card_pos.mp (by omega)
      let l := S.min' hS
      let r := S.max' hS
      have hl : l ∈ S := Finset.min'_mem S hS
      have hr : r ∈ S := Finset.max'_mem S hS
      have hlr : l < r := Finset.min'_lt_max'_of_card S (by omega)
      obtain ⟨m, hm, hml, hmr⟩ : ∃ m ∈ S, m ≠ l ∧ m ≠ r := by
        by_contra hnone
        push_neg at hnone
        have hsub : S ⊆ {l, r} := by
          intro x hx
          by_cases he : x = l
          · simp [he]
          · simp [hnone x hx he]
        have hle := Finset.card_le_card hsub
        have hpair : ({l, r} : Finset ℚ).card ≤ 2 := Finset.card_le_two
        omega
      have hlm : l < m := lt_of_le_of_ne (Finset.min'_le S m hm) hml.symm
      have hmr' : m < r := lt_of_le_of_ne (Finset.le_max' S m hm) hmr
      let x : ℚ := (m - l) / (r - l)
      have hx : 0 < x := div_pos (sub_pos.mpr hlm) (sub_pos.mpr hlr)
      have hx1 : x < 1 := (div_lt_one (sub_pos.mpr hlr)).mpr (by linarith)
      obtain ⟨a, b, hab⟩ := exists_betaPoint hx hx1
      let h : ℚ[X] := (beta a b).comp (normalize l r)
      have hdeg : 0 < h.natDegree := by
        dsimp [h]
        rw [natDegree_comp]
        exact Nat.mul_pos (beta_natDegree_pos a b) (normalize_degree hlr.ne)
      have hleft : h.eval l = 0 := by simp [h]
      have hright : h.eval r = 0 := by simp [h, normalize_right hlr.ne]
      have hmiddle : h.eval m = 1 := by
        have he : (normalize l r).eval m = betaPoint a b := by
          rw [hab]
          simp [normalize, x, div_eq_mul_inv, mul_comm]
        simp [h, he]
      have hcrit : GoodCrit K h := by
        intro z hz
        dsimp [h] at hz ⊢
        rw [map_comp, derivative_comp, eval_mul, eval_comp] at hz
        rw [map_comp, eval_comp]
        exact goodCrit_beta a b _
          ((mul_eq_zero.mp hz).resolve_left (normalize_no_critical hlr.ne z))
      let T : Finset ℚ := S.image h.eval
      have hzero : 0 ∈ T := by
        exact Finset.mem_image.mpr ⟨l, hl, hleft⟩
      have h_one : 1 ∈ T := by
        exact Finset.mem_image.mpr ⟨m, hm, hmiddle⟩
      have hlt : T.card < S.card := by
        have hle : T.card ≤ S.card := Finset.card_image_le
        have hne : T.card ≠ S.card := by
          intro heq
          have hinj : Set.InjOn h.eval S := Finset.card_image_iff.mp heq
          exact hlr.ne (hinj hl hr (hleft.trans hright.symm))
        omega
      obtain ⟨g, hgdeg, hgS, hgcrit⟩ := ih T.card (by omega) T rfl
      refine ⟨g.comp h, ?_, ?_, goodCrit_comp hgcrit hcrit (hgS 0 hzero) (hgS 1 h_one)⟩
      · rw [natDegree_comp]
        exact Nat.mul_pos hgdeg hdeg
      · intro z hz
        rw [eval_comp]
        exact hgS _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
  exact main S.card S rfl

#print axioms rational_descent
end BelyiConstruction


/-!
UNVERIFIED LOCAL DRAFT. No compiler has been run on this file.
Source: Bernhard Köck, Belyi's Theorem Revisited, Lemma 3.5,
https://arxiv.org/pdf/math/0108222 (printed page 11).

The induction uses all points of a Galois-stable finite set, rather than a
nonrational subfilter: its vanishing polynomial kills the marked set, and
its finite critical-value set has strictly smaller cardinality. Both the
marked images and every algebraic critical value are controlled.
-/
namespace BelyiConstruction
open Polynomial

abbrev DescentAlgNum := AlgebraicClosure ℚ
abbrev DescentGalois := DescentAlgNum ≃ₐ[ℚ] DescentAlgNum

noncomputable def rationalMap (q : ℚ[X]) : DescentAlgNum[X] :=
  q.map (algebraMap ℚ DescentAlgNum)

def GaloisStable (T : Finset DescentAlgNum) : Prop :=
  ∀ γ : DescentGalois, ∀ x ∈ T, γ x ∈ T

noncomputable def criticalValues (P : DescentAlgNum[X]) : Finset DescentAlgNum := by
  classical
  exact P.derivative.roots.toFinset.image P.eval

private lemma descent_orbit_finite (a : DescentAlgNum) :
    (Set.range (fun γ : DescentGalois => γ a)).Finite := by
  classical
  letI : Algebra.IsAlgebraic ℚ DescentAlgNum := AlgebraicClosure.isAlgebraic ℚ
  have ha : IsIntegral ℚ a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hne : (minpoly ℚ a).map (algebraMap ℚ DescentAlgNum) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℚ DescentAlgNum).injective).mpr
      (minpoly.ne_zero ha)
  apply (Polynomial.finite_setOfPred_isRoot hne).subset
  rintro b ⟨γ, rfl⟩
  change ((minpoly ℚ a).map (algebraMap ℚ DescentAlgNum)).eval (γ a) = 0
  rw [Polynomial.eval_map_algebraMap]
  exact minpoly.aeval_algHom ℚ γ.toAlgHom a

lemma exists_finite_galois_closure (S : Finset DescentAlgNum) :
    ∃ T : Finset DescentAlgNum, S ⊆ T ∧ GaloisStable T := by
  classical
  let T := S.biUnion (fun a => (descent_orbit_finite a).toFinset)
  have hmem (x : DescentAlgNum) : x ∈ T ↔
      ∃ a ∈ S, ∃ γ : DescentGalois, γ a = x := by
    simp only [T, Finset.mem_biUnion, Set.Finite.mem_toFinset, Set.mem_range]
  refine ⟨T, ?_, ?_⟩
  · intro a ha
    exact (hmem a).mpr ⟨a, ha, AlgEquiv.refl, rfl⟩
  · intro γ x hx
    obtain ⟨a, ha, δ, rfl⟩ := (hmem x).mp hx
    exact (hmem (γ (δ a))).mpr ⟨a, ha, δ.trans γ, rfl⟩

lemma rationalMap_fixed (q : ℚ[X]) (γ : DescentGalois) :
    (rationalMap q).map γ.toAlgHom.toRingHom = rationalMap q := by
  ext n
  simp only [rationalMap, coeff_map]
  exact γ.commutes (q.coeff n)

lemma rationalMap_eval_conjugate (q : ℚ[X]) (γ : DescentGalois)
    (z : DescentAlgNum) :
    (rationalMap q).eval (γ z) = γ ((rationalMap q).eval z) := by
  calc
    (rationalMap q).eval (γ z) =
        ((rationalMap q).map γ.toAlgHom.toRingHom).eval (γ z) :=
      congrArg (fun P : DescentAlgNum[X] => P.eval (γ z)) (rationalMap_fixed q γ).symm
    _ = γ ((rationalMap q).eval z) :=
      Polynomial.eval_map_apply γ.toAlgHom.toRingHom z

lemma rationalMap_eval_rational (q : ℚ[X]) (z : DescentAlgNum)
    (hz : z ∈ Set.range (algebraMap ℚ DescentAlgNum)) :
    (rationalMap q).eval z ∈ Set.range (algebraMap ℚ DescentAlgNum) := by
  obtain ⟨a, rfl⟩ := hz
  exact ⟨q.eval a, (Polynomial.eval_map_apply (algebraMap ℚ DescentAlgNum) a).symm⟩

lemma galoisStable_image [DecidableEq DescentAlgNum] (T : Finset DescentAlgNum) (hT : GaloisStable T)
    (γ : DescentGalois) : T.image γ = T := by
  classical
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hT γ y hy
  · intro hx
    exact Finset.mem_image.mpr ⟨γ.symm x, hT γ.symm x hx, γ.apply_symm_apply x⟩

lemma exists_rational_vanishing_polynomial (T : Finset DescentAlgNum)
    (hT : GaloisStable T) :
    ∃ q : ℚ[X], q.natDegree = T.card ∧
      rationalMap q = ∏ a ∈ T, (X - C a) := by
  classical
  letI : IsAlgClosure ℚ DescentAlgNum := AlgebraicClosure.instIsAlgClosure ℚ
  letI : IsGalois ℚ DescentAlgNum := IsAlgClosure.isGalois ℚ DescentAlgNum
  let P : DescentAlgNum[X] := ∏ a ∈ T, (X - C a)
  have hfixed (γ : DescentGalois) : P.map γ.toAlgHom.toRingHom = P := by
    simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C]
    calc
      (∏ a ∈ T, (X - C (γ a))) = ∏ a ∈ T.image γ, (X - C a) :=
        (Finset.prod_image (s := T) (g := (γ : DescentAlgNum → DescentAlgNum))
          (f := fun a : DescentAlgNum => (X - C a : DescentAlgNum[X]))
          γ.injective.injOn).symm
      _ = ∏ a ∈ T, (X - C a) := by rw [galoisStable_image T hT γ]
  have hlift : P ∈ Polynomial.lifts (algebraMap ℚ DescentAlgNum) := by
    apply (Polynomial.lifts_iff_coeff_lifts P).mpr
    intro n
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := ℚ) (P.coeff n)).mpr
    intro γ
    calc
      γ (P.coeff n) = γ.toAlgHom.toRingHom (P.coeff n) := rfl
      _ = (P.map γ.toAlgHom.toRingHom).coeff n := (Polynomial.coeff_map (p := P) γ.toAlgHom.toRingHom n).symm
      _ = P.coeff n := congrArg (fun Q : DescentAlgNum[X] => Q.coeff n) (hfixed γ)
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts P).mp hlift
  refine ⟨q, ?_, hq⟩
  have hd := Polynomial.natDegree_map_eq_of_injective
    (f := algebraMap ℚ DescentAlgNum) (algebraMap ℚ DescentAlgNum).injective q
  rw [hq] at hd
  simpa [P] using hd.symm

lemma mem_criticalValues_iff (P : DescentAlgNum[X]) (hP : 0 < P.natDegree)
    (v : DescentAlgNum) :
    v ∈ criticalValues P ↔ ∃ z, P.derivative.eval z = 0 ∧ P.eval z = v := by
  classical
  have hn : P.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (Nat.ne_of_gt hP)
  simp only [criticalValues, Finset.mem_image, Multiset.mem_toFinset,
    Polynomial.mem_roots hn, Polynomial.IsRoot.def]

lemma criticalValues_card_lt (P : DescentAlgNum[X]) (hP : 0 < P.natDegree) :
    (criticalValues P).card < P.natDegree := by
  classical
  exact lt_of_le_of_lt
    ((Finset.card_image_le).trans
      ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P.derivative)))
    (Polynomial.natDegree_derivative_lt (Nat.ne_of_gt hP))

lemma criticalValues_galoisStable (q : ℚ[X]) (hq : 0 < q.natDegree) :
    GaloisStable (criticalValues (rationalMap q)) := by
  classical
  have hd : 0 < (rationalMap q).natDegree := by
    simpa [rationalMap, Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℚ DescentAlgNum).injective] using hq
  intro γ v hv
  obtain ⟨z, hz, rfl⟩ := (mem_criticalValues_iff _ hd v).mp hv
  apply (mem_criticalValues_iff _ hd _).mpr
  refine ⟨γ z, ?_, rationalMap_eval_conjugate q γ z⟩
  have hz' : (rationalMap q.derivative).eval z = 0 := by
    simpa [rationalMap, Polynomial.derivative_map] using hz
  have he : (rationalMap q.derivative).eval (γ z) = 0 := by
    rw [rationalMap_eval_conjugate q.derivative γ z, hz', map_zero]
  simpa only [rationalMap, Polynomial.derivative_map] using he

/-- Exact algebraic rationalization interface. It includes every critical point
in the algebraic closure, with no separability or genericity side conditions. -/
def Rationalizes (q : ℚ[X]) (T : Finset DescentAlgNum) : Prop :=
  0 < q.natDegree ∧
  (∀ x ∈ T, (rationalMap q).eval x ∈ Set.range (algebraMap ℚ DescentAlgNum)) ∧
  (∀ z, (rationalMap q).derivative.eval z = 0 →
    (rationalMap q).eval z ∈ Set.range (algebraMap ℚ DescentAlgNum))

lemma rationalize_galoisStable (T : Finset DescentAlgNum) (hT : GaloisStable T) :
    ∃ q : ℚ[X], Rationalizes q T := by
  classical
  suffices H : ∀ n : ℕ, ∀ T : Finset DescentAlgNum, T.card = n →
      GaloisStable T → ∃ q : ℚ[X], Rationalizes q T from H T.card T rfl hT
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro T hn hT
    by_cases hempty : T = ∅
    · subst T
      refine ⟨X, ?_⟩
      constructor
      · simp
      constructor
      · simp
      · intro z hz
        simp [rationalMap] at hz
    · obtain ⟨q, hqdegree, hqprod⟩ := exists_rational_vanishing_polynomial T hT
      have hq : 0 < q.natDegree := by rw [hqdegree]; exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hempty)
      have hQdegree : (rationalMap q).natDegree = T.card := by
        rw [hqprod]
        simp
      have hQ : 0 < (rationalMap q).natDegree := by
        rw [hQdegree, ← hqdegree]
        exact hq
      have hlt : (criticalValues (rationalMap q)).card < n := by
        calc
          (criticalValues (rationalMap q)).card < (rationalMap q).natDegree :=
            criticalValues_card_lt (rationalMap q) hQ
          _ = T.card := hQdegree
          _ = n := hn
      obtain ⟨r, hrdegree, hrmarked, hrcritical⟩ :=
        ih (criticalValues (rationalMap q)).card hlt
          (criticalValues (rationalMap q)) rfl (criticalValues_galoisStable q hq)
      refine ⟨r.comp q, ?_⟩
      constructor
      · rw [Polynomial.natDegree_comp]
        exact Nat.mul_pos hrdegree hq
      constructor
      · intro x hx
        have hzero : (rationalMap q).eval x = 0 := by
          rw [hqprod, Polynomial.eval_prod]
          apply Finset.prod_eq_zero hx
          simp
        change ((r.comp q).map (algebraMap ℚ DescentAlgNum)).eval x ∈ _
        rw [Polynomial.map_comp, Polynomial.eval_comp]
        change (rationalMap r).eval ((rationalMap q).eval x) ∈ _
        rw [hzero]
        exact rationalMap_eval_rational r 0 ⟨0, by simp⟩
      · intro z hz
        have hh : (rationalMap q).derivative.eval z *
            (rationalMap r).derivative.eval ((rationalMap q).eval z) = 0 := by
          simpa only [rationalMap, Polynomial.map_comp, Polynomial.derivative_comp,
            Polynomial.eval_mul, Polynomial.eval_comp] using hz
        change ((r.comp q).map (algebraMap ℚ DescentAlgNum)).eval z ∈ _
        rw [Polynomial.map_comp, Polynomial.eval_comp]
        change (rationalMap r).eval ((rationalMap q).eval z) ∈ _
        rcases mul_eq_zero.mp hh with hinner | houter
        · exact hrmarked _ ((mem_criticalValues_iff _ hQ _).mpr ⟨z, hinner, rfl⟩)
        · exact hrcritical _ houter

/-- Köck's algebraic stage of polynomial Belyi construction, Lemma 3.5. -/
theorem rationalize_finite_algebraic_set (S : Finset DescentAlgNum) :
    ∃ q : ℚ[X], Rationalizes q S := by
  obtain ⟨T, hST, hT⟩ := exists_finite_galois_closure S
  obtain ⟨q, hqdegree, hqmarked, hqcritical⟩ := rationalize_galoisStable T hT
  exact ⟨q, hqdegree, fun x hx => hqmarked x (hST hx), hqcritical⟩

#print axioms rationalize_finite_algebraic_set
end BelyiConstruction


/- Complete-target assembly draft. No compilation or publication claimed. -/
open Polynomial Esquisse BelyiConstruction

theorem solution (S : Finset AlgNum) :
    ∃ f : Polynomial ℚ, IsBelyiPolynomial (f.map (algebraMap ℚ AlgNum)) ∧
      ∀ α ∈ S, (f.map (algebraMap ℚ AlgNum)).eval α = 0
        ∨ (f.map (algebraMap ℚ AlgNum)).eval α = 1 := by
  classical
  obtain ⟨q, hqdeg, hqmarked, hqcritical⟩ := rationalize_finite_algebraic_set S
  have hQdeg : 0 < (rationalMap q).natDegree := by
    rw [rationalMap, natDegree_map_eq_of_injective (algebraMap ℚ AlgNum).injective]
    exact hqdeg
  let T : Finset AlgNum := S.image (rationalMap q).eval ∪ criticalValues (rationalMap q)
  have hTrational : ∀ x ∈ T, x ∈ Set.range (algebraMap ℚ AlgNum) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hmarked | hcritical
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hmarked
      exact hqmarked a ha
    · obtain ⟨z, hz, rfl⟩ := (mem_criticalValues_iff _ hQdeg x).mp hcritical
      exact hqcritical z hz
  let R : Finset ℚ := T.preimage (algebraMap ℚ AlgNum)
    (algebraMap ℚ AlgNum).injective.injOn
  obtain ⟨f, hfdeg, hfmarked, hfcritical⟩ := rational_descent AlgNum R
  have hhom : Rat.castHom AlgNum = algebraMap ℚ AlgNum := Subsingleton.elim _ _
  have hfcritical' : ∀ z : AlgNum, (rationalMap f).derivative.eval z = 0 →
      (rationalMap f).eval z = 0 ∨ (rationalMap f).eval z = 1 := by
    simpa only [GoodCrit, rationalMap, hhom] using hfcritical
  have hfT : ∀ x ∈ T, (rationalMap f).eval x = 0 ∨ (rationalMap f).eval x = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hTrational x hx
    have ha : a ∈ R := Finset.mem_preimage.mpr hx
    have he : (rationalMap f).eval (algebraMap ℚ AlgNum a) =
        algebraMap ℚ AlgNum (f.eval a) :=
      Polynomial.eval_map_apply (algebraMap ℚ AlgNum) a
    rw [he]
    rcases hfmarked a ha with hzero | hone
    · left
      rw [hzero, map_zero]
    · right
      rw [hone, map_one]
  refine ⟨f.comp q, ⟨?_, ?_⟩, ?_⟩
  · rw [natDegree_map_eq_of_injective (algebraMap ℚ AlgNum).injective,
      natDegree_comp]
    exact Nat.mul_pos hfdeg hqdeg
  · intro z hz
    rw [map_comp, derivative_comp, eval_mul, eval_comp] at hz
    rw [map_comp, eval_comp]
    rcases mul_eq_zero.mp hz with hinner | houter
    · apply hfT
      exact Finset.mem_union_right _
        ((mem_criticalValues_iff _ hQdeg _).mpr ⟨z, hinner, rfl⟩)
    · exact hfcritical' _ houter
  · intro a ha
    rw [map_comp, eval_comp]
    apply hfT
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

#print axioms solution
