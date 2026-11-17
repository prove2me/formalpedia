-- Prove2me | solution 1 for BaconThesis.ExchangeUniv.mixing_lemma
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:33:41.519254+00:00
-- url     : https://prove2.me/submissions/13eaf55e-5395-451f-bcd8-f3aed4edf49d

import Mathlib
import Definitions.Def_BaconThesis_ExchangeUniv_suAlg
import Definitions.Def_BaconThesis_ExchangeUniv_suOn

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BaconThesis.ExchangeUniv.SolMixing

open BaconThesis.ExchangeUniv

section Gen

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The anti-Hermitian matrix `c |x⟩⟨y| - c̄ |y⟩⟨x|`. -/
def Mu (x y : ι) (c : ℂ) : Matrix ι ι ℂ := Matrix.single x y c - Matrix.single y x (star c)

lemma single_eq_smul (x y : ι) (v : ℂ) :
    Matrix.single x y v = v • Matrix.single x y (1 : ℂ) := by
  simp [Matrix.smul_single]

lemma single_apply' (x y : ι) (c : ℂ) (p q : ι) :
    Matrix.single x y c p q = if p = x ∧ q = y then c else 0 := by
  simp [Matrix.single_apply, eq_comm]

lemma Mu_swap (x y : ι) (c : ℂ) : Mu y x c = Mu x y (-star c) := by
  rw [Mu, Mu, single_eq_smul y x c, single_eq_smul x y (star c), single_eq_smul x y (-star c),
    single_eq_smul y x (star (-star c))]
  simp only [star_neg, star_star]
  module

lemma Mu_zero (x y : ι) : Mu x y 0 = 0 := by simp [Mu]

lemma lie_Mu_Mu {x y z : ι} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) (a b : ℂ) :
    ⁅Mu x y a, Mu y z b⁆ = Mu x z (a * b) := by
  simp [Mu, Ring.lie_def, sub_mul, mul_sub, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hxy, hyz, hxz, hxy.symm, hyz.symm, hxz.symm, mul_comm]

lemma single_mul_eq (x y : ι) (c : ℂ) (G : Matrix ι ι ℂ) :
    Matrix.single x y c * G = Matrix.of fun p q => if p = x then c * G y q else 0 := by
  ext p q
  by_cases h : p = x
  · subst h; simp [Matrix.single_mul_apply_same]
  · simp [Matrix.single_mul_apply_of_ne (h := h), h]

lemma mul_single_eq (x y : ι) (c : ℂ) (G : Matrix ι ι ℂ) :
    G * Matrix.single x y c = Matrix.of fun p q => if q = y then G p x * c else 0 := by
  ext p q
  by_cases h : q = y
  · subst h; simp [Matrix.mul_single_apply_same]
  · simp [Matrix.mul_single_apply_of_ne (hbj := h), h]

lemma diagonal_mul_single (f : ι → ℂ) (x y : ι) (c : ℂ) :
    Matrix.diagonal f * Matrix.single x y c = Matrix.single x y (f x * c) := by
  ext p q
  rw [Matrix.diagonal_mul, single_apply', single_apply']
  by_cases h : p = x ∧ q = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

lemma single_mul_diagonal (f : ι → ℂ) (x y : ι) (c : ℂ) :
    Matrix.single x y c * Matrix.diagonal f = Matrix.single x y (c * f y) := by
  ext p q
  rw [Matrix.mul_diagonal, single_apply', single_apply']
  by_cases h : p = x ∧ q = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

lemma lie_diag_Mu (f : ι → ℂ) (x y : ι) (c : ℂ) :
    ⁅Complex.I • Matrix.diagonal f, Mu x y c⁆ = (f x - f y) • Mu x y (Complex.I * c) := by
  simp only [Mu, Ring.lie_def, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.sub_mul,
    diagonal_mul_single, single_mul_diagonal, star_mul', Complex.star_def, Complex.conj_I]
  rw [single_eq_smul x y (f x * c), single_eq_smul y x (f y * _), single_eq_smul x y (c * f y),
    single_eq_smul y x (_ * f x), single_eq_smul x y (Complex.I * c),
    single_eq_smul y x (-Complex.I * _)]
  module

lemma lie_Mu_self {x y : ι} (hxy : x ≠ y) :
    ⁅Mu x y 1, Mu x y Complex.I⁆ =
      (2 * Complex.I) • (Matrix.single x x 1 - Matrix.single y y 1) := by
  simp [Mu, Ring.lie_def, sub_mul, mul_sub, Matrix.single_mul_single_same,
    Matrix.single_mul_single_of_ne, hxy, hxy.symm]
  simp only [single_eq_smul _ _ Complex.I, single_eq_smul _ _ (-Complex.I)]
  module

/-- Bracket with an anti-Hermitian `G` whose only entries in the rows and columns of `u`, `v`
are `G u u' = g` and `G u' u = -ḡ`. -/
lemma lie_Mu_of_rows (G : Matrix ι ι ℂ) {u u' v : ι} (g : ℂ)
    (hv1 : ∀ y, G v y = 0) (hv2 : ∀ x, G x v = 0)
    (hu1 : ∀ y, G u y = if y = u' then g else 0)
    (hu2 : ∀ x, G x u = if x = u' then -star g else 0) (a : ℂ) :
    ⁅Mu v u a, G⁆ = Mu v u' (a * g) := by
  have F1 : Matrix.single v u a * G = Matrix.single v u' (a * g) := by
    ext p q
    rw [single_mul_eq, Matrix.of_apply, single_apply', hu1]
    by_cases h1 : p = v <;> by_cases h2 : q = u' <;> simp [h1, h2]
  have F2 : Matrix.single u v (star a) * G = 0 := by
    ext p q
    rw [single_mul_eq, Matrix.of_apply, hv1]
    simp
  have F3 : G * Matrix.single v u a = 0 := by
    ext p q
    rw [mul_single_eq, Matrix.of_apply, hv2]
    simp
  have F4 : G * Matrix.single u v (star a) = Matrix.single u' v (-star g * star a) := by
    ext p q
    rw [mul_single_eq, Matrix.of_apply, single_apply', hu2]
    by_cases h1 : p = u' <;> by_cases h2 : q = v <;> simp [h1, h2]
  rw [Mu, Mu, Ring.lie_def, Matrix.sub_mul, Matrix.mul_sub, F1, F2, F3, F4, star_mul',
    single_eq_smul u' v (-star g * star a), single_eq_smul u' v (star a * star g)]
  module

lemma Mu_neg (x y : ι) (c : ℂ) : Mu x y (-c) = -Mu x y c := by
  rw [Mu, Mu, single_eq_smul x y (-c), single_eq_smul y x (star (-c)), single_eq_smul x y c,
    single_eq_smul y x (star c), star_neg]
  module

lemma Mu_decomp (x y : ι) (c : ℂ) :
    Mu x y c = c.re • Mu x y 1 + c.im • Mu x y Complex.I := by
  have hs : star c = (c.re : ℂ) - c.im * Complex.I := by
    apply Complex.ext <;> simp
  have hI : star Complex.I = -Complex.I := by simp
  rw [← Complex.coe_smul, ← Complex.coe_smul, Mu, Mu, Mu, single_eq_smul x y c,
    single_eq_smul y x (star c), single_eq_smul x y Complex.I,
    single_eq_smul y x (star Complex.I), star_one, hI]
  generalize Matrix.single x y (1 : ℂ) = E
  generalize Matrix.single y x (1 : ℂ) = E'
  have : c • E - star c • E' =
      ((c.re : ℂ) + c.im * Complex.I) • E - ((c.re : ℂ) - c.im * Complex.I) • E' := by
    rw [Complex.re_add_im, ← hs]
  rw [this]
  module

lemma Mu_apply (x y : ι) (c : ℂ) (p q : ι) :
    Mu x y c p q = (if p = x ∧ q = y then c else 0) - (if p = y ∧ q = x then star c else 0) := by
  rw [Mu, Matrix.sub_apply, single_apply', single_apply']

lemma Mu_add (x y : ι) (c d : ℂ) : Mu x y (c + d) = Mu x y c + Mu x y d := by
  ext p q; simp only [Mu_apply, Matrix.add_apply, star_add]; split_ifs <;> ring

lemma Mu_rsmul (x y : ι) (r : ℝ) (c : ℂ) : Mu x y ((r : ℂ) * c) = r • Mu x y c := by
  ext p q
  simp only [Mu_apply, Matrix.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  split_ifs <;> ring

/-- `X` vanishes outside the rows and columns satisfying `T`. -/
def supp (T : ι → Prop) (X : Matrix ι ι ℂ) : Prop := ∀ x y, X x y ≠ 0 → T x ∧ T y

/-- Traceless anti-Hermitian matrices supported on `T`. -/
def suT (T : ι → Prop) : Set (Matrix ι ι ℂ) := {X | Xᴴ = -X ∧ supp T X ∧ X.trace = 0}

lemma conjT_lie {A B : Matrix ι ι ℂ} (hA : Aᴴ = -A) (hB : Bᴴ = -B) : (⁅A, B⁆)ᴴ = -⁅A, B⁆ := by
  rw [Ring.lie_def, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hA, hB]
  noncomm_ring

lemma supp_lie {T : ι → Prop} {A B : Matrix ι ι ℂ} (hA : supp T A) (hB : supp T B) :
    supp T ⁅A, B⁆ := by
  intro p q h
  rw [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply] at h
  by_contra hc
  apply h
  have h1 : ∀ k, A p k * B k q = 0 := by
    intro k; by_contra hk
    obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hk
    exact hc ⟨(hA _ _ ha).1, (hB _ _ hb).2⟩
  have h2 : ∀ k, B p k * A k q = 0 := by
    intro k; by_contra hk
    obtain ⟨ha, hb⟩ := mul_ne_zero_iff.1 hk
    exact hc ⟨(hB _ _ ha).1, (hA _ _ hb).2⟩
  simp [h1, h2]

lemma Mu_suT {T : ι → Prop} {x y : ι} (hx : T x) (hy : T y) (hxy : x ≠ y) (c : ℂ) :
    Mu x y c ∈ suT T := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Mu, Matrix.conjTranspose_sub, Matrix.conjTranspose_single, Matrix.conjTranspose_single,
      star_star]
    abel
  · intro p q h
    rw [Mu_apply] at h
    by_cases h1 : p = x ∧ q = y
    · exact ⟨h1.1 ▸ hx, h1.2 ▸ hy⟩
    · by_cases h2 : p = y ∧ q = x
      · exact ⟨h2.1 ▸ hy, h2.2 ▸ hx⟩
      · simp [h1, h2] at h
  · rw [Mu, Matrix.trace_sub, Matrix.trace_single_eq_of_ne _ _ _ hxy,
      Matrix.trace_single_eq_of_ne _ _ _ hxy.symm, sub_zero]

lemma diag_suT {T : ι → Prop} {x y : ι} (hx : T x) (hy : T y) :
    Complex.I • (Matrix.single x x (1 : ℂ) - Matrix.single y y 1) ∈ suT T := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_single,
      Matrix.conjTranspose_single, star_one, Complex.star_def, Complex.conj_I, neg_smul]
  · intro p q h
    simp only [Matrix.smul_apply, Matrix.sub_apply, single_apply', smul_eq_mul] at h
    by_cases h1 : p = x ∧ q = x
    · exact ⟨h1.1 ▸ hx, h1.2 ▸ hx⟩
    · by_cases h2 : p = y ∧ q = y
      · exact ⟨h2.1 ▸ hy, h2.2 ▸ hy⟩
      · simp [h1, h2] at h
  · rw [Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_single_eq_same,
      Matrix.trace_single_eq_same, sub_self, smul_zero]

theorem su_mem (K : Submodule ℝ (Matrix ι ι ℂ)) (T : ι → Prop)
    (hoff' : ∀ x y, T x → T y → x ≠ y → ∀ c, Mu x y c ∈ K)
    (hdiag' : ∀ x y, T x → T y → x ≠ y →
      Complex.I • (Matrix.single x x (1 : ℂ) - Matrix.single y y 1) ∈ K) :
    suT T ⊆ K := by
  intro X ⟨hX, hXs, htr⟩
  have hstar : ∀ x y, star (X x y) = -X y x := by
    intro x y
    have := congrFun (congrFun hX y) x
    simpa [Matrix.conjTranspose_apply] using this
  have hoff : ∀ x y, x ≠ y → Mu x y (X x y) ∈ K := by
    intro x y hne
    by_cases hz : X x y = 0
    · rw [hz, Mu_zero]; exact K.zero_mem
    · obtain ⟨h1, h2⟩ := hXs x y hz
      exact hoff' x y h1 h2 hne _
  have hMd : ∀ x, Mu x x (X x x) = (2 * X x x) • Matrix.single x x (1 : ℂ) := by
    intro x
    rw [Mu, hstar, single_eq_smul x x (X x x), single_eq_smul x x (-X x x)]
    module
  have hXim : ∀ x, X x x = ((X x x).im : ℂ) * Complex.I := by
    intro x
    have h1 := congrArg Complex.re (hstar x x)
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h1
    apply Complex.ext
    · simp; linarith
    · simp
  have hdiag : ∑ x, Mu x x (X x x) ∈ K := by
    by_cases hex : ∃ x0, X x0 x0 ≠ 0
    · obtain ⟨x0, hx0⟩ := hex
      have hsum : ∑ x, Mu x x (X x x) =
          ∑ x, (2 * X x x) • (Matrix.single x x (1 : ℂ) - Matrix.single x0 x0 1) := by
        simp only [hMd, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, ← Finset.mul_sum]
        have : ∑ i, X i i = 0 := htr
        rw [this, mul_zero, zero_smul, sub_zero]
      rw [hsum]
      refine K.sum_mem fun x _ => ?_
      by_cases hz : X x x = 0
      · rw [hz, mul_zero, zero_smul]; exact K.zero_mem
      · by_cases hxx0 : x = x0
        · rw [hxx0, sub_self, smul_zero]; exact K.zero_mem
        · have hb := hdiag' x x0 (hXs x x hz).1 (hXs x0 x0 hx0).1 hxx0
          have := K.smul_mem (2 * (X x x).im) hb
          rw [← Complex.coe_smul, smul_smul] at this
          rwa [show ((2 * (X x x).im : ℝ) : ℂ) * Complex.I = 2 * X x x by
            conv_rhs => rw [hXim x]
            push_cast; ring] at this
    · push Not at hex
      have : ∑ x, Mu x x (X x x) = 0 :=
        Finset.sum_eq_zero fun x _ => by rw [hex x, Mu_zero]
      rw [this]; exact K.zero_mem
  have hXsum : (2 : ℂ) • X = ∑ x, ∑ y, Mu x y (X x y) := by
    have e1 : X = ∑ x, ∑ y, Matrix.single x y (X x y) := Matrix.matrix_eq_sum_single X
    have e2 : ∑ x, ∑ y, Matrix.single y x (star (X x y)) = -X := by
      rw [Finset.sum_comm]
      conv_rhs => rw [e1]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hstar, single_eq_smul y x (-X y x), single_eq_smul y x (X y x)]
      module
    simp only [Mu, Finset.sum_sub_distrib]
    rw [e2, ← e1]
    module
  have hsplit : ∑ x, ∑ y, Mu x y (X x y) =
      ∑ x, ∑ y, (if x = y then 0 else Mu x y (X x y)) + ∑ x, Mu x x (X x x) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : ∑ y, Mu x y (X x y) =
        ∑ y, ((if x = y then 0 else Mu x y (X x y)) + if x = y then Mu x y (X x y) else 0) :=
      Finset.sum_congr rfl fun y _ => by split_ifs <;> simp
    rw [this, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ x)]
  have hall : ∑ x, ∑ y, Mu x y (X x y) ∈ K := by
    rw [hsplit]
    refine K.add_mem (K.sum_mem fun x _ => K.sum_mem fun y _ => ?_) hdiag
    split_ifs with hxy
    · exact K.zero_mem
    · exact hoff x y hxy
  have hfin := K.smul_mem (1 / 2 : ℝ) hall
  rw [← hXsum, ← Complex.coe_smul, smul_smul] at hfin
  simpa using hfin

lemma diag_of_Mu (K : Submodule ℝ (Matrix ι ι ℂ)) {x y : ι} (hxy : x ≠ y)
    (h : ⁅Mu x y 1, Mu x y Complex.I⁆ ∈ K) :
    Complex.I • (Matrix.single x x (1 : ℂ) - Matrix.single y y 1) ∈ K := by
  rw [lie_Mu_self hxy] at h
  have := K.smul_mem (1 / 2 : ℝ) h
  rw [← Complex.coe_smul, smul_smul] at this
  convert this using 2
  push_cast; ring

theorem su_of_rel (L : LieSubalgebra ℝ (Matrix ι ι ℂ)) (T : ι → Prop)
    (h : ∀ x y, T x → T y → x ≠ y → ∀ c, Mu x y c ∈ L) : suT T ⊆ L :=
  su_mem L.toSubmodule T h fun x y hx hy hxy =>
    diag_of_Mu L.toSubmodule hxy (L.lie_mem (h x y hx hy hxy 1) (h x y hx hy hxy Complex.I))

lemma lie_diag_apply (f : ι → ℂ) (Y : Matrix ι ι ℂ) (p q : ι) :
    ⁅Complex.I • Matrix.diagonal f, Y⁆ p q = Complex.I * (f p - f q) * Y p q := by
  rw [Ring.lie_def, Matrix.sub_apply, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [smul_eq_mul]; ring

/-- Real traceless weights on `T`, peaked at `a`. -/
noncomputable def wts (T : ι → Prop) [DecidablePred T] (a : ι) (z : ι) : ℂ :=
  if T z then (if z = a then (((Finset.univ.filter T).card : ℝ) : ℂ) else 0) - 1 else 0

lemma wts_star (T : ι → Prop) [DecidablePred T] (a z : ι) : star (wts T a z) = wts T a z := by
  unfold wts; split_ifs <;> simp

lemma D_suT (T : ι → Prop) [DecidablePred T] {a : ι} (ha : T a) :
    Complex.I • Matrix.diagonal (wts T a) ∈ suT T := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.diagonal_conjTranspose,
      show star (wts T a) = wts T a from funext fun z => wts_star T a z, Complex.star_def,
      Complex.conj_I, neg_smul]
  · intro p q h
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul] at h
    by_cases hpq : p = q
    · subst hpq
      by_cases hp : T p
      · exact ⟨hp, hp⟩
      · simp [wts, hp] at h
    · simp [hpq] at h
  · rw [Matrix.trace_smul, Matrix.trace_diagonal]
    have : ∑ z, wts T a z = 0 := by
      unfold wts
      rw [← Finset.sum_filter, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        if_pos (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩)]
      simp
    rw [this, smul_zero]

lemma wts_of {T : ι → Prop} [DecidablePred T] (a : ι) {z : ι} (hz : T z) :
    wts T a z = (if z = a then (((Finset.univ.filter T).card : ℝ) : ℂ) else 0) - 1 := by
  simp [wts, hz]

theorem simple (K : Submodule ℝ (Matrix ι ι ℂ)) (T : ι → Prop)
    (hK : ∀ S ∈ suT T, ∀ w ∈ K, ⁅S, w⁆ ∈ K) {X : Matrix ι ι ℂ} (hXK : X ∈ K)
    (hXa : Xᴴ = -X) (hXs : supp T X)
    (hX : ∃ a b, T a ∧ T b ∧ a ≠ b ∧ (X a b ≠ 0 ∨ X a a ≠ X b b)) : suT T ⊆ K := by
  classical
  obtain ⟨a, b, ha, hb, hab, hX⟩ := hX
  obtain ⟨Y, hYK, hYa, hYs, hYab⟩ : ∃ Y ∈ K, Yᴴ = -Y ∧ supp T Y ∧ Y a b ≠ 0 := by
    rcases hX with h | h
    · exact ⟨X, hXK, hXa, hXs, h⟩
    · have hM := Mu_suT ha hb hab 1
      refine ⟨⁅Mu a b 1, X⁆, hK _ hM _ hXK, conjT_lie hM.1 hXa, supp_lie hM.2.1 hXs, ?_⟩
      rw [Ring.lie_def, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
      have e1 : ∀ k, Mu a b 1 a k * X k b = if k = b then X b b else 0 := by
        intro k; rw [Mu_apply]; by_cases hk : k = b <;> simp [hk, hab]
      have e2 : ∀ k, X a k * Mu a b 1 k b = if k = a then X a a else 0 := by
        intro k; rw [Mu_apply]; by_cases hk : k = a <;> simp [hk, hab, hab.symm]
      simp only [e1, e2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact sub_ne_zero.2 (Ne.symm h)
  set m : ℝ := ((Finset.univ.filter T).card : ℝ) with hm
  have hm0 : m ≠ 0 := by
    rw [hm, Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
  have hYstar : ∀ p q, star (Y p q) = -Y q p := by
    intro p q
    have := congrFun (congrFun hYa q) p
    simpa [Matrix.conjTranspose_apply] using this
  -- isolate the (a, b) entry
  have hiso : ⁅Complex.I • Matrix.diagonal (wts T a), ⁅Complex.I • Matrix.diagonal (wts T b), Y⁆⁆
      = Mu a b ((m : ℂ) ^ 2 * Y a b) := by
    ext p q
    rw [lie_diag_apply, lie_diag_apply, Mu_apply]
    by_cases h1 : p = a ∧ q = b
    · rw [h1.1, h1.2, if_pos ⟨rfl, rfl⟩, if_neg (fun h => hab h.1)]
      rw [wts_of a ha, wts_of a hb, wts_of b ha, wts_of b hb, ← hm]
      simp only [eq_self_iff_true, if_true, if_neg hab, if_neg (Ne.symm hab), sub_zero]
      linear_combination (-(m : ℂ) ^ 2 * Y a b) * Complex.I_sq
    · by_cases h2 : p = b ∧ q = a
      · rw [h2.1, h2.2, if_neg (fun h => hab h.2), if_pos ⟨rfl, rfl⟩, star_mul', hYstar]
        rw [wts_of a ha, wts_of a hb, wts_of b ha, wts_of b hb, ← hm]
        simp only [eq_self_iff_true, if_true, if_neg hab, if_neg (Ne.symm hab), zero_sub,
          star_pow, Complex.star_def, Complex.conj_ofReal]
        linear_combination (-(m : ℂ) ^ 2 * Y b a) * Complex.I_sq
      · rw [if_neg h1, if_neg h2, sub_zero]
        by_cases hpq : Y p q = 0
        · rw [hpq, mul_zero, mul_zero]
        · obtain ⟨hp, hq⟩ := hYs p q hpq
          rw [wts_of a hp, wts_of a hq, wts_of b hp, wts_of b hq, ← hm]
          have : ((if p = a then (m : ℂ) else 0) - 1 - ((if q = a then (m : ℂ) else 0) - 1)) *
              ((if p = b then (m : ℂ) else 0) - 1 - ((if q = b then (m : ℂ) else 0) - 1)) = 0 := by
            by_cases hpa : p = a <;> by_cases hqa : q = a <;> by_cases hpb : p = b <;>
              by_cases hqb : q = b <;> simp_all
          linear_combination (Complex.I * Complex.I * Y p q) * this
  have hmem0 : Mu a b ((m : ℂ) ^ 2 * Y a b) ∈ K := by
    rw [← hiso]
    exact hK _ (D_suT T ha) _ (hK _ (D_suT T hb) _ hYK)
  set c0 := (m : ℂ) ^ 2 * Y a b with hc0
  have hc0ne : c0 ≠ 0 := mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hm0)) hYab
  -- rotate the phase
  have hrot : ∀ c, Mu a b c ∈ K → Mu a b (Complex.I * c) ∈ K := by
    intro c hc
    have h := hK _ (D_suT T ha) _ hc
    rw [lie_diag_Mu, wts_of a ha, wts_of a hb, if_pos rfl, if_neg (Ne.symm hab), ← hm] at h
    have e : ((m : ℂ) - 1 - (0 - 1)) • Mu a b (Complex.I * c) = m • Mu a b (Complex.I * c) := by
      rw [← Complex.coe_smul]; congr 1; ring
    rw [e] at h
    have := K.smul_mem m⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hm0, one_smul] at this
  have hRab : ∀ c, Mu a b c ∈ K := by
    intro c
    have e : c = (((c / c0).re : ℝ) : ℂ) * c0 + (((c / c0).im : ℝ) : ℂ) * (Complex.I * c0) := by
      rw [show (((c / c0).re : ℝ) : ℂ) * c0 + (((c / c0).im : ℝ) : ℂ) * (Complex.I * c0)
        = ((((c / c0).re : ℝ) : ℂ) + (((c / c0).im : ℝ) : ℂ) * Complex.I) * c0 by ring,
        Complex.re_add_im, div_mul_cancel₀ _ hc0ne]
    rw [e, Mu_add, Mu_rsmul, Mu_rsmul]
    exact K.add_mem (K.smul_mem _ hmem0) (K.smul_mem _ (hrot _ hmem0))
  -- propagate
  have hsymm : ∀ x y, (∀ c, Mu x y c ∈ K) → ∀ c, Mu y x c ∈ K := by
    intro x y h c; rw [Mu_swap]; exact h _
  have hleft : ∀ x u v, T x → T u → x ≠ u → x ≠ v → u ≠ v → (∀ c, Mu u v c ∈ K) →
      ∀ c, Mu x v c ∈ K := by
    intro x u v hx hu hxu hxv huv h c
    have := hK _ (Mu_suT hx hu hxu 1) _ (h c)
    rwa [lie_Mu_Mu hxu huv hxv, one_mul] at this
  have hright : ∀ u v y, T v → T y → y ≠ u → y ≠ v → u ≠ v → (∀ c, Mu u v c ∈ K) →
      ∀ c, Mu u y c ∈ K := by
    intro u v y hv hy hyu hyv huv h c
    have := hK _ (Mu_suT hv hy (Ne.symm hyv) 1) _ (h c)
    rw [← lie_skew, lie_Mu_Mu huv (Ne.symm hyv) (Ne.symm hyu), mul_one] at this
    have := K.neg_mem this
    rwa [neg_neg] at this
  have hxb : ∀ x, T x → x ≠ b → ∀ c, Mu x b c ∈ K := by
    intro x hx hxb
    by_cases hxa : x = a
    · subst hxa; exact hRab
    · exact hleft x a b hx ha hxa hxb hab hRab
  have hall : ∀ x y, T x → T y → x ≠ y → ∀ c, Mu x y c ∈ K := by
    intro x y hx hy hxy
    by_cases hyb : y = b
    · subst hyb; exact hxb x hx hxy
    · by_cases hx' : x = b
      · subst hx'; exact hsymm _ _ (hxb y hy hyb)
      · exact hright x b y hb hy (Ne.symm hxy) hyb hx' (hxb x hx hx')
  exact su_mem K T hall fun x y hx hy hxy =>
    diag_of_Mu K hxy (hK _ (Mu_suT hx hy hxy 1) _ (hall x y hx hy hxy Complex.I))

end Gen

section Frame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Lie subalgebra of matrices whose conjugate `U X U†` lies in `L`. -/
def pull (U : Matrix ι ι ℂ) (hU1 : Uᴴ * U = 1) (L : LieSubalgebra ℝ (Matrix ι ι ℂ)) :
    LieSubalgebra ℝ (Matrix ι ι ℂ) where
  carrier := {X | U * X * Uᴴ ∈ L}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq, Matrix.mul_add, Matrix.add_mul] at *
    exact L.add_mem hX hY
  zero_mem' := by simp
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_setOf_eq, ← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul] at *
    rw [Complex.coe_smul]
    exact L.smul_mem r hX
  lie_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    have e : U * ⁅X, Y⁆ * Uᴴ = ⁅U * X * Uᴴ, U * Y * Uᴴ⁆ := by
      rw [Ring.lie_def, Ring.lie_def]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul, ← Matrix.mul_assoc Uᴴ U, hU1,
        Matrix.one_mul]
    rw [e]
    exact L.lie_mem hX hY

lemma mem_pull {U : Matrix ι ι ℂ} {hU1 : Uᴴ * U = 1} {L : LieSubalgebra ℝ (Matrix ι ι ℂ)}
    {X : Matrix ι ι ℂ} : X ∈ pull U hU1 L ↔ U * X * Uᴴ ∈ L := Iff.rfl

lemma conj_suT {U : Matrix ι ι ℂ} (hU1 : Uᴴ * U = 1) {T : ι → Prop} {X : Matrix ι ι ℂ}
    (hX : X ∈ suT T) : (U * X * Uᴴ)ᴴ = -(U * X * Uᴴ) ∧ (U * X * Uᴴ).trace = 0 := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hX.1]
    simp [Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU1, Matrix.one_mul]
    exact hX.2.2

/-- If the conjugates of all `Mu x y c` lie in `L`, then `L` contains `su(ι)`. -/
lemma su_sub_of_frame {U : Matrix ι ι ℂ} (hU1 : Uᴴ * U = 1) (hU2 : U * Uᴴ = 1)
    (L : LieSubalgebra ℝ (Matrix ι ι ℂ))
    (h : ∀ x y, x ≠ y → ∀ c, Mu x y c ∈ pull U hU1 L) :
    ∀ A : Matrix ι ι ℂ, Aᴴ = -A → A.trace = 0 → A ∈ L := by
  intro A hA htr
  have hsu := su_of_rel (pull U hU1 L) (fun _ => True) (fun x y _ _ hxy c => h x y hxy c)
  have hB : Uᴴ * A * U ∈ suT (fun _ : ι => True) := by
    refine ⟨?_, fun _ _ _ => ⟨trivial, trivial⟩, ?_⟩
    · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hA]
      simp [Matrix.mul_assoc]
    · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
      exact htr
  have : U * (Uᴴ * A * U) * Uᴴ ∈ L := hsu hB
  have e : U * (Uᴴ * A * U) * Uᴴ = A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU2, Matrix.one_mul, Matrix.mul_assoc, hU2,
      Matrix.mul_one]
  rwa [e] at this

lemma conj_single (U : Matrix ι ι ℂ) (x y : ι) (c : ℂ) :
    U * Matrix.single x y c * Uᴴ =
      c • Matrix.vecMulVec (fun a => U a x) (star fun a => U a y) := by
  rw [mul_single_eq]
  ext a b
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply]
  ring

lemma conj_Mu (U : Matrix ι ι ℂ) (x y : ι) (c : ℂ) :
    U * Mu x y c * Uᴴ =
      c • Matrix.vecMulVec (fun a => U a x) (star fun a => U a y) -
        star c • Matrix.vecMulVec (fun a => U a y) (star fun a => U a x) := by
  rw [Mu, Matrix.mul_sub, Matrix.sub_mul, conj_single, conj_single]

lemma conj_diag (U : Matrix ι ι ℂ) (x y : ι) :
    U * (Complex.I • (Matrix.single x x (1 : ℂ) - Matrix.single y y 1)) * Uᴴ =
      Complex.I • (Matrix.vecMulVec (fun a => U a x) (star fun a => U a x) -
        Matrix.vecMulVec (fun a => U a y) (star fun a => U a y)) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, conj_single, conj_single,
    one_smul, one_smul]

/-- A conjugated `suT T` element acts only on the span of the frame vectors indexed by `T`. -/
lemma conj_suOn {U : Matrix ι ι ℂ} (hU1 : Uᴴ * U = 1) {T : ι → Prop} {X : Matrix ι ι ℂ}
    (hX : X ∈ suT T) (S : Set (ι → ℂ))
    (hT : ∀ y, T y → ∀ v : ι → ℂ, (∀ w ∈ S, star w ⬝ᵥ v = 0) →
      star (fun a => U a y) ⬝ᵥ v = 0) :
    U * X * Uᴴ ∈ suOn S := by
  obtain ⟨h1, h2⟩ := conj_suT hU1 hX
  refine ⟨h1, h2, fun v hv => ?_⟩
  have hz : ∀ y, T y → (Uᴴ *ᵥ v) y = 0 := by
    intro y hy
    rw [← hT y hy v hv]
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
  have hXz : X *ᵥ (Uᴴ *ᵥ v) = 0 := by
    funext p
    change ∑ q, X p q * (Uᴴ *ᵥ v) q = 0
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : X p q = 0
    · rw [hq, zero_mul]
    · rw [hz q (hX.2.1 p q hq).2, mul_zero]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hXz, Matrix.mulVec_zero]

end Frame

section SuLie

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- `su(ι)` as a real Lie subalgebra. -/
def suLie : LieSubalgebra ℝ (Matrix ι ι ℂ) where
  carrier := suAlg ι
  add_mem' := by
    rintro X Y ⟨hX1, hX2⟩ ⟨hY1, hY2⟩
    refine ⟨?_, ?_⟩
    · rw [Matrix.conjTranspose_add, hX1, hY1, neg_add]
    · rw [Matrix.trace_add, hX2, hY2, add_zero]
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro r X ⟨hX1, hX2⟩
    refine ⟨?_, ?_⟩
    · rw [← Complex.coe_smul, Matrix.conjTranspose_smul, hX1]; simp
    · rw [← Complex.coe_smul, Matrix.trace_smul, hX2, smul_zero]
  lie_mem' := by
    rintro X Y ⟨hX1, -⟩ ⟨hY1, -⟩
    refine ⟨conjT_lie hX1 hY1, ?_⟩
    rw [Ring.lie_def, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

end SuLie

end BaconThesis.ExchangeUniv.SolMixing

open BaconThesis.ExchangeUniv BaconThesis.ExchangeUniv.SolMixing

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ)
    (P : Set ι) (hP : Fintype.card ι ≤ 1 ∨ (P.Nonempty ∧ Pᶜ.Nonempty)) :
    let ket : ι → ι → ℂ := fun k a => U a k
    let kb : ι → ι → Matrix ι ι ℂ := fun k l => Matrix.vecMulVec (ket k) (star (ket l))
    (LieSubalgebra.lieSpan ℝ (Matrix ι ι ℂ)
        {A | ∃ k ∈ P, ∃ l ∉ P,
          A = Complex.I • (kb k l + kb l k) ∨
          A = Complex.I • (Complex.I • kb k l - Complex.I • kb l k) ∨
          A = Complex.I • (kb k k - kb l l)} : Set (Matrix ι ι ℂ)) = suAlg ι := by
  intro ket kb
  have hU1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hU2 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have eX : ∀ k l, Complex.I • (kb k l + kb l k) = U * Mu k l Complex.I * Uᴴ := by
    intro k l
    rw [conj_Mu]
    simp only [kb, ket, Complex.star_def, Complex.conj_I, neg_smul, sub_neg_eq_add, smul_add]
  have eY : ∀ k l, Complex.I • (Complex.I • kb k l - Complex.I • kb l k) =
      U * Mu k l (-1) * Uᴴ := by
    intro k l
    rw [conj_Mu]
    simp only [kb, ket, smul_sub, smul_smul, Complex.I_mul_I, star_neg, star_one]
  have eZ : ∀ k l, Complex.I • (kb k k - kb l l) =
      U * (Complex.I • (Matrix.single k k (1 : ℂ) - Matrix.single l l 1)) * Uᴴ := by
    intro k l
    rw [conj_diag]
  set L := LieSubalgebra.lieSpan ℝ (Matrix ι ι ℂ)
    {A | ∃ k ∈ P, ∃ l ∉ P,
      A = Complex.I • (kb k l + kb l k) ∨
      A = Complex.I • (Complex.I • kb k l - Complex.I • kb l k) ∨
      A = Complex.I • (kb k k - kb l l)} with hL
  apply Set.Subset.antisymm
  · change L ≤ suLie ι
    rw [hL, LieSubalgebra.lieSpan_le]
    rintro A ⟨k, hk, l, hl, h | h | h⟩
    · have hkl : k ≠ l := fun e => hl (e ▸ hk)
      rw [h, eX]
      exact conj_suT hU1 (Mu_suT (T := fun _ => True) trivial trivial hkl _)
    · have hkl : k ≠ l := fun e => hl (e ▸ hk)
      rw [h, eY]
      exact conj_suT hU1 (Mu_suT (T := fun _ => True) trivial trivial hkl _)
    · rw [h, eZ]
      exact conj_suT hU1 (diag_suT (T := fun _ => True) trivial trivial)
  · intro A ⟨hA, htr⟩
    refine su_sub_of_frame hU1 hU2 L ?_ A hA htr
    have hcross : ∀ k ∈ P, ∀ l ∉ P, ∀ c, Mu k l c ∈ pull U hU1 L := by
      intro k hk l hl c
      have hI : Mu k l Complex.I ∈ pull U hU1 L := by
        rw [mem_pull, ← eX]
        exact LieSubalgebra.subset_lieSpan ⟨k, hk, l, hl, Or.inl rfl⟩
      have h1 : Mu k l 1 ∈ pull U hU1 L := by
        have : Mu k l (-1) ∈ pull U hU1 L := by
          rw [mem_pull, ← eY]
          exact LieSubalgebra.subset_lieSpan ⟨k, hk, l, hl, Or.inr (Or.inl rfl)⟩
        rw [Mu_neg] at this
        simpa using (pull U hU1 L).neg_mem this
      rw [Mu_decomp]
      exact (pull U hU1 L).add_mem ((pull U hU1 L).smul_mem _ h1)
        ((pull U hU1 L).smul_mem _ hI)
    have hcross' : ∀ k ∈ P, ∀ l ∉ P, ∀ c, Mu l k c ∈ pull U hU1 L := by
      intro k hk l hl c
      rw [Mu_swap]; exact hcross k hk l hl _
    have hpair : ∀ x y : ι, x ≠ y → P.Nonempty ∧ Pᶜ.Nonempty := by
      intro x y hxy
      rcases hP with h | h
      · exact absurd (Fintype.card_le_one_iff.mp h x y) hxy
      · exact h
    intro x y hxy c
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
    · obtain ⟨l, hl⟩ := (hpair x y hxy).2
      have hxl : x ≠ l := fun e => hl (e ▸ hx)
      have hly : l ≠ y := fun e => hl (e ▸ hy)
      have := (pull U hU1 L).lie_mem (hcross x hx l hl c) (hcross' y hy l hl 1)
      rwa [lie_Mu_Mu hxl hly hxy, mul_one] at this
    · exact hcross x hx y hy c
    · exact hcross' y hy x hx c
    · obtain ⟨k, hk⟩ := (hpair x y hxy).1
      have hxk : x ≠ k := fun e => hx (e ▸ hk)
      have hky : k ≠ y := fun e => hy (e ▸ hk)
      have := (pull U hU1 L).lie_mem (hcross' k hk x hx c) (hcross k hk y hy 1)
      rwa [lie_Mu_Mu hxk hky hxy, mul_one] at this
