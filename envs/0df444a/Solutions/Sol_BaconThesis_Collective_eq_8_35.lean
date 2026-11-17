-- Prove2me | solution 1 for BaconThesis.Collective.eq_8_35
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T22:35:36.298168+00:00
-- url     : https://prove2.me/submissions/3a359463-3d44-4e59-a0c3-22bb0ee4de54

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_exchange
import Definitions.Def_BaconThesis_ExchangeUniv_exchangeLie
import Definitions.Def_BaconThesis_ExchangeUniv_collS
import Definitions.Def_BaconThesis_ExchangeUniv_dfsSpace
import Definitions.Def_BaconThesis_ExchangeUniv_suOn
import Definitions.Def_BaconThesis_ExchangeUniv_totalS2
import Definitions.Def_BaconThesis_Collective_totalS2
import Definitions.Def_BaconThesis_Collective_dfsWeak

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BaconThesis.Collective.Sol921

open scoped Matrix

section Gen

variable {ι : Type} [Fintype ι] [DecidableEq ι]

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

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module

section Ladder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Raising `P`, lowering `M = P†` and weight `Z = Z†` with `[P, M] = 2Z`, `[Z, M] = -M`,
`[Z, P] = P`. -/
structure Ladder (P M Z : E →ₗ[ℂ] E) : Prop where
  adj : ∀ x y, ⟪M x, y⟫_ℂ = ⟪x, P y⟫_ℂ
  zsa : ∀ x y, ⟪Z x, y⟫_ℂ = ⟪x, Z y⟫_ℂ
  pm : ∀ x, P (M x) - M (P x) = (2 : ℂ) • Z x
  zm : ∀ x, Z (M x) - M (Z x) = - M x
  zp : ∀ x, Z (P x) - P (Z x) = P x

variable {P M Z : E →ₗ[ℂ] E} (h : Ladder P M Z)
include h

lemma Ladder.adj' (x y : E) : ⟪x, M y⟫_ℂ = ⟪P x, y⟫_ℂ := by
  rw [← inner_conj_symm, h.adj, inner_conj_symm]

lemma Ladder.M_eig {x : E} {μ : ℂ} (hx : Z x = μ • x) : Z (M x) = (μ - 1) • M x := by
  have := h.zm x
  rw [hx, map_smul, sub_eq_iff_eq_add] at this
  rw [this]; module

lemma Ladder.P_eig {x : E} {μ : ℂ} (hx : Z x = μ • x) : Z (P x) = (μ + 1) • P x := by
  have := h.zp x
  rw [hx, map_smul, sub_eq_iff_eq_add] at this
  rw [this]; module

lemma Ladder.z_pow {u : E} {J : ℂ} (hu : Z u = J • u) (k : ℕ) :
    Z ((M ^ k) u) = (J - k) • (M ^ k) u := by
  induction k with
  | zero => simp [hu]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, h.M_eig ih]
    push_cast; congr 1; ring

lemma Ladder.p_pow {u : E} {d : ℕ} (hu0 : P u = 0) (hu : Z u = ((d : ℂ) / 2) • u) (k : ℕ) :
    P ((M ^ (k + 1)) u) = (((k : ℂ) + 1) * ((d : ℂ) - k)) • (M ^ k) u := by
  induction k with
  | zero =>
    have := h.pm u
    rw [hu0, map_zero, sub_zero, hu] at this
    simp only [pow_one, pow_zero, Module.End.one_apply, CharP.cast_eq_zero, zero_add, one_mul,
      sub_zero]
    rw [this]; module
  | succ k ih =>
    have := h.pm ((M ^ (k + 1)) u)
    rw [ih, map_smul, h.z_pow hu, sub_eq_iff_eq_add] at this
    rw [pow_succ' M (k + 1), Module.End.mul_apply, this, ← Module.End.mul_apply, ← pow_succ']
    push_cast
    module

/-- `∏_{j<k} (j+1)(d-j)`, the squared norm of `M^k u` for a unit highest-weight vector `u`. -/
def F (d k : ℕ) : ℂ := ∏ j ∈ Finset.range k, (((j : ℂ) + 1) * ((d : ℂ) - j))

lemma Ladder.inner_pow {u u' : E} {d : ℕ} (hu0 : P u = 0) (hu : Z u = ((d : ℂ) / 2) • u)
    (hu0' : P u' = 0) (l : ℕ) : ∀ k : ℕ,
    ⟪(M ^ k) u, (M ^ l) u'⟫_ℂ = if k = l then F d k * ⟪u, u'⟫_ℂ else 0 := by
  induction l with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [F]
    · rw [pow_succ', Module.End.mul_apply, h.adj, pow_zero, Module.End.one_apply, hu0',
        inner_zero_right]
      simp
  | succ l ih =>
    intro k
    rw [pow_succ', Module.End.mul_apply, h.adj']
    rcases k with _ | k
    · rw [pow_zero, Module.End.one_apply, hu0, inner_zero_left]; simp
    · rw [h.p_pow hu0 hu, inner_smul_left, ih k]
      have hc : (starRingEnd ℂ) (((k : ℂ) + 1) * ((d : ℂ) - k)) = ((k : ℂ) + 1) * ((d : ℂ) - k) := by
        simp [map_mul, map_sub, map_add]
      rw [hc]
      by_cases hk : k = l
      · subst hk; rw [if_pos rfl, if_pos rfl, F, F, Finset.prod_range_succ]; ring
      · rw [if_neg hk, if_neg (fun e => hk (Nat.succ_injective e)), mul_zero]

lemma Ladder.M_top {u : E} {d : ℕ} (hu0 : P u = 0) (hu : Z u = ((d : ℂ) / 2) • u) :
    (M ^ (d + 1)) u = 0 := by
  have := h.inner_pow hu0 hu hu0 (d + 1) (d + 1)
  rw [if_pos rfl] at this
  have hF : F d (d + 1) = 0 :=
    Finset.prod_eq_zero (Finset.self_mem_range_succ d) (by simp)
  rw [hF, zero_mul] at this
  exact inner_self_eq_zero.1 this

lemma Ladder.normM (x : E) {ν : ℂ} (hx : Z x = ν • x) :
    ⟪M x, M x⟫_ℂ = ⟪P x, P x⟫_ℂ + 2 * ν * ⟪x, x⟫_ℂ := by
  rw [h.adj]
  have := h.pm x
  rw [sub_eq_iff_eq_add] at this
  rw [this, inner_add_right, ← h.adj', hx, inner_smul_right, inner_smul_right]
  ring

lemma Ladder.M_inj {x : E} {ν : ℝ} (hν : 0 < ν) (hx : Z x = (ν : ℂ) • x) (h0 : M x = 0) :
    x = 0 := by
  have := h.normM x hx
  rw [h0, inner_zero_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ((‖P x‖ ^ 2 + 2 * ν * ‖x‖ ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast; linear_combination -this
  have h3 : ‖P x‖ ^ 2 + 2 * ν * ‖x‖ ^ 2 = 0 := by exact_mod_cast h2
  have h4 : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖P x‖, sq_nonneg ‖x‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4)

lemma Ladder.P_inj {x : E} {ν : ℝ} (hν : ν < 0) (hx : Z x = (ν : ℂ) • x) (h0 : P x = 0) :
    x = 0 := by
  have := h.normM x hx
  rw [h0, inner_zero_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ((‖M x‖ ^ 2 - 2 * ν * ‖x‖ ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast; linear_combination this
  have h3 : ‖M x‖ ^ 2 - 2 * ν * ‖x‖ ^ 2 = 0 := by exact_mod_cast h2
  have h4 : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖M x‖, sq_nonneg ‖x‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4)

omit h

variable (M Z) in
/-- The image of the next-higher weight space under lowering. -/
noncomputable def Rg (μ : ℂ) : Submodule ℂ E := (Module.End.eigenspace Z (μ + 1)).map M

variable (M Z) in
/-- Highest-weight vectors of weight `μ`: the part of the weight space orthogonal to `Rg μ`. -/
noncomputable def Kh (μ : ℂ) : Submodule ℂ E := (Rg M Z μ)ᗮ ⊓ Module.End.eigenspace Z μ

include h

lemma Ladder.Rg_le (μ : ℂ) : Rg M Z μ ≤ Module.End.eigenspace Z μ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
  rw [Module.End.mem_eigenspace_iff, h.M_eig hx, add_sub_cancel_right]

lemma Ladder.Kh_P {μ : ℂ} {x : E} (hx : x ∈ Kh M Z μ) : P x = 0 := by
  have hx1 := hx.1
  have hx2 : Z x = μ • x := Module.End.mem_eigenspace_iff.1 hx.2
  have hm : M (P x) ∈ Rg M Z μ :=
    ⟨P x, Module.End.mem_eigenspace_iff.2 (h.P_eig hx2), rfl⟩
  have h0 := (Submodule.mem_orthogonal _ _).1 hx1 _ hm
  rw [← inner_conj_symm, h.adj', map_eq_zero_iff _ (RingHom.injective _)] at h0
  exact inner_self_eq_zero.1 h0

lemma Ladder.Kh_eig {μ : ℂ} {x : E} (hx : x ∈ Kh M Z μ) : Z x = μ • x :=
  Module.End.mem_eigenspace_iff.1 hx.2

lemma Ladder.finrank_Rg {μ : ℂ} {ν : ℝ} (hν : 0 < ν) (he : μ + 1 = ν) :
    finrank ℂ (Rg M Z μ) = finrank ℂ (Module.End.eigenspace Z (μ + 1)) := by
  have hr : Rg M Z μ = LinearMap.range (M ∘ₗ (Module.End.eigenspace Z (μ + 1)).subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  rw [hr, LinearMap.finrank_range_of_inj]
  intro x y hxy
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at hxy
  have hm : M ((x : E) - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hz : Z ((x : E) - y) = (ν : ℂ) • ((x : E) - y) := by
    rw [← he]; exact Module.End.mem_eigenspace_iff.1 (sub_mem x.2 y.2)
  exact Subtype.ext (sub_eq_zero.1 (h.M_inj hν hz hm))

lemma Ladder.finrank_Kh {μ : ℂ} {ν : ℝ} (hν : 0 < ν) (he : μ + 1 = ν) :
    finrank ℂ (Kh M Z μ) + finrank ℂ (Module.End.eigenspace Z (μ + 1)) = finrank ℂ (Module.End.eigenspace Z μ) := by
  rw [← h.finrank_Rg hν he, add_comm]
  exact Submodule.finrank_add_inf_finrank_orthogonal (h.Rg_le μ)

lemma Ladder.Kh_neg {μ : ℂ} {ν : ℝ} (hν : ν < 0) (he : μ = ν) {x : E} (hx : x ∈ Kh M Z μ) :
    x = 0 :=
  h.P_inj hν (he ▸ h.Kh_eig hx) (h.Kh_P hx)

lemma Ladder.span_step {S : Submodule ℂ E} (hS : ∀ x ∈ S, M x ∈ S) (μ : ℂ)
    (h1 : Module.End.eigenspace Z (μ + 1) ≤ S) (h2 : Kh M Z μ ≤ S) : Module.End.eigenspace Z μ ≤ S := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := (Rg M Z μ).exists_add_mem_mem_orthogonal x
  have hzV : z ∈ Module.End.eigenspace Z μ := by
    have := sub_mem hx (h.Rg_le μ hy)
    rwa [add_sub_cancel_left] at this
  refine S.add_mem ?_ (h2 ⟨hz, hzV⟩)
  obtain ⟨w, hw, rfl⟩ := hy
  exact hS w (h1 hw)

end Ladder

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Qubit

variable {n : ℕ}

abbrev St (n : ℕ) := Fin n → Fin 2

lemma sum_agr (i : Fin n) (x : St n) (g : St n → ℂ) :
    ∑ y, (if ∀ k, k ≠ i → x k = y k then g y else 0) = ∑ t, g (Function.update x i t) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun t _ => Function.update x i t)
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk
    rw [Function.update_of_ne hk]
  · intro t _ t' _ h
    have := congrFun h i
    simpa using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨y i, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk, hy k hk]
  · intro t _; rfl

lemma onQubit_add (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i (A + B) = onQubit i A + onQubit i B := by
  ext x y; simp only [onQubit, Matrix.add_apply]; split_ifs <;> simp

lemma onQubit_smul (i : Fin n) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i (c • A) = c • onQubit i A := by
  ext x y; simp only [onQubit, Matrix.smul_apply]; split_ifs <;> simp

lemma onQubit_star (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onQubit i A)ᴴ = onQubit i Aᴴ := by
  ext x y
  simp only [onQubit, conjTranspose_apply]
  by_cases h : ∀ k, k ≠ i → x k = y k
  · rw [if_pos h, if_pos (fun k hk => (h k hk).symm)]
  · rw [if_neg h, if_neg (fun h' => h (fun k hk => (h' k hk).symm)), star_zero]

lemma onQubit_mul_same (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit i B = onQubit i (A * B) := by
  ext x z
  rw [Matrix.mul_apply]
  have : ∀ y, onQubit i A x y * onQubit i B y z
      = if ∀ k, k ≠ i → x k = y k then A (x i) (y i) * onQubit i B y z else 0 := by
    intro y; simp only [onQubit]; split_ifs <;> simp
  simp only [this]
  rw [sum_agr]
  simp only [onQubit, Function.update_self, Matrix.mul_apply]
  by_cases h : ∀ k, k ≠ i → x k = z k
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [if_pos (fun k hk => by rw [Function.update_of_ne hk]; exact h k hk)]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun h' => h (fun k hk => by have := h' k hk; rwa [Function.update_of_ne hk] at this)),
      mul_zero]

lemma onQubit_mul_ne (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) (x z : St n) :
    (onQubit i A * onQubit j B) x z
      = if ∀ k, k ≠ i → k ≠ j → x k = z k then A (x i) (z i) * B (x j) (z j) else 0 := by
  rw [Matrix.mul_apply]
  have : ∀ y, onQubit i A x y * onQubit j B y z
      = if ∀ k, k ≠ i → x k = y k then A (x i) (y i) * onQubit j B y z else 0 := by
    intro y; simp only [onQubit]; split_ifs <;> simp
  simp only [this]
  rw [sum_agr]
  simp only [onQubit, Function.update_self, Function.update_of_ne hij.symm]
  rw [Finset.sum_eq_single (z i)]
  · by_cases h : ∀ k, k ≠ i → k ≠ j → x k = z k
    · rw [if_pos h, if_pos]
      intro k hk
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki]; exact h k hki hk
    · rw [if_neg h, if_neg, mul_zero]
      intro h'
      apply h
      intro k hki hkj
      have := h' k hkj
      rwa [Function.update_of_ne hki] at this
  · intro t _ ht
    rw [if_neg, mul_zero]
    intro h'
    have := h' i hij
    rw [Function.update_self] at this
    exact ht this
  · simp

lemma onQubit_comm (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit j B = onQubit j B * onQubit i A := by
  ext x z
  rw [onQubit_mul_ne i j hij, onQubit_mul_ne j i hij.symm]
  by_cases h : ∀ k, k ≠ i → k ≠ j → x k = z k
  · rw [if_pos h, if_pos (fun k h1 h2 => h k h2 h1), mul_comm]
  · rw [if_neg h, if_neg (fun h' => h (fun k h1 h2 => h' k h2 h1))]

variable (n) in
/-- `Σ_i O^(i)`. -/
noncomputable def coll (O : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (St n) (St n) ℂ :=
  ∑ i : Fin n, onQubit i O

lemma coll_add (A B : Matrix (Fin 2) (Fin 2) ℂ) : coll n (A + B) = coll n A + coll n B := by
  simp [coll, onQubit_add, Finset.sum_add_distrib]

lemma coll_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : coll n (c • A) = c • coll n A := by
  simp [coll, onQubit_smul, Finset.smul_sum]

lemma coll_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) : coll n (A - B) = coll n A - coll n B := by
  rw [sub_eq_add_neg, coll_add, ← neg_one_smul ℂ B, coll_smul]; module

lemma coll_star (A : Matrix (Fin 2) (Fin 2) ℂ) : (coll n A)ᴴ = coll n Aᴴ := by
  simp [coll, conjTranspose_sum, onQubit_star]

lemma coll_comm (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    coll n A * coll n B - coll n B * coll n A = coll n (A * B - B * A) := by
  simp only [coll, Finset.sum_mul_sum]
  rw [Finset.sum_comm (f := fun i j => onQubit i B * onQubit j A), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [onQubit_mul_same, onQubit_mul_same, sub_eq_add_neg (A * B), ← neg_one_smul ℂ (B * A),
      onQubit_add, onQubit_smul, neg_one_smul, ← sub_eq_add_neg]
  · intro j _ hj
    rw [onQubit_comm i j (Ne.symm hj), sub_self]
  · simp

lemma collS_eq (α : Axis) : collS n α = coll n ((1 / 2 : ℂ) • pauli α) := by
  simp [collS, coll, onQubit_smul]

def sp : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def sm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
noncomputable def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 0; 0, -1 / 2]

variable (n) in
noncomputable def Sp : Matrix (St n) (St n) ℂ := coll n sp
variable (n) in
noncomputable def Sm : Matrix (St n) (St n) ℂ := coll n sm
variable (n) in
noncomputable def Sz : Matrix (St n) (St n) ℂ := coll n sz

lemma collS_x : collS n .x = (1 / 2 : ℂ) • (Sp n + Sm n) := by
  rw [collS_eq, Sp, Sm, ← coll_add, ← coll_smul]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sp, sm]

lemma collS_y : collS n .y = (-(Complex.I / 2)) • (Sp n - Sm n) := by
  rw [collS_eq, Sp, Sm, ← coll_sub, ← coll_smul]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sp, sm] <;> ring

lemma collS_z : collS n .z = Sz n := by
  rw [collS_eq, Sz]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sz] <;> norm_num

lemma Sm_star : (Sm n)ᴴ = Sp n := by
  rw [Sm, Sp, coll_star]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sp, sm]

lemma Sz_star : (Sz n)ᴴ = Sz n := by
  rw [Sz, coll_star]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sz]

lemma comm_pm : Sp n * Sm n - Sm n * Sp n = (2 : ℂ) • Sz n := by
  rw [Sp, Sm, Sz, coll_comm, ← coll_smul]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sp, sm, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma comm_zm : Sz n * Sm n - Sm n * Sz n = -Sm n := by
  rw [Sz, Sm, coll_comm, ← neg_one_smul ℂ (coll n sm), ← coll_smul]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sm, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma comm_zp : Sz n * Sp n - Sp n * Sz n = Sp n := by
  rw [Sz, Sp, coll_comm]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sp, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Hamming weight: the number of qubits in state `1`. -/
def wt (x : St n) : ℕ := (Finset.univ.filter fun i => x i = 1).card

lemma Sz_eq : Sz n = Matrix.diagonal fun x => (n : ℂ) / 2 - wt x := by
  ext x y
  rw [Sz, coll, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have : ∀ i, onQubit i sz x x = 1 / 2 - (if x i = 1 then 1 else 0) := by
      intro i
      simp only [onQubit, if_pos (fun _ _ => rfl : ∀ k, k ≠ i → x k = x k)]
      rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h | h <;> simp [h, sz] <;> norm_num
    simp only [this, Finset.sum_sub_distrib, Finset.sum_boole, wt]
    simp
    ring
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [onQubit]
    split_ifs with h
    · have hi : x i ≠ y i := fun e => hxy (funext fun k => by
        by_cases hk : k = i
        · subst hk; exact e
        · exact h k hk)
      rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h1 | h1 <;>
        rcases Fin.exists_fin_two.1 ⟨y i, rfl⟩ with h2 | h2 <;>
        simp_all [sz]
    · rfl

lemma card_wt (w : ℕ) : (Finset.univ.filter fun y : St n => wt y = w).card = n.choose w := by
  have hc : n.choose w = (Finset.powersetCard w (Finset.univ : Finset (Fin n))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine Finset.card_bij' (fun y _ => Finset.univ.filter fun i => y i = 1)
    (fun s _ => fun i => if i ∈ s then 1 else 0) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hy⟩
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold wt
    have : (Finset.univ.filter fun i => (if i ∈ s then (1 : Fin 2) else 0) = 1) = s := by
      ext i; by_cases h : i ∈ s <;> simp [h]
    rw [this]; exact hs.2
  · intro y _
    funext i
    rcases Fin.exists_fin_two.1 ⟨y i, rfl⟩ with h | h <;> simp [h]
  · intro s _
    ext i; simp

end Qubit

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Eucl

variable {n : ℕ}

abbrev E (n : ℕ) := EuclideanSpace ℂ (St n)

noncomputable abbrev Lop (A : Matrix (St n) (St n) ℂ) : E n →ₗ[ℂ] E n := Matrix.toEuclideanLin A

lemma Lop_apply (A : Matrix (St n) (St n) ℂ) (v : E n) (x : St n) :
    Lop A v x = ∑ y, A x y * v y := by
  simp [Lop, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

lemma Lop_comp (A B : Matrix (St n) (St n) ℂ) (v : E n) : Lop A (Lop B v) = Lop (A * B) v := by
  simp [Lop, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma Lop_adj (A : Matrix (St n) (St n) ℂ) (v w : E n) : ⟪Lop A v, w⟫_ℂ = ⟪v, Lop Aᴴ w⟫_ℂ := by
  rw [Lop, Lop, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

lemma Lop_sub (A B : Matrix (St n) (St n) ℂ) (v : E n) : Lop (A - B) v = Lop A v - Lop B v := by
  rw [Lop, map_sub]; rfl

lemma Lop_smul (c : ℂ) (A : Matrix (St n) (St n) ℂ) (v : E n) : Lop (c • A) v = c • Lop A v := by
  rw [Lop, map_smul]; rfl

lemma ladder : Ladder (Lop (Sp n)) (Lop (Sm n)) (Lop (Sz n)) where
  adj x y := by rw [Lop_adj, Sm_star]
  zsa x y := by rw [Lop_adj, Sz_star]
  pm x := by rw [Lop_comp, Lop_comp, ← Lop_sub, comm_pm, Lop_smul]
  zm x := by rw [Lop_comp, Lop_comp, ← Lop_sub, comm_zm, ← neg_one_smul ℂ (Sm n), Lop_smul,
    neg_one_smul]
  zp x := by rw [Lop_comp, Lop_comp, ← Lop_sub, comm_zp]

/-- The basis vector `|y⟩`. -/
noncomputable abbrev ket (y : St n) : E n := EuclideanSpace.single y 1

lemma Sz_ket (y : St n) : Lop (Sz n) (ket y) = ((n : ℂ) / 2 - wt y) • ket y := by
  ext x
  rw [Lop_apply, Sz_eq]
  simp [Matrix.diagonal_apply, EuclideanSpace.single_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

/-- Basis strings whose weight-space eigenvalue is `μ`. -/
noncomputable def Tw (n : ℕ) (μ : ℂ) : Finset (St n) :=
  Finset.univ.filter fun y => (n : ℂ) / 2 - wt y = μ

lemma eig_eq (μ : ℂ) : Module.End.eigenspace (Lop (Sz n)) μ
    = Submodule.span ℂ (Set.range fun y : Tw n μ => ket (y : St n)) := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hc : ∀ y, y ∉ Tw n μ → v y = 0 := by
      intro y hy
      have := congrArg (fun w : E n => w y) hv
      simp only [Lop_apply, Sz_eq, Matrix.diagonal_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, PiLp.smul_apply, smul_eq_mul] at this
      have hne : (n : ℂ) / 2 - wt y ≠ μ := by simpa [Tw] using hy
      have : ((n : ℂ) / 2 - wt y - μ) * v y = 0 := by rw [sub_mul, this, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    have hv' : v = ∑ y, v y • ket y := by
      ext x
      simp [EuclideanSpace.single_apply, Pi.single_apply]
    rw [hv']
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : y ∈ Tw n μ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    · rw [hc y hy, zero_smul]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Sz_ket]
    congr 1
    simpa [Tw] using hy

lemma finrank_eig (μ : ℂ) :
    finrank ℂ (Module.End.eigenspace (Lop (Sz n)) μ) = (Tw n μ).card := by
  rw [eig_eq, finrank_span_eq_card, Fintype.card_coe]
  have := (EuclideanSpace.basisFun (St n) ℂ).toBasis.linearIndependent.comp
    (Subtype.val : Tw n μ → St n) Subtype.val_injective
  have e : (fun y : Tw n μ => ket (y : St n))
      = ⇑(EuclideanSpace.basisFun (St n) ℂ).toBasis ∘ Subtype.val := by
    funext y; simp
  rw [e]; exact this

lemma Tw_w (w : ℕ) : Tw n ((n : ℂ) / 2 - w) = Finset.univ.filter fun y : St n => wt y = w := by
  ext y
  simp only [Tw, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact_mod_cast (sub_right_injective h)
  · intro h; rw [h]

lemma finrank_eig_w (w : ℕ) :
    finrank ℂ (Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 - w)) = n.choose w := by
  rw [finrank_eig, Tw_w, card_wt]

lemma eig_top : Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 + 1) = ⊥ := by
  rw [eig_eq]
  have : Tw n ((n : ℂ) / 2 + 1) = ∅ := by
    ext y
    simp only [Tw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    have : (wt y : ℂ) + 1 = 0 := by linear_combination -h
    exact_mod_cast (Nat.cast_add_one_ne_zero (wt y)) this
  rw [Submodule.span_eq_bot]
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  rw [this] at hy
  exact absurd hy (Finset.notMem_empty y)

lemma ket_mem (y : St n) : ket y ∈ Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 - wt y) := by
  rw [Module.End.mem_eigenspace_iff, Sz_ket]

end Eucl

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Tens

variable {n : ℕ}

lemma sum_cons (f : St (n + 1) → ℂ) : ∑ x, f x = ∑ c : Fin 2, ∑ y : St n, f (Fin.cons c y) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 2) _ _ (fun _ => rfl)).symm

/-- `a ⊗ v`, with `a` on the newest qubit `0`. -/
noncomputable def tens (a : Fin 2 → ℂ) (v : E n) : E (n + 1) :=
  WithLp.toLp 2 fun x => a (x 0) * v (Fin.tail x)

@[simp] lemma tens_apply (a : Fin 2 → ℂ) (v : E n) (x : St (n + 1)) :
    tens a v x = a (x 0) * v (Fin.tail x) := rfl

lemma tens_add (a : Fin 2 → ℂ) (v w : E n) : tens a (v + w) = tens a v + tens a w := by
  ext x; simp [mul_add]

lemma tens_smul (a : Fin 2 → ℂ) (c : ℂ) (v : E n) : tens a (c • v) = c • tens a v := by
  ext x; simp; ring

lemma tens_add_left (a b : Fin 2 → ℂ) (v : E n) : tens (a + b) v = tens a v + tens b v := by
  ext x; simp [add_mul]

lemma tens_smul_left (a : Fin 2 → ℂ) (c : ℂ) (v : E n) : tens (c • a) v = c • tens a v := by
  ext x; simp; ring

lemma tens_zero (a : Fin 2 → ℂ) : tens a (0 : E n) = 0 := by ext x; simp

lemma inner_tens (a b : Fin 2 → ℂ) (v w : E n) :
    ⟪tens a v, tens b w⟫_ℂ = (∑ c, star (a c) * b c) * ⟪v, w⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, sum_cons, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [RCLike.inner_apply, starRingEnd_apply]
  have h1 := tens_apply a v (Fin.cons c y)
  have h2 := tens_apply b w (Fin.cons c y)
  simp only [Fin.cons_zero, Fin.tail_cons] at h1 h2
  rw [show (tens a v).ofLp (Fin.cons c y) = tens a v (Fin.cons c y) from rfl,
    show (tens b w).ofLp (Fin.cons c y) = tens b w (Fin.cons c y) from rfl, h1, h2, star_mul']
  ring

/-- Basis state of the newest qubit. -/
def qv (b : Fin 2) : Fin 2 → ℂ := fun c => if c = b then 1 else 0

lemma qv_inner (b b' : Fin 2) : (∑ c, star (qv b c) * qv b' c) = if b = b' then 1 else 0 := by
  fin_cases b <;> fin_cases b' <;> simp [qv, Fin.sum_univ_two]

lemma eq_tens (x : E (n + 1)) :
    x = tens (qv 0) (WithLp.toLp 2 fun y => x (Fin.cons 0 y))
      + tens (qv 1) (WithLp.toLp 2 fun y => x (Fin.cons 1 y)) := by
  ext z
  simp only [PiLp.add_apply, tens_apply, qv]
  rcases Fin.exists_fin_two.1 ⟨z 0, rfl⟩ with h | h <;> rw [h] <;> simp <;>
    rw [← h, Fin.cons_self_tail]

/-- `X` acting on qubits `1, …, n`. -/
def liftT (X : Matrix (St n) (St n) ℂ) : Matrix (St (n + 1)) (St (n + 1)) ℂ :=
  fun x y => if x 0 = y 0 then X (Fin.tail x) (Fin.tail y) else 0

lemma Lop_liftT (X : Matrix (St n) (St n) ℂ) (a : Fin 2 → ℂ) (v : E n) :
    Lop (liftT X) (tens a v) = tens a (Lop X v) := by
  ext x
  rw [Lop_apply, sum_cons, tens_apply, Lop_apply, Finset.mul_sum]
  rw [Finset.sum_eq_single (x 0)]
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp [liftT]; ring
  · intro c _ hc
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [liftT, Ne.symm hc]
  · simp

lemma liftT_mul (X Y : Matrix (St n) (St n) ℂ) : liftT (X * Y) = liftT X * liftT Y := by
  ext x z
  rw [Matrix.mul_apply, sum_cons, Finset.sum_eq_single (x 0)]
  · simp [liftT, Matrix.mul_apply]
  · intro c _ hc
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [liftT, Ne.symm hc]
  · simp

lemma liftT_add (X Y : Matrix (St n) (St n) ℂ) : liftT (X + Y) = liftT X + liftT Y := by
  ext x z; simp only [liftT, Matrix.add_apply]; split_ifs <;> simp

lemma liftT_smul (c : ℂ) (X : Matrix (St n) (St n) ℂ) : liftT (c • X) = c • liftT X := by
  ext x z; simp only [liftT, Matrix.smul_apply]; split_ifs <;> simp

lemma liftT_sub (X Y : Matrix (St n) (St n) ℂ) : liftT (X - Y) = liftT X - liftT Y := by
  ext x z; simp only [liftT, Matrix.sub_apply]; split_ifs <;> simp

lemma liftT_one : liftT (1 : Matrix (St n) (St n) ℂ) = 1 := by
  ext x z
  simp only [liftT, Matrix.one_apply]
  by_cases h0 : x 0 = z 0
  · rw [if_pos h0]
    by_cases ht : Fin.tail x = Fin.tail z
    · rw [if_pos ht, if_pos]; rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail z, h0, ht]
    · rw [if_neg ht, if_neg]; intro e; exact ht (by rw [e])
  · rw [if_neg h0, if_neg]; intro e; exact h0 (by rw [e])

lemma liftT_sum {ι : Type*} (s : Finset ι) (X : ι → Matrix (St n) (St n) ℂ) :
    liftT (∑ i ∈ s, X i) = ∑ i ∈ s, liftT (X i) := by
  ext x z; simp only [liftT, Matrix.sum_apply]; split_ifs <;> simp

lemma onQubit_succ (i : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i.succ O = liftT (onQubit i O) := by
  ext x y
  simp only [onQubit, liftT, Fin.tail]
  by_cases h0 : x 0 = y 0
  · rw [if_pos h0]
    congr 1
    apply propext
    constructor
    · intro h k hk; exact h k.succ (fun e => hk (Fin.succ_injective _ e))
    · intro h k hk
      cases k using Fin.cases with
      | zero => exact h0
      | succ k' => exact h k' (fun e => hk (by rw [e]))
  · rw [if_neg h0, if_neg]
    intro h; exact h0 (h 0 (Fin.succ_ne_zero i).symm)

lemma Lop_onQubit0 (O : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) (v : E n) :
    Lop (onQubit (0 : Fin (n + 1)) O) (tens a v) = tens (O *ᵥ a) v := by
  ext x
  rw [Lop_apply, sum_cons, tens_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (Fin.tail x)]
  · simp only [onQubit, tens_apply, Fin.cons_zero, Fin.tail_cons]
    rw [if_pos]
    · ring
    intro k hk
    obtain ⟨k', rfl⟩ := Fin.exists_succ_eq.2 hk
    simp [Fin.tail]
  · intro y _ hy
    simp only [onQubit, tens_apply]
    rw [if_neg, zero_mul]
    intro h
    apply hy
    funext k
    have := h k.succ (Fin.succ_ne_zero k)
    simpa [Fin.tail] using this.symm
  · simp

lemma coll_succ (O : Matrix (Fin 2) (Fin 2) ℂ) :
    coll (n + 1) O = onQubit 0 O + liftT (coll n O) := by
  rw [coll, Fin.sum_univ_succ, coll, liftT_sum]
  simp only [onQubit_succ]

lemma Lop_coll_tens (O : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 2 → ℂ) (v : E n) :
    Lop (coll (n + 1) O) (tens a v) = tens (O *ᵥ a) v + tens a (Lop (coll n O) v) := by
  rw [coll_succ, Lop, map_add, LinearMap.add_apply, ← Lop, ← Lop, Lop_onQubit0, Lop_liftT]

lemma exchange_succ (i j : Fin n) :
    exchange i.succ j.succ = liftT (exchange i j) := by
  ext x y
  simp only [exchange, liftT]
  have key : x = y ∘ Equiv.swap i.succ j.succ ↔
      x 0 = y 0 ∧ Fin.tail x = Fin.tail y ∘ Equiv.swap i j := by
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · rw [h]; simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
          (Fin.succ_ne_zero j).symm]
      · funext k; rw [h]; simp [Fin.tail, Equiv.swap_apply_def, Fin.succ_inj]
        split_ifs <;> rfl
    · rintro ⟨h0, ht⟩
      funext k
      refine Fin.cases ?_ (fun k' => ?_) k
      · simp [h0, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm
          (Fin.succ_ne_zero j).symm]
      · have := congrFun ht k'
        simp only [Fin.tail, Function.comp_apply] at this
        rw [this]; simp [Equiv.swap_apply_def, Fin.succ_inj]
        split_ifs <;> rfl
  by_cases h : x = y ∘ Equiv.swap i.succ j.succ
  · rw [if_pos h, if_pos (key.1 h).1, if_pos (key.1 h).2]
  · rw [if_neg h]
    by_cases h0 : x 0 = y 0
    · rw [if_pos h0, if_neg (fun h' => h (key.2 ⟨h0, h'⟩))]
    · rw [if_neg h0]

lemma Lop_exchange (i j : Fin n) (v : E n) (x : St n) :
    Lop (exchange i j) v x = v (x ∘ Equiv.swap i j) := by
  rw [Lop_apply, Finset.sum_eq_single (x ∘ Equiv.swap i j)]
  · rw [exchange, if_pos]; · ring
    funext k; simp
  · intro y _ hy
    rw [exchange, if_neg, zero_mul]
    intro h; apply hy; rw [h]; funext k; simp
  · simp

lemma Lop_exchange01 (a b : Fin 2 → ℂ) (v : E n) :
    Lop (exchange (0 : Fin (n + 2)) 1) (tens a (tens b v)) = tens b (tens a v) := by
  ext x
  rw [Lop_exchange]
  have e1 : (x ∘ Equiv.swap (0 : Fin (n + 2)) 1) 0 = x 1 := by simp
  have e2 : (x ∘ Equiv.swap (0 : Fin (n + 2)) 1) 1 = x 0 := by simp
  have e3 : Fin.tail (Fin.tail (x ∘ Equiv.swap (0 : Fin (n + 2)) 1)) = Fin.tail (Fin.tail x) := by
    funext k
    simp only [Fin.tail, Function.comp_apply]
    have hs : (Equiv.swap (0 : Fin (n + 2)) 1) k.succ.succ = k.succ.succ := by
      apply Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
      intro e
      have := congrArg Fin.val e
      simp at this
    rw [hs]
  show a ((x ∘ _) 0) * (b ((x ∘ _) 1) * v (Fin.tail (Fin.tail (x ∘ _))))
    = b (x 0) * (a (x 1) * v (Fin.tail (Fin.tail x)))
  rw [e1, e2, e3]
  ring

end Tens

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Path

lemma wt_eq_sum {n : ℕ} (x : St n) : wt x = ∑ i, (x i : ℕ) := by
  rw [wt, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h | h <;> simp [h]

lemma wt_cons {n : ℕ} (c : Fin 2) (y : St n) : wt (Fin.cons c y : St (n + 1)) = wt y + c := by
  rw [wt_eq_sum, wt_eq_sum, Fin.sum_univ_succ]
  simp [add_comm]

lemma wt_tail {n : ℕ} (w : St (n + 1)) : wt w = wt (Fin.tail w) + w 0 := by
  conv_lhs => rw [← Fin.cons_self_tail w]
  rw [wt_cons]

lemma wt_le {n : ℕ} (x : St n) : wt x ≤ n := by
  rw [wt]; exact (Finset.card_filter_le _ _).trans (by simp)

/-- Validity of a path: every `T` step (a `1`) needs total spin at least `1/2` before it. -/
def validB : (n : ℕ) → St n → Bool
  | 0, _ => true
  | n + 1, w => validB n (Fin.tail w) && (w 0 == 0 || decide (2 * wt (Fin.tail w) + 1 ≤ n))

lemma validB_succ {n : ℕ} (w : St (n + 1)) :
    validB (n + 1) w = true ↔
      validB n (Fin.tail w) = true ∧ (w 0 = 1 → 2 * wt (Fin.tail w) + 1 ≤ n) := by
  simp only [validB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun h => h2.resolve_left (by rw [h]; decide)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h | h
    · exact Or.inl h
    · exact Or.inr (h2 h)

lemma valid_two_wt {n : ℕ} (w : St n) (h : validB n w = true) : 2 * wt w ≤ n := by
  induction n with
  | zero => simp [wt]
  | succ n ih =>
    rw [validB_succ] at h
    have := ih _ h.1
    rw [wt_tail]
    rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h0 | h0
    · rw [h0]; simp; omega
    · rw [h0]; have := h.2 h0; simp; omega

/-- Paths to total spin `n/2 - r` on `n` qubits. -/
abbrev Path (n r : ℕ) := {w : St n // validB n w = true ∧ wt w = r}

instance (n r : ℕ) : Fintype (Path n r) := by unfold Path; infer_instance
instance (n r : ℕ) : DecidableEq (Path n r) := by unfold Path; infer_instance

lemma Path.two_le {n r : ℕ} (p : Path n r) : 2 * r ≤ n := p.2.2 ▸ valid_two_wt _ p.2.1

/-- `-√(d/(d+1))` and `1/√(d(d+1))`. -/
noncomputable def be (d : ℕ) : ℂ := ((1 / Real.sqrt ((d : ℝ) * (d + 1)) : ℝ) : ℂ)
noncomputable def al (d : ℕ) : ℂ := -(d : ℂ) * be d

lemma al_be (d : ℕ) : al d + be d * d = 0 := by rw [al]; ring

lemma be_sq {d : ℕ} (hd : 1 ≤ d) : be d * be d * ((d : ℂ) * (d + 1)) = 1 := by
  rw [be, ← Complex.ofReal_mul]
  have hp : (0 : ℝ) < (d : ℝ) * (d + 1) := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have : (1 / Real.sqrt ((d : ℝ) * (d + 1))) * (1 / Real.sqrt ((d : ℝ) * (d + 1)))
      * ((d : ℝ) * (d + 1)) = 1 := by
    have hne : Real.sqrt ((d : ℝ) * (d + 1)) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
    have hsq := Real.mul_self_sqrt hp.le
    field_simp
    linarith [hsq]
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) this
  push_cast at h2 ⊢
  exact h2

lemma al_sq {d : ℕ} (hd : 1 ≤ d) : al d * al d + be d * be d * d = 1 := by
  have := be_sq hd
  rw [al]; linear_combination this

lemma be_star (d : ℕ) : star (be d) = be d := by simp [be]
lemma al_star (d : ℕ) : star (al d) = al d := by simp [al, be]

lemma be_ne {d : ℕ} (hd : 1 ≤ d) : be d ≠ 0 := by
  intro h; have := be_sq hd; rw [h] at this; simp at this

/-- The `T` map: couple a spin-`d/2` highest-weight vector with a down spin to spin `(d-1)/2`. -/
noncomputable def Tm {n : ℕ} (d : ℕ) (u : E n) : E (n + 1) :=
  al d • tens (qv 1) u + be d • tens (qv 0) (Lop (Sm n) u)

noncomputable def Bm {n : ℕ} (u : E n) : E (n + 1) := tens (qv 0) u

/-- The path basis vector. -/
noncomputable def psi : (n : ℕ) → St n → E n
  | 0, _ => EuclideanSpace.single (fun i => i.elim0) 1
  | n + 1, w => if w 0 = 0 then Bm (psi n (Fin.tail w))
      else Tm (n - 2 * wt (Fin.tail w)) (psi n (Fin.tail w))

lemma psi_cons0 {n : ℕ} (y : St n) : psi (n + 1) (Fin.cons 0 y) = Bm (psi n y) := by
  simp [psi]

lemma psi_cons1 {n : ℕ} (y : St n) :
    psi (n + 1) (Fin.cons 1 y) = Tm (n - 2 * wt y) (psi n y) := by
  simp [psi]

lemma sz_qv0 : sz *ᵥ qv 0 = (1 / 2 : ℂ) • qv 0 := by
  ext c; fin_cases c <;> simp [sz, qv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
lemma sz_qv1 : sz *ᵥ qv 1 = (-1 / 2 : ℂ) • qv 1 := by
  ext c; fin_cases c <;> simp [sz, qv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
lemma sp_qv0 : sp *ᵥ qv 0 = 0 := by
  ext c; fin_cases c <;> simp [sp, qv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
lemma sp_qv1 : sp *ᵥ qv 1 = qv 0 := by
  ext c; fin_cases c <;> simp [sp, qv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
lemma sm_qv0 : sm *ᵥ qv 0 = qv 1 := by
  ext c; fin_cases c <;> simp [sm, qv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
lemma sm_qv1 : sm *ᵥ qv 1 = 0 := by
  ext c; fin_cases c <;> simp [sm, qv, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

variable {n : ℕ}

lemma tens_zero_left (v : E n) : tens 0 v = 0 := by ext x; simp

lemma Sz_tens (a : Fin 2 → ℂ) (v : E n) :
    Lop (Sz (n + 1)) (tens a v) = tens (sz *ᵥ a) v + tens a (Lop (Sz n) v) := Lop_coll_tens _ _ _
lemma Sp_tens (a : Fin 2 → ℂ) (v : E n) :
    Lop (Sp (n + 1)) (tens a v) = tens (sp *ᵥ a) v + tens a (Lop (Sp n) v) := Lop_coll_tens _ _ _
lemma Sm_tens (a : Fin 2 → ℂ) (v : E n) :
    Lop (Sm (n + 1)) (tens a v) = tens (sm *ᵥ a) v + tens a (Lop (Sm n) v) := Lop_coll_tens _ _ _

/-- Highest-weight vectors of total spin `n/2 - r`. -/
def HW (n r : ℕ) (x : E n) : Prop :=
  Lop (Sz n) x = ((n : ℂ) / 2 - r) • x ∧ Lop (Sp n) x = 0

lemma SpSm_hw {u : E n} {r : ℕ} (hu : HW n r u) :
    Lop (Sp n) (Lop (Sm n) u) = (((n : ℂ) - 2 * r)) • u := by
  have := (ladder (n := n)).pm u
  rw [hu.2, map_zero, sub_zero, hu.1, smul_smul] at this
  rw [this]; congr 1; ring

lemma Bm_hw {u : E n} {r : ℕ} (hu : HW n r u) : HW (n + 1) r (Bm u) := by
  constructor
  · rw [Bm, Sz_tens, sz_qv0, hu.1, tens_smul_left, tens_smul, ← add_smul]
    push_cast; congr 1; ring
  · rw [Bm, Sp_tens, sp_qv0, hu.2, tens_zero_left, tens_zero, add_zero]

lemma Tm_hw {u : E n} {r : ℕ} (hu : HW n r u) (hd : 1 ≤ n - 2 * r) :
    HW (n + 1) (r + 1) (Tm (n - 2 * r) u) := by
  have h2r : 2 * r ≤ n := by omega
  have hdc : ((n - 2 * r : ℕ) : ℂ) = (n : ℂ) - 2 * r := by
    rw [Nat.cast_sub h2r]; push_cast; ring
  constructor
  · rw [Tm, map_add, map_smul, map_smul, Sz_tens, Sz_tens, sz_qv1, sz_qv0, hu.1,
      (ladder (n := n)).M_eig hu.1]
    simp only [tens_smul_left, tens_smul, smul_add, smul_smul]
    push_cast
    rw [show ((n : ℂ) / 2 - r - 1) = ((n : ℂ) + 1) / 2 - (r + 1) + -1 / 2 + 1 / 2 - 1 / 2 by ring]
    module
  · rw [Tm, map_add, map_smul, map_smul, Sp_tens, Sp_tens, sp_qv1, sp_qv0, hu.2, SpSm_hw hu,
      tens_zero, tens_zero_left, zero_add, add_zero, tens_smul, smul_smul, ← add_smul, hdc.symm]
    rw [al_be, zero_smul]

lemma tens_inj (a b a' b' : E n)
    (h : tens (qv 0) a + tens (qv 1) b = tens (qv 0) a' + tens (qv 1) b') : a = a' ∧ b = b' := by
  constructor
  · ext y
    have := congrArg (fun x : E (n + 1) => x (Fin.cons 0 y)) h
    simpa [qv] using this
  · ext y
    have := congrArg (fun x : E (n + 1) => x (Fin.cons 1 y)) h
    simpa [qv] using this

lemma psi_hw : ∀ (n : ℕ) (w : St n), validB n w = true → HW n (wt w) (psi n w)
  | 0, w, _ => by
    constructor
    · rw [Sz_eq]; ext x
      simp [Lop_apply, wt]
    · rw [Sp, coll]; simp
  | n + 1, w, hv => by
    rw [validB_succ] at hv
    rw [← Fin.cons_self_tail w, wt_cons]
    rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h0 | h0
    · rw [h0, psi_cons0]; simpa using Bm_hw (psi_hw n _ hv.1)
    · rw [h0, psi_cons1]
      have := Tm_hw (psi_hw n _ hv.1) (by have := hv.2 h0; omega)
      simpa using this

lemma inner_psi : ∀ (n : ℕ) (w w' : St n), validB n w = true → validB n w' = true →
    ⟪psi n w, psi n w'⟫_ℂ = if w = w' then 1 else 0
  | 0, w, w', _, _ => by
    have : w = w' := funext fun i => i.elim0
    subst this
    simp only [psi, if_pos rfl]
    rw [EuclideanSpace.inner_single_left]
    simp
  | n + 1, w, w', hv, hv' => by
    rw [validB_succ] at hv hv'
    have ih := inner_psi n (Fin.tail w) (Fin.tail w') hv.1 hv'.1
    have hcons : w = w' ↔ w 0 = w' 0 ∧ Fin.tail w = Fin.tail w' := by
      constructor
      · rintro rfl; exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩; rw [← Fin.cons_self_tail w, ← Fin.cons_self_tail w', h1, h2]
    conv_lhs => rw [← Fin.cons_self_tail w, ← Fin.cons_self_tail w']
    have hw := psi_hw n _ hv.1
    have hw' := psi_hw n _ hv'.1
    rcases Fin.exists_fin_two.1 ⟨w 0, rfl⟩ with h0 | h0 <;>
      rcases Fin.exists_fin_two.1 ⟨w' 0, rfl⟩ with h0' | h0'
    · rw [h0, h0', psi_cons0, psi_cons0, Bm, Bm, inner_tens, qv_inner, if_pos rfl, one_mul, ih]
      simp [hcons, h0, h0']
    · rw [h0, h0', psi_cons0, psi_cons1, Bm, Tm, inner_add_right, inner_smul_right,
        inner_smul_right, inner_tens, inner_tens, qv_inner, qv_inner,
        (ladder (n := n)).adj', hw.2, inner_zero_left]
      simp [hcons, h0, h0']
    · rw [h0, h0', psi_cons1, psi_cons0, Bm, Tm, inner_add_left, inner_smul_left,
        inner_smul_left, inner_tens, inner_tens, qv_inner, qv_inner, (ladder (n := n)).adj,
        hw'.2, inner_zero_right]
      simp [hcons, h0, h0']
    · rw [h0, h0', psi_cons1, psi_cons1, Tm, Tm]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_tens,
        qv_inner]
      simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_false, if_true, zero_mul, mul_zero,
        add_zero, zero_add, one_mul]
      rw [(ladder (n := n)).adj, SpSm_hw hw', inner_smul_right, ih]
      by_cases ht : Fin.tail w = Fin.tail w'
      · rw [if_pos ht, if_pos (hcons.2 ⟨h0.trans h0'.symm, ht⟩)]
        rw [← ht]
        have hd := hv.2 h0
        have hdc : ((n - 2 * wt (Fin.tail w) : ℕ) : ℂ) = (n : ℂ) - 2 * wt (Fin.tail w) := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [starRingEnd_apply, starRingEnd_apply, al_star, be_star, ← hdc]
        have := al_sq (d := n - 2 * wt (Fin.tail w)) (by omega)
        linear_combination this
      · rw [if_neg ht, if_neg (fun e => ht (hcons.1 e).2)]; ring

end Path

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Span

variable {n : ℕ}

noncomputable def tensL (a : Fin 2 → ℂ) : E n →ₗ[ℂ] E (n + 1) where
  toFun := tens a
  map_add' := tens_add a
  map_smul' := tens_smul a

noncomputable def TmL (n d : ℕ) : E n →ₗ[ℂ] E (n + 1) :=
  al d • tensL (qv 1) + be d • (tensL (qv 0) ∘ₗ Lop (Sm n))

lemma TmL_apply (d : ℕ) (u : E n) : TmL n d u = Tm d u := rfl

variable (n) in
noncomputable def SP (r : ℕ) : Submodule ℂ (E n) :=
  Submodule.span ℂ (Set.range fun p : Path n r => psi n p.1)

lemma psi_mem (r : ℕ) (p : Path n r) : psi n p.1 ∈ SP n r :=
  Submodule.subset_span ⟨p, rfl⟩

lemma Bm_SP {r : ℕ} {v : E n} (hv : v ∈ SP n r) : Bm v ∈ SP (n + 1) r := by
  have := Submodule.apply_mem_span_image_of_mem_span (tensL (n := n) (qv 0)) hv
  refine Submodule.span_mono ?_ this
  rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
  refine ⟨⟨Fin.cons 0 p.1, ?_, ?_⟩, ?_⟩
  · rw [validB_succ]; simp [p.2.1]
  · rw [wt_cons]; simp [p.2.2]
  · show psi (n + 1) (Fin.cons 0 p.1) = tens (qv 0) (psi n p.1)
    rw [psi_cons0]; rfl

lemma Tm_SP {s : ℕ} (hd : 2 * s + 1 ≤ n) {u : E n} (hu : u ∈ SP n s) :
    Tm (n - 2 * s) u ∈ SP (n + 1) (s + 1) := by
  have := Submodule.apply_mem_span_image_of_mem_span (TmL n (n - 2 * s)) hu
  refine Submodule.span_mono ?_ this
  rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
  refine ⟨⟨Fin.cons 1 p.1, ?_, ?_⟩, ?_⟩
  · rw [validB_succ]; simp [p.2.1, p.2.2, hd]
  · rw [wt_cons]; simp [p.2.2]
  · show psi (n + 1) (Fin.cons 1 p.1) = Tm (n - 2 * s) (psi n p.1)
    rw [psi_cons1, p.2.2]

lemma hw_zero_of {s : ℕ} {u v : E n} (hs : n ≤ 2 * s) (hu : HW n s u)
    (hv : Lop (Sp n) v + u = 0) : u = 0 := by
  have hn := (ladder (n := n)).normM u hu.1
  rw [hu.2, inner_zero_left, zero_add] at hn
  have hm : Lop (Sm n) u = 0 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hn
    have h2 : ((‖Lop (Sm n) u‖ ^ 2 - 2 * ((n : ℝ) / 2 - s) * ‖u‖ ^ 2 : ℝ) : ℂ) = 0 := by
      push_cast; linear_combination hn
    have h3 : ‖Lop (Sm n) u‖ ^ 2 - 2 * ((n : ℝ) / 2 - s) * ‖u‖ ^ 2 = 0 := by exact_mod_cast h2
    have h4 : (n : ℝ) / 2 - s ≤ 0 := by
      have : (n : ℝ) ≤ 2 * s := by exact_mod_cast hs
      linarith
    have h5 : ‖Lop (Sm n) u‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖Lop (Sm n) u‖, sq_nonneg ‖u‖]
    exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h5)
  have hu' : u = -Lop (Sp n) v := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hv
  have : ⟪u, u⟫_ℂ = 0 := by
    nth_rewrite 1 [hu']
    rw [inner_neg_left, ← (ladder (n := n)).adj', hm, inner_zero_right, neg_zero]
  exact inner_self_eq_zero.1 this

lemma hw_span : ∀ (n r : ℕ) (x : E n), HW n r x → x ∈ SP n r
  | 0, r, x, hx => by
    by_cases hr : r = 0
    · subst hr
      have hp : validB 0 (fun i => i.elim0) = true ∧ wt (fun i : Fin 0 => i.elim0) = 0 :=
        ⟨rfl, by simp [wt]⟩
      have : x = x (fun i => i.elim0) • psi 0 (fun i => i.elim0) := by
        ext y
        have : y = fun i => i.elim0 := funext fun i => i.elim0
        subst this
        simp [psi]
      rw [this]
      exact Submodule.smul_mem _ _ (psi_mem 0 ⟨_, hp⟩)
    · have h1 := hx.1
      rw [Sz_eq] at h1
      have : x = 0 := by
        ext y
        have := congrArg (fun z : E 0 => z y) h1
        simp [Lop_apply, Matrix.diagonal_apply, wt] at this
        rcases this with h | h
        · exact absurd h (by exact_mod_cast hr)
        · simpa using h
      rw [this]; exact Submodule.zero_mem _
  | n + 1, r, x, hx => by
    set v : E n := WithLp.toLp 2 fun y => x (Fin.cons 0 y) with hvd
    set u : E n := WithLp.toLp 2 fun y => x (Fin.cons 1 y) with hud
    have hx' := eq_tens x
    rw [← hvd, ← hud] at hx'
    have hz := hx.1
    rw [hx', map_add, Sz_tens, Sz_tens, sz_qv0, sz_qv1, smul_add] at hz
    set μ : ℂ := ((n + 1 : ℕ) : ℂ) / 2 - r with hμ
    have hz2 := tens_inj (Lop (Sz n) v + (1 / 2 : ℂ) • v) (Lop (Sz n) u + (-1 / 2 : ℂ) • u)
      (μ • v) (μ • u) (by
        rw [tens_add, tens_add, tens_smul, tens_smul, tens_smul, tens_smul, ← tens_smul_left,
          ← tens_smul_left]
        rw [← hz]; abel)
    have hp := hx.2
    rw [hx', map_add, Sp_tens, Sp_tens, sp_qv0, sp_qv1, tens_zero_left, zero_add] at hp
    have hp2 := tens_inj (Lop (Sp n) v + u) (Lop (Sp n) u) 0 0 (by
      rw [tens_add, tens_zero, tens_zero, add_zero]
      rw [← hp]; abel)
    have hzv : Lop (Sz n) v = ((n : ℂ) / 2 - r) • v := by
      have e : Lop (Sz n) v = μ • v - (1 / 2 : ℂ) • v := by rw [← hz2.1]; abel
      rw [e, hμ]; push_cast; module
    have hzu : Lop (Sz n) u = ((n : ℂ) / 2 - r + 1) • u := by
      have e : Lop (Sz n) u = μ • u - (-1 / 2 : ℂ) • u := by rw [← hz2.2]; abel
      rw [e, hμ]; push_cast; module
    rcases Nat.eq_zero_or_eq_succ_pred r with hr | hr
    · subst hr
      have hu0 : u = 0 := by
        have : u ∈ Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 + 1) := by
          rw [Module.End.mem_eigenspace_iff, hzu]; push_cast; ring_nf
        rw [eig_top] at this; exact this
      rw [hu0, add_zero] at hp2
      rw [hx', hu0, tens_zero, add_zero]
      exact Bm_SP (hw_span n 0 v ⟨hzv, hp2.1⟩)
    · set s := r.pred with hs
      rw [hr] at hzv hzu ⊢
      have hu : HW n s u := ⟨by rw [hzu]; push_cast; ring_nf, hp2.2⟩
      by_cases hd : 2 * s + 1 ≤ n
      · set d := n - 2 * s with hdd
        have hd1 : 1 ≤ d := by omega
        have hdc : (d : ℂ) = (n : ℂ) - 2 * s := by rw [hdd, Nat.cast_sub (by omega)]; push_cast; ring
        have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
        set v1 := v + (1 / (d : ℂ)) • Lop (Sm n) u with hv1
        have hv1hw : HW n (s + 1) v1 := by
          constructor
          · rw [hv1, map_add, map_smul, hzv, (ladder (n := n)).M_eig hu.1, smul_add, smul_smul,
              smul_smul]
            push_cast; congr 1; ring_nf
          · rw [hv1, map_add, map_smul, SpSm_hw hu, smul_smul, ← hdc,
              one_div_mul_cancel hdne, one_smul]
            exact hp2.1
        have hal : al d ≠ 0 := by
          rw [al]; exact mul_ne_zero (neg_ne_zero.2 hdne) (be_ne hd1)
        have e : x = Bm v1 + (al d)⁻¹ • Tm d u := by
          rw [hx', Bm, Tm, hv1, tens_add, tens_smul, smul_add, smul_smul, smul_smul,
            inv_mul_cancel₀ hal, one_smul]
          have : (al d)⁻¹ * be d = -(1 / (d : ℂ)) := by
            rw [al]; field_simp [be_ne hd1]
          rw [this, neg_smul]; abel
        rw [e]
        exact Submodule.add_mem _ (Bm_SP (hw_span n _ _ hv1hw))
          (Submodule.smul_mem _ _ (Tm_SP hd (hw_span n s u hu)))
      · have hu0 := hw_zero_of (by omega) hu hp2.1
        rw [hu0, add_zero] at hp2
        rw [hx', hu0, tens_zero, add_zero]
        exact Bm_SP (hw_span n _ v ⟨hzv, hp2.1⟩)

/-- All lowered path vectors. -/
noncomputable def SA (n : ℕ) : Submodule ℂ (E n) :=
  Submodule.span ℂ {x | ∃ r k, ∃ p : Path n r, x = (Lop (Sm n) ^ k) (psi n p.1)}

lemma SA_M (x : E n) (hx : x ∈ SA n) : Lop (Sm n) x ∈ SA n := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, k, p, rfl⟩ := hy
    refine Submodule.subset_span ⟨r, k + 1, p, ?_⟩
    rw [pow_succ', Module.End.mul_apply]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma SP_le_SA (r : ℕ) : SP n r ≤ SA n := by
  rw [SP, Submodule.span_le]
  rintro _ ⟨p, rfl⟩
  exact Submodule.subset_span ⟨r, 0, p, by simp⟩

lemma Kh_le_SA (r : ℕ) : Kh (Lop (Sm n)) (Lop (Sz n)) ((n : ℂ) / 2 - r) ≤ SA n := by
  intro x hx
  exact SP_le_SA r (hw_span n r x ⟨(ladder (n := n)).Kh_eig hx, (ladder (n := n)).Kh_P hx⟩)

lemma eig_le_SA (w : ℕ) : Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 - w) ≤ SA n := by
  induction w with
  | zero =>
    apply (ladder (n := n)).span_step SA_M
    · rw [Nat.cast_zero, sub_zero, eig_top]; exact bot_le
    · simpa using Kh_le_SA (n := n) 0
  | succ w ih =>
    apply (ladder (n := n)).span_step SA_M
    · have e : (n : ℂ) / 2 - ((w + 1 : ℕ) : ℂ) + 1 = (n : ℂ) / 2 - w := by push_cast; ring
      rw [e]; exact ih
    · exact Kh_le_SA (w + 1)

lemma SA_top : SA n = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ y, v y • ket y := by
    ext x
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (eig_le_SA (wt y) (ket_mem y))

end Span

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Comm

variable {n : ℕ}

/-- `X` commutes with the collective ladder operators. -/
def Comm (n : ℕ) (X : Matrix (St n) (St n) ℂ) : Prop :=
  X * Sp n = Sp n * X ∧ X * Sm n = Sm n * X ∧ X * Sz n = Sz n * X

lemma Comm.lop {X A : Matrix (St n) (St n) ℂ} (h : X * A = A * X) (v : E n) :
    Lop X (Lop A v) = Lop A (Lop X v) := by
  rw [Lop_comp, Lop_comp, h]

lemma Comm.hw {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) {r : ℕ} {v : E n} (hv : HW n r v) :
    HW n r (Lop X v) := by
  constructor
  · rw [← Comm.lop hX.2.2, hv.1, map_smul]
  · rw [← Comm.lop hX.1, hv.2, map_zero]

/-- Matrix elements between path vectors (indexed by all bit strings). -/
noncomputable def blkS (X : Matrix (St n) (St n) ℂ) (x y : St n) : ℂ :=
  ⟪psi n x, Lop X (psi n y)⟫_ℂ

lemma SP_expand {r : ℕ} {y : E n} (hy : y ∈ SP n r) :
    y = ∑ q : Path n r, ⟪psi n q.1, y⟫_ℂ • psi n q.1 := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨p, rfl⟩ := hz
    rw [Finset.sum_eq_single p]
    · rw [inner_psi _ _ _ p.2.1 p.2.1, if_pos rfl, one_smul]
    · intro q _ hq
      rw [inner_psi _ _ _ q.2.1 p.2.1, if_neg (fun e => hq (Subtype.ext e)), zero_smul]
    · simp
  | zero => simp
  | add a b _ _ ha hb =>
    conv_lhs => rw [ha, hb]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_add_right, add_smul]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_smul_right, smul_smul]

lemma Lop_psi {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) {r : ℕ} (p : Path n r) :
    Lop X (psi n p.1) = ∑ q : Path n r, blkS X q.1 p.1 • psi n q.1 := by
  have h := hw_span n r _ (hX.hw (p.2.2 ▸ psi_hw n p.1 p.2.1))
  exact SP_expand h

lemma blkS_wt {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) {x y : St n}
    (hx : validB n x = true) (hy : validB n y = true) (h : wt x ≠ wt y) : blkS X x y = 0 := by
  have h1 := (ladder (n := n)).zsa (psi n x) (Lop X (psi n y))
  rw [(psi_hw n x hx).1, (hX.hw (psi_hw n y hy)).1, inner_smul_left, inner_smul_right] at h1
  have hc : (starRingEnd ℂ) ((n : ℂ) / 2 - wt x) = (n : ℂ) / 2 - wt x := by
    simp only [map_sub, map_div₀, map_natCast, map_ofNat]
  rw [hc] at h1
  have hne : ((n : ℂ) / 2 - wt x) - ((n : ℂ) / 2 - wt y) ≠ 0 := by
    rw [sub_sub_sub_cancel_left, sub_ne_zero]
    intro e; exact h (by exact_mod_cast e.symm)
  have : (((n : ℂ) / 2 - wt x) - ((n : ℂ) / 2 - wt y)) * blkS X x y = 0 := by
    rw [sub_mul, blkS, h1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left hne

lemma Lop_psi' {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) {y : St n} (hy : validB n y = true) :
    Lop X (psi n y) = ∑ q : Path n (wt y), blkS X q.1 y • psi n q.1 :=
  Lop_psi hX ⟨y, hy, rfl⟩

lemma blkS_mul {X Y : Matrix (St n) (St n) ℂ} (hY : Comm n Y) {x y : St n}
    (hy : validB n y = true) :
    blkS (X * Y) x y = ∑ q : Path n (wt y), blkS X x q.1 * blkS Y q.1 y := by
  rw [blkS, ← Lop_comp, Lop_psi' hY hy, map_sum, inner_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, inner_smul_right, blkS, mul_comm]; rfl

lemma blkS_add (X Y : Matrix (St n) (St n) ℂ) (x y : St n) :
    blkS (X + Y) x y = blkS X x y + blkS Y x y := by
  simp only [blkS, Lop, map_add, LinearMap.add_apply, inner_add_right]

lemma blkS_sub (X Y : Matrix (St n) (St n) ℂ) (x y : St n) :
    blkS (X - Y) x y = blkS X x y - blkS Y x y := by
  simp only [blkS, Lop, map_sub, LinearMap.sub_apply, inner_sub_right]

lemma blkS_smul (c : ℂ) (X : Matrix (St n) (St n) ℂ) (x y : St n) :
    blkS (c • X) x y = c * blkS X x y := by
  simp only [blkS, Lop, map_smul, LinearMap.smul_apply, inner_smul_right]

lemma blkS_rsmul (c : ℝ) (X : Matrix (St n) (St n) ℂ) (x y : St n) :
    blkS (c • X) x y = c * blkS X x y := by
  rw [show c • X = (c : ℂ) • X by ext; simp, blkS_smul]

lemma blkS_star (X : Matrix (St n) (St n) ℂ) (x y : St n) :
    blkS Xᴴ x y = star (blkS X y x) := by
  rw [blkS, blkS, ← Lop_adj, ← inner_conj_symm]; rfl

lemma blkS_one {x y : St n} (hx : validB n x = true) (hy : validB n y = true) :
    blkS (1 : Matrix (St n) (St n) ℂ) x y = if x = y then 1 else 0 := by
  have : Lop (1 : Matrix (St n) (St n) ℂ) (psi n y) = psi n y := by
    ext z; simp [Lop_apply, Matrix.one_apply]
  rw [blkS, this, inner_psi n x y hx hy]

/-- Commutant elements are determined by their path-basis matrix elements. -/
lemma comm_ext {X Y : Matrix (St n) (St n) ℂ} (hX : Comm n X) (hY : Comm n Y)
    (h : ∀ x y, validB n x = true → validB n y = true → blkS X x y = blkS Y x y) : X = Y := by
  have hpsi : ∀ y, validB n y = true → Lop X (psi n y) = Lop Y (psi n y) := by
    intro y hy
    rw [Lop_psi' hX hy, Lop_psi' hY hy]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h _ _ q.2.1 hy]
  have hpow : ∀ (k : ℕ) (v : E n), Lop X ((Lop (Sm n) ^ k) v) = (Lop (Sm n) ^ k) (Lop X v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, Comm.lop hX.2.1, ih, Module.End.mul_apply]
  have hpowY : ∀ (k : ℕ) (v : E n), Lop Y ((Lop (Sm n) ^ k) v) = (Lop (Sm n) ^ k) (Lop Y v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, Comm.lop hY.2.1, ih, Module.End.mul_apply]
  have hL : Lop X = Lop Y := by
    apply LinearMap.ext_on (s := {x | ∃ r k, ∃ p : Path n r, x = (Lop (Sm n) ^ k) (psi n p.1)})
    · have := SA_top (n := n); rw [SA] at this; exact this
    · rintro _ ⟨r, k, p, rfl⟩
      rw [hpow, hpowY, hpsi _ p.2.1]
  exact (Matrix.toEuclideanLin).injective hL

/-- The exchange operator commutes with every collective operator. -/
lemma exchange_mul (i j : Fin n) (A : Matrix (St n) (St n) ℂ) (x y : St n) :
    (exchange i j * A) x y = A (x ∘ Equiv.swap i j) y := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (x ∘ Equiv.swap i j)]
  · rw [exchange, if_pos (by funext k; simp), one_mul]
  · intro z _ hz
    rw [exchange, if_neg, zero_mul]
    intro h; apply hz; rw [h]; funext k; simp
  · simp

lemma mul_exchange (i j : Fin n) (A : Matrix (St n) (St n) ℂ) (x y : St n) :
    (A * exchange i j) x y = A x (y ∘ Equiv.swap i j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (y ∘ Equiv.swap i j)]
  · rw [exchange, if_pos rfl, mul_one]
  · intro z _ hz
    rw [exchange, if_neg, mul_zero]
    intro h; apply hz; rw [h]
  · simp

lemma exchange_coll (i j : Fin n) (O : Matrix (Fin 2) (Fin 2) ℂ) :
    exchange i j * coll n O = coll n O * exchange i j := by
  ext x y
  rw [exchange_mul, mul_exchange, coll, Matrix.sum_apply, Matrix.sum_apply]
  rw [← Equiv.sum_comp (Equiv.swap i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [onQubit, Function.comp_apply, Equiv.swap_apply_self]
  congr 1
  apply propext
  constructor
  · intro h l hl
    have := h (Equiv.swap i j l) (fun e => hl ((Equiv.swap i j).injective e))
    rwa [Equiv.swap_apply_self] at this
  · intro h l hl
    have := h (Equiv.swap i j l) (fun e => hl (by rw [← e, Equiv.swap_apply_self]))
    rwa [Equiv.swap_apply_self] at this

lemma comm_exchange (i j : Fin n) : Comm n (exchange i j) :=
  ⟨exchange_coll i j sp, exchange_coll i j sm, exchange_coll i j sz⟩

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n) in
/-- The commutant as a real Lie subalgebra. -/
def commLie : LieSubalgebra ℝ (Matrix (St n) (St n) ℂ) where
  carrier := {X | Comm n X}
  add_mem' := by
    intro X Y hX hY
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Matrix.add_mul, Matrix.mul_add]
    · rw [hX.1, hY.1]
    · rw [hX.2.1, hY.2.1]
    · rw [hX.2.2, hY.2.2]
  zero_mem' := by refine ⟨?_, ?_, ?_⟩ <;> simp
  smul_mem' := by
    intro c X hX
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Matrix.smul_mul, Matrix.mul_smul]
    · rw [hX.1]
    · rw [hX.2.1]
    · rw [hX.2.2]
  lie_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq, Ring.lie_def]
    have key : ∀ A : Matrix (St n) (St n) ℂ, X * A = A * X → Y * A = A * Y →
        (X * Y - Y * X) * A = A * (X * Y - Y * X) := by
      intro A hXA hYA
      have h1 : X * Y * A = A * (X * Y) := by
        rw [Matrix.mul_assoc, hYA, ← Matrix.mul_assoc, hXA, Matrix.mul_assoc]
      have h2 : Y * X * A = A * (Y * X) := by
        rw [Matrix.mul_assoc, hXA, ← Matrix.mul_assoc, hYA, Matrix.mul_assoc]
      rw [Matrix.sub_mul, Matrix.mul_sub, h1, h2]
    exact ⟨key _ hX.1 hY.1, key _ hX.2.1 hY.2.1, key _ hX.2.2 hY.2.2⟩

end Comm

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Lift

variable {n : ℕ}

lemma Lop_ext {X Y : Matrix (St (n + 1)) (St (n + 1)) ℂ}
    (h : ∀ (a : Fin 2 → ℂ) (v : E n), Lop X (tens a v) = Lop Y (tens a v)) : X = Y := by
  apply (Matrix.toEuclideanLin).injective
  ext1 x
  show Lop X x = Lop Y x
  rw [eq_tens x, map_add, map_add, h, h]

lemma liftT_onQubit0 (X : Matrix (St n) (St n) ℂ) (O : Matrix (Fin 2) (Fin 2) ℂ) :
    liftT X * onQubit 0 O = onQubit 0 O * liftT X := by
  apply Lop_ext
  intro a v
  rw [← Lop_comp, ← Lop_comp, Lop_onQubit0, Lop_liftT, Lop_liftT, Lop_onQubit0]

lemma liftT_coll (X : Matrix (St n) (St n) ℂ) (O : Matrix (Fin 2) (Fin 2) ℂ)
    (h : X * coll n O = coll n O * X) :
    liftT X * coll (n + 1) O = coll (n + 1) O * liftT X := by
  rw [coll_succ, Matrix.mul_add, Matrix.add_mul, liftT_onQubit0, ← liftT_mul, ← liftT_mul, h]

lemma Comm.liftT {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) : Comm (n + 1) (liftT X) :=
  ⟨liftT_coll X sp hX.1, liftT_coll X sm hX.2.1, liftT_coll X sz hX.2.2⟩

noncomputable def liftHom : Matrix (St n) (St n) ℂ →ₗ⁅ℝ⁆ Matrix (St (n + 1)) (St (n + 1)) ℂ where
  toFun := liftT
  map_add' := liftT_add
  map_smul' c X := by
    rw [show c • X = (c : ℂ) • X by ext; simp, liftT_smul]
    ext; simp
  map_lie' := by
    intro X Y
    simp only [Ring.lie_def, liftT_sub, liftT_mul]

lemma liftHom_apply (X : Matrix (St n) (St n) ℂ) : liftHom X = liftT X := rfl

lemma exchangeLie_lift {X : Matrix (St n) (St n) ℂ} (hX : X ∈ BaconThesis.ExchangeUniv.exchangeLie n) :
    liftT X ∈ BaconThesis.ExchangeUniv.exchangeLie (n + 1) := by
  have : BaconThesis.ExchangeUniv.exchangeLie n
      ≤ (BaconThesis.ExchangeUniv.exchangeLie (n + 1)).comap liftHom := by
    rw [BaconThesis.ExchangeUniv.exchangeLie, LieSubalgebra.lieSpan_le]
    rintro _ ⟨i, j, hij, rfl⟩
    rw [SetLike.mem_coe, LieSubalgebra.mem_comap, liftHom_apply, liftT_smul, ← exchange_succ]
    exact LieSubalgebra.subset_lieSpan
      ⟨i.succ, j.succ, fun e => hij (Fin.succ_injective _ e), rfl⟩
  exact this hX

lemma exchangeLie_comm {X : Matrix (St n) (St n) ℂ}
    (hX : X ∈ BaconThesis.ExchangeUniv.exchangeLie n) : Comm n X := by
  have : BaconThesis.ExchangeUniv.exchangeLie n ≤ commLie n := by
    rw [BaconThesis.ExchangeUniv.exchangeLie, LieSubalgebra.lieSpan_le]
    rintro _ ⟨i, j, _, rfl⟩
    exact (commLie n).smul_mem' (c := (1 : ℝ)) (by
      show Comm n (Complex.I • exchange i j)
      have h := comm_exchange (n := n) i j
      refine ⟨?_, ?_, ?_⟩ <;> simp only [Matrix.smul_mul, Matrix.mul_smul]
      · rw [h.1]
      · rw [h.2.1]
      · rw [h.2.2]) |> fun h => by simpa using h
  exact this hX

lemma Lop_liftT_Tm {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) (d : ℕ) (u : E n) :
    Lop (liftT X) (Tm d u) = Tm d (Lop X u) := by
  rw [Tm, Tm, map_add, map_smul, map_smul, Lop_liftT, Lop_liftT, Comm.lop hX.2.1]

lemma blkS_liftT {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) (a b : Fin 2) (x y : St n)
    (hx : validB (n + 1) (Fin.cons a x) = true) (hy : validB (n + 1) (Fin.cons b y) = true) :
    blkS (liftT X) (Fin.cons a x) (Fin.cons b y) = if a = b then blkS X x y else 0 := by
  rw [validB_succ] at hx hy
  simp only [Fin.tail_cons, Fin.cons_zero] at hx hy
  have hwy := hX.hw (psi_hw n y hy.1)
  have hwx := psi_hw n x hx.1
  rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.1 ⟨b, rfl⟩ with rfl | rfl
  · rw [blkS, psi_cons0, psi_cons0, Bm, Bm, Lop_liftT, inner_tens, qv_inner]; simp [blkS]
  · rw [blkS, psi_cons0, psi_cons1, Bm, Lop_liftT_Tm hX, Tm, inner_add_right, inner_smul_right,
      inner_smul_right, inner_tens, inner_tens, qv_inner, qv_inner,
      (ladder (n := n)).adj', hwx.2, inner_zero_left]
    simp
  · rw [blkS, psi_cons1, psi_cons0, Bm, Lop_liftT, Tm, inner_add_left, inner_smul_left,
      inner_smul_left, inner_tens, inner_tens, qv_inner, qv_inner, (ladder (n := n)).adj, hwy.2,
      inner_zero_right]
    simp
  · rw [blkS, psi_cons1, psi_cons1, Lop_liftT_Tm hX, Tm, Tm]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, inner_tens,
      qv_inner]
    simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_false, if_true, zero_mul, mul_zero,
      add_zero, zero_add, one_mul]
    rw [(ladder (n := n)).adj, SpSm_hw hwy, inner_smul_right]
    by_cases hw : wt x = wt y
    · have hd := hx.2 rfl
      have hdc : ((n - 2 * wt x : ℕ) : ℂ) = (n : ℂ) - 2 * wt x := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← hw, starRingEnd_apply, starRingEnd_apply, al_star, be_star, ← hdc]
      have := al_sq (d := n - 2 * wt x) (by omega)
      rw [blkS]
      linear_combination ⟪psi n x, Lop X (psi n y)⟫_ℂ * this
    · have h0 : ⟪psi n x, Lop X (psi n y)⟫_ℂ = 0 := blkS_wt hX hx.1 hy.1 hw
      rw [h0, blkS, h0]; ring

end Lift

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Exch

variable {n : ℕ}

/-- `|a b⟩ ⊗ v` on the two newest qubits. -/
noncomputable def t2 (a b : Fin 2) (v : E n) : E (n + 2) := tens (qv a) (tens (qv b) v)

lemma E01_t2 (a b : Fin 2) (v : E n) :
    Lop (exchange (0 : Fin (n + 2)) 1) (t2 a b v) = t2 b a v := Lop_exchange01 _ _ _

noncomputable def pc (d : ℕ) : ℂ := 1 / ((d : ℂ) + 1)
noncomputable def qc (d : ℕ) : ℂ := (d : ℂ) * be d / (((d : ℂ) + 1) * be (d + 1))

lemma be_succ_ne (d : ℕ) : be (d + 1) ≠ 0 := be_ne (by omega)

lemma Sm_tens0 (u : E n) :
    Lop (Sm (n + 1)) (tens (qv 0) u) = tens (qv 1) u + tens (qv 0) (Lop (Sm n) u) := by
  rw [Sm_tens, sm_qv0]

lemma Sm_tens1 (u : E n) : Lop (Sm (n + 1)) (tens (qv 1) u) = tens (qv 1) (Lop (Sm n) u) := by
  rw [Sm_tens, sm_qv1, tens_zero_left, zero_add]

lemma BT_eq (d : ℕ) (u : E n) :
    Bm (Tm d u) = al d • t2 0 1 u + be d • t2 0 0 (Lop (Sm n) u) := by
  rw [Bm, Tm, tens_add, tens_smul, tens_smul]; rfl

lemma TB_eq (d : ℕ) (u : E n) :
    Tm (d + 1) (Bm u) = al (d + 1) • t2 1 0 u + be (d + 1) • t2 0 1 u
      + be (d + 1) • t2 0 0 (Lop (Sm n) u) := by
  simp only [Tm, Bm, Sm_tens0, tens_add, tens_smul, smul_add, t2]
  abel

lemma TT_eq (d : ℕ) (u : E n) :
    Tm (d - 1) (Tm d u) = (al (d - 1) * al d) • t2 1 1 u + (al (d - 1) * be d) • t2 1 0 (Lop (Sm n) u)
      + (be (d - 1) * (al d + be d)) • t2 0 1 (Lop (Sm n) u)
      + (be (d - 1) * be d) • t2 0 0 (Lop (Sm n) (Lop (Sm n) u)) := by
  rw [Tm, Tm, map_add, map_smul, map_smul, Sm_tens1, Sm_tens0]
  simp only [tens_add, tens_smul, smul_add, smul_smul, t2]
  module

lemma E_BB (u : E n) : Lop (exchange (0 : Fin (n + 2)) 1) (Bm (Bm u)) = Bm (Bm u) :=
  E01_t2 0 0 u

lemma E_BT (d : ℕ) (u : E n) :
    Lop (exchange (0 : Fin (n + 2)) 1) (Bm (Tm d u)) = pc d • Bm (Tm d u) + qc d • Tm (d + 1) (Bm u) := by
  rw [BT_eq, TB_eq, map_add, map_smul, map_smul, E01_t2, E01_t2]
  have hb := be_succ_ne d
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have h1 : qc d * al (d + 1) = al d := by
    rw [qc, al, al]; push_cast; field_simp
  have h2 : pc d * al d + qc d * be (d + 1) = 0 := by
    rw [pc, qc, al]; field_simp; ring
  have h3 : pc d * be d + qc d * be (d + 1) = be d := by
    rw [pc, qc]; field_simp; ring
  have : pc d • (al d • t2 0 1 u + be d • t2 0 0 (Lop (Sm n) u)) + qc d • (al (d + 1) • t2 1 0 u
      + be (d + 1) • t2 0 1 u + be (d + 1) • t2 0 0 (Lop (Sm n) u))
      = (qc d * al (d + 1)) • t2 1 0 u + (pc d * al d + qc d * be (d + 1)) • t2 0 1 u
        + (pc d * be d + qc d * be (d + 1)) • t2 0 0 (Lop (Sm n) u) := by module
  rw [this, h1, h2, h3, zero_smul, add_zero]

lemma be_rel {d : ℕ} : ((d : ℂ) * be d) * ((d : ℂ) * be d) = (d : ℂ) * (d + 2) * (be (d + 1) * be (d + 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h1 := be_sq (d := d) hd
    have h2 := be_sq (d := d + 1) (by omega)
    push_cast at h2
    have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
    have hd2 : (d : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (d + 1)
    have e1 : be d * be d = 1 / ((d : ℂ) * (d + 1)) := by
      rw [eq_div_iff (mul_ne_zero (by exact_mod_cast hd.ne') hd1)]; exact h1
    have e2 : be (d + 1) * be (d + 1) = 1 / (((d : ℂ) + 1) * (d + 1 + 1)) := by
      rw [eq_div_iff (mul_ne_zero hd1 hd2)]; exact h2
    have : ((d : ℂ) * be d) * ((d : ℂ) * be d) = (d : ℂ) * (d : ℂ) * (be d * be d) := by ring
    rw [this, e1, e2]
    field_simp
    ring

lemma E_TB (d : ℕ) (u : E n) (hu : d = 0 → Lop (Sm n) u = 0) :
    Lop (exchange (0 : Fin (n + 2)) 1) (Tm (d + 1) (Bm u))
      = qc d • Bm (Tm d u) - pc d • Tm (d + 1) (Bm u) := by
  rw [BT_eq, TB_eq, map_add, map_add, map_smul, map_smul, map_smul, E01_t2, E01_t2, E01_t2]
  have hb := be_succ_ne d
  have hd1 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  have h1 : -(pc d * al (d + 1)) = be (d + 1) := by
    rw [pc, al]; push_cast; field_simp
  have h2 : qc d * al d - pc d * be (d + 1) = al (d + 1) := by
    have := be_rel (d := d)
    rw [pc, qc, al, al]; push_cast; field_simp
    linear_combination -this
  have key : qc d • (al d • t2 0 1 u + be d • t2 0 0 (Lop (Sm n) u)) - pc d • (al (d + 1) • t2 1 0 u
      + be (d + 1) • t2 0 1 u + be (d + 1) • t2 0 0 (Lop (Sm n) u))
      = (-(pc d * al (d + 1))) • t2 1 0 u + (qc d * al d - pc d * be (d + 1)) • t2 0 1 u
        + (qc d * be d - pc d * be (d + 1)) • t2 0 0 (Lop (Sm n) u) := by module
  rw [key, h1, h2]
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [hu rfl]
    simp only [t2, tens_zero, smul_zero, add_zero]
    abel
  · have h3 : qc d * be d - pc d * be (d + 1) = be (d + 1) := by
      have h1' := be_sq (d := d) hd
      have h2' := be_sq (d := d + 1) (by omega)
      push_cast at h2'
      have e : (d : ℂ) * be d ^ 2 = ((d : ℂ) + 2) * be (d + 1) ^ 2 := by
        apply mul_left_cancel₀ hd1
        linear_combination h1' - h2'
      have hp : (qc d * be d - pc d * be (d + 1) - be (d + 1)) * (((d : ℂ) + 1) * be (d + 1))
          = (d : ℂ) * be d ^ 2 - ((d : ℂ) + 2) * be (d + 1) ^ 2 := by
        rw [pc, qc]; field_simp; ring
      rw [e, sub_self] at hp
      have := (mul_eq_zero.1 hp).resolve_right (mul_ne_zero hd1 hb)
      exact sub_eq_zero.1 this
    rw [h3]; abel

lemma E_TT (d : ℕ) (hd : 2 ≤ d) (u : E n) :
    Lop (exchange (0 : Fin (n + 2)) 1) (Tm (d - 1) (Tm d u)) = Tm (d - 1) (Tm d u) := by
  rw [TT_eq, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, E01_t2, E01_t2,
    E01_t2, E01_t2]
  have h : al (d - 1) * be d = be (d - 1) * (al d + be d) := by
    rw [al, al, Nat.cast_sub (by omega)]; push_cast; ring
  rw [h]; abel

end Exch

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Block

variable {n : ℕ}

lemma Sm_hw_zero {u : E n} {w : ℕ} (hu : HW n w u) (hd : n - 2 * w = 0) (h2 : 2 * w ≤ n) :
    Lop (Sm n) u = 0 := by
  have hn := (ladder (n := n)).normM u hu.1
  rw [hu.2, inner_zero_left, zero_add] at hn
  have he : (n : ℂ) / 2 - w = 0 := by
    have : n = 2 * w := by omega
    rw [this]; push_cast; ring
  rw [he, mul_zero, zero_mul] at hn
  exact inner_self_eq_zero.1 hn

lemma psi_BB (u : St n) : psi (n + 2) (Fin.cons 0 (Fin.cons 0 u)) = Bm (Bm (psi n u)) := by
  rw [psi_cons0, psi_cons0]

lemma psi_BT (u : St n) :
    psi (n + 2) (Fin.cons 0 (Fin.cons 1 u)) = Bm (Tm (n - 2 * wt u) (psi n u)) := by
  rw [psi_cons0, psi_cons1]

lemma psi_TB (u : St n) (h : 2 * wt u ≤ n) :
    psi (n + 2) (Fin.cons 1 (Fin.cons 0 u)) = Tm (n - 2 * wt u + 1) (Bm (psi n u)) := by
  rw [psi_cons1, psi_cons0, wt_cons]
  congr 1; simp; omega

lemma psi_TT (u : St n) :
    psi (n + 2) (Fin.cons 1 (Fin.cons 1 u)) = Tm (n - 2 * wt u - 1) (Tm (n - 2 * wt u) (psi n u)) := by
  rw [psi_cons1, psi_cons1, wt_cons]
  congr 1; simp; omega

/-- Matrix elements of the newest exchange `E₀₁` in the path basis. -/
noncomputable def Ematf (P Q : St (n + 2)) : ℂ :=
  if Q 0 = Q 1 then (if P = Q then 1 else 0)
  else if Q 0 = 0 then
    pc (n - 2 * wt (Fin.tail (Fin.tail Q))) * (if P = Q then 1 else 0)
      + qc (n - 2 * wt (Fin.tail (Fin.tail Q))) *
        (if P = Fin.cons 1 (Fin.cons 0 (Fin.tail (Fin.tail Q))) then 1 else 0)
  else
    qc (n - 2 * wt (Fin.tail (Fin.tail Q))) *
        (if P = Fin.cons 0 (Fin.cons 1 (Fin.tail (Fin.tail Q))) then 1 else 0)
      - pc (n - 2 * wt (Fin.tail (Fin.tail Q))) * (if P = Q then 1 else 0)

lemma valid_cons_cons {a b : Fin 2} {u : St n}
    (h : validB (n + 2) (Fin.cons a (Fin.cons b u)) = true) :
    validB n u = true ∧ (b = 1 → 2 * wt u + 1 ≤ n) ∧
      (a = 1 → 2 * wt (Fin.cons b u : St (n + 1)) + 1 ≤ n + 1) := by
  rw [validB_succ] at h
  simp only [Fin.tail_cons, Fin.cons_zero] at h
  have h1 := h.1
  rw [validB_succ] at h1
  simp only [Fin.tail_cons, Fin.cons_zero] at h1
  exact ⟨h1.1, h1.2, h.2⟩

lemma blkS_E01 {P Q : St (n + 2)} (hP : validB (n + 2) P = true) (hQ : validB (n + 2) Q = true) :
    blkS (exchange (0 : Fin (n + 2)) 1) P Q = Ematf P Q := by
  obtain ⟨a, b, u, rfl⟩ : ∃ a b u, Q = Fin.cons a (Fin.cons b u) :=
    ⟨Q 0, Fin.tail Q 0, Fin.tail (Fin.tail Q), by simp [Fin.cons_self_tail]⟩
  have hv := valid_cons_cons hQ
  have hu := psi_hw n u hv.1
  have h2u := valid_two_wt u hv.1
  have hinner : ∀ R : St (n + 2), validB (n + 2) R = true →
      ⟪psi (n + 2) P, psi (n + 2) R⟫_ℂ = if P = R then 1 else 0 :=
    fun R hR => inner_psi _ _ _ hP hR
  simp only [Ematf, Fin.cons_zero, Fin.tail_cons]
  have h1 : (Fin.cons a (Fin.cons b u) : St (n + 2)) 1 = b := rfl
  rw [h1]
  rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.1 ⟨b, rfl⟩ with rfl | rfl
  · rw [if_pos rfl, blkS, psi_BB, E_BB, ← psi_BB, hinner _ hQ]
  · rw [if_neg (by decide), if_pos rfl, blkS, psi_BT, E_BT, ← psi_BT, inner_add_right,
      inner_smul_right, inner_smul_right, hinner _ hQ]
    have hd : 2 * wt u + 1 ≤ n := hv.2.1 rfl
    have hv2 : validB (n + 2) (Fin.cons 1 (Fin.cons 0 u)) = true := by
      rw [validB_succ, validB_succ]; simp [hv.1, wt_cons]; omega
    rw [← psi_TB u h2u, hinner _ hv2]
  · rw [if_neg (by decide), if_neg (by decide), blkS, psi_TB u h2u, E_TB]
    · rw [← psi_TB u h2u, inner_sub_right, inner_smul_right, inner_smul_right, hinner _ hQ]
      by_cases hd : 1 ≤ n - 2 * wt u
      · have hv2 : validB (n + 2) (Fin.cons 0 (Fin.cons 1 u)) = true := by
          rw [validB_succ, validB_succ]; simp [hv.1]; omega
        rw [← psi_BT, hinner _ hv2]
      · have h0 : n - 2 * wt u = 0 := by omega
        rw [h0]
        simp [qc]
    · intro h0; exact Sm_hw_zero hu h0 h2u
  · rw [if_pos rfl, blkS, psi_TT, E_TT, ← psi_TT, hinner _ hQ]
    have := hv.2.2 rfl
    rw [wt_cons] at this; simp at this; omega

end Block

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Struct

/-- Valid paths on `N` qubits (all total spins). -/
abbrev VP (N : ℕ) := {x : St N // validB N x = true}

variable {N : ℕ}

/-- The path-basis matrix of `Z`. -/
noncomputable def MZ (Z : Matrix (St N) (St N) ℂ) : Matrix (VP N) (VP N) ℂ :=
  fun p q => blkS Z p.1 q.1

/-- Weight (`= n/2 - J`) of a path. -/
def Wt (r : ℕ) (p : VP N) : Prop := wt p.1 = r

lemma MZ_add (X Y : Matrix (St N) (St N) ℂ) : MZ (X + Y) = MZ X + MZ Y := by
  ext p q; simp [MZ, blkS_add]

lemma MZ_sub (X Y : Matrix (St N) (St N) ℂ) : MZ (X - Y) = MZ X - MZ Y := by
  ext p q; simp [MZ, blkS_sub]

lemma MZ_smul (c : ℂ) (X : Matrix (St N) (St N) ℂ) : MZ (c • X) = c • MZ X := by
  ext p q; simp [MZ, blkS_smul]

lemma MZ_rsmul (c : ℝ) (X : Matrix (St N) (St N) ℂ) : MZ (c • X) = c • MZ X := by
  ext p q; simp [MZ, blkS_rsmul]

lemma MZ_wt {X : Matrix (St N) (St N) ℂ} (hX : Comm N X) {p q : VP N} (h : wt p.1 ≠ wt q.1) :
    MZ X p q = 0 := blkS_wt hX p.2 q.2 h

lemma MZ_mul {X Y : Matrix (St N) (St N) ℂ} (hY : Comm N Y) : MZ (X * Y) = MZ X * MZ Y := by
  ext p q
  rw [MZ, blkS_mul hY q.2, Matrix.mul_apply]
  have h1 : ∑ s : VP N, MZ X p s * MZ Y s q
      = ∑ s ∈ Finset.univ.filter (fun s : VP N => wt s.1 = wt q.1), MZ X p s * MZ Y s q := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h
    · rfl
    · rw [MZ_wt hY h, mul_zero]
  rw [h1]
  refine Finset.sum_bij' (fun t _ => (⟨t.1, t.2.1⟩ : VP N))
    (fun s hs => (⟨s.1, s.2, (Finset.mem_filter.1 hs).2⟩ : Path N (wt q.1))) ?_ ?_ ?_ ?_ ?_
  · intro t _; simp [t.2.2]
  · intro s _; simp
  · intro t _; rfl
  · intro s _; rfl
  · intro t _; rfl

lemma MZ_lie {X Y : Matrix (St N) (St N) ℂ} (hX : Comm N X) (hY : Comm N Y) :
    MZ ⁅X, Y⁆ = ⁅MZ X, MZ Y⁆ := by
  rw [Ring.lie_def, Ring.lie_def, MZ_sub, MZ_mul hY, MZ_mul hX]

lemma MZ_star (X : Matrix (St N) (St N) ℂ) : MZ Xᴴ = (MZ X)ᴴ := by
  ext p q; simp [MZ, blkS_star, conjTranspose_apply]

lemma exchange_star {n : ℕ} (i j : Fin n) : (exchange i j)ᴴ = exchange i j := by
  ext x y
  simp only [conjTranspose_apply, exchange]
  have : (y = x ∘ Equiv.swap i j) ↔ (x = y ∘ Equiv.swap i j) := by
    constructor <;> intro h <;> rw [h] <;> funext k <;> simp
  by_cases h : x = y ∘ Equiv.swap i j
  · rw [if_pos (this.2 h), if_pos h, star_one]
  · rw [if_neg (fun h' => h (this.1 h')), if_neg h, star_zero]

variable (N) in
def skewLie : LieSubalgebra ℝ (Matrix (St N) (St N) ℂ) where
  carrier := {X | Xᴴ = -X}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq, conjTranspose_add] at *
    rw [hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [show c • X = (c : ℂ) • X by ext; simp, conjTranspose_smul, hX]
    simp
  lie_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq, Ring.lie_def, conjTranspose_sub, conjTranspose_mul] at *
    rw [hX, hY]; simp

lemma exchangeLie_skew {Z : Matrix (St N) (St N) ℂ}
    (hZ : Z ∈ BaconThesis.ExchangeUniv.exchangeLie N) : Zᴴ = -Z := by
  have : BaconThesis.ExchangeUniv.exchangeLie N ≤ skewLie N := by
    rw [BaconThesis.ExchangeUniv.exchangeLie, LieSubalgebra.lieSpan_le]
    rintro _ ⟨i, j, _, rfl⟩
    show (Complex.I • exchange i j)ᴴ = -(Complex.I • exchange i j)
    rw [conjTranspose_smul, exchange_star]; simp
  exact this hZ

lemma blkS_zero (x y : St N) : blkS (0 : Matrix (St N) (St N) ℂ) x y = 0 := by
  simp [blkS, Lop]

variable (N) in
/-- The image of the exchange Lie algebra in the path basis. -/
noncomputable def Mf : LieSubalgebra ℝ (Matrix (VP N) (VP N) ℂ) where
  carrier := {A | ∃ Z ∈ BaconThesis.ExchangeUniv.exchangeLie N, MZ Z = A}
  add_mem' := by
    rintro _ _ ⟨Z1, h1, rfl⟩ ⟨Z2, h2, rfl⟩
    exact ⟨Z1 + Z2, add_mem h1 h2, MZ_add _ _⟩
  zero_mem' := ⟨0, zero_mem _, by ext; simp [MZ, blkS_zero]⟩
  smul_mem' := by
    rintro c _ ⟨Z, h, rfl⟩
    exact ⟨c • Z, (BaconThesis.ExchangeUniv.exchangeLie N).smul_mem c h, MZ_rsmul _ _⟩
  lie_mem' := by
    rintro _ _ ⟨Z1, h1, rfl⟩ ⟨Z2, h2, rfl⟩
    exact ⟨⁅Z1, Z2⁆, (BaconThesis.ExchangeUniv.exchangeLie N).lie_mem h1 h2,
      MZ_lie (exchangeLie_comm h1) (exchangeLie_comm h2)⟩

lemma Mf_BD {A : Matrix (VP N) (VP N) ℂ} (hA : A ∈ Mf N) {p q : VP N} (h : wt p.1 ≠ wt q.1) :
    A p q = 0 := by
  obtain ⟨Z, hZ, rfl⟩ := hA
  exact MZ_wt (exchangeLie_comm hZ) h

lemma Mf_skew {A : Matrix (VP N) (VP N) ℂ} (hA : A ∈ Mf N) : Aᴴ = -A := by
  obtain ⟨Z, hZ, rfl⟩ := hA
  rw [← MZ_star, exchangeLie_skew hZ, ← neg_one_smul ℂ Z, MZ_smul, neg_one_smul]

/-- Restriction to the weight-`r` block. -/
def proj (r : ℕ) (A : Matrix (VP N) (VP N) ℂ) : Matrix (VP N) (VP N) ℂ :=
  fun p q => if wt p.1 = r ∧ wt q.1 = r then A p q else 0

def BD (A : Matrix (VP N) (VP N) ℂ) : Prop := ∀ p q : VP N, wt p.1 ≠ wt q.1 → A p q = 0

lemma proj_mul {A B : Matrix (VP N) (VP N) ℂ} (hA : BD A) (hB : BD B) (r : ℕ) :
    proj r (A * B) = proj r A * proj r B := by
  ext p q
  simp only [proj, Matrix.mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : wt s.1 = r
    · rw [if_pos ⟨h.1, hs⟩, if_pos ⟨hs, h.2⟩]
    · rw [if_neg (fun h' => hs h'.2), zero_mul, hA p s (by rw [h.1]; exact Ne.symm hs), zero_mul]
  · symm
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases h1 : wt p.1 = r ∧ wt s.1 = r
    · rw [if_pos h1, if_neg (fun h2 => h ⟨h1.1, h2.2⟩), mul_zero]
    · rw [if_neg h1, zero_mul]

lemma proj_add (r : ℕ) (A B : Matrix (VP N) (VP N) ℂ) : proj r (A + B) = proj r A + proj r B := by
  ext p q; simp only [proj, Matrix.add_apply]; split_ifs <;> simp

lemma proj_sub (r : ℕ) (A B : Matrix (VP N) (VP N) ℂ) : proj r (A - B) = proj r A - proj r B := by
  ext p q; simp only [proj, Matrix.sub_apply]; split_ifs <;> simp

lemma proj_smul (r : ℕ) (c : ℝ) (A : Matrix (VP N) (VP N) ℂ) : proj r (c • A) = c • proj r A := by
  ext p q; simp only [proj, Matrix.smul_apply]; split_ifs <;> simp

variable (N) in
/-- Projections of `Mf` to the weight-`r` block. -/
noncomputable def Hf (r : ℕ) : LieSubalgebra ℝ (Matrix (VP N) (VP N) ℂ) where
  carrier := {S | ∃ A ∈ Mf N, proj r A = S}
  add_mem' := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    exact ⟨A + B, add_mem hA hB, proj_add _ _ _⟩
  zero_mem' := ⟨0, zero_mem _, by ext; simp [proj]⟩
  smul_mem' := by
    rintro c _ ⟨A, hA, rfl⟩
    exact ⟨c • A, (Mf N).smul_mem c hA, proj_smul _ _ _⟩
  lie_mem' := by
    rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    refine ⟨⁅A, B⁆, (Mf N).lie_mem hA hB, ?_⟩
    have hA' : BD A := fun p q h => Mf_BD hA h
    have hB' : BD B := fun p q h => Mf_BD hB h
    rw [Ring.lie_def, Ring.lie_def, proj_sub, proj_mul hA' hB', proj_mul hB' hA']

lemma proj_mem {A : Matrix (VP N) (VP N) ℂ} (hA : A ∈ Mf N) (r : ℕ) : proj r A ∈ Hf N r :=
  ⟨A, hA, rfl⟩

lemma lie_proj {A W : Matrix (VP N) (VP N) ℂ} (hA : BD A) {r : ℕ} (hW : supp (Wt r) W) :
    ⁅proj r A, W⁆ = ⁅A, W⁆ := by
  have h1 : proj r A * W = A * W := by
    ext p q
    simp only [Matrix.mul_apply, proj]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hw : W s q = 0
    · rw [hw, mul_zero, mul_zero]
    · have hs := (hW s q hw).1
      by_cases hp : wt p.1 = r
      · rw [if_pos ⟨hp, hs⟩]
      · rw [if_neg (fun h => hp h.1), zero_mul, hA p s (by rw [hs]; exact hp), zero_mul]
  have h2 : W * proj r A = W * A := by
    ext p q
    simp only [Matrix.mul_apply, proj]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hw : W p s = 0
    · rw [hw, zero_mul, zero_mul]
    · have hs := (hW p s hw).2
      by_cases hq : wt q.1 = r
      · rw [if_pos ⟨hs, hq⟩]
      · rw [if_neg (fun h => hq h.2), mul_zero, hA s q (by rw [hs]; exact Ne.symm hq), mul_zero]
  rw [Ring.lie_def, Ring.lie_def, h1, h2]

lemma supp_lie_BD {A W : Matrix (VP N) (VP N) ℂ} (hA : BD A) {r : ℕ} (hW : supp (Wt r) W) :
    supp (Wt r) ⁅A, W⁆ := by
  rw [← lie_proj hA hW]
  have hP : supp (Wt r) (proj r A) := by
    intro p q h
    simp only [proj] at h
    split_ifs at h with h'
    · exact h'
    · exact absurd rfl h
  exact supp_lie hP hW

variable (N) in
noncomputable def Kf (r : ℕ) : Submodule ℝ (Matrix (VP N) (VP N) ℂ) where
  carrier := {W | W ∈ Mf N ∧ supp (Wt r) W}
  add_mem' := by
    rintro A B ⟨hA, sA⟩ ⟨hB, sB⟩
    refine ⟨add_mem hA hB, fun p q h => ?_⟩
    by_cases ha : A p q = 0
    · exact sB p q (by simpa [ha] using h)
    · exact sA p q ha
  zero_mem' := ⟨zero_mem _, fun p q h => absurd rfl h⟩
  smul_mem' := by
    rintro c A ⟨hA, sA⟩
    refine ⟨(Mf N).smul_mem c hA, fun p q h => sA p q (fun h0 => h (by simp [h0]))⟩

/-- A block is reached once its projection contains `su` and some element localized on it is
non-scalar. -/
theorem block_of {r : ℕ} (hstep : suT (Wt r) ⊆ (Hf N r : Set (Matrix (VP N) (VP N) ℂ)))
    (hseed : ∃ W ∈ Mf N, supp (Wt r) W ∧ ∃ a b : VP N, Wt r a ∧ Wt r b ∧ a ≠ b ∧ W a b ≠ 0) :
    suT (Wt r) ⊆ (Mf N : Set (Matrix (VP N) (VP N) ℂ)) := by
  obtain ⟨W, hW, hWs, a, b, ha, hb, hab, hne⟩ := hseed
  have hK : ∀ S ∈ suT (Wt r : VP N → Prop), ∀ w ∈ Kf N r, ⁅S, w⁆ ∈ Kf N r := by
    intro S hS w hw
    obtain ⟨A, hA, rfl⟩ := hstep hS
    have hA' : BD A := fun p q h => Mf_BD hA h
    rw [lie_proj hA' hw.2]
    exact ⟨(Mf N).lie_mem hA hw.1, supp_lie_BD hA' hw.2⟩
  intro X hX
  exact (simple (Kf N r) (Wt r) hK (X := W) ⟨hW, hWs⟩ (Mf_skew hW) hWs
    ⟨a, b, ha, hb, hab, Or.inl hne⟩ hX).1

end Struct

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Lift2

variable {N : ℕ}

def tailV (p : VP (N + 1)) : VP N := ⟨Fin.tail p.1, ((validB_succ p.1).1 p.2).1⟩

def b0 (x : VP N) : VP (N + 1) :=
  ⟨Fin.cons 0 x.1, by rw [validB_succ]; simp [x.2]⟩

def b1 (x : VP N) (h : 2 * wt x.1 + 1 ≤ N) : VP (N + 1) :=
  ⟨Fin.cons 1 x.1, by rw [validB_succ]; simp [x.2, h]⟩

@[simp] lemma tailV_b0 (x : VP N) : tailV (b0 x) = x := by simp [tailV, b0]
@[simp] lemma tailV_b1 (x : VP N) (h) : tailV (b1 x h) = x := by simp [tailV, b1]
@[simp] lemma b0_zero (x : VP N) : (b0 x).1 0 = 0 := by simp [b0]
@[simp] lemma b1_zero (x : VP N) (h) : (b1 x h).1 0 = 1 := by simp [b1]

lemma wt_b0 (x : VP N) : wt (b0 x).1 = wt x.1 := by simp [b0, wt_cons]
lemma wt_b1 (x : VP N) (h) : wt (b1 x h).1 = wt x.1 + 1 := by simp [b1, wt_cons]

lemma wt_tailV (p : VP (N + 1)) : wt p.1 = wt (tailV p).1 + p.1 0 := wt_tail p.1

lemma eq_b0 {p : VP (N + 1)} (h : p.1 0 = 0) : p = b0 (tailV p) := by
  apply Subtype.ext
  simp only [b0, tailV]
  rw [← h, Fin.cons_self_tail]

lemma eq_b1 {p : VP (N + 1)} (h : p.1 0 = 1) :
    ∃ h', p = b1 (tailV p) h' := by
  have hv := (validB_succ p.1).1 p.2
  refine ⟨hv.2 h, Subtype.ext ?_⟩
  simp only [b1, tailV]
  rw [← h, Fin.cons_self_tail]

lemma b0_ne_b1 (x y : VP N) (h) : b0 x ≠ b1 y h := by
  intro e
  have := congrArg (fun p : VP (N + 1) => p.1 0) e
  simp at this

lemma b0_inj {x y : VP N} (h : b0 x = b0 y) : x = y := by
  have := congrArg tailV h; simpa using this

lemma b1_inj {x y : VP N} {hx hy} (h : b1 x hx = b1 y hy) : x = y := by
  have := congrArg tailV h; simpa using this

/-- Lift of a path-basis matrix from `N` to `N + 1` qubits (identity on the newest qubit). -/
def liftM (A : Matrix (VP N) (VP N) ℂ) : Matrix (VP (N + 1)) (VP (N + 1)) ℂ :=
  fun p q => if p.1 0 = q.1 0 then A (tailV p) (tailV q) else 0

lemma MZ_liftT {Z : Matrix (St N) (St N) ℂ} (hZ : Comm N Z) : MZ (liftT Z) = liftM (MZ Z) := by
  ext p q
  have hp : p.1 = Fin.cons (p.1 0) (Fin.tail p.1) := (Fin.cons_self_tail p.1).symm
  have hq : q.1 = Fin.cons (q.1 0) (Fin.tail q.1) := (Fin.cons_self_tail q.1).symm
  have hpv := p.2
  have hqv := q.2
  rw [hp] at hpv
  rw [hq] at hqv
  simp only [MZ, liftM]
  rw [hp, hq, blkS_liftT hZ _ _ _ _ hpv hqv]
  simp only [Fin.cons_zero]
  rfl

lemma liftM_mem {A : Matrix (VP N) (VP N) ℂ} (hA : A ∈ Mf N) : liftM A ∈ Mf (N + 1) := by
  obtain ⟨Z, hZ, rfl⟩ := hA
  exact ⟨liftT Z, exchangeLie_lift hZ, MZ_liftT (exchangeLie_comm hZ)⟩

lemma VP_cases (p : VP (N + 1)) : (∃ x, p = b0 x) ∨ (∃ x h, p = b1 x h) := by
  rcases Fin.exists_fin_two.1 ⟨p.1 0, rfl⟩ with h | h
  · exact Or.inl ⟨_, eq_b0 h⟩
  · obtain ⟨h', e⟩ := eq_b1 h; exact Or.inr ⟨_, h', e⟩

lemma b0_eq_iff {x y : VP N} : b0 x = b0 y ↔ x = y := ⟨b0_inj, fun e => e ▸ rfl⟩
lemma b1_eq_iff {x y : VP N} {hx hy} : b1 x hx = b1 y hy ↔ x = y :=
  ⟨b1_inj, fun e => by subst e; rfl⟩
lemma b1_ne_b0 (x y : VP N) (h) : b1 x h ≠ b0 y := fun e => b0_ne_b1 _ _ _ e.symm

@[simp] lemma liftM_b0b0 (A : Matrix (VP N) (VP N) ℂ) (x y : VP N) :
    liftM A (b0 x) (b0 y) = A x y := by simp [liftM]
@[simp] lemma liftM_b0b1 (A : Matrix (VP N) (VP N) ℂ) (x y : VP N) (h) :
    liftM A (b0 x) (b1 y h) = 0 := by simp [liftM]
@[simp] lemma liftM_b1b0 (A : Matrix (VP N) (VP N) ℂ) (x y : VP N) (h) :
    liftM A (b1 x h) (b0 y) = 0 := by simp [liftM]
@[simp] lemma liftM_b1b1 (A : Matrix (VP N) (VP N) ℂ) (x y : VP N) (h h') :
    liftM A (b1 x h) (b1 y h') = A x y := by simp [liftM]

lemma liftM_Mu (x y : VP N) (c : ℂ) (hw : wt x.1 = wt y.1) :
    liftM (Mu x y c) = Mu (b0 x) (b0 y) c +
      (if h : 2 * wt x.1 + 1 ≤ N then Mu (b1 x h) (b1 y (hw ▸ h)) c else 0) := by
  ext p q
  rw [Matrix.add_apply]
  rcases VP_cases p with ⟨x', rfl⟩ | ⟨x', hx', rfl⟩ <;>
    rcases VP_cases q with ⟨y', rfl⟩ | ⟨y', hy', rfl⟩
  · rw [liftM_b0b0]
    split_ifs with hN
    · simp [Mu_apply, b0_eq_iff, b1_ne_b0, b0_ne_b1]
    · simp [Mu_apply, b0_eq_iff]
  · rw [liftM_b0b1]
    split_ifs with hN
    · simp [Mu_apply, b0_eq_iff, b1_ne_b0, b0_ne_b1]
    · simp [Mu_apply, b0_ne_b1, b1_ne_b0]
  · rw [liftM_b1b0]
    split_ifs with hN
    · simp [Mu_apply, b0_eq_iff, b1_ne_b0, b0_ne_b1]
    · simp [Mu_apply, b1_ne_b0]
  · rw [liftM_b1b1]
    split_ifs with hN
    · simp [Mu_apply, b1_eq_iff, b1_ne_b0, b0_ne_b1]
    · have h1 : x' ≠ x := fun e => hN (e ▸ hx')
      have h2 : x' ≠ y := fun e => hN (hw ▸ e ▸ hx')
      simp [Mu_apply, b1_ne_b0, h1, h2]

lemma liftM_diag (g : VP N → ℂ) :
    liftM (Complex.I • Matrix.diagonal g) = Complex.I • Matrix.diagonal (g ∘ tailV) := by
  ext p q
  simp only [liftM, Matrix.smul_apply, Matrix.diagonal_apply, Function.comp_apply]
  by_cases hpq : p = q
  · subst hpq; simp
  · rw [if_neg hpq]
    split_ifs with h1 h2
    · exfalso; apply hpq
      apply Subtype.ext
      rw [← Fin.cons_self_tail p.1, ← Fin.cons_self_tail q.1, h1]
      have := congrArg Subtype.val h2
      simp only [tailV] at this
      rw [this]
    · simp
    · simp

lemma MZ_E01 {n : ℕ} (p q : VP (n + 2)) : MZ (exchange (0 : Fin (n + 2)) 1) p q = Ematf p.1 q.1 :=
  blkS_E01 p.2 q.2

lemma iE01_mem {n : ℕ} : Complex.I • MZ (exchange (0 : Fin (n + 2)) 1) ∈ Mf (n + 2) := by
  refine ⟨Complex.I • exchange 0 1, LieSubalgebra.subset_lieSpan ⟨0, 1, ?_, rfl⟩, MZ_smul _ _⟩
  intro e; have := congrArg Fin.val e; simp at this

/-- The highest path: all `T` steps first, then `B`. -/
def topS : (m s : ℕ) → St m
  | 0, _ => fun i => i.elim0
  | m + 1, 0 => Fin.cons 0 (topS m 0)
  | m + 1, s + 1 => Fin.cons 1 (topS m s)

lemma topS_spec : ∀ (m s : ℕ), 2 * s ≤ m → validB m (topS m s) = true ∧ wt (topS m s) = s
  | 0, s, h => by
    have : s = 0 := by omega
    subst this; exact ⟨rfl, by simp [wt]⟩
  | m + 1, 0, _ => by
    have ih := topS_spec m 0 (by omega)
    refine ⟨?_, ?_⟩
    · rw [validB_succ]; simp [topS, ih.1]
    · simp [topS, wt_cons, ih.2]
  | m + 1, s + 1, h => by
    have ih := topS_spec m s (by omega)
    refine ⟨?_, ?_⟩
    · rw [validB_succ]; simp [topS, ih.1, ih.2]; omega
    · simp [topS, wt_cons, ih.2]

def topV (m s : ℕ) (h : 2 * s ≤ m) : VP m := ⟨topS m s, (topS_spec m s h).1⟩

lemma wt_topV (m s : ℕ) (h) : wt (topV m s h).1 = s := (topS_spec m s h).2

lemma exists_two (m s : ℕ) (hs : 1 ≤ s) (h : 2 * s ≤ m) (hm : (m, s) ≠ (2, 1)) :
    ∃ x y : VP m, x ≠ y ∧ wt x.1 = s ∧ wt y.1 = s := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  by_cases h1 : 2 * s ≤ m'
  · refine ⟨b0 (topV m' s h1), b1 (topV m' (s - 1) (by omega)) (by rw [wt_topV]; omega),
      b0_ne_b1 _ _ _, by rw [wt_b0, wt_topV], by rw [wt_b1, wt_topV]; omega⟩
  · obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    have hs2 : 2 ≤ s := by
      by_contra hc
      apply hm
      have : s = 1 := by omega
      subst this
      simp; omega
    set x := b0 (topV m'' (s - 1) (by omega))
    set y := b1 (topV m'' (s - 2) (by omega)) (by rw [wt_topV]; omega)
    have hx : 2 * wt x.1 + 1 ≤ m'' + 1 := by rw [wt_b0, wt_topV]; omega
    have hy : 2 * wt y.1 + 1 ≤ m'' + 1 := by rw [wt_b1, wt_topV]; omega
    refine ⟨b1 x hx, b1 y hy, fun e => b0_ne_b1 _ _ _ (b1_inj e), ?_, ?_⟩
    · rw [wt_b1, wt_b0, wt_topV]; omega
    · rw [wt_b1, wt_b1, wt_topV]; omega

end Lift2

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Ind1

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def RelL (L : LieSubalgebra ℝ (Matrix ι ι ℂ)) (x y : ι) : Prop := x ≠ y ∧ ∀ c : ℂ, Mu x y c ∈ L

lemma RelL.symm {L : LieSubalgebra ℝ (Matrix ι ι ℂ)} {x y : ι} (h : RelL L x y) : RelL L y x :=
  ⟨h.1.symm, fun c => by rw [Mu_swap]; exact h.2 _⟩

lemma RelL.trans {L : LieSubalgebra ℝ (Matrix ι ι ℂ)} {x y z : ι} (hxy : RelL L x y)
    (hyz : RelL L y z) (hxz : x ≠ z) : RelL L x z :=
  ⟨hxz, fun c => by
    have := L.lie_mem (hxy.2 c) (hyz.2 1)
    rwa [lie_Mu_Mu hxy.1 hyz.1 hxz, mul_one] at this⟩

lemma rel_of_real {L : LieSubalgebra ℝ (Matrix ι ι ℂ)} {a b : ι} (hab : a ≠ b) {c0 : ℝ}
    (hc0 : c0 ≠ 0) (h1 : Mu a b c0 ∈ L) (h2 : Mu a b (Complex.I * c0) ∈ L) : RelL L a b := by
  refine ⟨hab, fun c => ?_⟩
  have e : Mu a b c = (c.re / c0) • Mu a b c0 + (c.im / c0) • Mu a b (Complex.I * c0) := by
    rw [← Mu_rsmul, ← Mu_rsmul, ← Mu_add]
    congr 1
    apply Complex.ext <;> simp <;> field_simp
  rw [e]
  exact L.add_mem (L.smul_mem _ h1) (L.smul_mem _ h2)

lemma lie_IdiagI (f : ι → ℂ) (Y : Matrix ι ι ℂ) (p q : ι) :
    ⁅Complex.I • Matrix.diagonal f, Complex.I • Y⁆ p q = -((f p - f q) * Y p q) := by
  rw [lie_smul, Matrix.smul_apply, lie_diag_apply, smul_eq_mul]
  ring_nf; rw [Complex.I_sq]; ring

/-- A traceless anti-Hermitian matrix on a block with at most one index vanishes. -/
lemma suT_small {T : ι → Prop} (hT : ∀ p q, T p → T q → p = q) {X : Matrix ι ι ℂ}
    (hX : X ∈ suT T) : X = 0 := by
  obtain ⟨_, hs, htr⟩ := hX
  ext p q
  by_contra hne
  obtain ⟨hp, hq⟩ := hs p q hne
  have hpq := hT p q hp hq
  subst hpq
  apply hne
  have : X.trace = X p p := by
    rw [Matrix.trace, Finset.sum_eq_single p]
    · rfl
    · intro b _ hb
      by_contra h
      exact hb (hT b p (hs b b h).1 hp)
    · simp
  rw [← this, htr]; rfl

end Ind1

section Ind1b

variable {n : ℕ}

/-- `BT u = b0 (b1 u)` and `TB u = b1 (b0 u)`: the two paths through `u` that `E₀₁` mixes. -/
def BTp (u : VP n) (h : 2 * wt u.1 + 1 ≤ n) : VP (n + 2) := b0 (b1 u h)

def TBp (u : VP n) : VP (n + 2) :=
  b1 (b0 u) (by rw [wt_b0]; have := valid_two_wt u.1 u.2; omega)

lemma wt_BTp (u : VP n) (h) : wt (BTp u h).1 = wt u.1 + 1 := by rw [BTp, wt_b0, wt_b1]
lemma wt_TBp (u : VP n) : wt (TBp u).1 = wt u.1 + 1 := by rw [TBp, wt_b1, wt_b0]

lemma BTp_ne_TBp (u v : VP n) (h) : BTp u h ≠ TBp v := b0_ne_b1 _ _ _

lemma Ematf_BT_TB (u : VP n) (h) :
    Ematf (BTp u h).1 (TBp u).1 = qc (n - 2 * wt u.1) := by
  simp [Ematf, BTp, TBp, b0, b1, Fin.tail]

lemma Ematf_TB_BT (u : VP n) (h) :
    Ematf (TBp u).1 (BTp u h).1 = qc (n - 2 * wt u.1) := by
  simp [Ematf, BTp, TBp, b0, b1, Fin.tail]

lemma qc_ne {d : ℕ} (hd : 1 ≤ d) : qc d ≠ 0 := by
  rw [qc]
  have h1 := be_ne hd
  have h2 := be_succ_ne d
  have h3 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have h4 : (d : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  exact div_ne_zero (mul_ne_zero h3 h1) (mul_ne_zero h4 h2)

lemma Ematf_off (P Q : St (n + 2)) (hPQ : P ≠ Q) (hE : Ematf P Q ≠ 0) :
    (Q = Fin.cons 0 (Fin.cons 1 (Fin.tail (Fin.tail Q))) ∧
        P = Fin.cons 1 (Fin.cons 0 (Fin.tail (Fin.tail Q)))) ∨
      (Q = Fin.cons 1 (Fin.cons 0 (Fin.tail (Fin.tail Q))) ∧
        P = Fin.cons 0 (Fin.cons 1 (Fin.tail (Fin.tail Q)))) := by
  have hQ : Q = Fin.cons (Q 0) (Fin.cons (Q 1) (Fin.tail (Fin.tail Q))) := by
    conv_lhs => rw [← Fin.cons_self_tail Q, ← Fin.cons_self_tail (Fin.tail Q)]
    rfl
  unfold Ematf at hE
  by_cases h1 : Q 0 = Q 1
  · rw [if_pos h1, if_neg hPQ] at hE; exact absurd rfl hE
  · rw [if_neg h1] at hE
    by_cases h2 : Q 0 = 0
    · rw [if_pos h2, if_neg hPQ, mul_zero, zero_add] at hE
      have hP : P = Fin.cons 1 (Fin.cons 0 (Fin.tail (Fin.tail Q))) := by
        by_contra hc; rw [if_neg hc, mul_zero] at hE; exact hE rfl
      have hq1 : Q 1 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨Q 1, rfl⟩ with h | h
        · exact absurd (h2.trans h.symm) h1
        · exact h
      left
      refine ⟨?_, hP⟩
      conv_lhs => rw [hQ]
      rw [h2, hq1]
    · rw [if_neg h2, if_neg hPQ, mul_zero, sub_zero] at hE
      have hP : P = Fin.cons 0 (Fin.cons 1 (Fin.tail (Fin.tail Q))) := by
        by_contra hc; rw [if_neg hc, mul_zero] at hE; exact hE rfl
      have h0 : Q 0 = 1 := by
        rcases Fin.exists_fin_two.1 ⟨Q 0, rfl⟩ with h | h
        · exact absurd h h2
        · exact h
      have hq1 : Q 1 = 0 := by
        rcases Fin.exists_fin_two.1 ⟨Q 1, rfl⟩ with h | h
        · exact h
        · exact absurd (h0.trans h.symm) h1
      right
      refine ⟨?_, hP⟩
      conv_lhs => rw [hQ]
      rw [h0, hq1]

/-- The only off-diagonal entries of `E₀₁` couple `BT u` and `TB u`. -/
lemma E_off {p q : VP (n + 2)} (hpq : p ≠ q) (hE : Ematf p.1 q.1 ≠ 0) :
    (∃ u h, p = TBp u ∧ q = BTp u h) ∨ (∃ u h, p = BTp u h ∧ q = TBp u) := by
  have hne : p.1 ≠ q.1 := fun e => hpq (Subtype.ext e)
  set u : VP n := tailV (tailV q) with hu
  have hp2 := p.2
  rcases Ematf_off p.1 q.1 hne hE with ⟨hq, hp⟩ | ⟨hq, hp⟩
  · have hq2 := q.2
    rw [hq, validB_succ, validB_succ] at hq2
    simp only [Fin.tail_cons, Fin.cons_zero] at hq2
    have hh : 2 * wt u.1 + 1 ≤ n := hq2.1.2 (by simp)
    left
    exact ⟨u, hh, Subtype.ext hp, Subtype.ext hq⟩
  · rw [hp, validB_succ, validB_succ] at hp2
    simp only [Fin.tail_cons, Fin.cons_zero] at hp2
    have hh : 2 * wt (Fin.tail (Fin.tail q.1)) + 1 ≤ n := hp2.1.2 (by simp)
    right
    exact ⟨u, hh, Subtype.ext hp, Subtype.ext hq⟩

end Ind1b

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Ind2

def Claim (m : ℕ) : Prop := ∀ r, suT (Wt r : VP m → Prop) ⊆ (Mf m : Set (Matrix (VP m) (VP m) ℂ))

variable {m n : ℕ}

def ind (a : VP m) : VP m → ℂ := fun p => if p = a then 1 else 0

lemma proj_Mu_in {r : ℕ} {a b : VP m} (ha : wt a.1 = r) (hb : wt b.1 = r) (c : ℂ) :
    proj r (Mu a b c) = Mu a b c := by
  ext p q
  simp only [proj, Mu_apply]
  by_cases h : wt p.1 = r ∧ wt q.1 = r
  · rw [if_pos h]
  · rw [if_neg h]
    have e1 : ¬(p = a ∧ q = b) := fun e => h ⟨e.1 ▸ ha, e.2 ▸ hb⟩
    have e2 : ¬(p = b ∧ q = a) := fun e => h ⟨e.1 ▸ hb, e.2 ▸ ha⟩
    rw [if_neg e1, if_neg e2, sub_zero]

lemma proj_Mu_out {r : ℕ} {a b : VP m} (ha : wt a.1 ≠ r) (hb : wt b.1 ≠ r) (c : ℂ) :
    proj r (Mu a b c) = 0 := by
  ext p q
  simp only [proj, Mu_apply, Matrix.zero_apply]
  by_cases h : wt p.1 = r ∧ wt q.1 = r
  · rw [if_pos h]
    have e1 : ¬(p = a ∧ q = b) := fun e => ha (e.1 ▸ h.1)
    have e2 : ¬(p = b ∧ q = a) := fun e => hb (e.1 ▸ h.1)
    rw [if_neg e1, if_neg e2, sub_zero]
  · rw [if_neg h]

lemma proj_zero_eq (r : ℕ) : proj r (0 : Matrix (VP m) (VP m) ℂ) = 0 := by
  ext p q; simp [proj]

lemma proj_diag (r : ℕ) (f : VP m → ℂ) :
    proj r (Complex.I • Matrix.diagonal f)
      = Complex.I • Matrix.diagonal (fun p => if wt p.1 = r then f p else 0) := by
  ext p q
  simp only [proj, Matrix.smul_apply, Matrix.diagonal_apply]
  by_cases hpq : p = q
  · subst hpq; by_cases h : wt p.1 = r <;> simp [h]
  · simp [hpq]

lemma diagInd_suT {s : ℕ} {a1 a2 : VP m} (hne : a1 ≠ a2) (h1 : wt a1.1 = s) (h2 : wt a2.1 = s) :
    Complex.I • Matrix.diagonal (ind a1 - ind a2) ∈ suT (Wt s) := by
  refine ⟨?_, ?_, ?_⟩
  · ext p q
    simp only [conjTranspose_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.neg_apply,
      ind, Pi.sub_apply]
    by_cases h : p = q
    · subst h; simp
    · simp [h, Ne.symm h]
  · intro p q h
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, ind, Pi.sub_apply] at h
    by_cases hpq : q = p
    · subst hpq
      by_cases ha : q = a1
      · subst ha; exact ⟨h1, h1⟩
      · by_cases hb : q = a2
        · subst hb; exact ⟨h2, h2⟩
        · simp [ha, hb] at h
    · simp [Ne.symm hpq] at h
  · rw [Matrix.trace]
    simp only [Matrix.diag, Matrix.smul_apply, Matrix.diagonal_apply_eq, ind, Pi.sub_apply,
      smul_eq_mul]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp

lemma liftDiag_mem (hC : Claim (n + 1)) {s : ℕ} {g : VP (n + 1) → ℂ}
    (hg : Complex.I • Matrix.diagonal g ∈ suT (Wt s)) :
    Complex.I • Matrix.diagonal (g ∘ tailV) ∈ Mf (n + 2) := by
  rw [← liftM_diag]; exact liftM_mem (hC s hg)

lemma W_apply (g : VP (n + 1) → ℂ) (p q : VP (n + 2)) :
    ⁅Complex.I • Matrix.diagonal (g ∘ tailV), Complex.I • MZ (exchange (0 : Fin (n + 2)) 1)⁆ p q
      = -((g (tailV p) - g (tailV q)) * Ematf p.1 q.1) := by
  rw [lie_IdiagI, MZ_E01]; rfl

lemma qc_im (d : ℕ) : (qc d).im = 0 := by
  simp [qc, be, Complex.div_im, Complex.mul_im]

lemma qc_real (d : ℕ) : qc d = (((qc d).re : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [qc_im]

lemma rel_b0 (hC : Claim (n + 1)) {r : ℕ} {x y : VP (n + 1)} (hne : x ≠ y) (hx : wt x.1 = r)
    (hy : wt y.1 = r) : RelL (Hf (n + 2) r) (b0 x) (b0 y) := by
  refine ⟨fun e => hne (b0_inj e), fun c => ?_⟩
  have hM := liftM_mem (hC r (Mu_suT (T := (Wt r : VP (n + 1) → Prop)) hx hy hne c))
  have := proj_mem hM r
  rw [liftM_Mu x y c (hx.trans hy.symm), proj_add, proj_Mu_in (by rw [wt_b0, hx])
    (by rw [wt_b0, hy])] at this
  split_ifs at this with h
  · rw [proj_Mu_out (by rw [wt_b1]; omega) (by rw [wt_b1]; omega), add_zero] at this
    exact this
  · rw [proj_zero_eq, add_zero] at this
    exact this

lemma rel_b1 (hC : Claim (n + 1)) {r : ℕ} {x y : VP (n + 1)} (hne : x ≠ y) (hx : wt x.1 + 1 = r)
    (hy : wt y.1 + 1 = r) (hx' : 2 * wt x.1 + 1 ≤ n + 1) (hy' : 2 * wt y.1 + 1 ≤ n + 1) :
    RelL (Hf (n + 2) r) (b1 x hx') (b1 y hy') := by
  refine ⟨fun e => hne (b1_inj e), fun c => ?_⟩
  have hxy : wt x.1 = wt y.1 := by omega
  have hM := liftM_mem (hC (wt x.1) (Mu_suT (T := (Wt (wt x.1) : VP (n + 1) → Prop)) rfl
    hxy.symm hne c))
  have := proj_mem hM r
  rw [liftM_Mu x y c hxy, proj_add, proj_Mu_out (by rw [wt_b0]; omega) (by rw [wt_b0]; omega),
    zero_add, dif_pos hx', proj_Mu_in (by rw [wt_b1]; omega) (by rw [wt_b1]; omega)] at this
  exact this

lemma cross_rel_gen (u0 : VP n) (h0 : 2 * wt u0.1 + 1 ≤ n) (g : VP (n + 1) → ℂ)
    (hD : Complex.I • Matrix.diagonal (g ∘ tailV) ∈ Mf (n + 2)) {t : ℝ} (ht : t ≠ 0)
    (hdiff : ∀ u h, wt u.1 = wt u0.1 →
      g (b1 u h) - g (b0 u) = if u = u0 then (t : ℂ) else 0) :
    RelL (Hf (n + 2) (wt u0.1 + 1)) (BTp u0 h0) (TBp u0) := by
  set r := wt u0.1 + 1 with hr
  set a := BTp u0 h0
  set b := TBp u0
  have hab : a ≠ b := BTp_ne_TBp _ _ _
  have hW := (Mf (n + 2)).lie_mem hD iE01_mem
  set c0 : ℝ := -(t * (qc (n - 2 * wt u0.1)).re) with hc0
  have hqc : qc (n - 2 * wt u0.1) = (((qc (n - 2 * wt u0.1)).re : ℝ) : ℂ) := qc_real _
  have hc0ne : c0 ≠ 0 := by
    intro e
    have : (qc (n - 2 * wt u0.1)).re = 0 := by
      rcases mul_eq_zero.1 (neg_eq_zero.1 e) with h | h
      · exact absurd h ht
      · exact h
    apply qc_ne (d := n - 2 * wt u0.1) (by omega)
    rw [hqc, this]; simp
  have hBTinj : ∀ u h, BTp u h = a → u = u0 := by
    intro u h e
    have := congrArg (fun p => tailV (tailV p)) e
    simpa [a, BTp] using this
  have hTBinj : ∀ u, TBp u = b → u = u0 := by
    intro u e
    have := congrArg (fun p => tailV (tailV p)) e
    simpa [b, TBp] using this
  have hga : g (tailV a) = g (b1 u0 h0) := by simp [a, BTp]
  have hgb : g (tailV b) = g (b0 u0) := by simp [b, TBp]
  have hdiff0 := hdiff u0 h0 rfl
  rw [if_pos rfl] at hdiff0
  have hEab : Ematf a.1 b.1 = qc (n - 2 * wt u0.1) := Ematf_BT_TB u0 h0
  have hEba : Ematf b.1 a.1 = qc (n - 2 * wt u0.1) := Ematf_TB_BT u0 h0
  have hP : proj r ⁅Complex.I • Matrix.diagonal (g ∘ tailV),
      Complex.I • MZ (exchange (0 : Fin (n + 2)) 1)⁆ = Mu a b (c0 : ℂ) := by
    ext p q
    simp only [proj]
    rw [Mu_apply]
    by_cases hb : wt p.1 = r ∧ wt q.1 = r
    · rw [if_pos hb, W_apply]
      by_cases hpq : p = q
      · subst hpq
        rw [sub_self, zero_mul, neg_zero, if_neg (fun e => hab (e.1.symm.trans e.2)),
          if_neg (fun e => hab (e.2.symm.trans e.1)), sub_zero]
      by_cases hE : Ematf p.1 q.1 = 0
      · rw [hE, mul_zero, neg_zero]
        have e1 : ¬(p = a ∧ q = b) := by
          rintro ⟨rfl, rfl⟩; rw [hEab] at hE; exact qc_ne (by omega) hE
        have e2 : ¬(p = b ∧ q = a) := by
          rintro ⟨rfl, rfl⟩; rw [hEba] at hE; exact qc_ne (by omega) hE
        rw [if_neg e1, if_neg e2, sub_zero]
      rcases E_off hpq hE with ⟨u, h, rfl, rfl⟩ | ⟨u, h, rfl, rfl⟩
      · -- p = TB u, q = BT u
        have hwu : wt u.1 = wt u0.1 := by have := hb.1; rw [wt_TBp] at this; omega
        have hd := hdiff u h hwu
        rw [Ematf_TB_BT]
        have h1 : tailV (TBp u) = b0 u := by simp [TBp]
        have h2 : tailV (BTp u h) = b1 u h := by simp [BTp]
        rw [h1, h2]
        have e1 : ¬(TBp u = a ∧ BTp u h = b) := fun e => BTp_ne_TBp _ _ _ e.2
        rw [if_neg e1]
        by_cases hu : u = u0
        · obtain rfl := hu
          rw [if_pos rfl] at hd
          have e2 : TBp u = b ∧ BTp u h = a := ⟨rfl, rfl⟩
          rw [if_pos e2, hc0]
          simp only [Complex.ofReal_neg, Complex.ofReal_mul, star_neg, star_mul', Complex.star_def,
            Complex.conj_ofReal, zero_sub, neg_neg]
          rw [← hqc]
          linear_combination (qc (n - 2 * wt u.1)) * hd
        · rw [if_neg hu] at hd
          have e2 : ¬(TBp u = b ∧ BTp u h = a) := fun e => hu (hTBinj u e.1)
          rw [if_neg e2, sub_zero]
          linear_combination (qc (n - 2 * wt u.1)) * hd
      · -- p = BT u, q = TB u
        have hwu : wt u.1 = wt u0.1 := by have := hb.1; rw [wt_BTp] at this; omega
        have hd := hdiff u h hwu
        rw [Ematf_BT_TB]
        have h1 : tailV (TBp u) = b0 u := by simp [TBp]
        have h2 : tailV (BTp u h) = b1 u h := by simp [BTp]
        rw [h1, h2]
        have e2 : ¬(BTp u h = b ∧ TBp u = a) := fun e => BTp_ne_TBp _ _ _ e.1
        rw [if_neg e2, sub_zero]
        by_cases hu : u = u0
        · obtain rfl := hu
          rw [if_pos rfl] at hd
          have e1 : BTp u h = a ∧ TBp u = b := ⟨rfl, rfl⟩
          rw [if_pos e1, hc0, Complex.ofReal_neg, Complex.ofReal_mul, ← hqc]
          linear_combination (-(qc (n - 2 * wt u.1))) * hd
        · rw [if_neg hu] at hd
          have e1 : ¬(BTp u h = a ∧ TBp u = b) := fun e => hu (hBTinj u h e.1)
          rw [if_neg e1]
          linear_combination (-(qc (n - 2 * wt u.1))) * hd
    · rw [if_neg hb]
      have hwa : wt a.1 = r := by rw [wt_BTp]
      have hwb : wt b.1 = r := by rw [wt_TBp]
      have e1 : ¬(p = a ∧ q = b) := fun e => hb ⟨e.1 ▸ hwa, e.2 ▸ hwb⟩
      have e2 : ¬(p = b ∧ q = a) := fun e => hb ⟨e.1 ▸ hwb, e.2 ▸ hwa⟩
      rw [if_neg e1, if_neg e2, sub_zero]
  have hM1 : Mu a b (c0 : ℂ) ∈ Hf (n + 2) r := hP ▸ proj_mem hW r
  have hDp := proj_mem hD r
  rw [proj_diag] at hDp
  have hM2 := (Hf (n + 2) r).lie_mem hDp hM1
  rw [lie_diag_Mu] at hM2
  have hfa : (if wt a.1 = r then (g ∘ tailV) a else 0) - (if wt b.1 = r then (g ∘ tailV) b else 0)
      = t := by
    rw [if_pos (wt_BTp _ _), if_pos (wt_TBp _), Function.comp_apply, Function.comp_apply, hga, hgb]
    exact hdiff0
  rw [hfa] at hM2
  have hM3 := (Hf (n + 2) r).smul_mem t⁻¹ hM2
  have e : ((t⁻¹ : ℝ) : ℂ) * (t : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ ht, Complex.ofReal_one]
  rw [← Complex.coe_smul, smul_smul, e, one_smul] at hM3
  exact rel_of_real hab hc0ne hM1 hM3

lemma cross_rel (hC : Claim (n + 1)) (u0 : VP n) (h0 : 2 * wt u0.1 + 1 ≤ n) {s : ℕ}
    {a1 a2 : VP (n + 1)} (hne : a1 ≠ a2) (hw1 : wt a1.1 = s) (hw2 : wt a2.1 = s)
    (hdiff : ∀ u h, wt u.1 = wt u0.1 →
      (ind a1 - ind a2) (b1 u h) - (ind a1 - ind a2) (b0 u) = if u = u0 then 1 else 0) :
    RelL (Hf (n + 2) (wt u0.1 + 1)) (BTp u0 h0) (TBp u0) :=
  cross_rel_gen u0 h0 _ (liftDiag_mem hC (diagInd_suT hne hw1 hw2)) (t := 1) one_ne_zero
    (by simpa using hdiff)

theorem step1 (hC : Claim (n + 1)) (r : ℕ)
    (hcross : 2 * r ≤ n + 1 → ∃ u0 h0, wt u0.1 + 1 = r ∧ RelL (Hf (n + 2) r) (BTp u0 h0) (TBp u0)) :
    suT (Wt r : VP (n + 2) → Prop) ⊆ (Hf (n + 2) r : Set (Matrix (VP (n + 2)) (VP (n + 2)) ℂ)) := by
  apply su_of_rel
  intro x y hx hy hxy
  suffices h : RelL (Hf (n + 2) r) x y from h.2
  have hx' : wt x.1 = r := hx
  have hy' : wt y.1 = r := hy
  have mixed : ∀ x' y' hy'', wt (b0 x').1 = r → wt (b1 y' hy'').1 = r →
      RelL (Hf (n + 2) r) (b0 x') (b1 y' hy'') := by
    intro x' y' hy'' h1 h2
    rw [wt_b0] at h1
    rw [wt_b1] at h2
    obtain ⟨u0, h0, hu0, R⟩ := hcross (by have := valid_two_wt x'.1 x'.2; omega)
    have R1 : RelL (Hf (n + 2) r) (b0 x') (TBp u0) := by
      by_cases e : x' = b1 u0 h0
      · subst e; exact R
      · have hw : wt (b1 u0 h0).1 = r := by rw [wt_b1]; omega
        exact (rel_b0 hC e h1 hw).trans R (b0_ne_b1 _ _ _)
    by_cases e : y' = b0 u0
    · subst e; exact R1
    · have hw : wt (b0 u0).1 + 1 = r := by rw [wt_b0]; omega
      have R2 := rel_b1 hC (Ne.symm e) hw (by omega) (by rw [wt_b0]; have := valid_two_wt u0.1 u0.2; omega) hy''
      exact R1.trans R2 (b0_ne_b1 _ _ _)
  rcases VP_cases x with ⟨x', rfl⟩ | ⟨x', hx'', rfl⟩ <;>
    rcases VP_cases y with ⟨y', rfl⟩ | ⟨y', hy'', rfl⟩
  · exact rel_b0 hC (fun e => hxy (e ▸ rfl)) (by rw [← wt_b0]; exact hx') (by rw [← wt_b0]; exact hy')
  · exact mixed x' y' hy'' hx' hy'
  · exact (mixed y' x' hx'' hy' hx').symm
  · exact rel_b1 hC (fun e => hxy (by subst e; rfl)) (by rw [← wt_b1]; exact hx')
      (by rw [← wt_b1]; exact hy') hx'' hy''

end Ind2

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Ind3

variable {m n : ℕ}

def Seed (M r : ℕ) : Prop :=
  ∃ W ∈ Mf M, supp (Wt r) W ∧ ∃ a b : VP M, Wt r a ∧ Wt r b ∧ a ≠ b ∧ W a b ≠ 0

lemma small_block {r : ℕ} (h : ∀ p q : VP m, wt p.1 = r → wt q.1 = r → p = q) :
    suT (Wt r : VP m → Prop) ⊆ (Mf m : Set (Matrix (VP m) (VP m) ℂ)) := by
  intro X hX
  rw [suT_small h hX]; exact zero_mem _

lemma block0_small : ∀ p q : VP m, wt p.1 = 0 → wt q.1 = 0 → p = q := by
  intro p q hp hq
  apply Subtype.ext
  have hz : ∀ x : St m, wt x = 0 → x = fun _ => 0 := by
    intro x hx
    funext i
    rw [wt, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hx
    have := hx (Finset.mem_univ i)
    rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h | h
    · exact h
    · exact absurd h this
  rw [hz _ hp, hz _ hq]

lemma empty_block {r : ℕ} (hr : m < 2 * r) : ∀ p q : VP m, wt p.1 = r → wt q.1 = r → p = q := by
  intro p _ hp _
  have := valid_two_wt p.1 p.2
  omega

lemma seedA (hC : Claim (n + 1)) {r : ℕ} {a1 a2 : VP (n + 1)} (hne : a1 ≠ a2)
    (hw1 : wt a1.1 = r) (hw2 : wt a2.1 = r) (u0 : VP n) (h0 : 2 * wt u0.1 + 1 ≤ n)
    (ha1 : a1 = b1 u0 h0) (hcond : ∀ u : VP n, (b0 u = a1 ∨ b0 u = a2) → ¬ (2 * wt u.1 + 1 ≤ n)) :
    Seed (n + 2) r := by
  obtain ⟨g, hg⟩ : ∃ g, g = ind a1 - ind a2 := ⟨_, rfl⟩
  have hD := liftDiag_mem hC (diagInd_suT hne hw1 hw2)
  rw [← hg] at hD
  have hW := (Mf (n + 2)).lie_mem hD iE01_mem
  refine ⟨_, hW, ?_, BTp u0 h0, TBp u0, ?_, ?_, BTp_ne_TBp _ _ _, ?_⟩
  · intro p q hpq
    rw [W_apply] at hpq
    have hE : Ematf p.1 q.1 ≠ 0 := fun h => hpq (by rw [h, mul_zero, neg_zero])
    have hgd : g (tailV p) ≠ g (tailV q) := fun h => hpq (by rw [h, sub_self, zero_mul, neg_zero])
    have hne' : p ≠ q := fun h => hgd (by rw [h])
    have key : ∀ u h, g (b1 u h) ≠ g (b0 u) → wt u.1 + 1 = r := by
      intro u h hgu
      have hb0 : g (b0 u) = 0 := by
        simp only [hg, Pi.sub_apply, ind]
        rw [if_neg (fun e => hcond u (Or.inl e) h), if_neg (fun e => hcond u (Or.inr e) h)]
        ring
      rw [hb0] at hgu
      simp only [hg, Pi.sub_apply, ind] at hgu
      by_cases e1 : b1 u h = a1
      · rw [← wt_b1 u h, e1, hw1]
      · by_cases e2 : b1 u h = a2
        · rw [← wt_b1 u h, e2, hw2]
        · rw [if_neg e1, if_neg e2, sub_zero] at hgu; exact absurd rfl hgu
    rcases E_off hne' hE with ⟨u, h, rfl, rfl⟩ | ⟨u, h, rfl, rfl⟩
    · have : wt u.1 + 1 = r := key u h (fun e => hgd (by simp [TBp, BTp] at e ⊢; exact e.symm))
      exact ⟨by show wt (TBp u).1 = r; rw [wt_TBp]; exact this,
        by show wt (BTp u h).1 = r; rw [wt_BTp]; exact this⟩
    · have : wt u.1 + 1 = r := key u h (fun e => hgd (by simp [TBp, BTp] at e ⊢; exact e))
      exact ⟨by show wt (BTp u h).1 = r; rw [wt_BTp]; exact this,
        by show wt (TBp u).1 = r; rw [wt_TBp]; exact this⟩
  · show wt (BTp u0 h0).1 = r; rw [wt_BTp, ← hw1, ha1, wt_b1]
  · show wt (TBp u0).1 = r; rw [wt_TBp, ← hw1, ha1, wt_b1]
  · rw [W_apply, Ematf_BT_TB]
    have h1 : tailV (BTp u0 h0) = b1 u0 h0 := by simp [BTp]
    have h2 : tailV (TBp u0) = b0 u0 := by simp [TBp]
    rw [h1, h2]
    have hg1 : g (b1 u0 h0) = 1 := by
      simp only [hg, Pi.sub_apply, ind]; rw [if_pos ha1.symm, if_neg (fun e => hne (ha1.trans e))]; ring
    have hg0 : g (b0 u0) = 0 := by
      simp only [hg, Pi.sub_apply, ind]
      rw [if_neg (fun e => hcond u0 (Or.inl e) h0), if_neg (fun e => hcond u0 (Or.inr e) h0)]
      ring
    rw [hg1, hg0, sub_zero, one_mul]
    exact neg_ne_zero.2 (qc_ne (by omega))

lemma seedT {r : ℕ} (hdone : suT (Wt r : VP (n + 2) → Prop) ⊆ (Mf (n + 2) : Set _))
    {x y : VP (n + 1)} (hne : x ≠ y) (hx : wt x.1 = r) (hy : wt y.1 = r)
    (hv : 2 * wt x.1 + 1 ≤ n + 1) (hC : Claim (n + 1)) : Seed (n + 2) (r + 1) := by
  have hL := liftM_mem (hC r (Mu_suT (T := (Wt r : VP (n + 1) → Prop)) hx hy hne 1))
  rw [liftM_Mu x y 1 (hx.trans hy.symm), dif_pos hv] at hL
  have h0 := hdone (Mu_suT (T := (Wt r : VP (n + 2) → Prop)) (show wt (b0 x).1 = r by rw [wt_b0, hx])
    (show wt (b0 y).1 = r by rw [wt_b0, hy]) (fun e => hne (b0_inj e)) 1)
  have hM := sub_mem hL h0
  rw [add_sub_cancel_left] at hM
  have hy' : 2 * wt y.1 + 1 ≤ n + 1 := by rw [hy, ← hx]; exact hv
  refine ⟨_, hM, ?_, b1 x hv, b1 y hy', ?_, ?_, fun e => hne (b1_inj e), ?_⟩
  · intro p q h
    rw [Mu_apply] at h
    by_cases e1 : p = b1 x hv ∧ q = b1 y hy'
    · obtain ⟨rfl, rfl⟩ := e1
      exact ⟨by show wt _ = _; rw [wt_b1, hx], by show wt _ = _; rw [wt_b1, hy]⟩
    · by_cases e2 : p = b1 y hy' ∧ q = b1 x hv
      · obtain ⟨rfl, rfl⟩ := e2
        exact ⟨by show wt _ = _; rw [wt_b1, hy], by show wt _ = _; rw [wt_b1, hx]⟩
      · rw [if_neg e1, if_neg e2, sub_zero] at h; exact absurd rfl h
  · show wt _ = _; rw [wt_b1, hx]
  · show wt _ = _; rw [wt_b1, hy]
  · rw [Mu_apply, if_pos ⟨rfl, rfl⟩, if_neg (fun e => hne (b1_inj e.1))]; simp

lemma seedB {r : ℕ} (hdone : suT (Wt (r + 1) : VP (n + 2) → Prop) ⊆ (Mf (n + 2) : Set _))
    {x y : VP (n + 1)} (hne : x ≠ y) (hx : wt x.1 = r) (hy : wt y.1 = r) (hC : Claim (n + 1)) :
    Seed (n + 2) r := by
  have hL := liftM_mem (hC r (Mu_suT (T := (Wt r : VP (n + 1) → Prop)) hx hy hne 1))
  rw [liftM_Mu x y 1 (hx.trans hy.symm)] at hL
  have hM : Mu (b0 x) (b0 y) 1 ∈ Mf (n + 2) := by
    split_ifs at hL with hv
    · have hy' : 2 * wt y.1 + 1 ≤ n + 1 := by rw [hy, ← hx]; exact hv
      have h1 := hdone (Mu_suT (T := (Wt (r + 1) : VP (n + 2) → Prop))
        (show wt (b1 x hv).1 = r + 1 by rw [wt_b1, hx]) (show wt (b1 y hy').1 = r + 1 by rw [wt_b1, hy])
        (fun e => hne (b1_inj e)) 1)
      have := sub_mem hL h1
      rwa [add_sub_cancel_right] at this
    · rwa [add_zero] at hL
  refine ⟨_, hM, ?_, b0 x, b0 y, ?_, ?_, fun e => hne (b0_inj e), ?_⟩
  · intro p q h
    rw [Mu_apply] at h
    by_cases e1 : p = b0 x ∧ q = b0 y
    · obtain ⟨rfl, rfl⟩ := e1
      exact ⟨by show wt _ = _; rw [wt_b0, hx], by show wt _ = _; rw [wt_b0, hy]⟩
    · by_cases e2 : p = b0 y ∧ q = b0 x
      · obtain ⟨rfl, rfl⟩ := e2
        exact ⟨by show wt _ = _; rw [wt_b0, hy], by show wt _ = _; rw [wt_b0, hx]⟩
      · rw [if_neg e1, if_neg e2, sub_zero] at h; exact absurd rfl h
  · show wt _ = _; rw [wt_b0, hx]
  · show wt _ = _; rw [wt_b0, hy]
  · rw [Mu_apply, if_pos ⟨rfl, rfl⟩, if_neg (fun e => hne (b0_inj e.1))]; simp

/-- The projection step for blocks with both halves, from an explicit diagonal weight. -/
lemma step_of (hC : Claim (n + 1)) (r : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ n) :
    suT (Wt r : VP (n + 2) → Prop) ⊆ (Hf (n + 2) r : Set _) := by
  apply step1 hC r
  intro h2r
  have hu : 2 * (r - 1) ≤ n := by omega
  set u0 := topV n (r - 1) hu
  have hwu : wt u0.1 = r - 1 := wt_topV _ _ _
  have h0 : 2 * wt u0.1 + 1 ≤ n := by rw [hwu]; omega
  refine ⟨u0, h0, by omega, ?_⟩
  have hr' : r = wt u0.1 + 1 := by omega
  rw [hr']
  by_cases hBB : 2 * r ≤ n
  · set v := topV n r hBB
    have hwv : wt v.1 = r := wt_topV _ _ _
    refine cross_rel hC u0 h0 (s := wt u0.1 + 1) (a1 := b1 u0 h0) (a2 := b0 v) (b1_ne_b0 _ _ _)
      (by rw [wt_b1]) (by rw [wt_b0, hwv]; omega) ?_
    intro u h hwu'
    simp only [Pi.sub_apply, ind]
    have e1 : b0 u ≠ b1 u0 h0 := b0_ne_b1 _ _ _
    have e2 : b1 u h ≠ b0 v := b1_ne_b0 _ _ _
    have e3 : b0 u ≠ b0 v := fun e => by have := b0_inj e; rw [this] at hwu'; omega
    rw [if_neg e1, if_neg e2, if_neg e3]
    by_cases hu : u = u0
    · subst hu; simp
    · rw [if_neg (fun e => hu (b1_inj e)), if_neg hu]; ring
  · have hr2 : 2 ≤ r := by omega
    have hvv : 2 * (r - 2) ≤ n := by omega
    set v := topV n (r - 2) hvv
    have hwv : wt v.1 = r - 2 := wt_topV _ _ _
    have hv1 : 2 * wt v.1 + 1 ≤ n := by rw [hwv]; omega
    refine cross_rel hC u0 h0 (s := wt u0.1) (a1 := b1 v hv1) (a2 := b0 u0) (b1_ne_b0 _ _ _)
      (by rw [wt_b1, hwv, hwu]; omega) (by rw [wt_b0]) ?_
    intro u h hwu'
    simp only [Pi.sub_apply, ind]
    have e1 : b0 u ≠ b1 v hv1 := b0_ne_b1 _ _ _
    have e2 : b1 u h ≠ b0 u0 := b1_ne_b0 _ _ _
    have e3 : b1 u h ≠ b1 v hv1 := fun e => by have := b1_inj e; rw [this] at hwu'; omega
    rw [if_neg e1, if_neg e2, if_neg e3]
    by_cases hu : u = u0
    · subst hu; simp
    · rw [if_neg (fun e => hu (b0_inj e)), if_neg hu]; ring

/-- The `J = 0` block has no `B` half. -/
lemma step_top (hC : Claim (n + 1)) (r : ℕ) (hr : n + 2 = 2 * r) :
    suT (Wt r : VP (n + 2) → Prop) ⊆ (Hf (n + 2) r : Set _) :=
  step1 hC r (fun h => absurd h (by omega))

end Ind3

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Claim

lemma MZ_E01_diag0 (p q : VP 2) (h : p ≠ q) : MZ (exchange (0 : Fin 2) 1) p q = 0 := by
  rw [MZ_E01]
  by_contra hE
  rcases E_off (n := 0) h hE with ⟨u, hu, _, _⟩ | ⟨u, hu, _, _⟩ <;> omega

lemma MZ2_diag : MZ (exchange (0 : Fin 2) 1) = Matrix.diagonal (fun p => MZ (exchange (0 : Fin 2) 1) p p) := by
  ext p q
  rw [Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h; simp
  · rw [if_neg h, MZ_E01_diag0 p q h]

def z1 : VP 1 := topV 1 0 (by norm_num)
lemma wt_z1 : wt z1.1 = 0 := wt_topV _ _ _
lemma hz1 : 2 * wt z1.1 + 1 ≤ 1 := by rw [wt_z1]

lemma VP1_wt0 (u : VP 1) (h : wt u.1 = 0) : u = z1 := block0_small u z1 h wt_z1

lemma block1_3 (p : VP 3) (hp : wt p.1 = 1) : p = BTp z1 hz1 ∨ p = TBp z1 := by
  rcases VP_cases p with ⟨x, rfl⟩ | ⟨x, hx, rfl⟩
  · rcases VP_cases x with ⟨u, rfl⟩ | ⟨u, hu, rfl⟩
    · exfalso; rw [wt_b0, wt_b0] at hp; have := valid_two_wt u.1 u.2; omega
    · left
      rw [wt_b0, wt_b1] at hp
      have := VP1_wt0 u (by omega)
      subst this; rfl
  · rcases VP_cases x with ⟨u, rfl⟩ | ⟨u, hu, rfl⟩
    · right
      rw [wt_b1, wt_b0] at hp
      have := VP1_wt0 u (by omega)
      subst this; rfl
    · exfalso; rw [wt_b1, wt_b1] at hp; omega

lemma Ematf_00 : Ematf (n := 0) (Fin.cons 0 (Fin.cons 0 (fun i => i.elim0))) (Fin.cons 0 (Fin.cons 0 (fun i => i.elim0))) = 1 := by
  simp [Ematf]

lemma Ematf_10 : Ematf (n := 0) (Fin.cons 1 (Fin.cons 0 (fun i => i.elim0))) (Fin.cons 1 (Fin.cons 0 (fun i => i.elim0))) = -1 := by
  simp [Ematf, pc, qc, Fin.tail]

lemma claim3 (hC : Claim 2) : Claim 3 := by
  intro r
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · exact small_block block0_small
    · -- the two-dimensional block `J = 1/2`
      set g : VP 2 → ℂ := fun p => MZ (exchange (0 : Fin 2) 1) p p with hg
      have hD : Complex.I • Matrix.diagonal (g ∘ tailV) ∈ Mf 3 := by
        rw [← liftM_diag, hg, ← MZ2_diag]
        have := liftM_mem (iE01_mem (n := 0))
        rwa [show liftM (Complex.I • MZ (exchange (0 : Fin 2) 1))
          = Complex.I • liftM (MZ (exchange (0 : Fin 2) 1)) by ext; simp [liftM]] at this ⊢
      have hg1 : g (b1 z1 hz1) = -1 := by
        show MZ (exchange (0 : Fin 2) 1) _ _ = _
        rw [MZ_E01]; exact Ematf_10
      have hg0 : g (b0 z1) = 1 := by
        show MZ (exchange (0 : Fin 2) 1) _ _ = _
        rw [MZ_E01]; exact Ematf_00
      have hR : RelL (Hf 3 1) (BTp z1 hz1) (TBp z1) := by
        have := cross_rel_gen (n := 1) z1 hz1 g hD (t := -2) (by norm_num) (by
          intro u h hu
          rw [wt_z1] at hu
          have := VP1_wt0 u hu
          subst this
          rw [if_pos rfl, hg1, hg0]; norm_num)
        rwa [wt_z1] at this
      have hstep : suT (Wt 1 : VP 3 → Prop) ⊆ (Hf 3 1 : Set _) :=
        step1 (n := 1) hC 1 (fun _ => ⟨z1, hz1, by rw [wt_z1], hR⟩)
      apply block_of hstep
      have hL := liftM_mem (iE01_mem (n := 0))
      have hY := sub_mem (iE01_mem (n := 1)) hL
      refine ⟨_, hY, ?_, BTp z1 hz1, TBp z1, ?_, ?_, BTp_ne_TBp _ _ _, ?_⟩
      · intro p q hpq
        have hBD := Mf_BD hY (p := p) (q := q)
        by_cases hw : wt p.1 = wt q.1
        · by_cases h0 : wt p.1 = 0
          · exfalso
            have hpq' : p = q := block0_small p q h0 (hw ▸ h0)
            subst hpq'
            apply hpq
            have hp0 : p.1 = Fin.cons 0 (Fin.cons 0 (Fin.cons 0 (fun i => i.elim0))) := by
              have := block0_small p (b0 (b0 (b0 ⟨fun i => i.elim0, rfl⟩))) h0
                (by rw [wt_b0, wt_b0, wt_b0]; simp [wt])
              rw [this]; rfl
            simp only [Matrix.sub_apply, Matrix.smul_apply, MZ_E01, liftM, if_pos rfl, smul_eq_mul,
              if_true]
            rw [hp0]
            have e1 : Ematf (n := 1) (Fin.cons 0 (Fin.cons 0 (Fin.cons 0 (fun i => i.elim0))))
                (Fin.cons 0 (Fin.cons 0 (Fin.cons 0 (fun i => i.elim0)))) = 1 := by simp [Ematf]
            have e2 : (tailV p).1 = Fin.cons 0 (Fin.cons 0 (fun i => i.elim0)) := by
              simp only [tailV, hp0, Fin.tail_cons]
            rw [e1, e2, Ematf_00]; ring
          · have h1 : wt p.1 = 1 := by have := valid_two_wt p.1 p.2; omega
            exact ⟨h1, by show wt q.1 = 1; rw [← hw, h1]⟩
        · exact absurd (hBD hw) hpq
      · show wt _ = 1; rw [wt_BTp, wt_z1]
      · show wt _ = 1; rw [wt_TBp, wt_z1]
      · simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        rw [MZ_E01, Ematf_BT_TB]
        have : liftM (Complex.I • MZ (exchange (0 : Fin 2) 1)) (BTp z1 hz1) (TBp z1) = 0 := by
          simp [BTp, TBp]
        rw [this, sub_zero, wt_z1]
        exact mul_ne_zero Complex.I_ne_zero (qc_ne (by norm_num))
  · exact small_block (empty_block (by omega))

lemma claim_le2 (M : ℕ) (hM : M ≤ 2) : Claim M := by
  intro r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact small_block block0_small
  by_cases h2 : M < 2 * r
  · exact small_block (empty_block h2)
  · have hM2 : M = 2 := by omega
    have hr1 : r = 1 := by omega
    subst hM2; subst hr1
    apply small_block
    intro p q hp hq
    have key : ∀ x : VP 2, wt x.1 = 1 → x = b1 z1 hz1 := by
      intro x hx
      rcases VP_cases x with ⟨y, rfl⟩ | ⟨y, hy, rfl⟩
      · exfalso; rw [wt_b0] at hx; have := valid_two_wt y.1 y.2; omega
      · rw [wt_b1] at hx
        have := VP1_wt0 y (by omega)
        subst this; rfl
    rw [key p hp, key q hq]

lemma claim_step (N : ℕ) (hN : 2 ≤ N) (hC : Claim (N + 1)) : Claim (N + 2) := by
  have hstep : ∀ r, 1 ≤ r → suT (Wt r : VP (N + 2) → Prop) ⊆ (Hf (N + 2) r : Set _) :=
    fun r hr => step_of hC r hr hN
  -- the blocks `r = 1, 2`
  have done12 : suT (Wt 1 : VP (N + 2) → Prop) ⊆ (Mf (N + 2) : Set _) ∧
      suT (Wt 2 : VP (N + 2) → Prop) ⊆ (Mf (N + 2) : Set _) := by
    rcases Nat.lt_or_ge N 3 with hN3 | hN3
    · have hN2 : N = 2 := by omega
      subst hN2
      set t := topV 2 0 (by norm_num)
      set s := topV 2 1 (by norm_num)
      have ht : wt t.1 = 0 := wt_topV _ _ _
      have hs : wt s.1 = 1 := wt_topV _ _ _
      have h0 : 2 * wt t.1 + 1 ≤ 2 := by rw [ht]; norm_num
      have d1 : suT (Wt 1 : VP 4 → Prop) ⊆ (Mf 4 : Set _) := by
        apply block_of (hstep 1 le_rfl)
        refine seedA hC (a1 := b1 t h0) (a2 := b0 s) (b1_ne_b0 _ _ _) (by rw [wt_b1, ht])
          (by rw [wt_b0, hs]) t h0 rfl ?_
        intro u hu
        rcases hu with hu | hu
        · exact absurd hu (b0_ne_b1 _ _ _)
        · rw [b0_inj hu, hs]; norm_num
      refine ⟨d1, ?_⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := exists_two 3 1 le_rfl (by norm_num) (by decide)
      exact block_of (hstep 2 (by norm_num)) (seedT (n := 2) (r := 1) d1 hxy hx hy
        (by rw [hx]) hC)
    · obtain ⟨x1, x2, hx12, hx1, hx2⟩ := exists_two N 1 le_rfl (by omega) (by
        intro h; simp at h; omega)
      have hv1 : 2 * wt x1.1 + 1 ≤ N := by rw [hx1]; omega
      have hv2 : 2 * wt x2.1 + 1 ≤ N := by rw [hx2]; omega
      have d2 : suT (Wt 2 : VP (N + 2) → Prop) ⊆ (Mf (N + 2) : Set _) := by
        apply block_of (hstep 2 (by norm_num))
        refine seedA hC (a1 := b1 x1 hv1) (a2 := b1 x2 hv2) (fun e => hx12 (b1_inj e))
          (by rw [wt_b1, hx1]) (by rw [wt_b1, hx2]) x1 hv1 rfl ?_
        intro u hu
        rcases hu with hu | hu <;> exact absurd hu (b0_ne_b1 _ _ _)
      refine ⟨?_, d2⟩
      obtain ⟨x, y, hxy, hx, hy⟩ := exists_two (N + 1) 1 le_rfl (by omega) (by
        intro h; simp at h; omega)
      exact block_of (hstep 1 le_rfl) (seedB (n := N) (r := 1) d2 hxy hx hy hC)
  -- higher blocks
  have done_ge : ∀ k : ℕ, suT (Wt (k + 2) : VP (N + 2) → Prop) ⊆ (Mf (N + 2) : Set _) := by
    intro k
    induction k with
    | zero => exact done12.2
    | succ k ih =>
      by_cases hk : N + 2 < 2 * (k + 3)
      · exact small_block (empty_block hk)
      · obtain ⟨x, y, hxy, hx, hy⟩ := exists_two (N + 1) (k + 2) (by omega) (by omega)
          (by intro h; simp at h)
        exact block_of (hstep (k + 3) (by omega))
          (seedT (n := N) (r := k + 2) ih hxy hx hy (by rw [hx]; omega) hC)
  intro r
  rcases r with _ | _ | k
  · exact small_block block0_small
  · exact done12.1
  · exact done_ge k

theorem claim_all : ∀ M, Claim M
  | 0 => claim_le2 0 (by norm_num)
  | 1 => claim_le2 1 (by norm_num)
  | 2 => claim_le2 2 le_rfl
  | 3 => claim3 (claim_le2 2 le_rfl)
  | n + 4 => claim_step (n + 2) (by omega) (claim_all (n + 3))

end Claim

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section Trace

variable {n : ℕ}

def Fr (d k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (((j : ℝ) + 1) * ((d : ℝ) - j))

noncomputable def cfr (d k : ℕ) : ℂ := (((Real.sqrt (Fr d k))⁻¹ : ℝ) : ℂ)

lemma F_eq' (d k : ℕ) : F d k = (Fr d k : ℂ) := by simp [F, Fr]

lemma Fr_pos {d k : ℕ} (hk : k ≤ d) : 0 < Fr d k := by
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  have : (j : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le hj hk)
  positivity

lemma cfr_conj (d k : ℕ) : (starRingEnd ℂ) (cfr d k) = cfr d k := by simp [cfr]

lemma cfr_sq {d k : ℕ} (hk : k ≤ d) : cfr d k * cfr d k * F d k = 1 := by
  rw [cfr, F_eq', ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hp := Fr_pos hk
  have : (Real.sqrt (Fr d k))⁻¹ * (Real.sqrt (Fr d k))⁻¹ * Fr d k = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  rw [this, Complex.ofReal_one]

lemma cfr_ne {d k : ℕ} (hk : k ≤ d) : cfr d k ≠ 0 := by
  intro h; have := cfr_sq hk; rw [h] at this; simp at this

variable (n) in
abbrev Idx := Σ p : VP n, Fin (n - 2 * wt p.1 + 1)

variable (n) in
noncomputable def evp (a : Idx n) : E n :=
  cfr (n - 2 * wt a.1.1) a.2 • (Lop (Sm n) ^ (a.2 : ℕ)) (psi n a.1.1)

lemma psi_half (p : VP n) :
    Lop (Sz n) (psi n p.1) = (((n - 2 * wt p.1 : ℕ) : ℂ) / 2) • psi n p.1 := by
  rw [(psi_hw n p.1 p.2).1]
  have := valid_two_wt p.1 p.2
  rw [Nat.cast_sub this]; push_cast; congr 1; ring

lemma pow_psi_inner (p : VP n) {u' : E n} (hu' : Lop (Sp n) u' = 0) (k l : ℕ) :
    ⟪(Lop (Sm n) ^ k) (psi n p.1), (Lop (Sm n) ^ l) u'⟫_ℂ
      = if k = l then F (n - 2 * wt p.1) k * ⟪psi n p.1, u'⟫_ℂ else 0 :=
  ladder.inner_pow (psi_hw n p.1 p.2).2 (psi_half p) hu' l k

lemma evp_orth : Orthonormal ℂ (evp n) := by
  rw [orthonormal_iff_ite]
  rintro ⟨p, k⟩ ⟨q, l⟩
  simp only [evp, inner_smul_left, inner_smul_right, cfr_conj]
  rw [pow_psi_inner p (psi_hw n q.1 q.2).2, inner_psi _ _ _ p.2 q.2]
  by_cases hpq : p = q
  · subst hpq
    by_cases hkl : k = l
    · subst hkl
      rw [if_pos rfl, if_pos rfl, if_pos rfl, mul_one, ← mul_assoc]
      exact cfr_sq (Nat.lt_succ_iff.1 k.isLt)
    · rw [if_neg (fun e => hkl (Fin.ext e)), if_neg, mul_zero, mul_zero]
      intro e; exact hkl (eq_of_heq (Sigma.mk.inj_iff.1 e).2)
  · rw [if_neg (fun e => hpq (Subtype.ext e))]
    simp only [mul_zero, ite_self]
    rw [if_neg]
    intro e; exact hpq (Sigma.mk.inj_iff.1 e).1

lemma evp_span : ⊤ ≤ Submodule.span ℂ (Set.range (evp n)) := by
  rw [← SA_top, SA, Submodule.span_le]
  rintro _ ⟨r, k, p, rfl⟩
  set q : VP n := ⟨p.1, p.2.1⟩
  by_cases hk : k ≤ n - 2 * wt q.1
  · have : (Lop (Sm n) ^ k) (psi n p.1) = (cfr (n - 2 * wt q.1) k)⁻¹ • evp n ⟨q, ⟨k, by omega⟩⟩ := by
      simp only [evp, smul_smul]
      rw [inv_mul_cancel₀ (cfr_ne hk), one_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have h0 := ladder.M_top (psi_hw n q.1 q.2).2 (psi_half q)
    have : (Lop (Sm n) ^ k) (psi n p.1) = 0 := by
      obtain ⟨j, hj⟩ : ∃ j, k = j + (n - 2 * wt q.1 + 1) := ⟨k - (n - 2 * wt q.1 + 1), by omega⟩
      rw [hj, pow_add, Module.End.mul_apply]
      show (Lop (Sm n) ^ j) ((Lop (Sm n) ^ (n - 2 * wt q.1 + 1)) (psi n q.1)) = 0
      rw [h0, map_zero]
    rw [SetLike.mem_coe, this]
    exact Submodule.zero_mem _

lemma trace_eq {X : Matrix (St n) (St n) ℂ} (hX : Comm n X) :
    X.trace = ∑ p : VP n, ((n - 2 * wt p.1 + 1 : ℕ) : ℂ) * blkS X p.1 p.1 := by
  have hT : X.trace = LinearMap.trace ℂ _ (Lop X) := by
    rw [Lop, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]
  rw [hT, LinearMap.trace_eq_sum_inner _ (OrthonormalBasis.mk evp_orth evp_span),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hpow : ∀ (k : ℕ) (v : E n), Lop X ((Lop (Sm n) ^ k) v) = (Lop (Sm n) ^ k) (Lop X v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, Comm.lop hX.2.1, ih, Module.End.mul_apply]
  have hterm : ∀ k : Fin (n - 2 * wt p.1 + 1),
      ⟪(OrthonormalBasis.mk evp_orth evp_span) ⟨p, k⟩,
        Lop X ((OrthonormalBasis.mk evp_orth evp_span) ⟨p, k⟩)⟫_ℂ = blkS X p.1 p.1 := by
    intro k
    rw [OrthonormalBasis.coe_mk]
    simp only [evp, map_smul, inner_smul_left, inner_smul_right, cfr_conj, hpow]
    rw [pow_psi_inner p (hX.hw (psi_hw n p.1 p.2)).2, if_pos rfl, ← mul_assoc, ← mul_assoc,
      cfr_sq (Nat.lt_succ_iff.1 k.isLt), one_mul]
    rfl
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Trace

end BaconThesis.Collective.Sol921

namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section Final

variable {n : ℕ}

local notation "EC" => BaconThesis.ExchangeUniv.collS

lemma EC_eq (α : Fin 3) : EC n α = coll n ((1 / 2 : ℂ) • BaconThesis.ExchangeUniv.pauli α) := by
  rw [BaconThesis.ExchangeUniv.collS, coll, Finset.smul_sum]
  simp only [onQubit_smul]

lemma Sp_EC : Sp n = EC n 0 + Complex.I • EC n 1 := by
  rw [EC_eq, EC_eq, ← coll_smul, ← coll_add, Sp]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sp, BaconThesis.ExchangeUniv.pauli] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num

lemma Sm_EC : Sm n = EC n 0 - Complex.I • EC n 1 := by
  rw [EC_eq, EC_eq, ← coll_smul, ← coll_sub, Sm]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sm, BaconThesis.ExchangeUniv.pauli] <;> ring_nf <;>
    simp [Complex.I_sq] <;> norm_num

lemma Sz_EC : Sz n = EC n 2 := by
  rw [EC_eq, Sz]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sz, BaconThesis.ExchangeUniv.pauli] <;> norm_num

lemma comm_of_EC {X : Matrix (St n) (St n) ℂ} (h : ∀ α : Fin 3, Commute X (EC n α)) : Comm n X := by
  have h0 := (h 0).eq
  have h1 := (h 1).eq
  have h2 := (h 2).eq
  refine ⟨?_, ?_, ?_⟩
  · rw [Sp_EC, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, h0, h1]
  · rw [Sm_EC, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, h0, h1]
  · rw [Sz_EC, h2]

lemma totalS2_eq : BaconThesis.ExchangeUniv.totalS2 n = Sm n * Sp n + Sz n + Sz n * Sz n := by
  rw [BaconThesis.ExchangeUniv.totalS2, Fin.sum_univ_three]
  have hpm := comm_pm (n := n)
  rw [Sp_EC, Sm_EC, Sz_EC] at hpm ⊢
  set A := EC n 0
  set B := EC n 1
  set C := EC n 2
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Complex.I_mul_I] at hpm ⊢
  have key : Complex.I • (A * B) - Complex.I • (B * A) = -C := by
    have : (2 : ℂ) • (Complex.I • (B * A) - Complex.I • (A * B)) = (2 : ℂ) • C := by
      rw [← hpm]; module
    have h2 := congrArg (fun M => (1 / 2 : ℂ) • M) this
    simp only [smul_smul] at h2
    norm_num at h2
    rw [← h2]; module
  rw [smul_sub, smul_smul, Complex.I_mul_I]
  linear_combination (norm := module) (-1 : ℂ) • key

lemma totalS2_star : (BaconThesis.ExchangeUniv.totalS2 n)ᴴ = BaconThesis.ExchangeUniv.totalS2 n := by
  have hp : (Sp n)ᴴ = Sm n := by rw [← Sm_star, conjTranspose_conjTranspose]
  rw [totalS2_eq, conjTranspose_add, conjTranspose_add, conjTranspose_mul, conjTranspose_mul,
    hp, Sm_star, Sz_star]

lemma totalS2_psi (p : VP n) :
    Lop (BaconThesis.ExchangeUniv.totalS2 n) (psi n p.1)
      = (((n : ℂ) / 2 - wt p.1) * ((n : ℂ) / 2 - wt p.1 + 1)) • psi n p.1 := by
  have hw := psi_hw n p.1 p.2
  rw [totalS2_eq, Lop, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ← Lop, ← Lop,
    ← Lop, ← Lop_comp, ← Lop_comp, hw.2, map_zero, hw.1, map_smul, hw.1, smul_smul, zero_add,
    ← add_smul]
  congr 1; ring

lemma orth_dfs {r : ℕ} (hr : 2 * r ≤ n) (p : VP n) (hp : wt p.1 ≠ r) (w : St n → ℂ)
    (hw : w ∈ BaconThesis.ExchangeUniv.dfsSpace n ((n : ℝ) / 2 - r)) :
    star w ⬝ᵥ (psi n p.1).ofLp = 0 := by
  set W : E n := WithLp.toLp 2 w
  set J : ℝ := (n : ℝ) / 2 - r
  have hW : Lop (BaconThesis.ExchangeUniv.totalS2 n) W = (((J * (J + 1) : ℝ)) : ℂ) • W := by
    have := hw
    simp only [BaconThesis.ExchangeUniv.dfsSpace, Set.mem_setOf_eq] at this
    ext x
    simp only [Lop, Matrix.toEuclideanLin_apply, PiLp.smul_apply, W]
    rw [this]; rfl
  have hadj := Lop_adj (BaconThesis.ExchangeUniv.totalS2 n) W (psi n p.1)
  rw [totalS2_star, hW, totalS2_psi, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hadj
  have hne : (((J * (J + 1) : ℝ)) : ℂ) - ((n : ℂ) / 2 - wt p.1) * ((n : ℂ) / 2 - wt p.1 + 1) ≠ 0 := by
    have h2 := valid_two_wt p.1 p.2
    have e : (((J * (J + 1) : ℝ)) : ℂ) - ((n : ℂ) / 2 - wt p.1) * ((n : ℂ) / 2 - wt p.1 + 1)
        = (((wt p.1 : ℝ) - r) * ((n : ℝ) - r - wt p.1 + 1) : ℝ) := by
      simp only [J]; push_cast; ring
    rw [e, Complex.ofReal_ne_zero]
    apply mul_ne_zero
    · intro h; apply hp; exact_mod_cast (sub_eq_zero.1 h)
    · have : (r : ℝ) + wt p.1 ≤ n := by
        have h1 : (2 * r : ℝ) ≤ n := by exact_mod_cast hr
        have h2' : (2 * wt p.1 : ℝ) ≤ n := by exact_mod_cast h2
        linarith
      linarith
  have hz : ⟪W, psi n p.1⟫_ℂ = 0 := by
    have : ((((J * (J + 1) : ℝ)) : ℂ) - ((n : ℂ) / 2 - wt p.1) * ((n : ℂ) / 2 - wt p.1 + 1))
        * ⟪W, psi n p.1⟫_ℂ = 0 := by rw [sub_mul, hadj, sub_self]
    exact (mul_eq_zero.1 this).resolve_left hne
  rw [PiLp.inner_apply] at hz
  rw [dotProduct]
  rw [← hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.inner_apply, W, Pi.star_apply, starRingEnd_apply]
  ring

theorem main {r : ℕ} (hr : 2 * r ≤ n) (X : Matrix (St n) (St n) ℂ)
    (hX : X ∈ BaconThesis.ExchangeUniv.suOn (BaconThesis.ExchangeUniv.dfsSpace n ((n : ℝ) / 2 - r)))
    (hcomm : ∀ α : Fin 3, Commute X (EC n α)) : X ∈ BaconThesis.ExchangeUniv.exchangeLie n := by
  have hC := comm_of_EC hcomm
  obtain ⟨hXa, hXt, hXk⟩ := hX
  have hzero : ∀ (x : St n) (q : VP n), wt q.1 ≠ r → blkS X x q.1 = 0 := by
    intro x q hq
    have h := hXk (psi n q.1).ofLp (fun w hw => orth_dfs hr q hq w hw)
    have : Lop X (psi n q.1) = 0 := by
      ext y; simp [Lop, Matrix.toEuclideanLin_apply, h]
    rw [blkS, this, inner_zero_right]
  have hzero' : ∀ p q : VP n, (wt p.1 ≠ r ∨ wt q.1 ≠ r) → MZ X p q = 0 := by
    intro p q h
    by_cases hq : wt q.1 = r
    · have hp : wt p.1 ≠ r := h.resolve_right (not_not.2 hq)
      exact MZ_wt hC (by rw [hq]; exact hp)
    · exact hzero p.1 q hq
  have hmem : MZ X ∈ suT (Wt r : VP n → Prop) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← MZ_star, hXa, ← neg_one_smul ℂ X, MZ_smul, neg_one_smul]
    · intro p q h
      by_contra hc
      apply h
      apply hzero'
      by_contra hc'
      push Not at hc'
      exact hc hc'
    · have htr := trace_eq hC
      rw [hXt] at htr
      have e : ∑ p : VP n, ((n - 2 * wt p.1 + 1 : ℕ) : ℂ) * blkS X p.1 p.1
          = ((n - 2 * r + 1 : ℕ) : ℂ) * ∑ p : VP n, MZ X p p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hp : wt p.1 = r
        · rw [hp]; rfl
        · have h0 : MZ X p p = 0 := hzero' p p (Or.inl hp)
          have h0' : blkS X p.1 p.1 = 0 := h0
          rw [h0, h0', mul_zero, mul_zero]
      rw [e] at htr
      have hne : ((n - 2 * r + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n - 2 * r)
      exact ((mul_eq_zero.1 htr.symm).resolve_left hne)
  obtain ⟨Z, hZ, hZX⟩ := claim_all n r hmem
  have : Z = X := comm_ext (exchangeLie_comm hZ) hC (fun x y hx hy => by
    have := congrFun (congrFun hZX ⟨x, hx⟩) ⟨y, hy⟩
    exact this)
  rw [← this]; exact hZ

end Final

end BaconThesis.Collective.Sol921




namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

section ExF

variable {n : ℕ}

lemma onQubit_one (i : Fin n) : onQubit i (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext x y
  simp only [onQubit, Matrix.one_apply]
  by_cases h : ∀ k, k ≠ i → x k = y k
  · rw [if_pos h]
    by_cases hi : x i = y i
    · have e : x = y := funext fun k => by
        by_cases hk : k = i
        · rw [hk]; exact hi
        · exact h k hk
      rw [if_pos hi, if_pos e]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]))]
  · rw [if_neg h, if_neg (fun e => h (fun k _ => by rw [e]))]

/-- `Σ_β σ_β ⊗ σ_β = 2 SWAP - I` on qubits `i ≠ j`. -/
lemma pauli_swap (P : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P = ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]])
    (i j : Fin n) (hij : i ≠ j) :
    ∑ β : Fin 3, onQubit i (P β) * onQubit j (P β) = (2 : ℂ) • exchange i j - 1 := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [onQubit_mul_ne i j hij]
  have key : ∀ a b c d : Fin 2, ∑ β : Fin 3, P β a c * P β b d
      = 2 * (if a = d ∧ b = c then 1 else 0) - (if a = c ∧ b = d then 1 else 0) := by
    subst hP
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp [Fin.sum_univ_three] <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, exchange]
  by_cases h : ∀ k, k ≠ i → k ≠ j → x k = y k
  · simp only [if_pos h]
    rw [key]
    have e1 : (x = y ∘ Equiv.swap i j) ↔ (x i = y j ∧ x j = y i) := by
      constructor
      · intro e; rw [e]; simp
      · rintro ⟨h1, h2⟩
        funext k
        by_cases hki : k = i
        · subst hki; simp [h1]
        · by_cases hkj : k = j
          · subst hkj; simp [h2]
          · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, h k hki hkj]
    have e2 : (x = y) ↔ (x i = y i ∧ x j = y j) := by
      constructor
      · intro e; rw [e]; simp
      · rintro ⟨h1, h2⟩
        funext k
        by_cases hki : k = i
        · subst hki; exact h1
        · by_cases hkj : k = j
          · subst hkj; exact h2
          · exact h k hki hkj
    by_cases a1 : x i = y j ∧ x j = y i <;> by_cases a2 : x i = y i ∧ x j = y j <;>
      simp [e1, e2, a1, a2, smul_eq_mul]
  · have e1 : ¬(x = y ∘ Equiv.swap i j) := by
      intro e; apply h; intro k hki hkj; rw [e]; simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
    have e2 : ¬(x = y) := by intro e; apply h; intro k _ _; rw [e]
    simp [h, e1, e2]

lemma exchange_symm (i j : Fin n) : exchange i j = exchange j i := by
  unfold exchange; rw [Equiv.swap_comm]

lemma sq_sum (P : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ)
    (hP : P = ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]) :
    ∑ α : Fin 3, ((1 / 2 : ℂ) • ∑ i : Fin n, onQubit i (P α)) * ((1 / 2 : ℂ) • ∑ i : Fin n, onQubit i (P α))
      = ((n : ℂ) * (1 - (n : ℂ) / 4)) • (1 : Matrix (St n) (St n) ℂ)
        + (1 / 2 : ℂ) • ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, exchange i j := by
  have hsq : ∀ α, P α * P α = 1 := by
    subst hP; intro α
    fin_cases α <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  set T : Fin 3 → Fin n → Matrix (St n) (St n) ℂ :=
    fun α i => ∑ j ∈ Finset.univ.erase i, onQubit i (P α) * onQubit j (P α) with hT
  have expand : ∀ α, ((1 / 2 : ℂ) • ∑ i : Fin n, onQubit i (P α)) * ((1 / 2 : ℂ) • ∑ i : Fin n, onQubit i (P α))
      = (1 / 4 : ℂ) • ∑ i : Fin n, (1 + T α i) := by
    intro α
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Finset.sum_mul_sum]
    congr 1
    · norm_num
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), onQubit_mul_same, hsq, onQubit_one]
  have h2 : ∀ i : Fin n, ∑ α : Fin 3, T α i
      = ∑ j ∈ Finset.univ.erase i, ((2 : ℂ) • exchange i j - 1) := by
    intro i
    simp only [hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    exact pauli_swap P hP i j (Finset.ne_of_mem_erase hj).symm
  have hsum : ∑ α : Fin 3, ∑ i : Fin n, (1 + T α i)
      = ((3 * n : ℕ) : ℂ) • (1 : Matrix (St n) (St n) ℂ)
        + ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, ((2 : ℂ) • exchange i j - 1) := by
    rw [Finset.sum_comm]
    simp only [Finset.sum_add_distrib, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [smul_smul, Nat.cast_smul_eq_nsmul, Nat.mul_comm]
  simp only [expand]
  rw [← Finset.smul_sum, hsum]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum]
  rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.cast_sub (by omega)]
    push_cast
    module

lemma EU_totalS2 :
    BaconThesis.ExchangeUniv.totalS2 n
      = ((n : ℂ) * (1 - (n : ℂ) / 4)) • (1 : Matrix (St n) (St n) ℂ)
        + (1 / 2 : ℂ) • ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, exchange i j := by
  rw [BaconThesis.ExchangeUniv.totalS2]
  exact sq_sum _ rfl

end ExF

end BaconThesis.Collective.Sol921



namespace BaconThesis.Collective.Sol921

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective

attribute [local instance 100] LieRing.ofAssociativeRing

section N3

lemma C8 (n : ℕ) :
    BaconThesis.Collective.totalS2 n =
      ((n : ℂ) * (1 - (n : ℂ) / 4)) • (1 : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) +
        (1 / 2 : ℂ) • ∑ i : Fin n, ∑ j ∈ Finset.univ.erase i, exchange i j := by
  rw [← sq_sum ![BBPSSW.Distill.pauli .x, BBPSSW.Distill.pauli .y, BBPSSW.Distill.pauli .z]
    (by ext k : 1; fin_cases k <;> rfl), BaconThesis.Collective.totalS2, Fin.sum_univ_three]
  simp only [collS, ← Finset.smul_sum, pow_two]
  rfl

lemma comm_totalS2_3 : Comm 3 (BaconThesis.ExchangeUniv.totalS2 3) := by
  rw [EU_totalS2]
  have hE : ∀ i j : Fin 3, Comm 3 (exchange i j) := comm_exchange
  have h1 : Comm 3 (1 : Matrix (St 3) (St 3) ℂ) := ⟨by simp, by simp, by simp⟩
  have hadd : ∀ A B : Matrix (St 3) (St 3) ℂ, Comm 3 A → Comm 3 B → Comm 3 (A + B) :=
    fun A B hA hB => (commLie 3).add_mem hA hB
  have hsm : ∀ (c : ℂ) (A : Matrix (St 3) (St 3) ℂ), Comm 3 A → Comm 3 (c • A) := by
    intro c A hA
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Matrix.smul_mul, Matrix.mul_smul]
    · rw [hA.1]
    · rw [hA.2.1]
    · rw [hA.2.2]
  have hsum : ∀ (s : Finset (Fin 3)) (f : Fin 3 → Matrix (St 3) (St 3) ℂ),
      (∀ i, Comm 3 (f i)) → Comm 3 (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; exact (commLie 3).zero_mem
    | insert a s ha ih => rw [Finset.sum_insert ha]; exact hadd _ _ (hf a) ih
  exact hadd _ _ (hsm _ _ h1) (hsm _ _ (hsum _ _ fun i => hsum _ _ fun j => hE i j))

/-- On three qubits `S²` only takes the values `15/4` and `3/4`. -/
lemma S2_poly3 : (BaconThesis.ExchangeUniv.totalS2 3 - (15 / 4 : ℂ) • 1) *
    (BaconThesis.ExchangeUniv.totalS2 3 - (3 / 4 : ℂ) • 1) = 0 := by
  have hS := comm_totalS2_3
  have h1 : Comm 3 (1 : Matrix (St 3) (St 3) ℂ) := ⟨by simp, by simp, by simp⟩
  have hc : ∀ c : ℂ, Comm 3 (BaconThesis.ExchangeUniv.totalS2 3 - c • 1) := by
    intro c
    have := (commLie 3).sub_mem hS ((commLie 3).smul_mem (1 : ℝ) h1)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    · rw [hS.1]
    · rw [hS.2.1]
    · rw [hS.2.2]
  have hP : Comm 3 ((BaconThesis.ExchangeUniv.totalS2 3 - (15 / 4 : ℂ) • 1) *
      (BaconThesis.ExchangeUniv.totalS2 3 - (3 / 4 : ℂ) • 1)) := by
    have := (commLie 3).lie_mem (hc (15 / 4)) (hc (3 / 4))
    refine ⟨?_, ?_, ?_⟩
    · rw [Matrix.mul_assoc, (hc _).1, ← Matrix.mul_assoc, (hc _).1, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, (hc _).2.1, ← Matrix.mul_assoc, (hc _).2.1, Matrix.mul_assoc]
    · rw [Matrix.mul_assoc, (hc _).2.2, ← Matrix.mul_assoc, (hc _).2.2, Matrix.mul_assoc]
  have h0 : Comm 3 (0 : Matrix (St 3) (St 3) ℂ) := (commLie 3).zero_mem
  refine comm_ext hP h0 (fun x y hx hy => ?_)
  rw [blkS_zero, blkS, ← Lop_comp]
  have hw := valid_two_wt y hy
  have key : ∀ c : ℂ, Lop (BaconThesis.ExchangeUniv.totalS2 3 - c • 1) (psi 3 y)
      = (((3 : ℂ) / 2 - wt y) * ((3 : ℂ) / 2 - wt y + 1) - c) • psi 3 y := by
    intro c
    rw [Lop_sub, Lop_smul, totalS2_psi (n := 3) ⟨y, hy⟩, sub_smul]
    have : Lop (1 : Matrix (St 3) (St 3) ℂ) (psi 3 y) = psi 3 y := by
      ext z; simp [Lop_apply, Matrix.one_apply]
    rw [this]
    push_cast; rfl
  rw [key, map_smul, key, smul_smul, inner_smul_right]
  have : wt y = 0 ∨ wt y = 1 := by omega
  rcases this with h | h <;> rw [h] <;> norm_num

lemma exchange_self {n : ℕ} (i : Fin n) : exchange i i = (1 : Matrix (St n) (St n) ℂ) := by
  ext x y; simp [exchange, Matrix.one_apply]

lemma S2_3 : BaconThesis.ExchangeUniv.totalS2 3
    = (3 / 4 : ℂ) • (1 : Matrix (St 3) (St 3) ℂ) + (exchange 0 1 + exchange 0 2 + exchange 1 2) := by
  rw [EU_totalS2, Fin.sum_univ_three]
  have e0 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  have e1 : (Finset.univ.erase (1 : Fin 3)) = {0, 2} := by decide
  have e2 : (Finset.univ.erase (2 : Fin 3)) = {0, 1} := by decide
  rw [e0, e1, e2, Finset.sum_pair (by decide), Finset.sum_pair (by decide),
    Finset.sum_pair (by decide), exchange_symm (1 : Fin 3) 0, exchange_symm (2 : Fin 3) 0,
    exchange_symm (2 : Fin 3) 1]
  push_cast
  module

open scoped ComplexOrder in
theorem n3_part1 :
    ∃ X ∈ BaconThesis.ExchangeUniv.exchangeLie 3,
      (∀ v ∈ BaconThesis.ExchangeUniv.dfsSpace 3 (3 / 2), X *ᵥ v = Complex.I • v) ∧
      (∀ v : (Fin 3 → Fin 2) → ℂ,
        (∀ w ∈ BaconThesis.ExchangeUniv.dfsSpace 3 (3 / 2), star w ⬝ᵥ v = 0) → X *ᵥ v = 0) := by
  obtain ⟨S, hSd⟩ : ∃ S, S = BaconThesis.ExchangeUniv.totalS2 3 := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : Matrix (St 3) (St 3) ℂ, A = S - (3 / 4 : ℂ) • 1 := ⟨_, rfl⟩
  have hAE : A = exchange 0 1 + exchange 0 2 + exchange 1 2 := by rw [hA, hSd, S2_3]; abel
  have hgen : ∀ i j : Fin 3, i ≠ j →
      Complex.I • exchange i j ∈ BaconThesis.ExchangeUniv.exchangeLie 3 :=
    fun i j h => LieSubalgebra.subset_lieSpan ⟨i, j, h, rfl⟩
  have hX : (1 / 3 : ℝ) • (Complex.I • exchange (0 : Fin 3) 1 + Complex.I • exchange 0 2
      + Complex.I • exchange 1 2) = (Complex.I / 3) • A := by
    rw [hAE, show ((1 / 3 : ℝ)) • (Complex.I • exchange (0 : Fin 3) 1 + Complex.I • exchange 0 2
      + Complex.I • exchange 1 2) = ((1 / 3 : ℝ) : ℂ) • (Complex.I • exchange (0 : Fin 3) 1
      + Complex.I • exchange 0 2 + Complex.I • exchange 1 2) by ext; simp; ring]
    push_cast; module
  refine ⟨(1 / 3 : ℝ) • (Complex.I • exchange 0 1 + Complex.I • exchange 0 2 + Complex.I • exchange 1 2),
    (BaconThesis.ExchangeUniv.exchangeLie 3).smul_mem _ (add_mem (add_mem (hgen 0 1 (by decide))
      (hgen 0 2 (by decide))) (hgen 1 2 (by decide))), ?_, ?_⟩
  · intro v hv
    rw [hX, Matrix.smul_mulVec, hA, Matrix.sub_mulVec]
    have hv' : S *ᵥ v = (((3 / 2 : ℝ) * (3 / 2 + 1) : ℝ) : ℂ) • v := by
      have := hv
      simp only [BaconThesis.ExchangeUniv.dfsSpace, Set.mem_setOf_eq] at this
      rw [hSd]; exact this
    rw [hv', Matrix.smul_mulVec, Matrix.one_mulVec, ← sub_smul, smul_smul]
    congr 1; push_cast; ring
  · intro v hv
    obtain ⟨w, hw⟩ : ∃ w, w = A *ᵥ v := ⟨_, rfl⟩
    have hpoly := S2_poly3
    have hSw : S *ᵥ w = (((3 / 2 : ℝ) * (3 / 2 + 1) : ℝ) : ℂ) • w := by
      have h0 : (S - (15 / 4 : ℂ) • 1) *ᵥ w = 0 := by
        rw [hw, Matrix.mulVec_mulVec, hA, hSd, hpoly, Matrix.zero_mulVec]
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
      rw [h0]; congr 1; push_cast; ring
    have hwdfs : w ∈ BaconThesis.ExchangeUniv.dfsSpace 3 (3 / 2) := by
      simp only [BaconThesis.ExchangeUniv.dfsSpace, Set.mem_setOf_eq]; rw [← hSd]; exact hSw
    have hAw : A *ᵥ w = (3 : ℂ) • w := by
      rw [hA, Matrix.sub_mulVec, hSw, Matrix.smul_mulVec, Matrix.one_mulVec, ← sub_smul]
      congr 1; push_cast; ring
    have hAh : Aᴴ = A := by
      rw [hA, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hSd, totalS2_star]
      congr 1; simp
    have hww : star w ⬝ᵥ w = 0 := by
      have e : star w ⬝ᵥ (A *ᵥ v) = star (Aᴴ *ᵥ w) ⬝ᵥ v := by
        rw [Matrix.star_mulVec, conjTranspose_conjTranspose, Matrix.dotProduct_mulVec]
      calc star w ⬝ᵥ w = star w ⬝ᵥ (A *ᵥ v) := by rw [← hw]
        _ = star (Aᴴ *ᵥ w) ⬝ᵥ v := e
        _ = 0 := by rw [hAh, hAw, star_smul, smul_dotProduct, hv w hwdfs, smul_zero]
    have hw0 : w = 0 := dotProduct_star_self_eq_zero.1 hww
    rw [hX, Matrix.smul_mulVec, ← hw, hw0, smul_zero]

end N3

end BaconThesis.Collective.Sol921



namespace BaconThesis.Collective.Sol921

open Module Matrix BaconThesis.Collective

section M835

lemma hw_eq {n : ℕ} (x : Fin n → Fin 2) : hammingWeight x = wt x := rfl

theorem eq835 (n h : ℕ) :
    Module.finrank ℂ (dfsWeak n h) = n.choose h ∧
      dfsWeak n h =
        Module.End.eigenspace (Matrix.toLin' (collS n .z)) (((n : ℂ) - 2 * (h : ℂ)) / 2) := by
  set T : Finset (St n) := Finset.univ.filter fun y => wt y = h with hT
  have hspan : dfsWeak n h = Submodule.span ℂ (Set.range fun y : T => (Pi.single (y : St n) (1 : ℂ) : St n → ℂ)) := by
    rw [dfsWeak]
    congr 1
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, Subtype.exists, hT,
      Finset.mem_filter, Finset.mem_univ, true_and, hw_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · rw [hspan, finrank_span_eq_card, Fintype.card_coe, hT, card_wt]
    have := (Pi.basisFun ℂ (St n)).linearIndependent.comp (Subtype.val : T → St n) Subtype.val_injective
    convert this using 1
    funext y; simp
  · have hz : collS n .z = Matrix.diagonal fun x => (n : ℂ) / 2 - wt x := by rw [collS_z, Sz_eq]
    apply le_antisymm
    · rw [hspan, Submodule.span_le]
      rintro _ ⟨⟨y, hy⟩, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hz]
      simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      ext x
      simp only [Matrix.mulVec_diagonal, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      split_ifs with hx
      · subst hx; rw [hy]; ring
      · simp
    · intro v hv
      rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, hz] at hv
      have hc : ∀ y, wt y ≠ h → v y = 0 := by
        intro y hy
        have := congrFun hv y
        simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
        have hne : (n : ℂ) / 2 - wt y - ((n : ℂ) - 2 * h) / 2 ≠ 0 := by
          intro e
          apply hy
          have : (wt y : ℂ) = h := by linear_combination -e
          exact_mod_cast this
        have : ((n : ℂ) / 2 - wt y - ((n : ℂ) - 2 * h) / 2) * v y = 0 := by
          rw [sub_mul, this]; ring
        exact (mul_eq_zero.1 this).resolve_left hne
      have hv' : v = ∑ y, v y • (Pi.single y (1 : ℂ) : St n → ℂ) := by
        ext x; simp [Pi.single_apply]
      rw [hv', hspan]
      refine Submodule.sum_mem _ fun y _ => ?_
      by_cases hy : wt y = h
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨y, by simp [hT, hy]⟩, rfl⟩)
      · rw [hc y hy, zero_smul]; exact Submodule.zero_mem _

end M835

end BaconThesis.Collective.Sol921

theorem solution (n h : ℕ) :
    Module.finrank ℂ (BaconThesis.Collective.dfsWeak n h) = n.choose h ∧
      BaconThesis.Collective.dfsWeak n h =
        Module.End.eigenspace (Matrix.toLin' (BaconThesis.Collective.collS n .z))
          (((n : ℂ) - 2 * (h : ℂ)) / 2) :=
  BaconThesis.Collective.Sol921.eq835 n h
