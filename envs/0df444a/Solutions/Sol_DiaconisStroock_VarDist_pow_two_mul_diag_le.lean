-- Prove2me | solution 1 for DiaconisStroock.VarDist.pow_two_mul_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-08T08:37:22.134222+00:00
-- url     : https://prove2.me/submissions/6e0db4cd-d06d-4adf-9bc3-dbae17a4ca70

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_mm_basic

-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE EigenBounds
section

set_option autoImplicit false

open MarkovMixing

namespace DiaconisStroock.VarDist.Proof

variable {V : Type*} [Fintype V]

lemma eigenvalue_abs_le_one (P : Matrix V V ℝ) (hP : IsStochastic P)
    (lam : ℝ) (hl : IsEigenvalue P lam) : |lam| ≤ 1 := by
  classical
  obtain ⟨f, hf, heig⟩ := hl
  have hex : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  obtain ⟨x, hx⟩ := hex
  let : Nonempty V := ⟨x⟩
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image Finset.univ (fun z => |f z|) Finset.univ_nonempty
  have hmax : ∀ z, |f z| ≤ |f a| := fun z => ha z (Finset.mem_univ _)
  have hpos : 0 < |f a| := (abs_pos.mpr hx).trans_le (hmax x)
  have he : ∑ y, P a y * f y = lam * f a := congrFun heig a
  have hb : |lam| * |f a| ≤ 1 * |f a| := by
    calc
      |lam| * |f a| = |∑ y, P a y * f y| := by rw [he, abs_mul]
      _ ≤ ∑ y, |P a y * f y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ y, P a y * |f y| := by
        apply Finset.sum_congr rfl
        intro y _
        rw [abs_mul, abs_of_nonneg (hP.1 a y)]
      _ ≤ ∑ y, P a y * |f a| := Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hmax y) (hP.1 a y))
      _ = 1 * |f a| := by rw [← Finset.sum_mul, hP.2 a]
  exact (mul_le_mul_iff_of_pos_right hpos).mp hb

lemma eigenvalue_abs_le_lambdaStar (P : Matrix V V ℝ) (hP : IsStochastic P)
    (lam : ℝ) (hl : IsEigenvalue P lam) (hne : lam ≠ 1) : |lam| ≤ lambdaStar P := by
  have hb : BddAbove {r : ℝ | ∃ a : ℝ, IsEigenvalue P a ∧ a ≠ 1 ∧ r = |a|} := by
    refine ⟨1, ?_⟩
    rintro r ⟨a, ha, _, rfl⟩
    exact eigenvalue_abs_le_one P hP a ha
  exact le_csSup hb ⟨lam, hl, hne, rfl⟩

lemma eigenfunction_mean_zero (P : Matrix V V ℝ) (π : V → ℝ)
    (hπ : IsStationary P π) (lam : ℝ) (f : V → ℝ)
    (heig : P.mulVec f = lam • f) (hne : lam ≠ 1) :
    ∑ x, π x * f x = 0 := by
  have hcol (y : V) : ∑ x, π x * P x y = π y := congrFun hπ.2 y
  have he (x : V) : ∑ y, P x y * f y = lam * f x := congrFun heig x
  have hm : lam * (∑ x, π x * f x) = ∑ x, π x * f x := by
    calc
      lam * (∑ x, π x * f x) = ∑ x, π x * (lam * f x) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ x, π x * ∑ y, P x y * f y := by simp_rw [he]
      _ = ∑ y, (∑ x, π x * P x y) * f y := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun x _ => by ring)
      _ = ∑ y, π y * f y := by simp_rw [hcol]
  have hz : (lam - 1) * (∑ x, π x * f x) = 0 := by nlinarith [hm]
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hne)

end DiaconisStroock.VarDist.Proof

end
-- END MODULE EigenBounds

-- Current accepted source by allychan327; receipt 8bd330a8-5d47-47c8-9c73-299b551b8d3f.
-- Historical root-body receipt differs; use current-upstream source readback.
set_option autoImplicit false

open scoped BigOperators
open MarkovMixing

theorem MarkovMixing.harmonic_eq_const {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (h : V → ℝ) (hh : Harmonic P h) (x y : V) :
    h x = h y := by
  haveI : Nonempty V := ⟨x⟩
  have hpow_nonneg : ∀ (t : ℕ) (a b : V), 0 ≤ (P ^ t) a b := by
    intro t
    induction t with
    | zero => intro a b; by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
    | succ n ih =>
        intro a b
        rw [pow_succ]
        exact Finset.sum_nonneg fun z _ => mul_nonneg (ih a z) (hP.1 z b)
  have hpow_row : ∀ (t : ℕ) (a : V), ∑ b, (P ^ t) a b = 1 := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have e : ∀ b : V, (P ^ n * P) a b = ∑ z, (P ^ n) a z * P z b := fun b => rfl
        rw [Finset.sum_congr rfl fun b _ => e b, Finset.sum_comm]
        rw [Finset.sum_congr rfl fun z _ => by rw [← Finset.mul_sum, hP.2 z, mul_one]]
        exact ih a
  have hharm_pow : ∀ (t : ℕ) (a : V), h a = ∑ b, (P ^ t) a b * h b := by
    intro t
    induction t with
    | zero => intro a; simp [Matrix.one_apply]
    | succ n ih =>
        intro a
        rw [pow_succ]
        have hmul : ∀ z : V, (P ^ n * P) a z = ∑ b, (P ^ n) a b * P b z := fun z => rfl
        rw [Finset.sum_congr rfl fun z _ => by rw [hmul z]]
        have expand : ∑ z, (∑ b, (P ^ n) a b * P b z) * h z
            = ∑ b, (P ^ n) a b * ∑ z, P b z * h z := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun z _ => by ring
        rw [expand]
        rw [ih a]
        exact Finset.sum_congr rfl fun b _ => by rw [← hh b]
  obtain ⟨x₀, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) h Finset.univ_nonempty
  have hmax' : ∀ z : V, h z ≤ h x₀ := fun z => hmax z (Finset.mem_univ z)
  have key : ∀ (t : ℕ) (z : V), 0 < (P ^ t) x₀ z → h z = h x₀ := by
    intro t z hz
    have hle : ∀ b ∈ (Finset.univ : Finset V),
        (P ^ t) x₀ b * h b ≤ (P ^ t) x₀ b * h (x₀) :=
      fun b _ => mul_le_mul_of_nonneg_left (hmax' b) (hpow_nonneg t x₀ b)
    have hEq : ∑ b, (P ^ t) x₀ b * h b = ∑ b, (P ^ t) x₀ b * h x₀ := by
      rw [← hharm_pow t x₀, ← Finset.sum_mul, hpow_row t x₀, one_mul]
    have hptw := (Finset.sum_eq_sum_iff_of_le hle).mp hEq z (Finset.mem_univ z)
    exact mul_left_cancel₀ hz.ne' hptw
  obtain ⟨t₁, ht₁⟩ := hirr x₀ x
  obtain ⟨t₂, ht₂⟩ := hirr x₀ y
  rw [key t₁ x ht₁, key t₂ y ht₂]


-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE SpectralMass
section

set_option autoImplicit false

open MarkovMixing

namespace DiaconisStroock.VarDist.Proof

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

lemma unit_eigenfunction_constant (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (f : V → ℝ) (hf : P.mulVec f = f)
    (x y : V) : f x = f y := by
  have hh : Harmonic P f := fun z => (congrFun hf z).symm
  exact MarkovMixing.harmonic_eq_const P hP hirr f hh x y

lemma spectral_completeness (P : Matrix V V ℝ) (π : V → ℝ)
    (lam : I → ℝ) (f : I → V → ℝ)
    (hspec : ∀ n x y, (P ^ n) x y / π y = ∑ j, f j x * f j y * lam j ^ n)
    (x y : V) : ∑ j, f j x * f j y = (if x = y then 1 else 0) / π y := by
  simpa [Matrix.one_apply] using (hspec 0 x y).symm

lemma unit_projection_mass (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (lam : I → ℝ) (f : I → V → ℝ)
    (heig : ∀ j, P.mulVec (f j) = lam j • f j)
    (hcomp : ∀ x y, ∑ j, f j x * f j y = (if x = y then 1 else 0) / π y)
    (x : V) : (∑ j, if lam j = 1 then (f j x)^2 else 0) = 1 := by
  classical
  have hm (j : I) : (∑ y, π y * f j y) = if lam j = 1 then f j x else 0 := by
    by_cases hj : lam j = 1
    · rw [if_pos hj]
      have hfix : P.mulVec (f j) = f j := by simpa [hj] using heig j
      have hc (y : V) := unit_eigenfunction_constant P hP hirr (f j) hfix y x
      simp_rw [hc]
      rw [← Finset.sum_mul, hπ.1.2, one_mul]
    · rw [if_neg hj]
      exact eigenfunction_mean_zero P π hπ (lam j) (f j) (heig j) hj
  have hone : (∑ j, f j x * ∑ y, π y * f j y) = 1 := by
    calc
      (∑ j, f j x * ∑ y, π y * f j y)
          = ∑ y, (∑ j, f j x * f j y) * π y := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = ∑ y, ((if x = y then 1 else 0) / π y) * π y := by simp_rw [hcomp]
      _ = ∑ y : V, if x = y then (1 : ℝ) else 0 := by
        exact Finset.sum_congr rfl (fun y _ => div_mul_cancel₀ _ (hpos y).ne')
      _ = 1 := by simp
  calc
    (∑ j, if lam j = 1 then (f j x)^2 else 0) = ∑ j, f j x * ∑ y, π y * f j y := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hm]
      split_ifs <;> ring
    _ = 1 := hone

omit [Fintype V] in
lemma nonunit_projection_mass (π : V → ℝ)
    (lam : I → ℝ) (f : I → V → ℝ)
    (hcomp : ∀ x y, ∑ j, f j x * f j y = (if x = y then 1 else 0) / π y)
    (x : V) (hone : (∑ j, if lam j = 1 then (f j x)^2 else 0) = 1) :
    (∑ j, if lam j ≠ 1 then (f j x)^2 else 0) = 1 / π x - 1 := by
  classical
  have hs : (∑ j, (f j x)^2) = 1 / π x := by simpa [pow_two] using hcomp x x
  have hsplit : (∑ j, (f j x)^2) =
      (∑ j, if lam j = 1 then (f j x)^2 else 0) +
      (∑ j, if lam j ≠ 1 then (f j x)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp_all)
  linarith

end DiaconisStroock.VarDist.Proof
end
-- END MODULE SpectralMass

-- Current accepted source by chenmin; receipt ea753f3c-4ef4-4584-88bb-75aed5112d02.
-- Historical root-body receipt differs; use current-upstream source readback.
set_option autoImplicit false

open MarkovMixing
open scoped BigOperators

theorem MarkovMixing.spectral_representation {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x)
    (hrev : DetailedBalance P π) :
    ∃ (lam : Fin (Fintype.card V) → ℝ) (f : Fin (Fintype.card V) → V → ℝ),
      (∀ j, P.mulVec (f j) = lam j • f j) ∧
      (∀ j k, innerPi π (f j) (f k) = if j = k then 1 else 0) ∧
      ∀ (t : ℕ) (x y : V),
        (P ^ t) x y / π y = ∑ j, f j x * f j y * lam j ^ t := by
  classical
  set s : V → ℝ := fun x => Real.sqrt (π x) with hs_def
  have hs : ∀ x, 0 < s x := fun x => Real.sqrt_pos.mpr (hpos x)
  have hs2 : ∀ x, s x * s x = π x := fun x => Real.mul_self_sqrt (hpos x).le
  -- the symmetrized matrix
  set A : Matrix V V ℝ := Matrix.of (fun x y => s x * P x y / s y) with hA_def
  have hAxy : ∀ x y, A x y = s x * P x y / s y := fun _ _ => rfl
  have hA : A.IsHermitian := by
    ext x y
    simp only [Matrix.conjTranspose_apply, star_trivial, hAxy]
    rw [div_eq_div_iff (hs x).ne' (hs y).ne']
    have h1 := hs2 x
    have h2 := hs2 y
    have h3 := hrev x y
    linear_combination P y x * h2 - P x y * h1 - h3
  set U : Matrix V V ℝ := (hA.eigenvectorUnitary : Matrix V V ℝ) with hU_def
  set lamV : V → ℝ := hA.eigenvalues with hlamV_def
  have hUstar : star U * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hUstar' : U * star U = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  have hspec : A = U * Matrix.diagonal lamV * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    have : (RCLike.ofReal ∘ lamV) = lamV := by
      funext i; simp [RCLike.ofReal_real_eq_id]
    rw [this] at h
    simpa [hU_def, Unitary.coe_star] using h
  have hpow : ∀ t : ℕ, A ^ t = U * Matrix.diagonal (fun i => lamV i ^ t) * star U := by
    intro t
    induction t with
    | zero => simp [Matrix.diagonal_one, hUstar']
    | succ t ih =>
      rw [pow_succ, ih, hspec]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUstar, Matrix.one_mul]
      rw [← Matrix.mul_assoc (Matrix.diagonal fun i => lamV i ^ t) (Matrix.diagonal lamV),
        Matrix.diagonal_mul_diagonal]
      congr 2
  have hcol : ∀ (i x : V), ∑ y, A x y * U y i = lamV i * U x i := by
    intro i x
    have h := congrFun (hA.mulVec_eigenvectorBasis i) x
    simpa [Matrix.mulVec, dotProduct, hU_def, hlamV_def,
      Matrix.IsHermitian.eigenvectorUnitary_apply] using h
  have hApow : ∀ (t : ℕ) (x y : V), (A ^ t) x y = s x * (P ^ t) x y / s y := by
    intro t
    induction t with
    | zero =>
      intro x y
      by_cases h : x = y
      · subst h; simp [Matrix.one_apply, (hs x).ne']
      · simp [Matrix.one_apply, h]
    | succ t ih =>
      intro x y
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [ih x z, hAxy]
      have hz := (hs z).ne'
      have hy := (hs y).ne'
      field_simp
  set e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm with he_def
  refine ⟨fun j => lamV (e j), fun j x => U x (e j) / s x, ?_, ?_, ?_⟩
  · intro j
    funext x
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    have hstep : ∀ y : V, P x y * (U y (e j) / s y) = A x y * U y (e j) / s x := by
      intro y
      rw [hAxy]
      have hx := (hs x).ne'
      have hy := (hs y).ne'
      field_simp
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.univ) => hstep y), ← Finset.sum_div,
      hcol (e j) x]
    ring
  · intro j k
    have h1 : innerPi π (fun x => U x (e j) / s x) (fun x => U x (e k) / s x)
        = ∑ x, U x (e j) * U x (e k) := by
      unfold innerPi
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← hs2 x]
      have hx := (hs x).ne'
      field_simp
    have h2 : ∑ x, U x (e j) * U x (e k) = (star U * U) (e j) (e k) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.star_apply, star_trivial]
    rw [h1, h2, hUstar, Matrix.one_apply]
    simp [he_def]
  · intro t x y
    have hAt : (A ^ t) x y = ∑ i, U x i * U y i * lamV i ^ t := by
      rw [hpow t, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
      ring
    have hxy : (P ^ t) x y / π y = ((A ^ t) x y) / (s x * s y) := by
      rw [hApow t x y, ← hs2 y]
      have hx := (hs x).ne'
      have hy := (hs y).ne'
      field_simp
    rw [hxy, hAt, Finset.sum_div]
    refine (Fintype.sum_equiv e _ _ ?_).symm
    intro j
    have hx := (hs x).ne'
    have hy := (hs y).ne'
    field_simp



-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE SpectralDiagonal
section

set_option autoImplicit false

open MarkovMixing

namespace DiaconisStroock.VarDist.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma spectral_diagonal_bound (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hpos : ∀ x, 0 < π x) (hrev : DetailedBalance P π) (x : V) (n : ℕ) :
    (P ^ (2*n)) x x / π x - 1 ≤ (1 - π x) / π x * lambdaStar P ^ (2*n) := by
  classical
  obtain ⟨lam, f, heig, horth, hspec⟩ :=
    MarkovMixing.spectral_representation P hP π hπ.1 hpos hrev
  have hcomp := spectral_completeness P π lam f hspec
  have hone := unit_projection_mass P hP hirr π hπ hpos lam f heig hcomp x
  have hnon := nonunit_projection_mass π lam f hcomp x hone
  have hev (j : Fin (Fintype.card V)) : IsEigenvalue P (lam j) := by
    refine ⟨f j, ?_, heig j⟩
    intro hf
    have hh := horth j j
    rw [hf] at hh
    simp [innerPi] at hh
  have hterm (j : Fin (Fintype.card V)) :
      f j x * f j x * lam j ^ (2*n) ≤
      (if lam j = 1 then (f j x)^2 else 0) +
        (if lam j ≠ 1 then (f j x)^2 else 0) * lambdaStar P ^ (2*n) := by
    by_cases hj : lam j = 1
    · simp [hj, pow_two]
    · rw [if_neg hj, if_pos hj, zero_add]
      have hb := eigenvalue_abs_le_lambdaStar P hP (lam j) (hev j) hj
      have hp : lam j ^ (2*n) ≤ lambdaStar P ^ (2*n) :=
        (le_abs_self _).trans ((abs_pow _ _).trans_le (pow_le_pow_left₀ (abs_nonneg _) hb _))
      simpa only [pow_two] using mul_le_mul_of_nonneg_left hp (sq_nonneg (f j x))
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hone, hnon, ← hspec (2*n) x x] at hsum
  have hfrac : 1 / π x - 1 = (1 - π x) / π x := by field_simp [(hpos x).ne']
  rw [hfrac] at hsum
  linarith

end DiaconisStroock.VarDist.Proof

end
-- END MODULE SpectralDiagonal

-- SPDX-License-Identifier: Apache-2.0
-- Extracted from the accepted vardist_root proof; see source-provenance.json.
set_option autoImplicit false
-- BEGIN MODULE MarkovPowers
section

set_option autoImplicit false

namespace DiaconisStroock.VarDist.Proof

open MarkovMixing

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem stochastic_pow (P : Matrix V V ℝ) (hP : IsStochastic P) (n : ℕ) :
    IsStochastic (P^n) := by
  induction n with
  | zero =>
    constructor
    · intro x y; by_cases h : x = y <;> simp [h]
    · intro x; simp [Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ]
    constructor
    · intro x y
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih.1 x z) (hP.1 z y))
    · intro x
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hP.2, mul_one]
      exact ih.2 x

theorem stationary_pow (P : Matrix V V ℝ) (π : V → ℝ)
    (hπ : IsStationary P π) (n : ℕ) : Matrix.vecMul π (P^n) = π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]

theorem stationary_positive (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π) :
    ∀ x, 0 < π x := by
  intro x
  have he : ∃ z, 0 < π z := by
    by_contra hh
    push Not at hh
    have hz : ∀ z, π z = 0 := fun z => le_antisymm (hh z) (hπ.1.1 z)
    have h := hπ.1.2
    simp only [hz, Finset.sum_const_zero] at h
    norm_num at h
  obtain ⟨z, hz⟩ := he
  obtain ⟨n, hn⟩ := hirr z x
  have hb : π z * (P^n) z x ≤ ∑ y, π y * (P^n) y x :=
    Finset.single_le_sum (fun y _ => mul_nonneg (hπ.1.1 y) ((stochastic_pow P hP n).1 y x))
      (Finset.mem_univ z)
  have heq := congrFun (stationary_pow P π hπ n) x
  change (∑ y, π y * (P^n) y x) = π x at heq
  exact (mul_pos hz hn).trans_le (hb.trans_eq heq)

theorem detailedBalance_pow (P : Matrix V V ℝ) (π : V → ℝ)
    (hdb : DetailedBalance P π) (n : ℕ) : DetailedBalance (P^n) π := by
  induction n with
  | zero =>
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · simp [h, Ne.symm h]
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    have ht (z : V) : π x * ((P^n) x z * P z y) = (P^n) z x * (π y * P y z) := by
      calc _ = (π x * (P^n) x z) * P z y := by ring
        _ = (π z * (P^n) z x) * P z y := by rw [ih x z]
        _ = (P^n) z x * (π z * P z y) := by ring
        _ = _ := by rw [hdb z y]
    simp_rw [ht]
    have hp : P^n * P = P * P^n := (Commute.self_pow P n).eq.symm
    rw [hp, Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z _ => by ring)

end DiaconisStroock.VarDist.Proof

end
-- END MODULE MarkovPowers

-- SPDX-License-Identifier: Apache-2.0
-- Reused accepted proof modules are credited in source-provenance.json.
set_option autoImplicit false
open scoped BigOperators
open MarkovMixing DiaconisStroock.VarDist


/-- The diagonal bound in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds for
eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`P^{2n}(x, x) ≤ π(x) + β_*^{2n} (1 − π(x))`, where `β_* = lambdaStar P` is the largest modulus of
an eigenvalue different from `1`. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), (P ^ (2 * n)) x x ≤ π x + lambdaStar P ^ (2 * n) * (1 - π x) := by
  intro x n
  have hpos := DiaconisStroock.VarDist.Proof.stationary_positive P hP hirr π hπ
  have hb := DiaconisStroock.VarDist.Proof.spectral_diagonal_bound P hP hirr π hπ hpos hrev x n
  have hh : (P^(2*n)) x x / π x ≤ 1 + (1-π x)/π x * lambdaStar P^(2*n) := by linarith
  have hm := (div_le_iff₀ (hpos x)).mp hh
  calc
    (P^(2*n)) x x ≤ (1 + (1-π x)/π x * lambdaStar P^(2*n))*π x := hm
    _ = π x + lambdaStar P^(2*n)*(1-π x) := by field_simp [(hpos x).ne']



#print axioms solution

open MarkovMixing
open scoped BigOperators
namespace DiaconisStroock.VarDist

/-- The diagonal bound in the proof of Proposition 3 (Diaconis and Stroock, Geometric bounds for
eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), §1D, proof of Proposition 3, p. 42):
for an irreducible chain `P` reversible with respect to its stationary distribution `π`,
`P^{2n}(x, x) ≤ π(x) + β_*^{2n} (1 − π(x))`, where `β_* = lambdaStar P` is the largest modulus of
an eigenvalue different from `1`. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ), (P ^ (2 * n)) x x ≤ π x + lambdaStar P ^ (2 * n) * (1 - π x) := by
  exact solution P hP hirr π hπ hrev

end DiaconisStroock.VarDist

#print axioms solution
