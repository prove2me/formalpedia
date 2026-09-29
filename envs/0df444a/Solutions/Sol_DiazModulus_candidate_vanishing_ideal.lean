-- Prove2me | solution 1 for DiazModulus.candidate_vanishing_ideal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-12T14:19:19.966474+00:00
-- url     : https://prove2.me/submissions/45344a3e-ca68-4834-b4e9-f0af44f6fa43

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate
open DiazModulus

-- Submission bytes for `/verify` against
-- `DiazModulus.candidate_vanishing_ideal`. Top-level `theorem solution`.

namespace DiazKernel

/-!
Route B (division by a monic quadratic in one variable via `finSuccEquiv`).
Variable convention matches the target signature: `X 0` is the real part, `X 1` the
imaginary part. `finSuccEquiv` makes `X 0` the *outer* polynomial variable, so we
divide by `X² + (Y² − ρ)` rather than `Y² + (X² − ρ)`. The two arguments are
symmetric.
-/

noncomputable section

abbrev K := ↥Qbar

instance : Algebra.IsAlgebraic ℚ K where
  isAlgebraic a := by
    obtain ⟨p, hp0, hp⟩ := (mem_Qbar_iff (a := (a : ℂ))).mp a.property
    refine ⟨p, hp0, ?_⟩
    have hinj : Function.Injective (algebraMap K ℂ) := Subtype.val_injective
    exact (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective hinj).mp hp

lemma I_mem_Qbar : (I : ℂ) ∈ Qbar := by
  rw [mem_Qbar_iff]
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (1 : ℚ),
    Polynomial.X_pow_add_C_ne_zero (by norm_num : (0 : ℕ) < 2) (1 : ℚ), ?_⟩
  simp [Polynomial.aeval_add, Polynomial.aeval_X_pow, I_sq]

lemma ofReal_re_sq_add_im_sq (u : ℂ) :
    ((u.re : ℝ) : ℂ) ^ 2 + ((u.im : ℝ) : ℂ) ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  calc
    ((u.re : ℝ) : ℂ) ^ 2 + ((u.im : ℝ) : ℂ) ^ 2
        = ((u.re ^ 2 + u.im ^ 2 : ℝ) : ℂ) := by simp [ofReal_pow, ofReal_add]
    _ = (Complex.normSq u : ℂ) := by simp [Complex.normSq_apply, pow_two]
    _ = ((‖u‖ : ℝ) : ℂ) ^ 2 := by rw [Complex.normSq_eq_norm_sq, ofReal_pow]

lemma candidate_re_add_im (u : ℂ) :
    u = ((u.re : ℝ) : ℂ) + ((u.im : ℝ) : ℂ) * I :=
  (Complex.re_add_im u).symm

lemma candidate_mem_Qbar_of_re_im {u : ℂ}
    (hx : ((u.re : ℝ) : ℂ) ∈ Qbar) (hy : ((u.im : ℝ) : ℂ) ∈ Qbar) : u ∈ Qbar := by
  rw [candidate_re_add_im u]
  exact Subfield.add_mem _ hx (Subfield.mul_mem _ hy I_mem_Qbar)

/-- The real part of a candidate is transcendental over `ℚ` (hence over `Q̄`). -/
theorem candidate_re_transcendental (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ ((u.re : ℝ) : ℂ) := by
  intro hx
  obtain ⟨hu, hnorm, hexp⟩ := h
  set x : ℂ := ((u.re : ℝ) : ℂ)
  set y : ℂ := ((u.im : ℝ) : ℂ)
  have hxQ : x ∈ Qbar := mem_Qbar_iff.mpr hx
  have hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar :=
    Subfield.pow_mem _ (mem_Qbar_iff.mpr hnorm) 2
  have hy2 : y ^ 2 ∈ Qbar := by
    have : y ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 - x ^ 2 := by
      have := ofReal_re_sq_add_im_sq u
      linear_combination this
    rw [this]
    exact Subfield.sub_mem _ hρ (Subfield.pow_mem _ hxQ 2)
  have hy : IsAlgebraic ℚ y :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hy2)
  have hyQ : y ∈ Qbar := mem_Qbar_iff.mpr hy
  have huQ : u ∈ Qbar := candidate_mem_Qbar_of_re_im hxQ hyQ
  exact hHL u hu (mem_Qbar_iff.mp huQ) hexp

/-- The imaginary part of a candidate is transcendental over `ℚ`. -/
theorem candidate_im_transcendental (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    Transcendental ℚ ((u.im : ℝ) : ℂ) := by
  intro hy
  obtain ⟨hu, hnorm, hexp⟩ := h
  set x : ℂ := ((u.re : ℝ) : ℂ)
  set y : ℂ := ((u.im : ℝ) : ℂ)
  have hyQ : y ∈ Qbar := mem_Qbar_iff.mpr hy
  have hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar :=
    Subfield.pow_mem _ (mem_Qbar_iff.mpr hnorm) 2
  have hx2 : x ^ 2 ∈ Qbar := by
    have : x ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 - y ^ 2 := by
      have := ofReal_re_sq_add_im_sq u
      linear_combination this
    rw [this]
    exact Subfield.sub_mem _ hρ (Subfield.pow_mem _ hyQ 2)
  have hx : IsAlgebraic ℚ x :=
    IsAlgebraic.of_pow (n := 2) (by norm_num) (mem_Qbar_iff.mp hx2)
  have hxQ : x ∈ Qbar := mem_Qbar_iff.mpr hx
  have huQ : u ∈ Qbar := candidate_mem_Qbar_of_re_im hxQ hyQ
  exact hHL u hu (mem_Qbar_iff.mp huQ) hexp

/-- The circle polynomial `X₀² + X₁² − ρ`. -/
def circlePoly {u : ℂ} (hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 -
    MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩

def evalPt (u : ℂ) : Fin 2 → ℂ := fun i =>
  if i = 0 then ((u.re : ℝ) : ℂ) else ((u.im : ℝ) : ℂ)

lemma evalPt_zero (u : ℂ) : evalPt u 0 = ((u.re : ℝ) : ℂ) := by
  simp [evalPt]

lemma evalPt_one (u : ℂ) : evalPt u 1 = ((u.im : ℝ) : ℂ) := by
  simp [evalPt]

lemma aeval_circlePoly {u : ℂ} (hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar) :
    MvPolynomial.aeval (evalPt u) (circlePoly hρ) = 0 := by
  simp only [circlePoly, map_sub, map_add, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  rw [evalPt_zero, evalPt_one]
  have hcoe : (algebraMap K ℂ) ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩ = ((‖u‖ : ℝ) : ℂ) ^ 2 := rfl
  rw [hcoe]
  exact sub_eq_zero.mpr (ofReal_re_sq_add_im_sq u)

/-- Reverse direction: vanishing of a multiple of the circle is immediate. -/
theorem candidate_vanishing_ideal_of_dvd {u : ℂ} (hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar)
    (P : MvPolynomial (Fin 2) K) (h : circlePoly (u := u) hρ ∣ P) :
    MvPolynomial.aeval (evalPt u) P = 0 := by
  obtain ⟨Q, rfl⟩ := h
  simp [aeval_circlePoly]

lemma candidate_re_transcendental_Qbar (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    Transcendental K ((u.re : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.transcendental_iff (R := ℚ) (S := K) (A := ℂ)).mp
    (candidate_re_transcendental hHL h)

lemma candidate_im_transcendental_Qbar (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u) :
    Transcendental K ((u.im : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.transcendental_iff (R := ℚ) (S := K) (A := ℂ)).mp
    (candidate_im_transcendental hHL h)

open Polynomial

lemma sq_C_mul_X_add_C (a b : K) :
    ((C a * X + C b : K[X]) ^ 2) =
      C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b) := by
  have ha : (C a) ^ 2 = C (a * a) := by rw [pow_two, ← map_mul]
  have hb : (C b) ^ 2 = C (b * b) := by rw [pow_two, ← map_mul]
  have hab : (2 : K[X]) * (C a * C b) = C ((2 : K) * a * b) := by
    have h2 : (2 : K[X]) = C (2 : K) := (map_natCast (C : K →+* K[X]) 2).symm
    rw [h2, ← map_mul, ← map_mul]
    congr 1
    ring
  trans (C a) ^ 2 * X ^ 2 + (2 : K[X]) * (C a * C b) * X + (C b) ^ 2
  · ring
  · rw [ha, hb, hab]

/-- `ρ − X²` is not a square in `Q̄[X]` when `ρ ≠ 0`. -/
theorem not_isSquare_C_sub_X_sq {ρ : K} (hρ : (ρ : ℂ) ≠ 0) :
    ¬ IsSquare (C ρ - X ^ 2 : K[X]) := by
  rintro ⟨g, hg⟩
  have hdeg : natDegree (C ρ - X ^ 2 : K[X]) = 2 := by
    rw [show (C ρ - X ^ 2 : K[X]) = -(X ^ 2 - C ρ) by ring, natDegree_neg,
      natDegree_X_pow_sub_C]
  have hg0 : g ≠ 0 := by
    intro h0
    have := congrArg natDegree hg
    simp [h0, natDegree_zero, hdeg] at this
  have hgdeg : natDegree g = 1 := by
    have hsum : natDegree (g * g) = natDegree g + natDegree g := natDegree_mul hg0 hg0
    have : natDegree (g * g) = 2 := by rw [← hg, hdeg]
    omega
  obtain ⟨a, b, hgAB⟩ := exists_eq_X_add_C_of_natDegree_le_one (p := g) hgdeg.le
  have hpoly : C ρ - X ^ 2 = C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b) := by
    rw [hg, hgAB, ← pow_two, sq_C_mul_X_add_C]
  have ha2 : a * a = -1 := by
    have hcongr := congrArg (fun p : K[X] => coeff p 2) hpoly
    have hr : coeff (C ρ - X ^ 2 : K[X]) 2 = -1 := by simp [coeff_sub, coeff_X_pow]
    have hl : coeff (C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b)) 2 = a * a := by
      have h2' : coeff (C (a * a) * X ^ 2) 2 = a * a := by
        rw [coeff_C_mul, coeff_X_pow]; simp
      have h1' : coeff (C ((2 : K) * a * b) * X) 2 = 0 := by
        rw [coeff_C_mul, coeff_X]; simp
      have h0' : coeff (C (b * b) : K[X]) 2 = 0 := by simp [coeff_C]
      calc
        coeff (C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b)) 2
            = coeff (C (a * a) * X ^ 2) 2 + coeff (C ((2 : K) * a * b) * X) 2 +
                coeff (C (b * b)) 2 := by rw [coeff_add, coeff_add]
        _ = a * a + 0 + 0 := by rw [h2', h1', h0']
        _ = a * a := by simp
    exact hl.symm.trans (hcongr.symm.trans hr)
  have hab : (2 : K) * a * b = 0 := by
    have hcongr := congrArg (fun p : K[X] => coeff p 1) hpoly
    have hr : coeff (C ρ - X ^ 2 : K[X]) 1 = 0 := by simp [coeff_sub, coeff_X_pow]
    have hl : coeff (C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b)) 1 =
        (2 : K) * a * b := by
      have h2' : coeff (C (a * a) * X ^ 2) 1 = 0 := by
        rw [coeff_C_mul, coeff_X_pow]; simp
      have h1' : coeff (C ((2 : K) * a * b) * X) 1 = (2 : K) * a * b := by
        rw [coeff_C_mul, coeff_X]; simp
      have h0' : coeff (C (b * b) : K[X]) 1 = 0 := by simp [coeff_C]
      calc
        coeff (C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b)) 1
            = coeff (C (a * a) * X ^ 2) 1 + coeff (C ((2 : K) * a * b) * X) 1 +
                coeff (C (b * b)) 1 := by rw [coeff_add, coeff_add]
        _ = 0 + (2 : K) * a * b + 0 := by rw [h2', h1', h0']
        _ = (2 : K) * a * b := by simp
    exact hl.symm.trans (hcongr.symm.trans hr)
  have hb2 : b * b = ρ := by
    have hcongr := congrArg (fun p : K[X] => coeff p 0) hpoly
    have hr : coeff (C ρ - X ^ 2 : K[X]) 0 = ρ := by simp [coeff_sub, coeff_X_pow]
    have hl : coeff (C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b)) 0 = b * b := by
      have h2' : coeff (C (a * a) * X ^ 2) 0 = 0 := by
        rw [coeff_C_mul, coeff_X_pow]; simp
      have h1' : coeff (C ((2 : K) * a * b) * X) 0 = 0 := by
        rw [coeff_C_mul, coeff_X]; simp
      have h0' : coeff (C (b * b) : K[X]) 0 = b * b := by simp [coeff_C]
      calc
        coeff (C (a * a) * X ^ 2 + C ((2 : K) * a * b) * X + C (b * b)) 0
            = coeff (C (a * a) * X ^ 2) 0 + coeff (C ((2 : K) * a * b) * X) 0 +
                coeff (C (b * b)) 0 := by rw [coeff_add, coeff_add]
        _ = 0 + 0 + b * b := by rw [h2', h1', h0']
        _ = b * b := by simp
    exact hl.symm.trans (hcongr.symm.trans hr)
  have ha0 : a ≠ 0 := fun ha => by simp [ha] at ha2
  have hb0 : b = 0 := by
    have h2 : (2 : K) ≠ 0 := two_ne_zero
    have : a * b = 0 := by
      have h := hab
      rw [mul_assoc] at h
      exact (mul_eq_zero.mp h).resolve_left h2
    exact (mul_eq_zero.mp this).resolve_left ha0
  have hρ0 : (ρ : ℂ) = 0 := by
    have : ρ = 0 := by simp [hb0] at hb2; exact hb2.symm
    simp [this]
  exact hρ hρ0

lemma aeval_evalPt_finSuccEquiv (P : MvPolynomial (Fin 2) K) (u : ℂ) :
    MvPolynomial.aeval (evalPt u) P =
      eval₂ (MvPolynomial.aeval (R := K) (fun _ : Fin 1 => evalPt u 1)).toRingHom
        (evalPt u 0) (MvPolynomial.finSuccEquiv K 1 P) := by
  apply MvPolynomial.induction_on P
  · intro r
    rw [MvPolynomial.finSuccEquiv_apply]
    simp [MvPolynomial.eval₂Hom_C, eval₂_C, MvPolynomial.aeval_C]
  · intro p q hp hq
    simp [hp, hq]
  · intro p n hp
    rw [map_mul, map_mul, eval₂_mul, hp]
    congr 1
    rw [MvPolynomial.aeval_X]
    refine Fin.cases ?_ ?_ n
    · rw [MvPolynomial.finSuccEquiv_X_zero, eval₂_X]
    · intro j
      have hj : j = 0 := Subsingleton.elim _ _
      rw [hj, MvPolynomial.finSuccEquiv_X_succ, eval₂_C]
      simpa [evalPt] using
        (MvPolynomial.aeval_X (R := K) (fun _ : Fin 1 => evalPt u 1) (0 : Fin 1)).symm

lemma monic_circle_finSucc (ρ : K) :
    Monic (X ^ 2 + C (MvPolynomial.X (0 : Fin 1) ^ 2 - MvPolynomial.C ρ) :
      (MvPolynomial (Fin 1) K)[X]) :=
  monic_X_pow_add <| (degree_C_le).trans_lt (by exact_mod_cast (show (0 : ℕ) < 2 from by norm_num))

lemma finSuccEquiv_circlePoly {u : ℂ} (hρ : ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar) :
    MvPolynomial.finSuccEquiv K 1 (circlePoly (u := u) hρ) =
      X ^ 2 + C (MvPolynomial.X (0 : Fin 1) ^ 2 -
        MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩) := by
  unfold circlePoly
  rw [map_sub, map_add, map_pow, map_pow]
  rw [MvPolynomial.finSuccEquiv_X_zero]
  have h1 : MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) =
      C (MvPolynomial.X (0 : Fin 1)) := by
    have : (1 : Fin 2) = (0 : Fin 1).succ := rfl
    rw [this]
    exact MvPolynomial.finSuccEquiv_X_succ (R := K) (n := 1) (j := 0)
  rw [h1]
  have hC : MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩) =
      C (MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩) :=
    (MvPolynomial.finSuccEquiv K 1).commutes _
  rw [hC]
  have hpow : (C (MvPolynomial.X (0 : Fin 1)) : (MvPolynomial (Fin 1) K)[X]) ^ 2 =
      C (MvPolynomial.X (0 : Fin 1) ^ 2) :=
    (map_pow (C (R := MvPolynomial (Fin 1) K)) (MvPolynomial.X (0 : Fin 1)) 2).symm
  rw [hpow]
  trans X ^ 2 +
      (C (MvPolynomial.X (0 : Fin 1) ^ 2) - C (MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩))
  · abel
  · congr 1
    exact (map_sub (C (R := MvPolynomial (Fin 1) K)) _ _).symm

lemma eval₂_C_mul_X_add_C (σ : MvPolynomial (Fin 1) K →+* ℂ) (x : ℂ)
    (A B : MvPolynomial (Fin 1) K) :
    eval₂ σ x (C A * X + C B) = σ A * x + σ B := by
  simp [eval₂_add, eval₂_mul, eval₂_X, eval₂_C]

lemma aeval_eq_zero_of_transcendental {x : ℂ} (hx : Transcendental K x) {p : K[X]}
    (h : aeval x p = 0) : p = 0 := by
  by_contra hp
  exact hx ⟨p, hp, h⟩

lemma aeval_uniqueAlgEquiv (p : MvPolynomial (Fin 1) K) (y : ℂ) :
    aeval y (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) =
      MvPolynomial.aeval (fun _ : Fin 1 => y) p := by
  simpa [aeval_def, MvPolynomial.aeval_def] using
    (MvPolynomial.eval₂_const_uniqueAlgEquiv (f := p) (φ := algebraMap K ℂ) (a := y))

lemma mv_eq_zero_of_transcendental {y : ℂ} (hy : Transcendental K y)
    {p : MvPolynomial (Fin 1) K}
    (h : MvPolynomial.aeval (fun _ : Fin 1 => y) p = 0) : p = 0 := by
  have h' : aeval y (MvPolynomial.uniqueAlgEquiv K (Fin 1) p) = 0 := by
    rw [aeval_uniqueAlgEquiv, h]
  have hz : MvPolynomial.uniqueAlgEquiv K (Fin 1) p = 0 :=
    aeval_eq_zero_of_transcendental hy h'
  exact (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective (by simpa using hz)

lemma uniqueAlgEquiv_X_zero :
    MvPolynomial.uniqueAlgEquiv K (Fin 1) (MvPolynomial.X 0) = X := by
  simp [MvPolynomial.uniqueAlgEquiv, MvPolynomial.eval₂_X]

lemma uniqueAlgEquiv_circle_univariate (ρ : K) :
    MvPolynomial.uniqueAlgEquiv K (Fin 1)
        (MvPolynomial.C ρ - MvPolynomial.X 0 ^ 2) = C ρ - X ^ 2 := by
  rw [map_sub, map_pow, uniqueAlgEquiv_X_zero]
  congr 1
  simpa using (MvPolynomial.uniqueAlgEquiv K (Fin 1)).commutes ρ

lemma sq_mul_eq_sq_of_not_isSquare {A B f : K[X]} (hf : ¬ IsSquare f)
    (h : A ^ 2 * f = B ^ 2) : A = 0 ∧ B = 0 := by
  by_cases hA : A = 0
  · subst hA
    have hB : B ^ 2 = 0 := by simpa using h.symm
    exact ⟨rfl, sq_eq_zero_iff.mp hB⟩
  · have hdiv : A ∣ B :=
      (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 2) (by decide : (2 : ℕ) ≠ 0)).mp
        ⟨f, h.symm⟩
    obtain ⟨C, rfl⟩ := hdiv
    have hmul : A ^ 2 * f = A ^ 2 * C ^ 2 := by
      convert h using 1
      ring
    have hf' : f = C ^ 2 := mul_left_cancel₀ (pow_ne_zero 2 hA) hmul
    exact (hf ⟨C, by rw [hf', pow_two]⟩).elim

lemma candidate_norm_sq_mem {u : ℂ} (h : IsCandidate u) :
    ((‖u‖ : ℝ) : ℂ) ^ 2 ∈ Qbar :=
  Subfield.pow_mem _ (mem_Qbar_iff.mpr h.2.1) 2

lemma natDegree_modByMonic_le_one (f D : (MvPolynomial (Fin 1) K)[X])
    (hmon : Monic D) (hD2 : natDegree D = 2) :
    natDegree (f %ₘ D) ≤ 1 := by
  by_cases hr0 : f %ₘ D = 0
  · simp [hr0]
  · have hlt := degree_modByMonic_lt (R := MvPolynomial (Fin 1) K) f hmon
    have hDdeg : degree D = 2 := by
      rw [degree_eq_natDegree hmon.ne_zero, hD2]
      rfl
    have : natDegree (f %ₘ D) < 2 :=
      (natDegree_lt_iff_degree_lt hr0).2 (by rwa [hDdeg] at hlt)
    omega

set_option maxHeartbeats 800000 in
theorem candidate_vanishing_ideal_dvd (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u)
    (P : MvPolynomial (Fin 2) K)
    (hP : MvPolynomial.aeval (evalPt u) P = 0) :
    circlePoly (u := u) (candidate_norm_sq_mem h) ∣ P := by
  set hρ := candidate_norm_sq_mem h
  set ρ : K := ⟨((‖u‖ : ℝ) : ℂ) ^ 2, hρ⟩
  set D := MvPolynomial.finSuccEquiv K 1 (circlePoly (u := u) hρ)
  set f := MvPolynomial.finSuccEquiv K 1 P
  have hDeq : D = X ^ 2 + C (MvPolynomial.X (0 : Fin 1) ^ 2 - MvPolynomial.C ρ) :=
    finSuccEquiv_circlePoly (u := u) hρ
  have hmon : Monic D := by
    rw [hDeq]
    exact monic_circle_finSucc ρ
  have hD2 : natDegree D = 2 := by
    rw [hDeq]
    exact natDegree_X_pow_add_C
  have hrle := natDegree_modByMonic_le_one f D hmon hD2
  obtain ⟨A, B, hrAB⟩ := exists_eq_X_add_C_of_natDegree_le_one (p := f %ₘ D) hrle
  let σ : MvPolynomial (Fin 1) K →+* ℂ :=
    (MvPolynomial.aeval (R := K) (fun _ : Fin 1 => evalPt u 1)).toRingHom
  have hf0 : eval₂ σ (evalPt u 0) f = 0 := by
    rw [← aeval_evalPt_finSuccEquiv, hP]
  have hD0 : eval₂ σ (evalPt u 0) D = 0 := by
    rw [← aeval_evalPt_finSuccEquiv, aeval_circlePoly]
  have hr0eval : eval₂ σ (evalPt u 0) (f %ₘ D) = 0 := by
    rw [modByMonic_eq_sub_mul_div, eval₂_sub, eval₂_mul, hf0, hD0]
    ring
  have hlin : σ A * evalPt u 0 + σ B = 0 := by
    have := hr0eval
    rw [hrAB, eval₂_C_mul_X_add_C] at this
    exact this
  have hx2 : evalPt u 0 ^ 2 = (ρ : ℂ) - evalPt u 1 ^ 2 := by
    have hsum := ofReal_re_sq_add_im_sq u
    rw [evalPt_zero, evalPt_one]
    exact eq_sub_of_add_eq hsum
  have hQeval :
      MvPolynomial.aeval (fun _ : Fin 1 => evalPt u 1)
          (A ^ 2 * (MvPolynomial.C ρ - MvPolynomial.X 0 ^ 2) - B ^ 2) = 0 := by
    have hxA : σ A * evalPt u 0 = -σ B := eq_neg_iff_add_eq_zero.mpr hlin
    have hsqpt : (σ A) ^ 2 * evalPt u 0 ^ 2 = (σ B) ^ 2 := by
      have := congrArg (fun z : ℂ => z ^ 2) hxA
      simpa [mul_pow, neg_sq] using this
    have hsqpt' : (σ A) ^ 2 * ((ρ : ℂ) - evalPt u 1 ^ 2) = (σ B) ^ 2 := by
      rwa [hx2] at hsqpt
    have hexpand :
        MvPolynomial.aeval (fun _ : Fin 1 => evalPt u 1)
            (A ^ 2 * (MvPolynomial.C ρ - MvPolynomial.X 0 ^ 2) - B ^ 2) =
          (σ A) ^ 2 * (algebraMap K ℂ ρ - evalPt u 1 ^ 2) - (σ B) ^ 2 := by
      simp [σ, map_sub, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    have hcoe : algebraMap K ℂ ρ = (ρ : ℂ) := rfl
    rw [hexpand, hcoe, hsqpt', sub_self]
  have hQ : A ^ 2 * (MvPolynomial.C ρ - MvPolynomial.X 0 ^ 2) - B ^ 2 = 0 :=
    mv_eq_zero_of_transcendental (candidate_im_transcendental_Qbar hHL h) hQeval
  have hsq : A ^ 2 * (MvPolynomial.C ρ - MvPolynomial.X 0 ^ 2) = B ^ 2 :=
    sub_eq_zero.mp hQ
  have hρ0 : (ρ : ℂ) ≠ 0 := by
    have hn : ((‖u‖ : ℝ) : ℂ) ≠ 0 := by
      simpa [ofReal_eq_zero] using (norm_ne_zero_iff.mpr h.1)
    exact pow_ne_zero 2 hn
  have hAB : A = 0 ∧ B = 0 := by
    let e := MvPolynomial.uniqueAlgEquiv K (Fin 1)
    have hf : ¬ IsSquare (C ρ - X ^ 2 : K[X]) := not_isSquare_C_sub_X_sq hρ0
    have h' : (e A) ^ 2 * (C ρ - X ^ 2) = (e B) ^ 2 := by
      have hmap := congrArg e hsq
      rw [map_mul, map_pow, map_pow, uniqueAlgEquiv_circle_univariate] at hmap
      exact hmap
    have hAB' := sq_mul_eq_sq_of_not_isSquare hf h'
    exact ⟨e.injective hAB'.1, e.injective hAB'.2⟩
  have hrem : f %ₘ D = 0 := by
    rw [hrAB, hAB.1, hAB.2]
    simp
  have hDf : D ∣ f := (modByMonic_eq_zero_iff_dvd hmon).mp hrem
  exact (map_dvd_iff (MvPolynomial.finSuccEquiv K 1)).mp hDf

theorem candidate_vanishing_ideal (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u)
    (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.aeval (evalPt u) P = 0 ↔
      circlePoly (u := u) (candidate_norm_sq_mem h) ∣ P := by
  constructor
  · exact candidate_vanishing_ideal_dvd hHL h P
  · exact candidate_vanishing_ideal_of_dvd (u := u) (candidate_norm_sq_mem h) P

end

end DiazKernel

open DiazKernel

theorem solution (hHL : HermiteLindemann) {u : ℂ} (h : IsCandidate u)
    (P : MvPolynomial (Fin 2) (↥Qbar)) :
    MvPolynomial.aeval
        (fun i : Fin 2 => if i = 0 then ((u.re : ℝ) : ℂ) else ((u.im : ℝ) : ℂ)) P = 0 ↔
      (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 -
          MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2,
            Subfield.pow_mem (s := Qbar) (mem_Qbar_iff.mpr h.2.1) 2⟩) ∣ P := by
  have hpt :
      (fun i : Fin 2 => if i = 0 then ((u.re : ℝ) : ℂ) else ((u.im : ℝ) : ℂ)) = evalPt u := by
    funext i
    simp [evalPt]
  have hcirc :
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 -
          MvPolynomial.C ⟨((‖u‖ : ℝ) : ℂ) ^ 2,
            Subfield.pow_mem (s := Qbar) (mem_Qbar_iff.mpr h.2.1) 2⟩ =
        circlePoly (u := u) (candidate_norm_sq_mem h) := by
    simp [circlePoly, candidate_norm_sq_mem]
  rw [hpt, hcirc]
  exact candidate_vanishing_ideal hHL h P
