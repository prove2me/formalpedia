-- Prove2me | solution 2 for DiaconisStroock.VarDist.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T01:42:32.660708+00:00
-- url     : https://prove2.me/submissions/5516a272-83a5-4ffc-86fc-7eb4e1f03591

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing
import Definitions.Def_mm_spectral
import Theorems.Thm_MarkovMixing_harmonic_eq_const
import Theorems.Thm_MarkovMixing_spectral_representation

-- carved verbatim out of submission ff2af8d5-3a34-40c0-bd49-07293c3ed9a3, lines 639-653

section
set_option autoImplicit false
open MarkovMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem chiSquare_eq_second_moment_sub_one (μ π : V → ℝ) (hμ : IsDist μ)
    (hπ : IsDist π) (hpos : ∀ x, 0 < π x) :
    (∑ x, (μ x - π x)^2 / π x) = (∑ x, μ x ^ 2 / π x) - 1 := by
  have he (x : V) : (μ x - π x)^2 / π x = μ x ^ 2 / π x - 2 * μ x + π x := by
    field_simp [(hpos x).ne']
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hμ.2, hπ.2]
  ring

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

end

section
set_option autoImplicit false
open MarkovMixing
variable {V : Type*} [Fintype V]

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

end

section
set_option autoImplicit false
open MarkovMixing
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tvDist_le_half_abs_sum (μ π : V → ℝ) (hμ : IsDist μ) (hπ : IsDist π) :
    tvDist μ π ≤ (∑ x, |μ x - π x|) / 2 := by
  classical
  apply ciSup_le
  intro A
  have hz : ∑ x, (μ x - π x) = 0 := by
    rw [Finset.sum_sub_distrib, hμ.2, hπ.2, sub_self]
  have hsplit := Finset.sum_add_sum_compl A (fun x => μ x - π x)
  rw [hz] at hsplit
  have he : ∑ x ∈ Aᶜ, (μ x - π x) = -(∑ x ∈ A, (μ x - π x)) := by linarith
  have h1 := Finset.abs_sum_le_sum_abs (fun x => μ x - π x) A
  have h2 := Finset.abs_sum_le_sum_abs (fun x => μ x - π x) Aᶜ
  rw [he, abs_neg] at h2
  have hs := Finset.sum_add_sum_compl A (fun x => |μ x - π x|)
  rw [← Finset.sum_sub_distrib]
  linarith

theorem tvDist_nonneg (μ π : V → ℝ) : 0 ≤ tvDist μ π := by
  have h := le_ciSup (Set.finite_range (fun A : Finset V =>
    |∑ x ∈ A, μ x - ∑ x ∈ A, π x|)).bddAbove (∅ : Finset V)
  simpa only [tvDist, Finset.sum_empty, sub_self, abs_zero] using h

theorem four_tvDist_sq_le_chiSquare (μ π : V → ℝ) (hμ : IsDist μ) (hπ : IsDist π)
    (hpos : ∀ x, 0 < π x) :
    4 * tvDist μ π ^ 2 ≤ ∑ x, (μ x - π x)^2 / π x := by
  have ht := tvDist_le_half_abs_sum μ π hμ hπ
  have ht0 := tvDist_nonneg μ π
  have hsquare := pow_le_pow_left₀ ht0 ht 2
  have hc := Finset.sq_sum_div_le_sum_sq_div (Finset.univ : Finset V)
    (fun x => |μ x - π x|) (fun x _ => hpos x)
  simp only [hπ.2, div_one, sq_abs] at hc
  nlinarith

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

theorem rowDist_isDist (P : Matrix V V ℝ) (hP : IsStochastic P) (n : ℕ) (x : V) :
    IsDist (rowDist P n x) :=
  ⟨(stochastic_pow P hP n).1 x, (stochastic_pow P hP n).2 x⟩

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

theorem sum_square_div_eq_diagonal (P : Matrix V V ℝ) (π : V → ℝ)
    (hpos : ∀ x, 0 < π x) (hrev : DetailedBalance P π) (n : ℕ) (x : V) :
    (∑ y, (P^n) x y ^ 2 / π y) = (P^(2*n)) x x / π x := by
  rw [two_mul, pow_add, Matrix.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  have h := detailedBalance_pow P π hrev n x y
  field_simp [(hpos x).ne', (hpos y).ne']
  linear_combination (P^n) x y * h

theorem four_tvDist_sq_le_diagonal (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (x : V) (n : ℕ) :
    4 * tvDist (rowDist P n x) π ^ 2 ≤ (P^(2*n)) x x / π x - 1 := by
  have hpos := stationary_positive P hP hirr π hπ
  have hμ := rowDist_isDist P hP n x
  have ht := four_tvDist_sq_le_chiSquare (rowDist P n x) π hμ hπ.1 hpos
  rw [chiSquare_eq_second_moment_sub_one (rowDist P n x) π hμ hπ.1 hpos] at ht
  change 4 * tvDist (rowDist P n x) π ^ 2 ≤ (∑ y, (P^n) x y ^ 2 / π y) - 1 at ht
  rwa [sum_square_div_eq_diagonal P π hpos hrev n x] at ht

end

section
set_option autoImplicit false
open MarkovMixing
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

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

lemma spectral_completeness (P : Matrix V V ℝ) (π : V → ℝ)
    (lam : I → ℝ) (f : I → V → ℝ)
    (hspec : ∀ n x y, (P ^ n) x y / π y = ∑ j, f j x * f j y * lam j ^ n)
    (x y : V) : ∑ j, f j x * f j y = (if x = y then 1 else 0) / π y := by
  simpa [Matrix.one_apply] using (hspec 0 x y).symm

lemma unit_eigenfunction_constant (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : MarkovMixing.Irreducible P) (f : V → ℝ) (hf : P.mulVec f = f)
    (x y : V) : f x = f y := by
  have hh : Harmonic P f := fun z => (congrFun hf z).symm
  exact MarkovMixing.harmonic_eq_const P hP hirr f hh x y

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

end

section
set_option autoImplicit false
open MarkovMixing
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

end

section
set_option autoImplicit false
open MarkovMixing

theorem proposition_3 {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ),
      4 * tvDist (rowDist P n x) π ^ 2 ≤ (1 - π x) / π x * lambdaStar P ^ (2 * n) := by
  intro x n
  have hpos := stationary_positive P hP hirr π hπ
  exact (four_tvDist_sq_le_diagonal P hP hirr π hπ hrev x n).trans
    (spectral_diagonal_bound P hP hirr π hπ hpos hrev x n)

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    ∀ (x : V) (n : ℕ),
      4 * tvDist (rowDist P n x) π ^ 2 ≤ (1 - π x) / π x * lambdaStar P ^ (2 * n) := by
  exact proposition_3 P hP hirr π hπ hrev

end
