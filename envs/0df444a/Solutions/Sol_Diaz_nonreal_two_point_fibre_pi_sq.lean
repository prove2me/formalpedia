-- Prove2me | solution 1 for Diaz.nonreal_two_point_fibre_pi_sq
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:19:20.519681+00:00
-- url     : https://prove2.me/submissions/676710c4-62f8-49a1-9531-59d2d74932b0

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation
import Theorems.Thm_Diaz_indep_of_algebraic_product
import Theorems.Thm_Diaz_diaz_2007_cor2_P1
import Theorems.Thm_DiazModulus_pi_transcendental

open ComplexConjugate
open Diaz

private noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

private theorem mem_Qbar {z : ℂ} : z ∈ Diaz.Qbar ↔ IsAlgebraic ℚ z := by
  rw [Diaz.Qbar, IntermediateField.mem_toSubfield, mem_algebraicClosure_iff]

private theorem Qbar_conj {z : ℂ} (h : z ∈ Diaz.Qbar) : conj z ∈ Diaz.Qbar := by
  rw [mem_Qbar] at h ⊢
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

private theorem Qbar_sqrt {z : ℂ} (h : z ^ 2 ∈ Diaz.Qbar) : z ∈ Diaz.Qbar := by
  rw [mem_Qbar] at h ⊢; exact h.of_pow (by norm_num)

private theorem Qbar_I : Complex.I ∈ Diaz.Qbar := by
  rw [mem_Qbar]
  have h : IsAlgebraic ℚ (Complex.I ^ 2) := by
    rw [Complex.I_sq]; exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
  exact h.of_pow (by norm_num)

/-! ## Scaffolding for the augmented logarithm space -/

private theorem one_mem_aLog {K : Subfield ℂ} (aLog : Submodule ↥K ℂ)
    (haLog : aLog = Submodule.span ↥K (insert (1 : ℂ) {l : ℂ | Complex.exp l ∈ K})) :
    (1 : ℂ) ∈ aLog := by
  rw [haLog]; exact Submodule.subset_span (Set.mem_insert _ _)

private theorem log_mem_aLog {K : Subfield ℂ} (aLog : Submodule ↥K ℂ)
    (haLog : aLog = Submodule.span ↥K (insert (1 : ℂ) {l : ℂ | Complex.exp l ∈ K}))
    {l : ℂ} (hl : Complex.exp l ∈ K) : l ∈ aLog := by
  rw [haLog]; exact Submodule.subset_span (Set.mem_insert_of_mem _ hl)

private theorem base_mem_aLog {K : Subfield ℂ} (aLog : Submodule ↥K ℂ)
    (haLog : aLog = Submodule.span ↥K (insert (1 : ℂ) {l : ℂ | Complex.exp l ∈ K}))
    {a : ℂ} (ha : a ∈ K) : a ∈ aLog := by
  have h1 := one_mem_aLog aLog haLog
  have e : (algebraMap ↥K ℂ) (⟨a, ha⟩ : K) = a := rfl
  have := Submodule.smul_mem aLog (⟨a, ha⟩ : K) h1
  rw [Algebra.smul_def, e, mul_one] at this
  exact this

private theorem base_smul_mem_aLog {K : Subfield ℂ} (aLog : Submodule ↥K ℂ)
    {a z : ℂ} (ha : a ∈ K) (hz : z ∈ aLog) : a * z ∈ aLog := by
  have e : (algebraMap ↥K ℂ) (⟨a, ha⟩ : K) = a := rfl
  have := Submodule.smul_mem aLog (⟨a, ha⟩ : K) hz
  rw [Algebra.smul_def, e] at this
  exact this


theorem solution
    (aLog : Submodule ↥Diaz.Qbar ℂ)
    (haLog : aLog = Submodule.span ↥Diaz.Qbar
        (insert (1 : ℂ) {l : ℂ | Complex.exp l ∈ Diaz.Qbar}))
    (hSSE : ∀ l₀ l₁ l₂ l₃ : ℂ, l₀ ∈ aLog → l₁ ∈ aLog → l₂ ∈ aLog → l₃ ∈ aLog →
      (∀ a b : ℂ, a ∈ Diaz.Qbar → b ∈ Diaz.Qbar → a * l₀ + b * l₁ = 0 → a = 0 ∧ b = 0) →
      (∀ a b c : ℂ, a ∈ Diaz.Qbar → b ∈ Diaz.Qbar → c ∈ Diaz.Qbar →
        a * l₀ + b * l₂ + c * l₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0) →
      ¬ (l₁ * l₂ / l₀ ∈ aLog ∧ l₁ * l₃ / l₀ ∈ aLog))
    {α u v : ℂ}
    (hα : α ∈ Diaz.Qbar) (hαim : α.im ≠ 0)
    (heu : Complex.exp u = α) (hev : Complex.exp v = α) (huv : u ≠ v)
    (hqu : u * conj u ∈ Diaz.Qbar) (hqv : v * conj v ∈ Diaz.Qbar) :
    ((Real.pi : ℂ)) ^ 2 ∉ aLog ∧
      Transcendental ℚ (Complex.exp (((Real.pi : ℂ)) ^ 2)) := by
  classical
  -- Lindemann, from the platform node `DiazModulus.pi_transcendental`
  have hpiT : Transcendental ↥Diaz.Qbar ((Real.pi : ℂ)) :=
    DiazModulus.pi_transcendental.algebraicClosure
  have hLind : Transcendental Diaz.Qbar ((Real.pi : ℂ) * Complex.I) := by
    intro hAlg
    apply hpiT
    have hI : IsAlgebraic ↥Diaz.Qbar (-Complex.I) :=
      isAlgebraic_algebraMap (⟨-Complex.I, neg_mem Qbar_I⟩ : Diaz.Qbar)
    have hmul := hAlg.mul hI
    have e : ((Real.pi : ℂ) * Complex.I) * (-Complex.I) = (Real.pi : ℂ) := by
      have hII : Complex.I * Complex.I = -1 := by simpa using Complex.I_sq
      linear_combination (-(Real.pi : ℂ)) * hII
    rwa [e] at hmul
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (hev.trans heu.symm)
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply huv
    rw [hn]
    simp
  set θ : ℝ := u.im with hθ
  set t : ℝ := θ + Real.pi * n with ht
  have hvre : v.re = u.re := by rw [hn]; simp
  have hvim : v.im = θ + 2 * Real.pi * n := by rw [hn]; simp [hθ]; ring
  have hmulconj : ∀ z : ℂ, z * conj z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj]; push_cast [Complex.normSq_apply]; ring
  have hdiff : ((4 * (n : ℝ) * (Real.pi * t) : ℝ) : ℂ) = v * conj v - u * conj u := by
    rw [hmulconj, hmulconj, hvre, hvim, ht]; push_cast; ring
  have hQ : ((4 * (n : ℝ) * (Real.pi * t) : ℝ) : ℂ) ∈ Diaz.Qbar := by
    rw [hdiff]; exact sub_mem hqv hqu
  have h4n : ((4 * n : ℤ) : ℂ) ∈ Diaz.Qbar := intCast_mem _ _
  have h4n0 : ((4 * n : ℤ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Int.cast_eq_zero]; omega
  have hpt : ((Real.pi * t : ℝ) : ℂ) ∈ Diaz.Qbar := by
    have hd := div_mem hQ h4n
    have : ((4 * (n : ℝ) * (Real.pi * t) : ℝ) : ℂ) / ((4 * n : ℤ) : ℂ)
        = ((Real.pi * t : ℝ) : ℂ) := by
      push_cast; field_simp
    rwa [this] at hd
  set ν : ℂ := (t : ℂ) * Complex.I with hνdef
  have hβeq : ((Real.pi : ℂ) * Complex.I) * ν = -(((Real.pi * t : ℝ) : ℂ)) := by
    rw [hνdef]; push_cast
    have : Complex.I * Complex.I = -1 := by
      simpa using Complex.I_sq
    linear_combination ((Real.pi : ℂ) * (t : ℂ)) * this
  have hβ : ((Real.pi : ℂ) * Complex.I) * ν ∈ Diaz.Qbar := by
    rw [hβeq]; exact neg_mem hpt
  -- t ≠ 0, else α would be real
  have ht0 : t ≠ 0 := by
    intro h
    apply hαim
    have hθval : θ = -(Real.pi * n) := by rw [ht] at h; linarith
    rw [← heu, Complex.exp_im, ← hθ, hθval]
    have : Real.sin (-(Real.pi * (n : ℝ))) = 0 := by
      rw [show -(Real.pi * (n:ℝ)) = ((-n : ℤ) : ℝ) * Real.pi by push_cast; ring]
      exact Real.sin_int_mul_pi _
    rw [this, mul_zero]
  have hβ0 : ((Real.pi : ℂ) * Complex.I) * ν ≠ 0 := by
    rw [hβeq]
    simp only [ne_eq, neg_eq_zero, Complex.ofReal_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero ht0
  -- exp ν is algebraic
  have hexpθ : Complex.exp ((θ : ℂ) * Complex.I) ∈ Diaz.Qbar := by
    apply Qbar_sqrt
    have hsq : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 2 = α / conj α := by
      rw [← Complex.exp_nat_mul]
      have huc : (2 : ℕ) * ((θ : ℂ) * Complex.I) = u - conj u := by
        rw [Complex.sub_conj, ← hθ]; push_cast; ring
      rw [huc, Complex.exp_sub, Complex.exp_conj, heu]
    rw [hsq]
    exact div_mem hα (Qbar_conj hα)
  have hexppn : Complex.exp (((Real.pi : ℂ) * (n : ℂ)) * Complex.I) ∈ Diaz.Qbar := by
    have e : ((Real.pi : ℂ) * (n : ℂ)) * Complex.I
        = (n : ℂ) * ((Real.pi : ℂ) * Complex.I) := by ring
    rw [e, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    exact zpow_mem (neg_mem (one_mem _)) n
  have hexpν : Complex.exp ν ∈ Diaz.Qbar := by
    have e : ν = (θ : ℂ) * Complex.I + ((Real.pi : ℂ) * (n : ℂ)) * Complex.I := by
      rw [hνdef, ht]; push_cast; ring
    rw [e, Complex.exp_add]
    exact mul_mem hexpθ hexppn
  have hexppiI : Complex.exp ((Real.pi : ℂ) * Complex.I) ∈ Diaz.Qbar := by
    rw [Complex.exp_pi_mul_I]; exact neg_mem (one_mem _)
  -- the independence step, from the platform node
  have hindep : ∀ A B C : ℂ, A ∈ Diaz.Qbar → B ∈ Diaz.Qbar → C ∈ Diaz.Qbar →
      A + B * ν + C * ((Real.pi : ℂ) * Complex.I) = 0 → A = 0 ∧ B = 0 ∧ C = 0 :=
    fun A B C hA hB hC h =>
      Diaz.indep_of_algebraic_product (K := Diaz.Qbar) hLind hβ hβ0 hA hB hC h
  have hpiI : ((Real.pi : ℂ) * Complex.I) ∉ Diaz.Qbar := by
    intro hmem
    have := hindep ((Real.pi : ℂ) * Complex.I) 0 (-1) hmem (zero_mem _)
      (neg_mem (one_mem _)) (by ring)
    exact absurd this.2.2 (by norm_num)
  have hνQ : ν ∉ Diaz.Qbar := by
    intro hmem
    have := hindep ν (-1) 0 hmem (neg_mem (one_mem _)) (zero_mem _) (by ring)
    exact absurd this.2.1 (by norm_num)
  have hpiImem : ((Real.pi : ℂ) * Complex.I) ∈ aLog := log_mem_aLog aLog haLog hexppiI
  have hνmem : ν ∈ aLog := log_mem_aLog aLog haLog hexpν
  have hcor := Diaz.diaz_2007_cor2_P1 aLog haLog hSSE hpiImem hpiI hνmem hνQ hpiImem hpiI hindep
  have hleft : ((Real.pi : ℂ) * Complex.I) * ν ∈ aLog := base_mem_aLog aLog haLog hβ
  have hright : ¬ (((Real.pi : ℂ) * Complex.I) * ((Real.pi : ℂ) * Complex.I) ∈ aLog) :=
    fun h => hcor ⟨hleft, h⟩
  have hsq : ((Real.pi : ℂ) * Complex.I) * ((Real.pi : ℂ) * Complex.I)
      = -((Real.pi : ℂ) ^ 2) := by
    have : Complex.I * Complex.I = -1 := by simpa using Complex.I_sq
    linear_combination ((Real.pi : ℂ) ^ 2) * this
  have hpi2 : ((Real.pi : ℂ)) ^ 2 ∉ aLog := by
    intro h
    exact hright (by rw [hsq]; exact neg_mem h)
  refine ⟨hpi2, ?_⟩
  intro halg
  apply hpi2
  refine log_mem_aLog aLog haLog ?_
  rw [mem_Qbar]
  exact halg


