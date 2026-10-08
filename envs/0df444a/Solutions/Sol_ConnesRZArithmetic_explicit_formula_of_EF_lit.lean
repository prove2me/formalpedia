-- Prove2me | solution 1 for ConnesRZArithmetic.explicit_formula_of_EF_lit
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T14:39:35.669051+00:00
-- url     : https://prove2.me/submissions/6199ea07-1e81-42fb-a033-5f026057ab08

import Definitions.Def_ConnesRZ_weil_defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_Statement
set_option autoImplicit false
open Complex MeasureTheory Set
noncomputable section

namespace ConnesRZArithmetic

lemma connes_paperFT_dictionary (g : ℝ → ℂ) (z : ℂ) :
    Zeta23.paperFT g z = ConnesRZ.mellinHat g (1 / 2 + I * z) := by
  unfold Zeta23.paperFT ConnesRZ.mellinHat
  congr 1
  funext t
  congr 1
  congr 1
  ring

lemma connes_paperFT_at_zero (g : ℝ → ℂ) (s : ℂ) :
    Zeta23.paperFT g (Zeta23.gammaOf s) = ConnesRZ.mellinHat g s := by
  rw [connes_paperFT_dictionary]
  congr 1
  unfold Zeta23.gammaOf
  field_simp
  ring

lemma connes_arithmetic_dictionary (g : ℝ → ℂ) :
    Zeta23.EF.literatureRHS g = ConnesRZ.weilDistribution g := by
  have h0 : (1 / 2 : ℂ) + I * (I / 2) = 0 := by
    calc
      _ = (1 + I ^ 2) / 2 := by ring
      _ = 0 := by rw [I_sq]; norm_num
  have h1 : (1 / 2 : ℂ) + I * (-I / 2) = 1 := by
    calc
      _ = (1 - I ^ 2) / 2 := by ring
      _ = 1 := by rw [I_sq]; norm_num
  unfold Zeta23.EF.literatureRHS ConnesRZ.weilDistribution ConnesRZ.primeSum
  simp only [connes_paperFT_dictionary, h0, h1]
  unfold ConnesRZ.archTerm Zeta23.EF.gammaBracket Complex.digamma
  rfl


end ConnesRZArithmetic
namespace ConnesRZArithmetic

lemma paperFT_shifted_eq_mellinHat (g : ℝ → ℂ) (s : ℂ) :
    Zeta23.paperFT g ((s - 1 / 2) / I) = ConnesRZ.mellinHat g s :=
  connes_paperFT_at_zero g s

lemma paperFT_real_eq_mellinHat (g : ℝ → ℂ) (r : ℝ) :
    Zeta23.paperFT g r = ConnesRZ.mellinHat g (1 / 2 + I * r) :=
  connes_paperFT_dictionary g r

lemma paperFT_pole_zero (g : ℝ → ℂ) :
    Zeta23.paperFT g (I / 2) = ConnesRZ.mellinHat g 0 := by
  rw [connes_paperFT_dictionary]
  congr 1
  calc
    (1 / 2 : ℂ) + I * (I / 2) = (1 + I ^ 2) / 2 := by ring
    _ = 0 := by rw [I_sq]; norm_num

lemma paperFT_pole_one (g : ℝ → ℂ) :
    Zeta23.paperFT g (-I / 2) = ConnesRZ.mellinHat g 1 := by
  rw [connes_paperFT_dictionary]
  congr 1
  calc
    (1 / 2 : ℂ) + I * (-I / 2) = (1 - I ^ 2) / 2 := by ring
    _ = 1 := by rw [I_sq]; norm_num

lemma gammaBracket_eq_logDeriv (r : ℝ) :
    Zeta23.EF.gammaBracket r =
      (logDeriv Complex.Gamma (1 / 4 + I * r / 2)).re - Real.log Real.pi := rfl

lemma literature_gamma_integral_eq_archTerm (g : ℝ → ℂ) :
    (1 / (2 * Real.pi) : ℂ) *
      (∫ r : ℝ, Zeta23.paperFT g r * (Zeta23.EF.gammaBracket r : ℂ)) =
      ConnesRZ.archTerm g := by
  unfold ConnesRZ.archTerm
  simp only [paperFT_real_eq_mellinHat, gammaBracket_eq_logDeriv]

/-- The exact summand in BOTH original prime contributions. -/
def explicitPrimeSummand (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
    (g (Real.log n) + g (-Real.log n))

lemma explicitPrimeSummand_zero (g : ℝ → ℂ) : explicitPrimeSummand g 0 = 0 := by
  simp [explicitPrimeSummand]

lemma explicitPrimeSummand_one (g : ℝ → ℂ) : explicitPrimeSummand g 1 = 0 := by
  simp [explicitPrimeSummand, ArithmeticFunction.vonMangoldt_apply_one]

lemma explicitPrimeSummand_support_ge_two (g : ℝ → ℂ) :
    Function.support (explicitPrimeSummand g) ⊆ {n : ℕ | 2 ≤ n} := by
  intro n hn
  change explicitPrimeSummand g n ≠ 0 at hn
  by_contra h
  have hn2 : n < 2 := Nat.lt_of_not_ge h
  interval_cases n
  · exact hn (explicitPrimeSummand_zero g)
  · exact hn (explicitPrimeSummand_one g)

lemma literature_prime_sum_eq_primeSum (g : ℝ → ℂ) :
    (∑' n : ℕ, explicitPrimeSummand g n) = ConnesRZ.primeSum g := rfl

lemma primeSum_eq_sum_ge_one (g : ℝ → ℂ) :
    ConnesRZ.primeSum g = ∑' n : {n : ℕ // 1 ≤ n}, explicitPrimeSummand g n.1 := by
  rw [← literature_prime_sum_eq_primeSum]
  symm
  apply tsum_subtype_eq_of_support_subset
  exact (explicitPrimeSummand_support_ge_two g).trans
    (fun n hn => (show 1 ≤ n from le_trans (by decide : 1 ≤ 2) hn))

lemma primeSum_eq_sum_ge_two (g : ℝ → ℂ) :
    ConnesRZ.primeSum g = ∑' n : {n : ℕ // 2 ≤ n}, explicitPrimeSummand g n.1 := by
  rw [← literature_prime_sum_eq_primeSum]
  exact (tsum_subtype_eq_of_support_subset (explicitPrimeSummand_support_ge_two g)).symm

lemma literatureRHS_eq_weilDistribution (g : ℝ → ℂ) :
    Zeta23.EF.literatureRHS g = ConnesRZ.weilDistribution g := by
  unfold Zeta23.EF.literatureRHS ConnesRZ.weilDistribution
  rw [paperFT_pole_zero, paperFT_pole_one, literature_gamma_integral_eq_archTerm]
  rfl

/-- Both predicates specify actual Mathlib zeta zeros in the OPEN strip.
Despite its name, `IsCriticalZero` does not assume real part one half. -/
lemma zeta_zero_predicate_iff (s : ℂ) :
    Zeta23.IsNontrivialZero s ↔ ConnesRZ.IsCriticalZero s := Iff.rfl

lemma zeta_zero_mult_eq (s : ℂ) : Zeta23.zeroMult s = ConnesRZ.zeroMult s := rfl

/-- Explicit carrier equivalence; no enumeration, RH, or arbitrary ZeroConfig. -/
def zetaZeroEquiv (hs : Zeta23.ZetaSeam) :
    (Zeta23.zetaZeros hs).carrier ≃ {s : ℂ // ConnesRZ.IsCriticalZero s} where
  toFun ρ := ⟨ρ.1, (zeta_zero_predicate_iff ρ.1).mp ρ.2⟩
  invFun ρ := ⟨ρ.1, (zeta_zero_predicate_iff ρ.1).mpr ρ.2⟩
  left_inv ρ := by apply Subtype.ext; rfl
  right_inv ρ := by apply Subtype.ext; rfl

lemma zetaZeroEquiv_coe (hs : Zeta23.ZetaSeam) (ρ : (Zeta23.zetaZeros hs).carrier) :
    (zetaZeroEquiv hs ρ).1 = ρ.1 := rfl

lemma zetaZeroEquiv_mult (hs : Zeta23.ZetaSeam) (ρ : (Zeta23.zetaZeros hs).carrier) :
    (Zeta23.zetaZeros hs).mult ρ = ConnesRZ.zeroMult (zetaZeroEquiv hs ρ).1 := rfl

lemma zeta_zero_summand_transport (hs : Zeta23.ZetaSeam) (g : ℝ → ℂ)
    (ρ : (Zeta23.zetaZeros hs).carrier) :
    ((Zeta23.zetaZeros hs).mult ρ : ℂ) * Zeta23.paperFT g (Zeta23.gammaOf ρ) =
      (ConnesRZ.zeroMult (zetaZeroEquiv hs ρ).1 : ℂ) *
        ConnesRZ.mellinHat g (zetaZeroEquiv hs ρ).1 := by
  rw [connes_paperFT_at_zero]
  rfl

/-- Transport an actual-zero unordered sum along the certified carrier equivalence. -/
lemma zeta_zero_hasSum_transport (hs : Zeta23.ZetaSeam) (g : ℝ → ℂ) (a : ℂ)
    (h : HasSum (fun ρ : (Zeta23.zetaZeros hs).carrier =>
      ((Zeta23.zetaZeros hs).mult ρ : ℂ) * Zeta23.paperFT g (Zeta23.gammaOf ρ)) a) :
    HasSum (fun ρ : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (ConnesRZ.zeroMult ρ.1 : ℂ) * ConnesRZ.mellinHat g ρ.1) a := by
  apply (zetaZeroEquiv hs).hasSum_iff.mp
  simpa only [Function.comp_def, ← zeta_zero_summand_transport] using h

lemma zeta_zero_summable_transport (hs : Zeta23.ZetaSeam) (g : ℝ → ℂ)
    (h : Summable (fun ρ : (Zeta23.zetaZeros hs).carrier =>
      ((Zeta23.zetaZeros hs).mult ρ : ℂ) * Zeta23.paperFT g (Zeta23.gammaOf ρ))) :
    Summable (fun ρ : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (ConnesRZ.zeroMult ρ.1 : ℂ) * ConnesRZ.mellinHat g ρ.1) :=
  (zeta_zero_hasSum_transport hs g _ h.hasSum).summable

lemma zeta_zero_tsum_transport (hs : Zeta23.ZetaSeam) (g : ℝ → ℂ)
    (h : Summable (fun ρ : (Zeta23.zetaZeros hs).carrier =>
      ((Zeta23.zetaZeros hs).mult ρ : ℂ) * Zeta23.paperFT g (Zeta23.gammaOf ρ))) :
    (∑' ρ : (Zeta23.zetaZeros hs).carrier,
      ((Zeta23.zetaZeros hs).mult ρ : ℂ) * Zeta23.paperFT g (Zeta23.gammaOf ρ)) =
      ConnesRZ.zeroSum g :=
  (zeta_zero_hasSum_transport hs g _ h.hasSum).tsum_eq.symm

/-- A transport lemma with the PRECISE literature proposition as its input.
The unconditional theorem below discharges this input with `EF_lit_zeta`. -/
theorem explicit_formula_of_EF_lit_aux (hs : Zeta23.ZetaSeam)
    (hEF : Zeta23.EF.EF_lit (Zeta23.zetaZeros hs)) (g : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    HasSum (fun ρ : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (ConnesRZ.zeroMult ρ.1 : ℂ) * ConnesRZ.mellinHat g ρ.1)
      (ConnesRZ.weilDistribution g) := by
  obtain ⟨hsum, heq⟩ := hEF g hg hgc
  have h := zeta_zero_hasSum_transport hs g _ hsum.hasSum
  rw [heq, literatureRHS_eq_weilDistribution] at h
  exact h


end ConnesRZArithmetic
theorem solution (hs : Zeta23.ZetaSeam)
    (hEF : Zeta23.EF.EF_lit (Zeta23.zetaZeros hs)) (g : ℝ → ℂ)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    HasSum (fun ρ : {s : ℂ // ConnesRZ.IsCriticalZero s} =>
      (ConnesRZ.zeroMult ρ.1 : ℂ) * ConnesRZ.mellinHat g ρ.1)
      (ConnesRZ.weilDistribution g) := ConnesRZArithmetic.explicit_formula_of_EF_lit_aux hs hEF g hg hgc
