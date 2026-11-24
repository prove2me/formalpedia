-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.semi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:10.77031+00:00
-- url     : https://prove2.me/submissions/42636882-a09a-4ddb-8c7e-015cf04e20c9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_altE_theta
import Theorems.Thm_Formalism_L2_Th1_F_LegendreModelEllipticTorsion_key
import Theorems.Thm_Formalism_L2_Th1_F_areaPos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
section Main
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
private theorem coord_lemma (z : ℂ) (hz : z ∈ L.lattice) :
    ∃ m n : ℤ, z = (m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂ := by
  obtain ⟨m, n, h⟩ := Submodule.mem_span_pair.mp hz
  exact ⟨m, n, by rw [← h]; simp [zsmul_eq_mul]⟩
private theorem exists_sign_EE_lattice_eq_det : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ a b c e : ℤ,
    EE ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂) =
      ((s * (a * e - b * c) : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (L.ω₁ * conj L.ω₂).im := ⟨_, rfl⟩
  have hA : Formalism.L2.Th1.F.area L = |t| := by
    unfold Formalism.L2.Th1.F.area
    rw [ht, show (conj L.ω₁ * L.ω₂).im = -(L.ω₁ * conj L.ω₂).im by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring, abs_neg]
  have hpos : 0 < |t| := hA ▸ Formalism.L2.Th1.F.areaPos L
  have hIm : ∀ a b c e : ℤ, (((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) *
      conj ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂)).im = ((a : ℝ) * e - b * c) * t := by
    intro a b c e
    rw [ht]
    simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.conj_re,
      Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
    ring
  have key : ∀ a b c e : ℤ, EE ((a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂) ((c : ℂ) * L.ω₁ + (e : ℂ) * L.ω₂) =
      ((a : ℝ) * e - b * c) * t / |t| := by
    intro a b c e
    simp only [Formalism.L2.Th1.F.altE, herm]
    rw [Complex.div_ofReal_im, hIm, hA]
  rcases lt_or_gt_of_ne (abs_pos.mp hpos) with hneg | hp
  · refine ⟨-1, Or.inr rfl, fun a b c e => ?_⟩
    rw [key, abs_of_neg hneg, mul_div_assoc, div_neg, div_self hneg.ne]
    push_cast
    ring
  · refine ⟨1, Or.inl rfl, fun a b c e => ?_⟩
    rw [key, abs_of_pos hp, mul_div_assoc, div_self hp.ne']
    push_cast
    ring
private theorem exists_int_EE_eq_of_mem_lattice (x : ℂ) (hx : x ∈ L.lattice) (y : ℂ) (hy : y ∈ L.lattice) :
    ∃ m : ℤ, EE x y = m := by
  obtain ⟨s, -, hs⟩ := exists_sign_EE_lattice_eq_det L
  obtain ⟨a, b, rfl⟩ := coord_lemma L x hx
  obtain ⟨c, e, rfl⟩ := coord_lemma L y hy
  exact ⟨_, hs a b c e⟩
private theorem exp_pi_I_intCast_eq_neg_one_pow (m : ℤ) :
    Complex.exp ((Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ)) = (-1 : ℂ) ^ m := by
  have h : (Real.pi : ℂ) * Complex.I * (((m : ℝ)) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul, Complex.exp_pi_mul_I]
private theorem cmTheta_one_eq :
    cmTheta 1 d = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt d / 2 : ℝ) : ℂ) * Complex.I := by
  simp only [cmTheta]
  push_cast
  ring
private theorem q1_add (x y : ℂ) :
    q1 L d (x + y) = q1 L d x + q1 L d y + 2 * EE (cmTheta 1 d * x) y - EE x y := by
  simp only [q1, Formalism.L2.Th1.F.altE, herm, cmTheta_one_eq, map_add]
  simp only [Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
end Main
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution :
    (∀ x ∈ L.lattice, ∃ m : ℤ, q1 L d x = (m : ℝ)) ∧ (∀ x ∈ L.lattice, aa L d x = 1 ∨ aa L d x = -1) ∧
    ∀ x ∈ L.lattice, ∀ y ∈ L.lattice, aa L d (x + y) = aa L d x * aa L d y *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (EE x y : ℂ)) := by
  have hint : ∀ x ∈ L.lattice, ∃ m : ℤ, q1 L d x = (m : ℝ) := by
    intro x hx
    obtain ⟨m, hm⟩ := exists_int_EE_eq_of_mem_lattice L _ (hst x hx) x hx
    exact ⟨m, (altE_theta L d x).symm.trans hm⟩
  refine ⟨hint, fun x hx => ?_, fun x hx y hy => ?_⟩
  · obtain ⟨m, hm⟩ := hint x hx
    unfold aa
    rw [hm, exp_pi_I_intCast_eq_neg_one_pow]
    rcases Int.even_or_odd m with he | ho
    · exact Or.inl he.neg_one_zpow
    · exact Or.inr ho.neg_one_zpow
  · obtain ⟨m1, hm1⟩ := exists_int_EE_eq_of_mem_lattice L _ (hst x hx) y hy
    obtain ⟨m2, hm2⟩ := exists_int_EE_eq_of_mem_lattice L x hx y hy
    unfold aa
    rw [q1_add, hm1, hm2, ← Complex.exp_add, ← Complex.exp_add,
      Complex.exp_eq_exp_iff_exists_int]
    exact ⟨m1 - m2, by push_cast; ring⟩
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
