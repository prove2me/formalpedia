-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:10.001086+00:00
-- url     : https://prove2.me/submissions/70bd5b0a-e6b2-4974-8c61-c9585ff1b731

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_half_mem
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_altE_theta
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_SC_half_notMem
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
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
private theorem half_periods_not_mem_cm_lattice : ω₀ / 2 ∉ L.lattice ∧ cmTheta 1 d * ω₀ / 2 ∉ L.lattice ∧
    (ω₀ + cmTheta 1 d * ω₀) / 2 ∉ L.lattice := by
  refine ⟨half_notMem hst h0 hθ hθ', ?_, ?_⟩
  · rw [mul_div_assoc]
    exact hθ
  · intro h
    apply hθ'
    have e : (1 - cmTheta 1 d) * (ω₀ / 2) = ω₀ - (ω₀ + cmTheta 1 d * ω₀) / 2 := by ring
    rw [e]
    exact L.lattice.sub_mem h0 h
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
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
theorem _root_.solution : ∃ Q : ℤ, Odd Q ∧ q1 L d ω₀ = (Q : ℝ) := by
  obtain ⟨n1, n2, n3⟩ := half_periods_not_mem_cm_lattice hst h0 hθ hθ'
  obtain ⟨a, b, hab⟩ := coord_lemma L ω₀ h0
  obtain ⟨c, e, hce⟩ := coord_lemma L _ (hst _ h0)
  have p1 : ¬(2 ∣ a ∧ 2 ∣ b) := fun h => n1 (by rw [hab]; exact half_mem L a b h.1 h.2)
  have p2 : ¬(2 ∣ c ∧ 2 ∣ e) := fun h => n2 (by rw [hce]; exact half_mem L c e h.1 h.2)
  have p3 : ¬(2 ∣ a + c ∧ 2 ∣ b + e) := by
    intro h
    apply n3
    have eq : ω₀ + cmTheta 1 d * ω₀ = (((a + c : ℤ)) : ℂ) * L.ω₁ + ((b + e : ℤ) : ℂ) * L.ω₂ := by
      rw [hce]
      rw [hab]
      push_cast
      ring
    rw [eq]
    exact half_mem L _ _ h.1 h.2
  obtain ⟨s, hs, hE⟩ := exists_sign_EE_lattice_eq_det L
  have hq : q1 L d ω₀ = ((s * (c * b - e * a) : ℤ) : ℝ) := by
    rw [← altE_theta, hce]
    rw [hab]
    exact hE c e a b
  have hodd : Odd (c * b - e * a) := by
    rw [Int.odd_iff, Int.sub_emod, Int.mul_emod c, Int.mul_emod e]
    rcases Int.emod_two_eq_zero_or_one a with ha | ha <;>
    rcases Int.emod_two_eq_zero_or_one b with hb | hb <;>
    rcases Int.emod_two_eq_zero_or_one c with hc | hc <;>
    rcases Int.emod_two_eq_zero_or_one e with he | he <;>
    simp only [ha, hb, hc, he] <;> omega
  refine ⟨s * (c * b - e * a), ?_, hq⟩
  rcases hs with rfl | rfl
  · simpa using hodd
  · have h2 : Odd (e * a - c * b) := by
      rw [← neg_sub]
      exact hodd.neg
    simpa using h2
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
