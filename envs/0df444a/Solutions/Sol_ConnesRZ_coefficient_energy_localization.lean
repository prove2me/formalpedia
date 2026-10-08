-- Prove2me | solution 1 for ConnesRZ.coefficient_energy_localization
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-06T22:21:41.69008+00:00
-- url     : https://prove2.me/submissions/6e79a21b-9618-4e10-aaf8-6233ea3ec8ef

import Theorems.Thm_ConnesRZ_finite_mellin_interpolation
import Theorems.Thm_ConnesRZ_finite_mellin_exceptional
import Theorems.Thm_ConnesRZ_explicit_formula

set_option autoImplicit false
open Complex MeasureTheory ConnesRZ
open scoped BigOperators
noncomputable section

namespace ConnesRZFrontier
abbrev CriticalZeros := {s : ℂ // IsCriticalZero s}
def ExplicitFormula : Prop :=
  ∀ g : ℝ → ℂ, IsTest g →
    HasSum (fun ρ : CriticalZeros => (zeroMult ρ.1 : ℂ) * mellinHat g ρ.1)
      (weilDistribution g)
end ConnesRZFrontier
open ConnesRZFrontier
namespace ConnesRZInterpolation
lemma weighted_integrable (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ) :
    Integrable (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) := by
  have hc : Continuous (fun t : ℝ => g t * Complex.exp ((z - 1 / 2) * t)) :=
    hg.1.continuous.mul (Complex.continuous_exp.comp (by fun_prop))
  exact hc.integrable_of_hasCompactSupport hg.2.mul_right
end ConnesRZInterpolation
open ConnesRZInterpolation
namespace ConnesRZDecay

def envelope (g : ℝ → ℂ) (t : ℝ) : ℝ := ‖g t‖ * Real.exp (|t| / 2)
def envelopeMass (g : ℝ → ℂ) : ℝ := ∫ t : ℝ, envelope g t

lemma envelope_integrable (g : ℝ → ℂ) (hg : IsTest g) : Integrable (envelope g) := by
  have hc : Continuous (envelope g) := hg.1.continuous.norm.mul (by fun_prop)
  exact hc.integrable_of_hasCompactSupport hg.2.norm.mul_right

lemma envelopeMass_nonneg (g : ℝ → ℂ) : 0 ≤ envelopeMass g := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

lemma kernel_bound (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) (t : ℝ) :
    ‖Complex.exp ((z - 1 / 2) * t)‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
    nlinarith
  · rw [abs_of_neg (lt_of_not_ge ht)]
    nlinarith

lemma mellin_bound (g : ℝ → ℂ) (hg : IsTest g) (z : ℂ)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) : ‖mellinHat g z‖ ≤ envelopeMass g := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono (weighted_integrable g hg z).norm (envelope_integrable g hg)
  intro t
  change ‖g t * Complex.exp ((z - 1 / 2) * t)‖ ≤ ‖g t‖ * Real.exp (|t| / 2)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (kernel_bound z hz0 hz1 t) (norm_nonneg _)

end ConnesRZDecay
namespace ConnesRZPos
lemma isTest_conv {g₁ g₂ : ℝ → ℂ} (h₁ : IsTest g₁) (h₂ : IsTest g₂) :
    IsTest (conv g₁ g₂) := by
  change IsTest (convolution g₁ g₂ (ContinuousLinearMap.mul ℝ ℂ) volume)
  refine ⟨?_, HasCompactSupport.convolution _ h₁.2 h₂.2⟩
  exact HasCompactSupport.contDiff_convolution_right (n := (⊤ : ℕ∞)) _ h₂.2
    (h₁.1.continuous.locallyIntegrable) h₂.1
end ConnesRZPos
open ConnesRZPos
namespace ConnesRZConvolution

lemma integrable_pair (f h : ℝ → ℂ) (hf : IsTest f) (hh : IsTest h) (z : ℂ) :
    Integrable (fun p : ℝ × ℝ => f p.2 * h (p.1 - p.2) *
      Complex.exp ((z - 1 / 2) * p.1)) := by
  have hc : Continuous (fun p : ℝ × ℝ => f p.2 * h (p.1 - p.2) *
      Complex.exp ((z - 1 / 2) * p.1)) := by
    have hfcont := hf.1.continuous
    have hhcont := hh.1.continuous
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro
    (K := (fun q : ℝ × ℝ => (q.1 + q.2, q.1)) '' (tsupport f ×ˢ tsupport h))
    ((hf.2.prod hh.2).image (by fun_prop)) ?_
  rintro ⟨t, s⟩ hts
  by_contra hn
  have hf' : f s ≠ 0 := by intro he; apply hn; simp [he]
  have hh' : h (t - s) ≠ 0 := by intro he; apply hn; simp [he]
  exact hts ⟨(s, t-s), ⟨subset_tsupport _ hf', subset_tsupport _ hh'⟩, by simp⟩

lemma mellin_conv (f h : ℝ → ℂ) (hf : IsTest f) (hh : IsTest h) (z : ℂ) :
    mellinHat (conv f h) z = mellinHat f z * mellinHat h z := by
  unfold mellinHat
  have h1 : ∀ t : ℝ, conv f h t * Complex.exp ((z - 1 / 2) * t) =
      ∫ s : ℝ, f s * h (t-s) * Complex.exp ((z - 1 / 2) * t) := by
    intro t
    unfold conv
    rw [← integral_mul_const]
  rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
  rw [integral_integral_swap (integrable_pair f h hf hh z)]
  have h2 : ∀ s : ℝ, (∫ t : ℝ, f s * h (t-s) * Complex.exp ((z - 1 / 2) * t)) =
      (f s * Complex.exp ((z - 1 / 2) * s)) *
        ∫ u : ℝ, h u * Complex.exp ((z - 1 / 2) * u) := by
    intro s
    rw [← integral_const_mul]
    have ht := integral_sub_right_eq_self
      (fun u : ℝ => (f s * Complex.exp ((z - 1 / 2) * s)) *
        (h u * Complex.exp ((z - 1 / 2) * u))) s (μ := volume)
    rw [← ht]
    apply integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    have he : Complex.exp ((z - 1 / 2) * s) *
        Complex.exp ((z - 1 / 2) * ((t-s : ℝ) : ℂ)) =
        Complex.exp ((z - 1 / 2) * t) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (-(f s * h (t-s))) * he
  rw [integral_congr_ae (Filter.Eventually.of_forall h2), integral_mul_const]

def amplify (φ κ : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => κ
  | N+1 => conv φ (amplify φ κ N)

lemma isTest_amplify (φ κ : ℝ → ℂ) (hφ : IsTest φ) (hκ : IsTest κ) (N : ℕ) :
    IsTest (amplify φ κ N) := by
  induction N with
  | zero => exact hκ
  | succ N ih => exact isTest_conv hφ ih

lemma mellin_amplify (φ κ : ℝ → ℂ) (hφ : IsTest φ) (hκ : IsTest κ) (N : ℕ) (z : ℂ) :
    mellinHat (amplify φ κ N) z = mellinHat κ z * mellinHat φ z ^ N := by
  induction N with
  | zero => simp [amplify]
  | succ N ih =>
    rw [amplify, mellin_conv φ _ hφ (isTest_amplify φ κ hφ hκ N), ih, pow_succ]
    ring

end ConnesRZConvolution

open ConnesRZConvolution
namespace ConnesRZPacket

lemma choose_base (S : Finset CriticalZeros) :
    ∃ φ : ℝ → ℂ, IsTest φ ∧ ∀ ρ ∈ S, mellinHat φ ρ.1 = 1 := by
  classical
  obtain ⟨φ, hφ, he⟩ := finite_mellin_interpolation (fun ρ : S => ρ.1.1)
    (fun i j h => Subtype.ext (Subtype.ext h)) (fun _ => (1 : ℂ))
  exact ⟨φ, hφ, fun ρ hρ => he ⟨ρ, hρ⟩⟩

lemma choose_corrector (S : Finset CriticalZeros) (a : ℂ → ℂ)
    (φ : ℝ → ℂ) (hφ : IsTest φ) :
    ∃ κ : ℝ → ℂ, IsTest κ ∧ (∀ ρ ∈ S, mellinHat κ ρ.1 = a ρ.1) ∧
      ∀ ρ : CriticalZeros, ρ ∉ S → (1 / 2 : ℝ) ≤ ‖mellinHat φ ρ.1‖ →
        mellinHat κ ρ.1 = 0 := by
  classical
  let E := {z : ℂ | IsCriticalZero z ∧ (1 / 2 : ℝ) ≤ ‖mellinHat φ z‖}
  have hE : E.Finite := finite_mellin_exceptional φ hφ _ (by norm_num)
  let P : Finset ℂ := S.image Subtype.val
  let T := P ∪ hE.toFinset
  obtain ⟨κ, hκ, he⟩ := finite_mellin_interpolation (fun z : T => z.1)
    Subtype.val_injective (fun z => if z.1 ∈ P then a z.1 else 0)
  refine ⟨κ, hκ, ?_, ?_⟩
  · intro ρ hρ
    have hp : ρ.1 ∈ P := Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩
    simpa [hp] using he ⟨ρ.1, Finset.mem_union_left _ hp⟩
  · intro ρ hρ hlarge
    have hp : ρ.1 ∉ P := by
      intro hm
      obtain ⟨τ, hτ, heq⟩ := Finset.mem_image.mp hm
      exact hρ (Subtype.ext heq ▸ hτ)
    have hm : ρ.1 ∈ T := Finset.mem_union_right _ (hE.mem_toFinset.mpr ⟨ρ.2, hlarge⟩)
    simpa [hp] using he ⟨ρ.1, hm⟩


end ConnesRZPacket
namespace ConnesRZEnergy

/-- The actual multiplicity-weighted raw coefficient energy, before any native
Green weighting or Hilbert realization. -/
def coefficientEnergy (g : ℝ → ℂ) (ρ : CriticalZeros) : ℝ :=
  (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2

lemma coefficientEnergy_nonneg (g : ℝ → ℂ) (ρ : CriticalZeros) :
    0 ≤ coefficientEnergy g ρ := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

/-- The LINEAR explicit formula, together with the existing strip envelope,
controls individual squared coefficients; no signed pair cancellation is used. -/
theorem coefficientEnergy_summable (hEF : ExplicitFormula) (g : ℝ → ℂ)
    (hg : IsTest g) : Summable (coefficientEnergy g) := by
  have hs : Summable (fun ρ : CriticalZeros =>
      (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖) := by
    simpa only [norm_mul, Complex.norm_natCast] using (hEF g hg).summable.norm
  apply Summable.of_nonneg_of_le (coefficientEnergy_nonneg g) ?_
    (hs.mul_left (ConnesRZDecay.envelopeMass g))
  intro ρ
  have hb := ConnesRZDecay.mellin_bound g hg ρ.1 ρ.2.2.1.le ρ.2.2.2.le
  have hn := norm_nonneg (mellinHat g ρ.1)
  have hm : (0 : ℝ) ≤ zeroMult ρ.1 := Nat.cast_nonneg _
  dsimp [coefficientEnergy]
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hn) hm]

/-- Individual complementary coefficient energy can be made arbitrarily small
while retaining prescribed values on the same finite ACTUAL-zero packet.
The support radius may grow with the convolution exponent. -/
theorem coefficient_energy_localization (hEF : ExplicitFormula)
    (S : Finset CriticalZeros) (a : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, IsTest g ∧ (∀ ρ ∈ S, mellinHat g ρ.1 = a ρ.1) ∧
      Summable (fun ρ : CriticalZeros => if ρ ∈ S then 0 else coefficientEnergy g ρ) ∧
      (∑' ρ : CriticalZeros, if ρ ∈ S then 0 else coefficientEnergy g ρ) < ε := by
  classical
  obtain ⟨φ, hφ, hφS⟩ := ConnesRZPacket.choose_base S
  obtain ⟨κ, hκ, hκS, hkill⟩ := ConnesRZPacket.choose_corrector S a φ hφ
  let c : CriticalZeros → ℝ := fun ρ => if ρ ∈ S then 0 else coefficientEnergy κ ρ
  have hc0 : ∀ ρ, 0 ≤ c ρ := by
    intro ρ
    dsimp [c]
    split_ifs <;> simp [coefficientEnergy_nonneg]
  have hc : Summable c := by
    apply Summable.of_nonneg_of_le hc0 ?_ (coefficientEnergy_summable hEF κ hκ)
    intro ρ
    dsimp [c]
    split_ifs <;> simp [coefficientEnergy_nonneg]
  have ht : Filter.Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N * ∑' ρ, c ρ)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun N : ℕ => (1 / 4 : ℝ) ^ N) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hp.mul_const (∑' ρ, c ρ)
  obtain ⟨N, hN⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  let g := amplify φ κ N
  let e : CriticalZeros → ℝ := fun ρ => if ρ ∈ S then 0 else coefficientEnergy g ρ
  have he0 : ∀ ρ, 0 ≤ e ρ := by
    intro ρ
    dsimp [e]
    split_ifs <;> simp [coefficientEnergy_nonneg]
  have hb : ∀ ρ, e ρ ≤ (1 / 4 : ℝ) ^ N * c ρ := by
    intro ρ
    by_cases hp : ρ ∈ S
    · simp [e, c, hp]
    · by_cases hlarge : (1 / 2 : ℝ) ≤ ‖mellinHat φ ρ.1‖
      · have hk := hkill ρ hp hlarge
        simp [e, c, hp, coefficientEnergy, g,
          mellin_amplify φ κ hφ hκ N, hk]
      · have hn := norm_nonneg (mellinHat φ ρ.1)
        have hs : ‖mellinHat φ ρ.1‖ ^ 2 ≤ (1 / 4 : ℝ) := by
          have hh : ‖mellinHat φ ρ.1‖ < (1 / 2 : ℝ) := lt_of_not_ge hlarge
          nlinarith
        have hpow := pow_le_pow_left₀ (sq_nonneg ‖mellinHat φ ρ.1‖) hs N
        have heq : coefficientEnergy g ρ = coefficientEnergy κ ρ *
            (‖mellinHat φ ρ.1‖ ^ 2) ^ N := by
          simp only [coefficientEnergy, g, mellin_amplify φ κ hφ hκ N,
            norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm N 2]
          ring
        simp only [e, c, if_neg hp]
        rw [heq, mul_comm ((1 / 4 : ℝ) ^ N)]
        exact mul_le_mul_of_nonneg_left hpow (coefficientEnergy_nonneg κ ρ)
  have he : Summable e := Summable.of_nonneg_of_le he0 hb (hc.mul_left _)
  refine ⟨g, isTest_amplify φ κ hφ hκ N, ?_, he, ?_⟩
  · intro ρ hρ
    simp [g, mellin_amplify φ κ hφ hκ N, hκS ρ hρ, hφS ρ hρ]
  · calc
      ∑' ρ, e ρ ≤ ∑' ρ, (1 / 4 : ℝ) ^ N * c ρ :=
        he.tsum_le_tsum hb (hc.mul_left _)
      _ = (1 / 4 : ℝ) ^ N * ∑' ρ, c ρ := tsum_mul_left
      _ < ε := hN


end ConnesRZEnergy

theorem solution (S : Finset {s : ℂ // IsCriticalZero s}) (a : ℂ → ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, IsTest g ∧ (∀ ρ ∈ S, mellinHat g ρ.1 = a ρ.1) ∧
      Summable (fun ρ : {s : ℂ // IsCriticalZero s} =>
        if ρ ∈ S then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) ∧
      (∑' ρ : {s : ℂ // IsCriticalZero s},
        if ρ ∈ S then 0 else (zeroMult ρ.1 : ℝ) * ‖mellinHat g ρ.1‖ ^ 2) < ε := by
  simpa only [ConnesRZEnergy.coefficientEnergy] using
    ConnesRZEnergy.coefficient_energy_localization ConnesRZ.explicit_formula S a ε hε
