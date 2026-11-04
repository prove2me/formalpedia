-- Prove2me | solution 1 for GPhNGIDiffusion.EMError.lemma_A_1_generator
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T18:01:43.571622+00:00
-- url     : https://prove2.me/submissions/52e56a38-37e5-48c2-85a7-167f1dec8deb

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Distances
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_EulerMaruyama
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
open Matrix

namespace EMErrGen
open GPhNGIDiffusion.EMError

variable {d : ℕ}

lemma fderiv_pow_eq (V : EthierKurtz.SDEState d → ℝ) (hV : Differentiable ℝ V) (ℓ : ℕ) :
    fderiv ℝ (fun y => V y ^ ℓ) = fun y => ((ℓ : ℝ) * V y ^ (ℓ - 1)) • fderiv ℝ V y := by
  funext y
  have := ((hV y).hasFDerivAt.pow ℓ).fderiv
  rw [this, nsmul_eq_mul]

lemma gradient_pow_eq (V : EthierKurtz.SDEState d → ℝ) (hV : Differentiable ℝ V) (ℓ : ℕ)
    (y : EthierKurtz.SDEState d) :
    gradient (fun y => V y ^ ℓ) y = ((ℓ : ℝ) * V y ^ (ℓ - 1)) • gradient V y := by
  simp only [gradient, fderiv_pow_eq V hV ℓ, map_smul]

lemma partial2_pow_eq (V : EthierKurtz.SDEState d → ℝ) (hV : ContDiff ℝ 2 V) (ℓ : ℕ)
    (i j : Fin d) (y : EthierKurtz.SDEState d) :
    partial2 (fun y => V y ^ ℓ) i j y =
      (ℓ : ℝ) * V y ^ (ℓ - 1) * partial2 V i j y +
      (ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V y ^ (ℓ - 1 - 1) * (partial1 V i y * partial1 V j y) := by
  have hd : Differentiable ℝ V := hV.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (fderiv ℝ V) := hV.fderiv_right (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ V) := hc1.differentiable one_ne_zero
  have hp2 : ∀ (f : EthierKurtz.SDEState d → ℝ) (i j : Fin d) (y : EthierKurtz.SDEState d),
      partial2 f i j y = fderiv ℝ (fderiv ℝ f) y (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
    intro f i j y; simp [partial2, iteratedFDeriv_two_apply]
  rw [hp2, hp2, fderiv_pow_eq V hd ℓ]
  have hc : HasFDerivAt (fun y => (ℓ : ℝ) * V y ^ (ℓ - 1))
      ((ℓ : ℝ) • (((ℓ - 1 : ℕ) • V y ^ (ℓ - 1 - 1)) • fderiv ℝ V y)) y :=
    (((hd y).hasFDerivAt.pow (ℓ - 1))).const_mul (ℓ : ℝ)
  have hL : HasFDerivAt (fderiv ℝ V) (fderiv ℝ (fderiv ℝ V) y) y := (hdd y).hasFDerivAt
  have hs := hc.smul hL
  have e : (fun y => ((ℓ : ℝ) * V y ^ (ℓ - 1)) • fderiv ℝ V y) =
      (fun y => (ℓ : ℝ) * V y ^ (ℓ - 1)) • fderiv ℝ V := rfl
  rw [e, hs.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, nsmul_eq_mul, partial1]
  ring

end EMErrGen

open GPhNGIDiffusion.EMError EMErrGen in
theorem solution {d : ℕ} (M : Model d)
    (V : EthierKurtz.SDEState d → ℝ) (c₁ c₁' : ℝ) (hV : IsLyapunovFn M V c₁ c₁')
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ cℓ : ℝ, 0 < cℓ ∧
      ∀ x, generator M.drift M.σ (fun y => V y ^ ℓ) x ≤ -c₁ * V x ^ ℓ + cℓ := by
  obtain ⟨hVc2, hV0, ⟨a, A, B0, ha, hA, hB0, hVq⟩, ⟨Cg, hCg, hgrad⟩, hc1, hc1', hgen⟩ := hV
  have hd : Differentiable ℝ V := hVc2.differentiable (by norm_num)
  set S : ℝ := ∑ i, ∑ j, |(M.σ * M.σᵀ) i j| with hSdef
  have hS : 0 ≤ S := by positivity
  -- quadratic form bound
  have hq : ∀ x, ∑ i, ∑ j, (M.σ * M.σᵀ) i j * (partial1 V i x * partial1 V j x) ≤
      S * ‖gradient V x‖ ^ 2 := by
    intro x
    have hpi : ∀ i, |partial1 V i x| ≤ ‖gradient V x‖ := by
      intro i
      have : partial1 V i x = inner ℝ (gradient V x) (EuclideanSpace.single i 1) := by
        rw [gradient, InnerProductSpace.toDual_symm_apply]; rfl
      rw [this]
      calc |inner ℝ (gradient V x) (EuclideanSpace.single i (1:ℝ))|
          ≤ ‖gradient V x‖ * ‖(EuclideanSpace.single i (1:ℝ) : EthierKurtz.SDEState d)‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖gradient V x‖ := by simp
    calc ∑ i, ∑ j, (M.σ * M.σᵀ) i j * (partial1 V i x * partial1 V j x)
        ≤ ∑ i, ∑ j, |(M.σ * M.σᵀ) i j| * ‖gradient V x‖ ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
          calc (M.σ * M.σᵀ) i j * (partial1 V i x * partial1 V j x)
              ≤ |(M.σ * M.σᵀ) i j * (partial1 V i x * partial1 V j x)| := le_abs_self _
            _ = |(M.σ * M.σᵀ) i j| * (|partial1 V i x| * |partial1 V j x|) := by
                rw [abs_mul, abs_mul]
            _ ≤ |(M.σ * M.σᵀ) i j| * (‖gradient V x‖ * ‖gradient V x‖) := by
                gcongr
                · exact hpi i
                · exact hpi j
            _ = _ := by ring
      _ = S * ‖gradient V x‖ ^ 2 := by
          rw [hSdef, Finset.sum_mul]
          simp_rw [Finset.sum_mul]
  -- gradient squared bound by V
  have hg2 : ∀ x, ‖gradient V x‖ ^ 2 ≤ 2 * Cg ^ 2 * (1 + V x / a) := by
    intro x
    have h1 := hgrad x
    have h2 : (1 + ‖x‖) ^ 2 ≤ 2 * (1 + ‖x‖ ^ 2) := by nlinarith [sq_nonneg (‖x‖ - 1)]
    have h3 : ‖x‖ ^ 2 ≤ V x / a := by rw [le_div_iff₀ ha, mul_comm]; exact (hVq x).1
    have h4 : ‖gradient V x‖ ^ 2 ≤ (Cg * (1 + ‖x‖)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    calc ‖gradient V x‖ ^ 2 ≤ Cg ^ 2 * (1 + ‖x‖) ^ 2 := by rw [← mul_pow]; exact h4
      _ ≤ Cg ^ 2 * (2 * (1 + ‖x‖ ^ 2)) := by gcongr
      _ ≤ Cg ^ 2 * (2 * (1 + V x / a)) := by gcongr
      _ = _ := by ring
  -- generator formula
  have hform : ∀ x, generator M.drift M.σ (fun y => V y ^ ℓ) x =
      (ℓ : ℝ) * V x ^ (ℓ - 1) * generator M.drift M.σ V x +
      (1 / 2) * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1)) *
        ∑ i, ∑ j, (M.σ * M.σᵀ) i j * (partial1 V i x * partial1 V j x) := by
    intro x
    simp only [generator, gradient_pow_eq V hd ℓ x, inner_smul_left, partial2_pow_eq V hVc2 ℓ]
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, conj_trivial]
    ring_nf
    congr 1
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  -- polynomial bound
  set D : ℝ := (ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * (S * Cg ^ 2) with hDdef
  have hD : 0 ≤ D := by positivity
  set A1 : ℝ := (ℓ : ℝ) * c₁' + D / a with hA1def
  have hA1 : 0 ≤ A1 := by positivity
  have hstep : ∀ x, generator M.drift M.σ (fun y => V y ^ ℓ) x ≤
      -(ℓ : ℝ) * c₁ * V x ^ ℓ + A1 * V x ^ (ℓ - 1) + D * V x ^ (ℓ - 1 - 1) := by
    intro x
    rw [hform x]
    have hv := hV0 x
    have hp1 : 0 ≤ (ℓ : ℝ) * V x ^ (ℓ - 1) := by positivity
    have hcoef : 0 ≤ (1 / 2) * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1)) := by positivity
    have e1 : (ℓ : ℝ) * V x ^ (ℓ - 1) * generator M.drift M.σ V x ≤
        (ℓ : ℝ) * V x ^ (ℓ - 1) * (-c₁ * V x + c₁') := mul_le_mul_of_nonneg_left (hgen x) hp1
    have e2 : (1 / 2) * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1)) *
        ∑ i, ∑ j, (M.σ * M.σᵀ) i j * (partial1 V i x * partial1 V j x) ≤
        (1 / 2) * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1)) *
        (S * (2 * Cg ^ 2 * (1 + V x / a))) :=
      mul_le_mul_of_nonneg_left ((hq x).trans (mul_le_mul_of_nonneg_left (hg2 x) hS)) hcoef
    have hpowl : V x ^ ℓ = V x * V x ^ (ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    -- V^{ℓ-2} * V = V^{ℓ-1} when ℓ ≥ 2; when ℓ = 1 the coefficient (ℓ-1) vanishes
    have hmix : ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1) * V x = ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1) := by
      rcases Nat.lt_or_ge ℓ 2 with h | h
      · have : ℓ - 1 = 0 := by omega
        simp [this]
      · rw [mul_assoc, ← pow_succ]; congr 2; omega
    have expand : (1 / 2) * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1)) *
        (S * (2 * Cg ^ 2 * (1 + V x / a))) =
        D * V x ^ (ℓ - 1 - 1) + (D / a) * V x ^ (ℓ - 1) := by
      have : (1 / 2) * ((ℓ : ℝ) * ((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1)) *
          (S * (2 * Cg ^ 2 * (1 + V x / a))) =
          D * V x ^ (ℓ - 1 - 1) + (D / a) * (((ℓ - 1 : ℕ) : ℝ) * V x ^ (ℓ - 1 - 1) * V x) /
            ((ℓ - 1 : ℕ) : ℝ) := by
        rcases Nat.lt_or_ge ℓ 2 with h | h
        · have : ℓ - 1 = 0 := by omega
          simp [this, hDdef]
        · have hne : ((ℓ - 1 : ℕ) : ℝ) ≠ 0 := by
            have : 1 ≤ ℓ - 1 := by omega
            exact_mod_cast (by omega : ℓ - 1 ≠ 0)
          rw [hDdef]; field_simp
      rw [this, hmix]
      rcases Nat.lt_or_ge ℓ 2 with h | h
      · have : ℓ - 1 = 0 := by omega
        simp [this, hDdef]
      · have hne : ((ℓ - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : ℓ - 1 ≠ 0)
        field_simp
    rw [expand] at e2
    rw [hpowl]
    simp only [hA1def]
    nlinarith
  -- bound the polynomial in t = V x
  set T : ℝ := max 1 ((A1 + D) / c₁ + 1) with hTdef
  have hT1 : 1 ≤ T := le_max_left _ _
  set cℓ : ℝ := (A1 + D) * T ^ ℓ + c₁' with hcdef
  refine ⟨cℓ, by positivity, fun x => ?_⟩
  refine (hstep x).trans ?_
  have hv := hV0 x
  set t := V x
  rcases Nat.lt_or_ge ℓ 2 with hl | hl
  · -- ℓ = 1
    have h1 : ℓ = 1 := by omega
    have hTl : 1 ≤ T ^ ℓ := one_le_pow₀ hT1
    have hAc : A1 ≤ cℓ := by
      have : A1 * 1 ≤ (A1 + D) * T ^ ℓ := mul_le_mul (by linarith) hTl zero_le_one (by positivity)
      linarith
    have e0 : ℓ - 1 = 0 := by omega
    have e00 : ℓ - 1 - 1 = 0 := by omega
    have hD0 : D = 0 := by rw [hDdef, e0]; simp
    rw [e0, Nat.zero_sub, pow_zero, h1, pow_one, Nat.cast_one, hD0]
    linarith
  · have hl1 : (1 : ℝ) ≤ (ℓ : ℝ) - 1 := by
      have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hl
      linarith
    have hpow : t ^ ℓ = t * t ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
    rcases le_or_gt t T with htT | htT
    · -- bounded region
      have e1 : t ^ (ℓ - 1) ≤ T ^ ℓ := by
        calc t ^ (ℓ - 1) ≤ T ^ (ℓ - 1) := pow_le_pow_left₀ hv htT _
          _ ≤ T ^ ℓ := pow_le_pow_right₀ hT1 (by omega)
      have e2 : t ^ (ℓ - 1 - 1) ≤ T ^ ℓ := by
        calc t ^ (ℓ - 1 - 1) ≤ T ^ (ℓ - 1 - 1) := pow_le_pow_left₀ hv htT _
          _ ≤ T ^ ℓ := pow_le_pow_right₀ hT1 (by omega)
      have e3 : 0 ≤ (ℓ : ℝ) * c₁ * t ^ ℓ := by positivity
      have e4 : 0 ≤ (ℓ : ℝ) * c₁ * t ^ ℓ - c₁ * t ^ ℓ := by
        have : 0 ≤ t ^ ℓ := by positivity
        have : (1:ℝ) ≤ ℓ := by exact_mod_cast hℓ
        nlinarith
      have := mul_le_mul_of_nonneg_left e1 hA1
      have := mul_le_mul_of_nonneg_left e2 hD
      nlinarith
    · -- large t: the leading term dominates
      have ht1 : 1 ≤ t := hT1.trans htT.le
      have htb : (A1 + D) / c₁ + 1 ≤ t := (le_max_right _ _).trans htT.le
      have hA1D : A1 + D ≤ c₁ * (t - 1) := by
        have := (div_le_iff₀ hc1).mp (by linarith : (A1 + D) / c₁ ≤ t - 1)
        linarith
      have e2 : t ^ (ℓ - 1 - 1) ≤ t ^ (ℓ - 1) := pow_le_pow_right₀ ht1 (by omega)
      have hq0 : 0 ≤ t ^ (ℓ - 1) := by positivity
      have key : A1 * t ^ (ℓ - 1) + D * t ^ (ℓ - 1 - 1) ≤ (A1 + D) * t ^ (ℓ - 1) := by
        have := mul_le_mul_of_nonneg_left e2 hD; nlinarith
      have key2 : (A1 + D) * t ^ (ℓ - 1) ≤ c₁ * (t - 1) * t ^ (ℓ - 1) :=
        mul_le_mul_of_nonneg_right hA1D hq0
      have key3 : c₁ * (t - 1) * t ^ (ℓ - 1) ≤ ((ℓ : ℝ) - 1) * c₁ * t ^ ℓ := by
        rw [hpow]
        have hu : 0 ≤ c₁ * t ^ (ℓ - 1) := by positivity
        have h5 : 1 * (c₁ * t ^ (ℓ - 1) * t) ≤ ((ℓ : ℝ) - 1) * (c₁ * t ^ (ℓ - 1) * t) :=
          mul_le_mul_of_nonneg_right hl1 (mul_nonneg hu (by linarith))
        have h6 : c₁ * t ^ (ℓ - 1) * (t - 1) ≤ c₁ * t ^ (ℓ - 1) * t :=
          mul_le_mul_of_nonneg_left (by linarith) hu
        calc c₁ * (t - 1) * t ^ (ℓ - 1) = c₁ * t ^ (ℓ - 1) * (t - 1) := by ring
          _ ≤ c₁ * t ^ (ℓ - 1) * t := h6
          _ = 1 * (c₁ * t ^ (ℓ - 1) * t) := by ring
          _ ≤ ((ℓ : ℝ) - 1) * (c₁ * t ^ (ℓ - 1) * t) := h5
          _ = ((ℓ : ℝ) - 1) * c₁ * (t * t ^ (ℓ - 1)) := by ring
      have hc0 : 0 ≤ cℓ := by positivity
      linarith
