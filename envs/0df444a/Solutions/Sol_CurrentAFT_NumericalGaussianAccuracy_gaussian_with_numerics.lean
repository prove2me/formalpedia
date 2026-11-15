-- Prove2me | solution 1 for CurrentAFT.NumericalGaussianAccuracy.gaussian_with_numerics
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:48:17.976728+00:00
-- url     : https://prove2.me/submissions/5070984f-f012-4a17-9942-8cdc7bf2b333

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Mathlib
import Theorems.Thm_AFT_FiniteDist_totalVariation_eq_half_l1
import Theorems.Thm_CurrentAFT_ActualCalibratedPublic_positive_eventually
import Theorems.Thm_CurrentAFT_ActualCompletePhysical_selected_physical_explicit_order
namespace P2Mb748e9da
end P2Mb748e9da
section
set_option backward.isDefEq.respectTransparency false
namespace AFT
open scoped BigOperators
end AFT
namespace AFT
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h120 (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] _root_.AFT.zeroSumLattice n)
    (B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (c w : Fin (n + 1) → ℤ) (a : Fin n → ℤ)
    (ha : _root_.AFT.pathLoad n a = w - c) (x : (Fin n → ℤ) × ℤ) :
    _root_.AFT.roundingLoad n c (_root_.AFT.blockTransport n (_root_.AFT.edgeBasisChange n treeBasis) B a x) =
      (treeBasis (B x.1) : Fin (n + 1) → ℤ) + x.2 • w := by
  simp only [_root_.AFT.roundingLoad, _root_.AFT.blockTransport, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.AFT.pathLoad_add, _root_.AFT.pathLoad_smul, _root_.AFT.pathLoad_edgeBasisChange, ha, smul_sub]
  abel
open _root_.P2Mb748e9da renaming h120 → _p2mH120
end AFT
open _root_.P2Mb748e9da renaming h120 → _p2mH120
namespace AFT
end AFT
namespace AFT
end AFT
end
open _root_.P2Mb748e9da renaming h120 → _p2mH120
namespace AFT
end AFT
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.mk
end AFT.FiniteDist.mk
namespace AFT.FiniteDist.uniform
end AFT.FiniteDist.uniform
section
namespace AFT
namespace FiniteDist
open scoped BigOperators
open scoped Classical
variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h69 {p q : _root_.AFT.FiniteDist α} {error largerError : ℝ}
    (h : _root_.AFT.FiniteDist.TVBound p q error) (hle : error ≤ largerError) :
    _root_.AFT.FiniteDist.TVBound p q largerError := fun s => (h s).trans hle
open _root_.P2Mb748e9da renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2Mb748e9da renaming h69 → _p2mH69
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h70 {p q r : _root_.AFT.FiniteDist α} {firstError secondError : ℝ}
    (hfirst : _root_.AFT.FiniteDist.TVBound p q firstError) (hsecond : _root_.AFT.FiniteDist.TVBound q r secondError) :
    _root_.AFT.FiniteDist.TVBound p r (firstError + secondError) := by
  intro s
  calc
    |p.event s - r.event s| ≤ |p.event s - q.event s| + |q.event s - r.event s| :=
      abs_sub_le _ _ _
    _ ≤ firstError + secondError := add_le_add (hfirst s) (hsecond s)
open _root_.P2Mb748e9da renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2Mb748e9da renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h73 (p : _root_.AFT.FiniteDist α) (f : α → β) (s : Finset β) :
    (p.map f).event s = ∑ a, if f a ∈ s then p.weight a else 0 := by
  classical
  simp only [_root_.AFT.FiniteDist.event, _root_.AFT.FiniteDist.map_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]
open _root_.P2Mb748e9da renaming h73 → _p2mH73
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h67 {p q : _root_.AFT.FiniteDist α} {error : ℝ}
    (h : _root_.AFT.FiniteDist.TVBound p q error) (f : α → β) : _root_.AFT.FiniteDist.TVBound (p.map f) (q.map f) error := by
  classical
  intro s
  rw [_p2mH73, _p2mH73]
  simpa only [_root_.AFT.FiniteDist.event, Finset.sum_filter] using
    h (Finset.univ.filter (fun a => f a ∈ s))
open _root_.P2Mb748e9da renaming h67 → AFT.FiniteDist.TVBound.map
open _root_.P2Mb748e9da renaming h67 → _p2mH67
end FiniteDist
open _root_.P2Mb748e9da renaming h67 → AFT.FiniteDist.TVBound.map
open _root_.P2Mb748e9da renaming h67 → _p2mH67
open _root_.P2Mb748e9da renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2Mb748e9da renaming h69 → _p2mH69
open _root_.P2Mb748e9da renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2Mb748e9da renaming h70 → _p2mH70
open _root_.P2Mb748e9da renaming h73 → _p2mH73
end AFT
open _root_.P2Mb748e9da renaming h67 → AFT.FiniteDist.TVBound.map
open _root_.P2Mb748e9da renaming h67 → _p2mH67
open _root_.P2Mb748e9da renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2Mb748e9da renaming h69 → _p2mH69
open _root_.P2Mb748e9da renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2Mb748e9da renaming h70 → _p2mH70
open _root_.P2Mb748e9da renaming h73 → _p2mH73
end
open _root_.P2Mb748e9da renaming h67 → AFT.FiniteDist.TVBound.map
open _root_.P2Mb748e9da renaming h67 → _p2mH67
open _root_.P2Mb748e9da renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2Mb748e9da renaming h69 → _p2mH69
open _root_.P2Mb748e9da renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2Mb748e9da renaming h70 → _p2mH70
open _root_.P2Mb748e9da renaming h73 → _p2mH73
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.event
end AFT.FiniteDist.event
namespace AFT.negativeMass
end AFT.negativeMass
namespace AFT.positiveMass
end AFT.positiveMass
namespace AFT.signedMass
end AFT.signedMass
section
namespace AFT
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h118 (weight test : α → ℝ)
    (hzero : _root_.AFT.signedMass weight = 0) (htest : ∀ a, 0 ≤ test a ∧ test a ≤ 1) :
    |∑ a, weight a * test a| ≤ _root_.AFT.positiveMass weight := by
  have hpoint (a : α) :
      -max (-weight a) 0 ≤ weight a * test a ∧
        weight a * test a ≤ max (weight a) 0 := by
    obtain ⟨ht0, ht1⟩ := htest a
    by_cases hw : 0 ≤ weight a
    · rw [max_eq_left hw, max_eq_right (neg_nonpos.mpr hw)]
      constructor <;> nlinarith
    · have hw' : weight a ≤ 0 := le_of_not_ge hw
      rw [max_eq_right hw', max_eq_left (neg_nonneg.mpr hw')]
      constructor <;> nlinarith
  have hmass : _root_.AFT.positiveMass weight = _root_.AFT.negativeMass weight := by
    simpa [hzero] using _root_.AFT.positiveMass_eq weight
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => (hpoint a).1)
    rw [hmass]
    simpa only [Finset.sum_neg_distrib, _root_.AFT.negativeMass] using h
  · exact Finset.sum_le_sum (fun a _ => (hpoint a).2)
open _root_.P2Mb748e9da renaming h118 → _p2mH118
namespace FiniteDist
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h80 (p q : _root_.AFT.FiniteDist α) :
    _root_.AFT.signedMass (fun a => p.weight a - q.weight a) = 0 := by
  simp [_root_.AFT.signedMass, Finset.sum_sub_distrib, p.sum_one, q.sum_one]
open _root_.P2Mb748e9da renaming h80 → _p2mH80
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h81 (p q : _root_.AFT.FiniteDist α) (error : ℝ) :
    _root_.AFT.FiniteDist.TVBound p q error ↔ _root_.AFT.FiniteDist.totalVariation p q ≤ error := by
  classical
  constructor
  · intro h
    let s := Finset.univ.filter (fun a => 0 ≤ p.weight a - q.weight a)
    have hevent : p.event s - q.event s = _root_.AFT.FiniteDist.totalVariation p q := by
      simp only [_root_.AFT.FiniteDist.event, s, Finset.sum_filter, ← Finset.sum_sub_distrib,
        _root_.AFT.FiniteDist.totalVariation, _root_.AFT.positiveMass]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 0 ≤ p.weight a - q.weight a
      · simp [ha]
      · simp [ha, max_eq_right (le_of_not_ge ha)]
    have hn : 0 ≤ _root_.AFT.FiniteDist.totalVariation p q :=
      Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    have he := h s
    rwa [hevent, abs_of_nonneg hn] at he
  · intro h s
    have ht : ∀ a : α, 0 ≤ (if a ∈ s then (1 : ℝ) else 0) ∧
        (if a ∈ s then (1 : ℝ) else 0) ≤ 1 := by
      intro a
      split_ifs <;> norm_num
    have hb := _p2mH118 (fun a => p.weight a - q.weight a)
      (fun a => if a ∈ s then 1 else 0) (_p2mH80 p q) ht
    have he : (∑ a, (p.weight a - q.weight a) * (if a ∈ s then (1 : ℝ) else 0)) =
        p.event s - q.event s := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      simp [_root_.AFT.FiniteDist.event, Finset.sum_sub_distrib]
    rw [he] at hb
    exact hb.trans h
open _root_.P2Mb748e9da renaming h81 → _p2mH81
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h74 (p : _root_.AFT.FiniteDist α) (kernel : α → _root_.AFT.FiniteDist β) (s : Finset β) :
    (p.mix kernel).event s = ∑ a, p.weight a * (kernel a).event s := by
  simp only [_root_.AFT.FiniteDist.event, _root_.AFT.FiniteDist.mix_weight, Finset.mul_sum]
  exact Finset.sum_comm
open _root_.P2Mb748e9da renaming h74 → _p2mH74
end FiniteDist
open _root_.P2Mb748e9da renaming h74 → _p2mH74
open _root_.P2Mb748e9da renaming h80 → _p2mH80
open _root_.P2Mb748e9da renaming h81 → _p2mH81
end AFT
open _root_.P2Mb748e9da renaming h74 → _p2mH74
open _root_.P2Mb748e9da renaming h80 → _p2mH80
open _root_.P2Mb748e9da renaming h81 → _p2mH81
open _root_.P2Mb748e9da renaming h118 → _p2mH118
end
open _root_.P2Mb748e9da renaming h74 → _p2mH74
open _root_.P2Mb748e9da renaming h80 → _p2mH80
open _root_.P2Mb748e9da renaming h81 → _p2mH81
open _root_.P2Mb748e9da renaming h118 → _p2mH118
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.independentCoordinates
end AFT.GaussianSource.independentCoordinates
namespace AFT.GaussianSource.independentCoordinates.match_1
end AFT.GaussianSource.independentCoordinates.match_1
namespace AFT.GaussianSource.integerGaussian
end AFT.GaussianSource.integerGaussian
namespace AFT.GaussianSource.latticeGaussian
end AFT.GaussianSource.latticeGaussian
namespace AFT.GaussianSource.latticeWeight
end AFT.GaussianSource.latticeWeight
namespace AFT.GaussianSource.residueGaussian
end AFT.GaussianSource.residueGaussian
namespace AFT.GaussianSource.weight
end AFT.GaussianSource.weight
section
namespace AFT.GaussianSource
open scoped BigOperators Classical
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h87 (width : ℝ) :
    _root_.AFT.GaussianSource.realNormalizer width = (_root_.AFT.GaussianSource.normalizer width).toReal := by
  rw [_root_.AFT.GaussianSource.normalizer, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
  simp [_root_.AFT.GaussianSource.realNormalizer, ENNReal.toReal_ofReal, (_root_.AFT.GaussianSource.weight_pos width _).le]
open _root_.P2Mb748e9da renaming h87 → _p2mH87
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false in
theorem _root_.P2Mb748e9da.h86 (width : ℝ) (hw : 0 < width) (z : ℤ) :
    (_root_.AFT.GaussianSource.integerGaussian width hw z).toReal = _root_.AFT.GaussianSource.weight width z / _root_.AFT.GaussianSource.realNormalizer width := by
  rw [_root_.AFT.GaussianSource.integerGaussian, PMF.normalize_apply, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (_root_.AFT.GaussianSource.weight_pos width z).le]
  change _root_.AFT.GaussianSource.weight width z * (_root_.AFT.GaussianSource.normalizer width).toReal⁻¹ = _
  rw [← _p2mH87]
  rfl
open _root_.P2Mb748e9da renaming h86 → _p2mH86
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h93 (width cutoff : ℝ) (hw : 0 < width) :
    Summable (fun z : ℤ => if cutoff ≤ |(z : ℝ)| then _root_.AFT.GaussianSource.weight width z else 0) := by
  apply Summable.of_nonneg_of_le _ _ (_root_.AFT.GaussianSource.summable_weight width hw)
  · intro z
    split_ifs
    · exact (_root_.AFT.GaussianSource.weight_pos width z).le
    · rfl
  · intro z
    split_ifs
    · rfl
    · exact (_root_.AFT.GaussianSource.weight_pos width z).le
open _root_.P2Mb748e9da renaming h93 → _p2mH93
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h83 (width cutoff : ℝ) (hw : 0 < width) (hc : 0 ≤ cutoff) :
    _root_.AFT.GaussianSource.clippingMass width cutoff ≤
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        _root_.AFT.GaussianSource.realNormalizer (Real.sqrt 2 * width) := by
  have hw2 : 0 < Real.sqrt 2 * width := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hw
  have hsq : (Real.sqrt 2 * width) ^ 2 = 2 * width ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpoint (z : ℤ) : (if cutoff ≤ |(z : ℝ)| then _root_.AFT.GaussianSource.weight width z else 0) ≤
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        _root_.AFT.GaussianSource.weight (Real.sqrt 2 * width) z := by
    split_ifs with hz
    · have hzsq : cutoff ^ 2 ≤ (z : ℝ) ^ 2 := by nlinarith [sq_abs (z : ℝ)]
      unfold _root_.AFT.GaussianSource.weight
      rw [hsq, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hcoef : 0 ≤ Real.pi / width ^ 2 := by positivity
      have hh : -Real.pi * cutoff ^ 2 / (2 * width ^ 2) +
          -(Real.pi / (2 * width ^ 2)) * (z : ℝ) ^ 2 =
          -(Real.pi / width ^ 2) * (cutoff ^ 2 + (z : ℝ) ^ 2) / 2 := by ring
      rw [hh]
      nlinarith [mul_nonneg hcoef (sub_nonneg.mpr hzsq)]
    · exact mul_nonneg (Real.exp_pos _).le (_root_.AFT.GaussianSource.weight_pos _ z).le
  have hsum := (_p2mH93 width cutoff hw).tsum_le_tsum hpoint
    ((_root_.AFT.GaussianSource.summable_weight _ hw2).mul_left (Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2))))
  have heq : (∑' z : ℤ, Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
      _root_.AFT.GaussianSource.weight (Real.sqrt 2 * width) z) =
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        _root_.AFT.GaussianSource.realNormalizer (Real.sqrt 2 * width) := tsum_mul_left
  exact hsum.trans_eq heq
open _root_.P2Mb748e9da renaming h83 → _p2mH83
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h84 (width cutoff : ℝ) (hw : 0 < width) :
    _root_.AFT.GaussianSource.clippingProbability width cutoff hw = _root_.AFT.GaussianSource.clippingMass width cutoff / _root_.AFT.GaussianSource.realNormalizer width := by
  unfold _root_.AFT.GaussianSource.clippingProbability _root_.AFT.GaussianSource.clippingMass
  simp_rw [_p2mH86]
  have heq (z : ℤ) : (if cutoff ≤ |(z : ℝ)| then _root_.AFT.GaussianSource.weight width z / _root_.AFT.GaussianSource.realNormalizer width else 0) =
      (if cutoff ≤ |(z : ℝ)| then _root_.AFT.GaussianSource.weight width z else 0) / _root_.AFT.GaussianSource.realNormalizer width := by
    split_ifs <;> simp
  simp_rw [heq]
  exact tsum_div_const
open _root_.P2Mb748e9da renaming h84 → _p2mH84
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h85 (width cutoff : ℝ) (hw : 0 < width) (hc : 0 ≤ cutoff) :
    _root_.AFT.GaussianSource.clippingProbability width cutoff hw ≤
      Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        (1 + 4 * width ^ 2 / Real.pi) := by
  have hm : 0 ≤ _root_.AFT.GaussianSource.clippingMass width cutoff := tsum_nonneg (fun z => by
    split_ifs
    · exact (_root_.AFT.GaussianSource.weight_pos width z).le
    · rfl)
  have hw2 : 0 < Real.sqrt 2 * width := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hw
  have hn := _root_.AFT.GaussianSource.realNormalizer_le_quadratic (Real.sqrt 2 * width) hw2
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
  have hn' : _root_.AFT.GaussianSource.realNormalizer (Real.sqrt 2 * width) ≤ 1 + 4 * width ^ 2 / Real.pi := by
    convert hn using 1
    ring
  calc
    _ = _root_.AFT.GaussianSource.clippingMass width cutoff / _root_.AFT.GaussianSource.realNormalizer width := _p2mH84 width cutoff hw
    _ ≤ _root_.AFT.GaussianSource.clippingMass width cutoff := div_le_self hm (_root_.AFT.GaussianSource.realNormalizer_ge_one width hw)
    _ ≤ Real.exp (-Real.pi * cutoff ^ 2 / (2 * width ^ 2)) *
        _root_.AFT.GaussianSource.realNormalizer (Real.sqrt 2 * width) := _p2mH83 width cutoff hw hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hn' (Real.exp_pos _).le
open _root_.P2Mb748e9da renaming h85 → _p2mH85
end AFT.GaussianSource
open _root_.P2Mb748e9da renaming h83 → _p2mH83
open _root_.P2Mb748e9da renaming h84 → _p2mH84
open _root_.P2Mb748e9da renaming h85 → _p2mH85
open _root_.P2Mb748e9da renaming h86 → _p2mH86
open _root_.P2Mb748e9da renaming h87 → _p2mH87
open _root_.P2Mb748e9da renaming h93 → _p2mH93
end
open _root_.P2Mb748e9da renaming h83 → _p2mH83
open _root_.P2Mb748e9da renaming h84 → _p2mH84
open _root_.P2Mb748e9da renaming h85 → _p2mH85
open _root_.P2Mb748e9da renaming h86 → _p2mH86
open _root_.P2Mb748e9da renaming h87 → _p2mH87
open _root_.P2Mb748e9da renaming h93 → _p2mH93
section
namespace AFT
open Filter
open scoped Topology
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h119 (power exponent rate : ℝ)
    (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Tendsto (fun parameter : ℝ => parameter ^ power *
      Real.exp (-rate * parameter ^ exponent)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (power / exponent) rate hrate).comp (tendsto_rpow_atTop hexponent)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with parameter hp
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hp, mul_div_cancel₀ power hexponent.ne']
open _root_.P2Mb748e9da renaming h119 → _p2mH119
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h116
    (constant : ℝ) (degree : ℕ) (exponent rate : ℝ)
    (hconstant : 0 ≤ constant) (hexponent : 0 < exponent) (hrate : 0 < rate) :
    _root_.AFT.Negligible (fun parameter => constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent)) := by
  intro order
  have hreal := (_p2mH119 (degree + order : ℕ) exponent rate
    hexponent hrate).const_mul constant
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ parameter : ℕ in atTop,
      constant * ((parameter : ℝ) ^ (degree + order : ℕ) *
        Real.exp (-rate * (parameter : ℝ) ^ exponent)) < 1 := by
    simpa only [Function.comp_apply, mul_zero, Real.rpow_natCast] using
      hnat.eventually (gt_mem_nhds (show constant * (0 : ℝ) < 1 by simp))
  filter_upwards [hsmall, eventually_ge_atTop 1] with parameter hs hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have hnonneg : 0 ≤ constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent) := by positivity
  rw [abs_of_nonneg hnonneg, le_div_iff₀ (pow_pos hp' order)]
  rw [pow_add] at hs
  nlinarith [hs]
open _root_.P2Mb748e9da renaming h116 → _p2mH116
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h105 {error bound : ℕ → ℝ} (hbound : _root_.AFT.Negligible bound)
    (h : ∀ᶠ parameter in atTop, |error parameter| ≤ |bound parameter|) :
    _root_.AFT.Negligible error := by
  intro order
  filter_upwards [h, hbound order] with parameter hp hq
  exact hp.trans hq
open _root_.P2Mb748e9da renaming h105 → AFT.Negligible.of_eventually_le
open _root_.P2Mb748e9da renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h104 {error : ℕ → ℝ} (h : _root_.AFT.Negligible error) (offset : ℕ) :
    _root_.AFT.Negligible (fun parameter => error (parameter + offset)) := by
  intro order
  have ht : Tendsto (fun parameter : ℕ => parameter + offset) atTop atTop :=
    tendsto_atTop_mono (fun parameter => Nat.le_add_right parameter offset) tendsto_id
  filter_upwards [ht.eventually (h order), eventually_ge_atTop 1] with parameter he hp
  apply he.trans
  apply one_div_le_one_div_of_le
  · exact pow_pos (by exact_mod_cast (show 0 < parameter by omega)) order
  · exact pow_le_pow_left₀ (Nat.cast_nonneg parameter) (by exact_mod_cast
      (show parameter ≤ parameter + offset by omega)) order
open _root_.P2Mb748e9da renaming h104 → AFT.Negligible.comp_add
open _root_.P2Mb748e9da renaming h104 → _p2mH104
end AFT
open _root_.P2Mb748e9da renaming h104 → AFT.Negligible.comp_add
open _root_.P2Mb748e9da renaming h104 → _p2mH104
open _root_.P2Mb748e9da renaming h105 → AFT.Negligible.of_eventually_le
open _root_.P2Mb748e9da renaming h105 → _p2mH105
open _root_.P2Mb748e9da renaming h116 → _p2mH116
open _root_.P2Mb748e9da renaming h119 → _p2mH119
end
open _root_.P2Mb748e9da renaming h104 → AFT.Negligible.comp_add
open _root_.P2Mb748e9da renaming h104 → _p2mH104
open _root_.P2Mb748e9da renaming h105 → AFT.Negligible.of_eventually_le
open _root_.P2Mb748e9da renaming h105 → _p2mH105
open _root_.P2Mb748e9da renaming h116 → _p2mH116
open _root_.P2Mb748e9da renaming h119 → _p2mH119
namespace AFT.FiniteDist.expectation
end AFT.FiniteDist.expectation
namespace AFT.FiniteDist.independent
end AFT.FiniteDist.independent
namespace AFT.FiniteDist.l2Sq
end AFT.FiniteDist.l2Sq
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.Hoeffding.centeredAtom
end AFT.Hoeffding.centeredAtom
namespace AFT.Hoeffding.densityComponent
end AFT.Hoeffding.densityComponent
namespace AFT.coordinateActivity
end AFT.coordinateActivity
namespace AFT.finitePrimaryRankEquiv
end AFT.finitePrimaryRankEquiv
namespace AFT.fixedFiberNorm
end AFT.fixedFiberNorm
namespace AFT.integratedFiberNorm
end AFT.integratedFiberNorm
namespace AFT.partialProfileOperator
end AFT.partialProfileOperator
namespace AFT.profileRankOne
end AFT.profileRankOne
namespace AFT.profileSignMap
end AFT.profileSignMap
section
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h101 (reference : Slot → _root_.AFT.FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) : 0 ≤ _root_.AFT.MixedKernel.fiberSq reference kernel fixed values :=
  _root_.AFT.FiniteDist.l2Sq_nonneg _ _
open _root_.P2Mb748e9da renaming h101 → _p2mH101
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h97 (reference : Slot → _root_.AFT.FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) : 0 ≤ _root_.AFT.MixedKernel.fiberNorm reference kernel fixed := norm_nonneg _
open _root_.P2Mb748e9da renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h99 (reference : Slot → _root_.AFT.FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (fixed : Finset Slot) (values : Slot → Color) :
    _root_.AFT.MixedKernel.fiberSq reference kernel fixed values ≤ _root_.AFT.MixedKernel.fiberNorm reference kernel fixed ^ 2 := by
  have h := norm_le_pi_norm (fun values => Real.sqrt (_root_.AFT.MixedKernel.fiberSq reference kernel fixed values)) values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at h
  have hh := sq_le_sq₀ (Real.sqrt_nonneg _) (_p2mH97 reference kernel fixed) |>.mpr h
  rwa [Real.sq_sqrt (_p2mH101 reference kernel fixed values)] at hh
open _root_.P2Mb748e9da renaming h99 → _p2mH99
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h94 (rate : Slot → ℝ) (reference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) :
    0 ≤ _root_.AFT.MixedKernel.activity rate reference kernel := by
  exact mul_nonneg (Finset.prod_nonneg fun slot _ => hrate slot)
    (Finset.sum_nonneg fun fixed _ => mul_nonneg
      (Finset.prod_nonneg fun slot _ => hrate slot) (_p2mH97 reference kernel fixed))
open _root_.P2Mb748e9da renaming h94 → _p2mH94
end
open _root_.P2Mb748e9da renaming h94 → _p2mH94
open _root_.P2Mb748e9da renaming h97 → _p2mH97
open _root_.P2Mb748e9da renaming h99 → _p2mH99
open _root_.P2Mb748e9da renaming h101 → _p2mH101
end AFT.MixedKernel
open _root_.P2Mb748e9da renaming h94 → _p2mH94
open _root_.P2Mb748e9da renaming h97 → _p2mH97
open _root_.P2Mb748e9da renaming h99 → _p2mH99
open _root_.P2Mb748e9da renaming h101 → _p2mH101
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
end
end AFT.MixedKernel
end
open _root_.P2Mb748e9da renaming h94 → _p2mH94
open _root_.P2Mb748e9da renaming h97 → _p2mH97
open _root_.P2Mb748e9da renaming h99 → _p2mH99
open _root_.P2Mb748e9da renaming h101 → _p2mH101
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.inputIteration
end AFT.MixedKernel.inputIteration
section
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h103 (kernel : (Slot → Color) → ℝ) :
    kernel = ∑ point : Slot → Color, kernel point •
      _root_.AFT.MixedKernel.productKernel (fun slot color => if color = point slot then 1 else 0) := by
  funext word
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.AFT.MixedKernel.productKernel]
  have heq (point : Slot → Color) :
      (∏ slot : Slot, if word slot = point slot then (1 : ℝ) else 0) = if word = point then 1 else 0 := by
    by_cases hp : word = point
    · simp [hp]
    · have hd : ∃ slot, word slot ≠ point slot := by
        by_contra hn
        push_neg at hn
        exact hp (funext hn)
      obtain ⟨slot, hs⟩ := hd
      rw [if_neg hp]
      exact Finset.prod_eq_zero (Finset.mem_univ slot) (if_neg hs)
  simp only [heq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
open _root_.P2Mb748e9da renaming h103 → _p2mH103
end
open _root_.P2Mb748e9da renaming h103 → _p2mH103
end AFT.MixedKernel
open _root_.P2Mb748e9da renaming h103 → _p2mH103
end
open _root_.P2Mb748e9da renaming h103 → _p2mH103
namespace AFT.FiniteDist.normalize
end AFT.FiniteDist.normalize
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.GaussianSource.windowGaussian
end AFT.GaussianSource.windowGaussian
namespace AFT.GaussianSource.windowNormalizer
end AFT.GaussianSource.windowNormalizer
namespace AFT.GaussianSource.windowZero
end AFT.GaussianSource.windowZero
section
namespace AFT.GaussianSource
open scoped BigOperators Classical
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h92 (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    0 < _root_.AFT.GaussianSource.retainedFraction width cutoff :=
  div_pos (zero_lt_one.trans_le (_root_.AFT.GaussianSource.windowNormalizer_ge_one width cutoff))
    (zero_lt_one.trans_le (_root_.AFT.GaussianSource.realNormalizer_ge_one width hw))
open _root_.P2Mb748e9da renaming h92 → _p2mH92
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h91 (width : ℝ) (cutoff : ℕ) :
    (∑' z : ℤ, _root_.AFT.GaussianSource.restrictWindow (_root_.AFT.GaussianSource.integerMass width) cutoff z) = _root_.AFT.GaussianSource.retainedFraction width cutoff := by
  rw [tsum_eq_sum (s := Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ))
    (fun z hz => by simp [_root_.AFT.GaussianSource.restrictWindow, hz]), ← Finset.sum_coe_sort]
  have heq (z : _root_.AFT.GaussianSource.Window cutoff) : _root_.AFT.GaussianSource.restrictWindow (_root_.AFT.GaussianSource.integerMass width) cutoff z = _root_.AFT.GaussianSource.integerMass width z := by
    unfold _root_.AFT.GaussianSource.restrictWindow
    split_ifs with hz
    · rfl
    · exact False.elim (hz z.property)
  simp_rw [heq]
  unfold _root_.AFT.GaussianSource.integerMass _root_.AFT.GaussianSource.retainedFraction _root_.AFT.GaussianSource.windowNormalizer
  rw [Finset.sum_div]
open _root_.P2Mb748e9da renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h90 (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z) (cutoff : ℕ) (z : ℤ) :
    0 ≤ _root_.AFT.GaussianSource.restrictWindow mass cutoff z := by unfold _root_.AFT.GaussianSource.restrictWindow; split_ifs; exact hm z; rfl
open _root_.P2Mb748e9da renaming h90 → _p2mH90
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h89 (mass : ℤ → ℝ) (hm : ∀ z, 0 ≤ mass z) (cutoff : ℕ) (z : ℤ) :
    _root_.AFT.GaussianSource.restrictWindow mass cutoff z ≤ mass z := by unfold _root_.AFT.GaussianSource.restrictWindow; split_ifs; rfl; exact hm z
open _root_.P2Mb748e9da renaming h89 → _p2mH89
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h88 (width : ℝ) (cutoff : ℕ) (hw : 0 < width) :
    (∑' z : ℤ, (_root_.AFT.GaussianSource.integerMass width z - _root_.AFT.GaussianSource.restrictWindow (_root_.AFT.GaussianSource.integerMass width) cutoff z)) =
      1 - _root_.AFT.GaussianSource.retainedFraction width cutoff := by
  have hs := _root_.AFT.GaussianSource.summable_integerMass width hw
  have hr := Summable.of_nonneg_of_le (_p2mH90 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hw) cutoff)
    (_p2mH89 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hw) cutoff) hs
  rw [Summable.tsum_sub hs hr, _root_.AFT.GaussianSource.integerMass_sum width hw, _p2mH91]
open _root_.P2Mb748e9da renaming h88 → _p2mH88
end AFT.GaussianSource
open _root_.P2Mb748e9da renaming h88 → _p2mH88
open _root_.P2Mb748e9da renaming h89 → _p2mH89
open _root_.P2Mb748e9da renaming h90 → _p2mH90
open _root_.P2Mb748e9da renaming h91 → _p2mH91
open _root_.P2Mb748e9da renaming h92 → _p2mH92
end
open _root_.P2Mb748e9da renaming h88 → _p2mH88
open _root_.P2Mb748e9da renaming h89 → _p2mH89
open _root_.P2Mb748e9da renaming h90 → _p2mH90
open _root_.P2Mb748e9da renaming h91 → _p2mH91
open _root_.P2Mb748e9da renaming h92 → _p2mH92
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h23 (reference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : Slot → Color → _root_.AFT.FiniteDist Color) :
    (_root_.AFT.FiniteDist.independent reference).mix (fun word => _root_.AFT.FiniteDist.independent (fun slot => kernel slot (word slot))) =
      _root_.AFT.FiniteDist.independent (fun slot => (reference slot).mix (kernel slot)) := by
  ext word
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.independent, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun slot color => (reference slot).weight color * (kernel slot color).weight (word slot))).symm
open _root_.P2Mb748e9da renaming h23 → _p2mH23
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h43 (reference : Slot → _root_.AFT.FiniteDist Color) (first second : Finset Slot)
    (word : Slot → Color) :
    (_root_.AFT.CanonicalMoments.refreshLaw reference first word).mix (_root_.AFT.CanonicalMoments.refreshLaw reference second) =
      _root_.AFT.CanonicalMoments.refreshLaw reference (first ∪ second) word := by
  unfold _root_.AFT.CanonicalMoments.refreshLaw
  rw [_p2mH23 _ (fun slot color => if slot ∈ second then reference slot else _root_.AFT.CanonicalMoments.pointLaw color)]
  congr 1
  funext slot
  by_cases hf : slot ∈ first <;> by_cases hs : slot ∈ second <;> simp [hf, hs]
open _root_.P2Mb748e9da renaming h43 → _p2mH43
set_option maxRecDepth 8192
omit [Fintype Slot] in
theorem _root_.P2Mb748e9da.h6 (law : _root_.AFT.FiniteDist Color) (kernel : Color → _root_.AFT.FiniteDist Color)
    (function : Color → ℝ) :
    (law.mix kernel).expectation function = law.expectation (fun value => (kernel value).expectation function) := by
  unfold _root_.AFT.FiniteDist.expectation
  simp only [_root_.AFT.FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro color _
  ring
open _root_.P2Mb748e9da renaming h6 → _p2mH6
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h47 (reference : Slot → _root_.AFT.FiniteDist Color) (first second : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) :
    _root_.AFT.CanonicalMoments.refresh reference first (_root_.AFT.CanonicalMoments.refresh reference second function) word =
      _root_.AFT.CanonicalMoments.refresh reference (first ∪ second) function word := by
  unfold _root_.AFT.CanonicalMoments.refresh
  rw [← _p2mH6, _p2mH43]
open _root_.P2Mb748e9da renaming h47 → _p2mH47
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h24 (reference : Slot → _root_.AFT.FiniteDist Color) (resampled : Finset Slot) :
    (_root_.AFT.FiniteDist.independent reference).mix (_root_.AFT.CanonicalMoments.refreshLaw reference resampled) = _root_.AFT.FiniteDist.independent reference := by
  unfold _root_.AFT.CanonicalMoments.refreshLaw
  rw [_p2mH23 _ (fun slot color => if slot ∈ resampled then reference slot else _root_.AFT.CanonicalMoments.pointLaw color)]
  congr 1
  funext slot
  by_cases hs : slot ∈ resampled <;> simp [hs]
open _root_.P2Mb748e9da renaming h24 → _p2mH24
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h7 (reference : Slot → _root_.AFT.FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) :
    (_root_.AFT.FiniteDist.independent reference).expectation (_root_.AFT.CanonicalMoments.refresh reference resampled function) =
      (_root_.AFT.FiniteDist.independent reference).expectation function := by
  unfold _root_.AFT.CanonicalMoments.refresh
  rw [← _p2mH6, _p2mH24]
open _root_.P2Mb748e9da renaming h7 → _p2mH7
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h22 (reference : Slot → _root_.AFT.FiniteDist Color) (function : Slot → Color → Color) :
    (_root_.AFT.FiniteDist.independent reference).map (fun word slot => function slot (word slot)) =
      _root_.AFT.FiniteDist.independent (fun slot => (reference slot).map (function slot)) := by
  ext target
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_ite_zero]
  have heq : (∀ slot ∈ (Finset.univ : Finset Slot), function slot (word slot) = target slot) ↔
      (fun slot => function slot (word slot)) = target := by
    simp only [Finset.mem_univ, forall_true_left, funext_iff]
  simp only [heq]
open _root_.P2Mb748e9da renaming h22 → _p2mH22
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h42 (reference : Slot → _root_.AFT.FiniteDist Color) (resampled : Finset Slot)
    (word : Slot → Color) :
    _root_.AFT.CanonicalMoments.refreshLaw reference resampled word =
      (_root_.AFT.FiniteDist.independent reference).map (_root_.AFT.MixedKernel.freeze resampledᶜ word) := by
  have hfreeze : _root_.AFT.MixedKernel.freeze resampledᶜ word =
      (fun integrated slot => (fun color => if slot ∈ resampled then color else word slot) (integrated slot)) := by
    funext integrated slot
    by_cases hs : slot ∈ resampled <;> simp [_root_.AFT.MixedKernel.freeze, hs]
  rw [hfreeze, _p2mH22 reference
    (fun slot color => if slot ∈ resampled then color else word slot)]
  unfold _root_.AFT.CanonicalMoments.refreshLaw
  congr 1
  funext slot
  by_cases hs : slot ∈ resampled
  · simp only [hs, if_true]
    exact (_root_.AFT.CanonicalMoments.map_identity _).symm
  · simp only [hs, if_false]
    exact (_root_.AFT.CanonicalMoments.map_constant _ _).symm
open _root_.P2Mb748e9da renaming h42 → _p2mH42
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h45 (reference : Slot → _root_.AFT.FiniteDist Color) (resampled : Finset Slot)
    (function : (Slot → Color) → ℝ) (word : Slot → Color) :
    _root_.AFT.CanonicalMoments.refresh reference resampled function word =
      (_root_.AFT.FiniteDist.independent reference).expectation (fun integrated =>
        function (_root_.AFT.MixedKernel.freeze resampledᶜ word integrated)) := by
  unfold _root_.AFT.CanonicalMoments.refresh
  rw [_p2mH42, _root_.AFT.FiniteDist.expectation_map]
  rfl
open _root_.P2Mb748e9da renaming h45 → _p2mH45
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h44 (reference : Slot → _root_.AFT.FiniteDist Color) (resampled selected : Finset Slot)
    (function : (Slot → Color) → ℝ) (hdepends : _root_.AFT.Hoeffding.DependsOn selected function) :
    _root_.AFT.Hoeffding.DependsOn (selected \ resampled) (_root_.AFT.CanonicalMoments.refresh reference resampled function) := by
  intro first second hequal
  simp only [_p2mH45, _root_.AFT.FiniteDist.expectation]
  apply Finset.sum_congr rfl
  intro integrated _
  congr 1
  apply hdepends
  intro slot hslot
  by_cases hs : slot ∈ resampled
  · simp [_root_.AFT.MixedKernel.freeze, hs]
  · simp only [_root_.AFT.MixedKernel.freeze, Finset.mem_compl, hs, not_false_eq_true, if_true]
    exact hequal slot (Finset.mem_sdiff.mpr ⟨hslot, hs⟩)
open _root_.P2Mb748e9da renaming h44 → _p2mH44
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h46 (reference : Slot → _root_.AFT.FiniteDist Color) (resampled : Finset Slot)
    (first second : (Slot → Color) → ℝ) (hfixed : _root_.AFT.Hoeffding.DependsOn resampledᶜ second)
    (word : Slot → Color) :
    _root_.AFT.CanonicalMoments.refresh reference resampled (fun values => first values * second values) word =
      _root_.AFT.CanonicalMoments.refresh reference resampled first word * second word := by
  have hs (integrated : Slot → Color) : second (_root_.AFT.MixedKernel.freeze resampledᶜ word integrated) = second word := by
    apply hfixed
    intro slot hslot
    simp [_root_.AFT.MixedKernel.freeze, hslot]
  simp only [_p2mH45, hs, _root_.AFT.FiniteDist.expectation, Finset.sum_mul, mul_assoc]
open _root_.P2Mb748e9da renaming h46 → _p2mH46
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h6 → _p2mH6
open _root_.P2Mb748e9da renaming h7 → _p2mH7
open _root_.P2Mb748e9da renaming h22 → _p2mH22
open _root_.P2Mb748e9da renaming h23 → _p2mH23
open _root_.P2Mb748e9da renaming h24 → _p2mH24
open _root_.P2Mb748e9da renaming h42 → _p2mH42
open _root_.P2Mb748e9da renaming h43 → _p2mH43
open _root_.P2Mb748e9da renaming h44 → _p2mH44
open _root_.P2Mb748e9da renaming h45 → _p2mH45
open _root_.P2Mb748e9da renaming h46 → _p2mH46
open _root_.P2Mb748e9da renaming h47 → _p2mH47
end
open _root_.P2Mb748e9da renaming h6 → _p2mH6
open _root_.P2Mb748e9da renaming h7 → _p2mH7
open _root_.P2Mb748e9da renaming h22 → _p2mH22
open _root_.P2Mb748e9da renaming h23 → _p2mH23
open _root_.P2Mb748e9da renaming h24 → _p2mH24
open _root_.P2Mb748e9da renaming h42 → _p2mH42
open _root_.P2Mb748e9da renaming h43 → _p2mH43
open _root_.P2Mb748e9da renaming h44 → _p2mH44
open _root_.P2Mb748e9da renaming h45 → _p2mH45
open _root_.P2Mb748e9da renaming h46 → _p2mH46
open _root_.P2Mb748e9da renaming h47 → _p2mH47
namespace AFT.CanonicalMoments.pointLaw
end AFT.CanonicalMoments.pointLaw
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
set_option maxRecDepth 8192
omit [Fintype Slot] [Fintype Color] in
theorem _root_.P2Mb748e9da.h3 (small large : Finset Slot) (function : (Slot → Color) → ℝ)
    (hsmall : _root_.AFT.Hoeffding.DependsOn small function) (hsubset : small ⊆ large) :
    _root_.AFT.Hoeffding.DependsOn large function := by
  intro first second hequal
  exact hsmall first second (fun slot hslot => hequal slot (hsubset hslot))
open _root_.P2Mb748e9da renaming h3 → _p2mH3
set_option maxRecDepth 8192
omit [Fintype Slot] [Fintype Color] in
theorem _root_.P2Mb748e9da.h4 (selected : Finset Slot) (function : (Slot → Color) → ℝ)
    (hdepends : _root_.AFT.Hoeffding.DependsOn selected function) :
    _root_.AFT.Hoeffding.DependsOn selected (fun word => function word ^ 2) := by
  intro first second hequal
  dsimp only
  rw [hdepends first second hequal]
open _root_.P2Mb748e9da renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h48 (reference : Slot → _root_.AFT.FiniteDist Color)
    (resampled selected : Finset Slot) (function : (Slot → Color) → ℝ)
    (hdepends : _root_.AFT.Hoeffding.DependsOn selected function) (word : Slot → Color) :
    _root_.AFT.CanonicalMoments.refresh reference resampled (fun values => function values ^ 2) word =
      _root_.AFT.MixedKernel.fiberSq reference function (selected \ resampled) word := by
  rw [_p2mH45]
  unfold _root_.AFT.MixedKernel.fiberSq _root_.AFT.FiniteDist.l2Sq _root_.AFT.FiniteDist.expectation
  apply Finset.sum_congr rfl
  intro integrated _
  dsimp only
  congr 2
  apply hdepends
  intro slot hslot
  by_cases hs : slot ∈ resampled <;> simp [_root_.AFT.MixedKernel.freeze, hslot, hs]
open _root_.P2Mb748e9da renaming h48 → _p2mH48
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h19 (reference : Slot → _root_.AFT.FiniteDist Color)
    (active selected ending : Finset Slot) (kernel input : (Slot → Color) → ℝ)
    (hkernel : _root_.AFT.Hoeffding.DependsOn selected kernel) (hinput : _root_.AFT.Hoeffding.DependsOn active input) :
    (_root_.AFT.FiniteDist.independent reference).l2Sq
      (_root_.AFT.CanonicalMoments.refresh reference ending (fun word => kernel word * input word)) ≤
      _root_.AFT.MixedKernel.fiberNorm reference kernel (selected \ ((selected \ active) ∪ ending)) ^ 2 *
        (_root_.AFT.FiniteDist.independent reference).l2Sq input := by
  let fresh := selected \ active
  let first := _root_.AFT.CanonicalMoments.refresh reference ending (fun word => kernel word ^ 2)
  let second := _root_.AFT.CanonicalMoments.refresh reference ending (fun word => input word ^ 2)
  let bound := _root_.AFT.MixedKernel.fiberNorm reference kernel (selected \ (fresh ∪ ending)) ^ 2
  have hsecond (word : Slot → Color) : 0 ≤ second word :=
    Finset.sum_nonneg fun value _ => mul_nonneg ((_root_.AFT.CanonicalMoments.refreshLaw reference ending word).nonneg _) (sq_nonneg _)
  have hdepends : _root_.AFT.Hoeffding.DependsOn freshᶜ second := by
    apply _p2mH3 (active \ ending) freshᶜ second
      (_p2mH44 reference ending active _ (_p2mH4 active input hinput))
    intro slot hslot
    simp only [fresh, Finset.mem_compl, Finset.mem_sdiff, not_and]
    intro _
    exact not_not_intro (Finset.mem_sdiff.mp hslot).1
  have hfirst (word : Slot → Color) : _root_.AFT.CanonicalMoments.refresh reference fresh first word ≤ bound := by
    rw [_p2mH47, _p2mH48 reference _ selected kernel hkernel]
    exact _p2mH99 reference kernel _ word
  have hpoint (word : Slot → Color) :
      _root_.AFT.CanonicalMoments.refresh reference ending (fun values => kernel values * input values) word ^ 2 ≤ first word * second word :=
    _root_.AFT.CanonicalMoments.expectation_mul_sq_le (_root_.AFT.CanonicalMoments.refreshLaw reference ending word) kernel input
  have hcs : (_root_.AFT.FiniteDist.independent reference).l2Sq
      (_root_.AFT.CanonicalMoments.refresh reference ending (fun word => kernel word * input word)) ≤
      (_root_.AFT.FiniteDist.independent reference).expectation (fun word => first word * second word) :=
    Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left (hpoint word)
      ((_root_.AFT.FiniteDist.independent reference).nonneg word)
  apply hcs.trans
  rw [← _p2mH7 reference fresh (fun word => first word * second word)]
  have heq : _root_.AFT.CanonicalMoments.refresh reference fresh (fun word => first word * second word) =
      (fun word => _root_.AFT.CanonicalMoments.refresh reference fresh first word * second word) :=
    funext (_p2mH46 reference fresh first second hdepends)
  rw [heq]
  have hh : (_root_.AFT.FiniteDist.independent reference).expectation
      (fun word => _root_.AFT.CanonicalMoments.refresh reference fresh first word * second word) ≤
      (_root_.AFT.FiniteDist.independent reference).expectation (fun word => bound * second word) :=
    Finset.sum_le_sum fun word _ => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hfirst word) (hsecond word)) ((_root_.AFT.FiniteDist.independent reference).nonneg word)
  apply hh.trans_eq
  have hfactor : (_root_.AFT.FiniteDist.independent reference).expectation (fun word => bound * second word) =
      bound * (_root_.AFT.FiniteDist.independent reference).expectation second := by
    unfold _root_.AFT.FiniteDist.expectation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro word _
    ring
  rw [hfactor, _p2mH7]
  rfl
open _root_.P2Mb748e9da renaming h19 → _p2mH19
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h3 → _p2mH3
open _root_.P2Mb748e9da renaming h4 → _p2mH4
open _root_.P2Mb748e9da renaming h19 → _p2mH19
open _root_.P2Mb748e9da renaming h48 → _p2mH48
end
open _root_.P2Mb748e9da renaming h3 → _p2mH3
open _root_.P2Mb748e9da renaming h4 → _p2mH4
open _root_.P2Mb748e9da renaming h19 → _p2mH19
open _root_.P2Mb748e9da renaming h48 → _p2mH48
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Label Color : Type*} [Fintype Label] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h13 (reference : Label → _root_.AFT.FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, _root_.AFT.Hoeffding.DependsOn (scope index) (kernel index)) (count : ℕ) :
    _root_.AFT.Hoeffding.DependsOn (_root_.AFT.CanonicalMoments.graphActive scope ending count) (_root_.AFT.CanonicalMoments.graphMessage reference ending kernel count) := by
  induction count with
  | zero => intro first second _; rfl
  | succ index ih =>
    apply _p2mH44
    intro first second hequal
    dsimp only
    rw [hkernel index first second (fun label hlabel => hequal label (Finset.mem_union_left _ hlabel)),
      ih first second (fun label hlabel => hequal label (Finset.mem_union_right _ hlabel))]
open _root_.P2Mb748e9da renaming h13 → _p2mH13
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h14 (reference : Label → _root_.AFT.FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, _root_.AFT.Hoeffding.DependsOn (scope index) (kernel index)) (count : ℕ) :
    (_root_.AFT.FiniteDist.independent reference).l2Sq (_root_.AFT.CanonicalMoments.graphMessage reference ending kernel count) ≤
      ∏ index ∈ Finset.range count, _root_.AFT.MixedKernel.fiberNorm reference (kernel index) (_root_.AFT.CanonicalMoments.graphFixed scope ending index) ^ 2 := by
  induction count with
  | zero =>
    simp only [_root_.AFT.CanonicalMoments.graphMessage, _root_.AFT.FiniteDist.l2Sq, _root_.AFT.FiniteDist.expectation, one_pow, mul_one,
      _root_.AFT.FiniteDist.sum_one, Finset.range_zero, Finset.prod_empty, le_refl]
  | succ index ih =>
    have h := _p2mH19 reference (_root_.AFT.CanonicalMoments.graphActive scope ending index) (scope index) (ending index)
      (kernel index) (_root_.AFT.CanonicalMoments.graphMessage reference ending kernel index) (hkernel index)
      (_p2mH13 reference scope ending kernel hkernel index)
    have hh := mul_le_mul_of_nonneg_left ih
      (sq_nonneg (_root_.AFT.MixedKernel.fiberNorm reference (kernel index) (_root_.AFT.CanonicalMoments.graphFixed scope ending index)))
    apply h.trans
    rw [Finset.prod_range_succ]
    simpa only [_root_.AFT.CanonicalMoments.graphFixed, mul_comm] using hh
open _root_.P2Mb748e9da renaming h14 → _p2mH14
set_option maxRecDepth 8192
omit [Fintype Color] in
theorem _root_.P2Mb748e9da.h16 (scope ending : ℕ → Finset Label)
    (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, _root_.AFT.Hoeffding.DependsOn (scope index) (kernel index))
    (length index : ℕ) (hending : ∀ later, index < later → later < length →
      Disjoint (ending index) (scope later)) :
    _root_.AFT.Hoeffding.DependsOn (ending index)ᶜ (_root_.AFT.CanonicalMoments.graphSuffix kernel length (index + 1)) := by
  intro first second hequal
  apply Finset.prod_congr rfl
  intro later hlater
  apply hkernel later
  intro label hlabel
  apply hequal label
  exact Finset.mem_compl.mpr (fun he =>
    Finset.disjoint_left.mp (hending later (by have := (Finset.mem_Ico.mp hlater).1; omega)
      (Finset.mem_Ico.mp hlater).2) he hlabel)
open _root_.P2Mb748e9da renaming h16 → _p2mH16
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h15 (reference : Label → _root_.AFT.FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, _root_.AFT.Hoeffding.DependsOn (scope index) (kernel index)) (length : ℕ)
    (hending : ∀ index later, index < later → later < length → Disjoint (ending index) (scope later)) :
    (_root_.AFT.FiniteDist.independent reference).expectation (_root_.AFT.CanonicalMoments.graphMessage reference ending kernel length) =
      (_root_.AFT.FiniteDist.independent reference).expectation (fun word => ∏ index ∈ Finset.range length, kernel index word) := by
  have hinvariant (count : ℕ) (hcount : count ≤ length) :
      (_root_.AFT.FiniteDist.independent reference).expectation (fun word => _root_.AFT.CanonicalMoments.graphMessage reference ending kernel count word *
        _root_.AFT.CanonicalMoments.graphSuffix kernel length count word) =
      (_root_.AFT.FiniteDist.independent reference).expectation (fun word => ∏ index ∈ Finset.range length, kernel index word) := by
    induction count with
    | zero => simp only [_root_.AFT.CanonicalMoments.graphMessage, _root_.AFT.CanonicalMoments.graphSuffix, Nat.Ico_zero_eq_range, one_mul]
    | succ index ih =>
      have hi : index < length := by omega
      have hfixed := _p2mH16 scope ending kernel hkernel length index (hending index)
      have heq (word : Label → Color) : _root_.AFT.CanonicalMoments.graphMessage reference ending kernel (index + 1) word *
          _root_.AFT.CanonicalMoments.graphSuffix kernel length (index + 1) word =
          _root_.AFT.CanonicalMoments.refresh reference (ending index) (fun values => _root_.AFT.CanonicalMoments.graphMessage reference ending kernel index values *
            _root_.AFT.CanonicalMoments.graphSuffix kernel length index values) word := by
        rw [_root_.AFT.CanonicalMoments.graphMessage, ← _p2mH46 reference (ending index) _ _ hfixed]
        congr 1
        funext values
        unfold _root_.AFT.CanonicalMoments.graphSuffix
        rw [Finset.prod_eq_prod_Ico_succ_bot hi]
        ring
      simp_rw [heq]
      rw [_p2mH7]
      exact ih (by omega)
  simpa only [_root_.AFT.CanonicalMoments.graphSuffix, Finset.Ico_self, Finset.prod_empty, mul_one] using hinvariant length le_rfl
open _root_.P2Mb748e9da renaming h15 → _p2mH15
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h18 (reference : Label → _root_.AFT.FiniteDist Color)
    (scope ending : ℕ → Finset Label) (kernel : ℕ → (Label → Color) → ℝ)
    (hkernel : ∀ index, _root_.AFT.Hoeffding.DependsOn (scope index) (kernel index)) (length : ℕ)
    (hending : ∀ index later, index < later → later < length → Disjoint (ending index) (scope later)) :
    (_root_.AFT.FiniteDist.independent reference).expectation (fun word => ∏ index ∈ Finset.range length, kernel index word) ^ 2 ≤
      ∏ index ∈ Finset.range length, _root_.AFT.MixedKernel.fiberNorm reference (kernel index) (_root_.AFT.CanonicalMoments.graphFixed scope ending index) ^ 2 := by
  rw [← _p2mH15 reference scope ending kernel hkernel length hending]
  have h := _root_.AFT.CanonicalMoments.expectation_mul_sq_le (_root_.AFT.FiniteDist.independent reference)
    (_root_.AFT.CanonicalMoments.graphMessage reference ending kernel length) (fun _ => 1)
  have hone : (_root_.AFT.FiniteDist.independent reference).l2Sq (fun _ => (1 : ℝ)) = 1 := by
    simp [_root_.AFT.FiniteDist.l2Sq, _root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.sum_one]
  simp only [mul_one, hone] at h
  exact h.trans (_p2mH14 reference scope ending kernel hkernel length)
open _root_.P2Mb748e9da renaming h18 → _p2mH18
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h13 → _p2mH13
open _root_.P2Mb748e9da renaming h14 → _p2mH14
open _root_.P2Mb748e9da renaming h15 → _p2mH15
open _root_.P2Mb748e9da renaming h16 → _p2mH16
open _root_.P2Mb748e9da renaming h18 → _p2mH18
end
open _root_.P2Mb748e9da renaming h13 → _p2mH13
open _root_.P2Mb748e9da renaming h14 → _p2mH14
open _root_.P2Mb748e9da renaming h15 → _p2mH15
open _root_.P2Mb748e9da renaming h16 → _p2mH16
open _root_.P2Mb748e9da renaming h18 → _p2mH18
namespace AFT.CanonicalMoments.graphActive
end AFT.CanonicalMoments.graphActive
namespace AFT.CanonicalMoments.graphActive.match_1
end AFT.CanonicalMoments.graphActive.match_1
namespace AFT.CanonicalMoments.graphFixed
end AFT.CanonicalMoments.graphFixed
namespace AFT.CanonicalMoments.graphMessage
end AFT.CanonicalMoments.graphMessage
namespace AFT.CanonicalMoments.graphSuffix
end AFT.CanonicalMoments.graphSuffix
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Label : Type*} [Fintype Label] {count : ℕ}
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h49 (scope : Fin count → Finset Label) (index later : ℕ)
    (hbefore : index < later) (hlater : later < count) :
    Disjoint (_root_.AFT.CanonicalMoments.scopeEnding scope index) (_root_.AFT.CanonicalMoments.scopeAt scope later) := by
  apply Finset.disjoint_left.mpr
  intro label hend hl
  have hnot := (Finset.mem_sdiff.mp hend).2
  apply hnot
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ⟨⟨later, hlater⟩, by dsimp only; omega, ?_⟩⟩
  simpa only [_root_.AFT.CanonicalMoments.scopeAt, dif_pos hlater] using hl
open _root_.P2Mb748e9da renaming h49 → _p2mH49
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h50 (scope : Fin count → Finset Label) (index : ℕ) (hi : index < count) :
    _root_.AFT.CanonicalMoments.scopePrefix scope (index + 1) = _root_.AFT.CanonicalMoments.scopePrefix scope index ∪ _root_.AFT.CanonicalMoments.scopeAt scope index := by
  ext label
  simp only [_root_.AFT.CanonicalMoments.scopePrefix, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.AFT.CanonicalMoments.scopeAt, dif_pos hi, Finset.mem_union]
  constructor
  · rintro ⟨copy, hcopy, hlabel⟩
    by_cases hlt : copy.val < index
    · exact Or.inl ⟨copy, hlt, hlabel⟩
    · right
      have heq : copy = ⟨index, hi⟩ := Fin.ext (by dsimp only; omega)
      simpa only [heq] using hlabel
  · rintro (⟨copy, hcopy, hlabel⟩ | hlabel)
    · exact ⟨copy, by omega, hlabel⟩
    · exact ⟨⟨index, hi⟩, by dsimp only; omega, hlabel⟩
open _root_.P2Mb748e9da renaming h50 → _p2mH50
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h51 (scope : Fin count → Finset Label) (index : ℕ) (hi : index < count) :
    _root_.AFT.CanonicalMoments.scopeSuffix scope index = _root_.AFT.CanonicalMoments.scopeAt scope index ∪ _root_.AFT.CanonicalMoments.scopeSuffix scope (index + 1) := by
  ext label
  simp only [_root_.AFT.CanonicalMoments.scopeSuffix, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.AFT.CanonicalMoments.scopeAt, dif_pos hi, Finset.mem_union]
  constructor
  · rintro ⟨copy, hcopy, hlabel⟩
    by_cases heq : copy.val = index
    · left
      have hc : copy = ⟨index, hi⟩ := Fin.ext heq
      simpa only [hc] using hlabel
    · exact Or.inr ⟨copy, by omega, hlabel⟩
  · rintro (hlabel | ⟨copy, hcopy, hlabel⟩)
    · exact ⟨⟨index, hi⟩, le_rfl, hlabel⟩
    · exact ⟨copy, by omega, hlabel⟩
open _root_.P2Mb748e9da renaming h51 → _p2mH51
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h11 (scope : Fin count → Finset Label)
    (index : ℕ) (hi : index ≤ count) :
    _root_.AFT.CanonicalMoments.graphActive (_root_.AFT.CanonicalMoments.scopeAt scope) (_root_.AFT.CanonicalMoments.scopeEnding scope) index = _root_.AFT.CanonicalMoments.scopePrefix scope index ∩ _root_.AFT.CanonicalMoments.scopeSuffix scope index := by
  induction index with
  | zero => simp [_root_.AFT.CanonicalMoments.graphActive, _root_.AFT.CanonicalMoments.scopePrefix]
  | succ index ih =>
    have hlt : index < count := by omega
    rw [_root_.AFT.CanonicalMoments.graphActive, ih (by omega), _p2mH50 scope index hlt, _p2mH51 scope index hlt]
    ext label
    simp only [_root_.AFT.CanonicalMoments.scopeEnding, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
    tauto
open _root_.P2Mb748e9da renaming h11 → _p2mH11
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h12 (scope : Fin count → Finset Label) (index : ℕ) (hi : index < count) :
    _root_.AFT.CanonicalMoments.graphFixed (_root_.AFT.CanonicalMoments.scopeAt scope) (_root_.AFT.CanonicalMoments.scopeEnding scope) index =
      _root_.AFT.CanonicalMoments.scopeAt scope index ∩ _root_.AFT.CanonicalMoments.scopePrefix scope index ∩ _root_.AFT.CanonicalMoments.scopeSuffix scope (index + 1) := by
  rw [_root_.AFT.CanonicalMoments.graphFixed, _p2mH11 scope index hi.le, _p2mH51 scope index hi]
  ext label
  simp only [_root_.AFT.CanonicalMoments.scopeEnding, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
  tauto
open _root_.P2Mb748e9da renaming h12 → _p2mH12
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h10 (reference : Label → _root_.AFT.FiniteDist Color)
    (scope : Fin count → Finset Label) (kernel : Fin count → (Label → Color) → ℝ)
    (hkernel : ∀ copy, _root_.AFT.Hoeffding.DependsOn (scope copy) (kernel copy)) :
    (_root_.AFT.FiniteDist.independent reference).expectation (fun word => ∏ copy, kernel copy word) ^ 2 ≤
      ∏ copy, _root_.AFT.MixedKernel.fiberNorm reference (kernel copy)
        (scope copy ∩ _root_.AFT.CanonicalMoments.scopePrefix scope copy.val ∩ _root_.AFT.CanonicalMoments.scopeSuffix scope (copy.val + 1)) ^ 2 := by
  have hdepends (index : ℕ) : _root_.AFT.Hoeffding.DependsOn (_root_.AFT.CanonicalMoments.scopeAt scope index) (_root_.AFT.CanonicalMoments.kernelAt kernel index) := by
    by_cases hi : index < count
    · simpa only [_root_.AFT.CanonicalMoments.scopeAt, _root_.AFT.CanonicalMoments.kernelAt, dif_pos hi] using hkernel ⟨index, hi⟩
    · intro first second _
      simp only [_root_.AFT.CanonicalMoments.kernelAt, dif_neg hi]
  have h := _p2mH18 reference (_root_.AFT.CanonicalMoments.scopeAt scope) (_root_.AFT.CanonicalMoments.scopeEnding scope)
    (_root_.AFT.CanonicalMoments.kernelAt kernel) hdepends count (_p2mH49 scope)
  simp only [Finset.prod_range] at h
  have hfixed (copy : Fin count) : _root_.AFT.CanonicalMoments.graphFixed (_root_.AFT.CanonicalMoments.scopeAt scope) (_root_.AFT.CanonicalMoments.scopeEnding scope) copy.val =
      scope copy ∩ _root_.AFT.CanonicalMoments.scopePrefix scope copy.val ∩ _root_.AFT.CanonicalMoments.scopeSuffix scope (copy.val + 1) := by
    rw [_p2mH12 scope copy.val copy.isLt]
    simp only [_root_.AFT.CanonicalMoments.scopeAt, dif_pos copy.isLt]
  simpa only [_root_.AFT.CanonicalMoments.kernelAt, dif_pos (Fin.isLt _), hfixed] using h
open _root_.P2Mb748e9da renaming h10 → _p2mH10
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h10 → _p2mH10
open _root_.P2Mb748e9da renaming h11 → _p2mH11
open _root_.P2Mb748e9da renaming h12 → _p2mH12
open _root_.P2Mb748e9da renaming h49 → _p2mH49
open _root_.P2Mb748e9da renaming h50 → _p2mH50
open _root_.P2Mb748e9da renaming h51 → _p2mH51
end
open _root_.P2Mb748e9da renaming h10 → _p2mH10
open _root_.P2Mb748e9da renaming h11 → _p2mH11
open _root_.P2Mb748e9da renaming h12 → _p2mH12
open _root_.P2Mb748e9da renaming h49 → _p2mH49
open _root_.P2Mb748e9da renaming h50 → _p2mH50
open _root_.P2Mb748e9da renaming h51 → _p2mH51
namespace AFT.CanonicalMoments.NoSingleton
end AFT.CanonicalMoments.NoSingleton
namespace AFT.CanonicalMoments.placedKernel
end AFT.CanonicalMoments.placedKernel
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
variable {Slot Pool Copy : Type*} [Fintype Slot] [Fintype Pool] [Fintype Copy]
set_option maxRecDepth 8192
omit [Fintype Pool] in
theorem _root_.P2Mb748e9da.h1 (used : ℕ)
    (pattern : _root_.AFT.CanonicalMoments.PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used)
    (occurrence : Copy × Slot) :
    (_root_.AFT.CanonicalMoments.collisionCode used pattern).1 ((_root_.AFT.CanonicalMoments.collisionCode used pattern).2 occurrence) =
      pattern.val occurrence.1 occurrence.2 := by
  simp [_root_.AFT.CanonicalMoments.collisionCode]
open _root_.P2Mb748e9da renaming h1 → _p2mH1
set_option maxRecDepth 8192
omit [Fintype Pool] in
theorem _root_.P2Mb748e9da.h0 (used : ℕ) :
    Function.Injective (_root_.AFT.CanonicalMoments.collisionCode (Slot := Slot) (Pool := Pool) (Copy := Copy) used) := by
  intro first second h
  apply Subtype.ext
  funext copy
  apply Function.Embedding.ext
  intro slot
  have hh := congrArg (fun code : (Fin used ↪ Pool) × (Copy × Slot → Fin used) =>
    code.1 (code.2 (copy, slot))) h
  simpa only [_p2mH1] using hh
open _root_.P2Mb748e9da renaming h0 → _p2mH0
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h36 (used : ℕ) :
    Fintype.card (_root_.AFT.CanonicalMoments.PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) ≤
      (Fintype.card Pool).descFactorial used * used ^ (Fintype.card Copy * Fintype.card Slot) := by
  have hh := Fintype.card_le_of_injective _ (_p2mH0 (Slot := Slot) (Pool := Pool) (Copy := Copy) used)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_embedding_eq] using hh
open _root_.P2Mb748e9da renaming h36 → _p2mH36
set_option maxRecDepth 8192
omit [Fintype Pool] in
theorem _root_.P2Mb748e9da.h66 (pattern : Copy → Slot ↪ Pool) :
    (_root_.AFT.CanonicalMoments.usedLabels pattern).card ≤ Fintype.card Copy * Fintype.card Slot := by
  simpa only [_root_.AFT.CanonicalMoments.usedLabels, Finset.card_univ, Fintype.card_prod] using
    Finset.card_image_le (s := Finset.univ) (f := fun occurrence : Copy × Slot => pattern occurrence.1 occurrence.2)
open _root_.P2Mb748e9da renaming h66 → _p2mH66
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h37 (used : ℕ) :
    Fintype.card (_root_.AFT.CanonicalMoments.PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) ≤
      (Fintype.card Pool).descFactorial used *
        (Fintype.card Copy * Fintype.card Slot) ^ (Fintype.card Copy * Fintype.card Slot) := by
  by_cases hle : used ≤ Fintype.card Copy * Fintype.card Slot
  · exact (_p2mH36 used).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hle _))
  · have hempty : IsEmpty (_root_.AFT.CanonicalMoments.PatternsWithLabels (Slot := Slot) (Pool := Pool) (Copy := Copy) used) :=
      ⟨fun pattern => hle (pattern.property ▸ _p2mH66 pattern.val)⟩
    rw [Fintype.card_eq_zero]
    exact Nat.zero_le _
open _root_.P2Mb748e9da renaming h37 → _p2mH37
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h28 (used : ℕ) :
    (Finset.univ.filter (fun pattern : Copy → Slot ↪ Pool =>
      _root_.AFT.CanonicalMoments.NoSingleton pattern ∧ (_root_.AFT.CanonicalMoments.usedLabels pattern).card = used)).card ≤
      (Fintype.card Pool).descFactorial used *
        (Fintype.card Copy * Fintype.card Slot) ^ (Fintype.card Copy * Fintype.card Slot) := by
  apply (Finset.card_le_card (show
    Finset.univ.filter (fun pattern : Copy → Slot ↪ Pool => _root_.AFT.CanonicalMoments.NoSingleton pattern ∧ (_root_.AFT.CanonicalMoments.usedLabels pattern).card = used) ⊆
    Finset.univ.filter (fun pattern : Copy → Slot ↪ Pool => (_root_.AFT.CanonicalMoments.usedLabels pattern).card = used) from
      fun _ h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.2⟩)).trans
  simpa only [← Fintype.card_subtype] using _p2mH37 (Slot := Slot) (Pool := Pool) (Copy := Copy) used
open _root_.P2Mb748e9da renaming h28 → _p2mH28
set_option maxRecDepth 8192
omit [Fintype Slot] [Fintype Pool] [Fintype Copy] in
theorem _root_.P2Mb748e9da.h5 (population order : ℕ) (hlarge : 2 * order ≤ population) :
    ((population : ℝ) / 2) ^ order ≤ (population.descFactorial order : ℝ) := by
  have hsub : order ≤ population + 1 := by omega
  have hbase : (population : ℝ) / 2 ≤ (population + 1 - order : ℕ) := by
    rw [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_one]
    have hh : (2 : ℝ) * order ≤ population := by exact_mod_cast hlarge
    linarith
  exact (pow_le_pow_left₀ (by positivity) hbase order).trans
    (by exact_mod_cast Nat.pow_sub_le_descFactorial population order)
open _root_.P2Mb748e9da renaming h5 → _p2mH5
set_option maxRecDepth 8192
omit [Fintype Slot] [Fintype Pool] [Fintype Copy] in
theorem _root_.P2Mb748e9da.h2 (population order power used : ℕ)
    (hpopulation : 0 < population) (hlarge : 2 * order ≤ population)
    (hused : used ≤ power * order) :
    (population.descFactorial used : ℝ) * (population : ℝ) ^ (power * order - used) /
        (population.descFactorial order : ℝ) ^ power ≤ (2 : ℝ) ^ (power * order) := by
  have hpos : (0 : ℝ) < population.descFactorial order := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : order ≤ population))
  have hnum : (population.descFactorial used : ℝ) * (population : ℝ) ^ (power * order - used) ≤
      (population : ℝ) ^ (power * order) := by
    calc
      _ ≤ (population : ℝ) ^ used * (population : ℝ) ^ (power * order - used) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.descFactorial_le_pow population used) (by positivity)
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le hused]
  have hden := pow_le_pow_left₀ (by positivity : 0 ≤ ((population : ℝ) / 2) ^ order)
    (_p2mH5 population order hlarge) power
  rw [← pow_mul, Nat.mul_comm order power, div_pow] at hden
  have hden' : (population : ℝ) ^ (power * order) ≤
      (2 : ℝ) ^ (power * order) * (population.descFactorial order : ℝ) ^ power := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (power * order))).mp hden
    simpa only [mul_comm] using hh
  exact (div_le_iff₀ (pow_pos hpos _)).mpr (hnum.trans hden')
open _root_.P2Mb748e9da renaming h2 → _p2mH2
end
open _root_.P2Mb748e9da renaming h0 → _p2mH0
open _root_.P2Mb748e9da renaming h1 → _p2mH1
open _root_.P2Mb748e9da renaming h2 → _p2mH2
open _root_.P2Mb748e9da renaming h5 → _p2mH5
open _root_.P2Mb748e9da renaming h28 → _p2mH28
open _root_.P2Mb748e9da renaming h36 → _p2mH36
open _root_.P2Mb748e9da renaming h37 → _p2mH37
open _root_.P2Mb748e9da renaming h66 → _p2mH66
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h0 → _p2mH0
open _root_.P2Mb748e9da renaming h1 → _p2mH1
open _root_.P2Mb748e9da renaming h2 → _p2mH2
open _root_.P2Mb748e9da renaming h5 → _p2mH5
open _root_.P2Mb748e9da renaming h28 → _p2mH28
open _root_.P2Mb748e9da renaming h36 → _p2mH36
open _root_.P2Mb748e9da renaming h37 → _p2mH37
open _root_.P2Mb748e9da renaming h66 → _p2mH66
end
open _root_.P2Mb748e9da renaming h0 → _p2mH0
open _root_.P2Mb748e9da renaming h1 → _p2mH1
open _root_.P2Mb748e9da renaming h2 → _p2mH2
open _root_.P2Mb748e9da renaming h5 → _p2mH5
open _root_.P2Mb748e9da renaming h28 → _p2mH28
open _root_.P2Mb748e9da renaming h36 → _p2mH36
open _root_.P2Mb748e9da renaming h37 → _p2mH37
open _root_.P2Mb748e9da renaming h66 → _p2mH66
namespace AFT.CanonicalMoments.collisionCode
end AFT.CanonicalMoments.collisionCode
namespace AFT.CanonicalMoments.usedLabels
end AFT.CanonicalMoments.usedLabels
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
variable {Copy Label : Type*} [Fintype Copy] [LinearOrder Copy] [Fintype Label]
set_option maxRecDepth 8192
omit [LinearOrder Copy] in
theorem _root_.P2Mb748e9da.h52 (scope : Copy → Finset Label) :
    (∑ copy, (scope copy).card) = ∑ label, (_root_.AFT.CanonicalMoments.occurrenceCopies scope label).card := by
  have hcount (copy : Copy) : (scope copy).card = ∑ label : Label, if label ∈ scope copy then 1 else 0 := by
    simp
  simp_rw [hcount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro label _
  simp only [_root_.AFT.CanonicalMoments.occurrenceCopies, Finset.card_filter]
open _root_.P2Mb748e9da renaming h52 → _p2mH52
set_option maxRecDepth 8192
omit [Fintype Label] in
theorem _root_.P2Mb748e9da.h26 (scope : Copy → Finset Label) (label : Label)
    (hne : (_root_.AFT.CanonicalMoments.occurrenceCopies scope label).Nonempty) :
    _root_.AFT.CanonicalMoments.occurrenceCopies (_root_.AFT.CanonicalMoments.middleScopes scope) label =
      ((_root_.AFT.CanonicalMoments.occurrenceCopies scope label).erase ((_root_.AFT.CanonicalMoments.occurrenceCopies scope label).min' hne)).erase
        ((_root_.AFT.CanonicalMoments.occurrenceCopies scope label).max' hne) := by
  ext copy
  simp only [_root_.AFT.CanonicalMoments.occurrenceCopies, _root_.AFT.CanonicalMoments.middleScopes, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hmem, ⟨before, hbefore, hbeforeMem⟩, ⟨after, hafter, hafterMem⟩⟩
    have hmin := Finset.min'_le (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) before
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbeforeMem⟩)
    have hmax := Finset.le_max' (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) after
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hafterMem⟩)
    exact ⟨ne_of_lt (hafter.trans_le hmax), ne_of_gt (hmin.trans_lt hbefore), hmem⟩
  · rintro ⟨hmax, hmin, hmem⟩
    have hcopy : copy ∈ _root_.AFT.CanonicalMoments.occurrenceCopies scope label := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
    have hminle := Finset.min'_le (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) copy hcopy
    have hmaxle := Finset.le_max' (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) copy hcopy
    refine ⟨hmem, ?_, ?_⟩
    · exact ⟨_, lt_of_le_of_ne hminle (Ne.symm hmin), (Finset.mem_filter.mp (Finset.min'_mem _ hne)).2⟩
    · exact ⟨_, lt_of_le_of_ne hmaxle hmax, (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2⟩
open _root_.P2Mb748e9da renaming h26 → _p2mH26
set_option maxRecDepth 8192
omit [LinearOrder Copy] [Fintype Label] in
theorem _root_.P2Mb748e9da.h29 (scope : Copy → Finset Label) (hscope : _root_.AFT.CanonicalMoments.NoSingletonScopes scope)
    (label : Label) (hlabel : label ∈ _root_.AFT.CanonicalMoments.scopeUnion scope) : 2 ≤ (_root_.AFT.CanonicalMoments.occurrenceCopies scope label).card := by
  obtain ⟨copy, _, hcopy⟩ := Finset.mem_biUnion.mp hlabel
  obtain ⟨other, hother, hmem⟩ := hscope copy label hcopy
  apply Finset.one_lt_card.mpr
  exact ⟨copy, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcopy⟩,
    other, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, Ne.symm hother⟩
open _root_.P2Mb748e9da renaming h29 → _p2mH29
set_option maxRecDepth 8192
omit [Fintype Label] in
theorem _root_.P2Mb748e9da.h25 (scope : Copy → Finset Label) (hscope : _root_.AFT.CanonicalMoments.NoSingletonScopes scope)
    (label : Label) (hlabel : label ∈ _root_.AFT.CanonicalMoments.scopeUnion scope) :
    (_root_.AFT.CanonicalMoments.occurrenceCopies (_root_.AFT.CanonicalMoments.middleScopes scope) label).card + 2 = (_root_.AFT.CanonicalMoments.occurrenceCopies scope label).card := by
  have htwo := _p2mH29 scope hscope label hlabel
  have hne : (_root_.AFT.CanonicalMoments.occurrenceCopies scope label).Nonempty := Finset.card_pos.mp (by omega)
  have hmin := Finset.min'_mem (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) hne
  have hmax := Finset.max'_mem (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) hne
  obtain ⟨first, hfirst, second, hsecond, hdiff⟩ := Finset.one_lt_card.mp htwo
  have hlt := Finset.min'_lt_max' (_root_.AFT.CanonicalMoments.occurrenceCopies scope label) hfirst hsecond hdiff
  rw [_p2mH26 scope label hne,
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨ne_of_gt hlt, hmax⟩),
    Finset.card_erase_of_mem hmin]
  omega
open _root_.P2Mb748e9da renaming h25 → _p2mH25
set_option maxRecDepth 8192
omit [LinearOrder Copy] in
theorem _root_.P2Mb748e9da.h58 (scope : Copy → Finset Label) :
    (∑ label ∈ _root_.AFT.CanonicalMoments.scopeUnion scope, (_root_.AFT.CanonicalMoments.occurrenceCopies scope label).card) = ∑ copy, (scope copy).card := by
  rw [_p2mH52]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro label _ hnot
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro copy hcopy
  exact hnot (Finset.mem_biUnion.mpr ⟨copy, Finset.mem_univ _, (Finset.mem_filter.mp hcopy).2⟩)
open _root_.P2Mb748e9da renaming h58 → _p2mH58
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h27 (scope : Copy → Finset Label) (hscope : _root_.AFT.CanonicalMoments.NoSingletonScopes scope) :
    (∑ copy, (_root_.AFT.CanonicalMoments.middleScopes scope copy).card) + 2 * (_root_.AFT.CanonicalMoments.scopeUnion scope).card =
      ∑ copy, (scope copy).card := by
  have hmiddle : (∑ label ∈ _root_.AFT.CanonicalMoments.scopeUnion scope, (_root_.AFT.CanonicalMoments.occurrenceCopies (_root_.AFT.CanonicalMoments.middleScopes scope) label).card) =
      ∑ copy, (_root_.AFT.CanonicalMoments.middleScopes scope copy).card := by
    rw [_p2mH52]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro label _ hnot
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro copy hcopy
    have hm := (Finset.mem_filter.mp hcopy).2
    exact hnot (Finset.mem_biUnion.mpr ⟨copy, Finset.mem_univ _, (Finset.mem_filter.mp hm).1⟩)
  have hh := Finset.sum_congr rfl (fun label hlabel => _p2mH25 scope hscope label hlabel)
  rw [Finset.sum_add_distrib, hmiddle, _p2mH58] at hh
  simpa only [Finset.sum_const, smul_eq_mul, mul_comm] using hh
open _root_.P2Mb748e9da renaming h27 → _p2mH27
end
open _root_.P2Mb748e9da renaming h25 → _p2mH25
open _root_.P2Mb748e9da renaming h26 → _p2mH26
open _root_.P2Mb748e9da renaming h27 → _p2mH27
open _root_.P2Mb748e9da renaming h29 → _p2mH29
open _root_.P2Mb748e9da renaming h52 → _p2mH52
open _root_.P2Mb748e9da renaming h58 → _p2mH58
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h25 → _p2mH25
open _root_.P2Mb748e9da renaming h26 → _p2mH26
open _root_.P2Mb748e9da renaming h27 → _p2mH27
open _root_.P2Mb748e9da renaming h29 → _p2mH29
open _root_.P2Mb748e9da renaming h52 → _p2mH52
open _root_.P2Mb748e9da renaming h58 → _p2mH58
end
open _root_.P2Mb748e9da renaming h25 → _p2mH25
open _root_.P2Mb748e9da renaming h26 → _p2mH26
open _root_.P2Mb748e9da renaming h27 → _p2mH27
open _root_.P2Mb748e9da renaming h29 → _p2mH29
open _root_.P2Mb748e9da renaming h52 → _p2mH52
open _root_.P2Mb748e9da renaming h58 → _p2mH58
namespace AFT.CanonicalMoments.kernelAt
end AFT.CanonicalMoments.kernelAt
namespace AFT.CanonicalMoments.middleScopes
end AFT.CanonicalMoments.middleScopes
namespace AFT.CanonicalMoments.occurrenceCopies
end AFT.CanonicalMoments.occurrenceCopies
namespace AFT.CanonicalMoments.placementFixed
end AFT.CanonicalMoments.placementFixed
namespace AFT.CanonicalMoments.scopeAt
end AFT.CanonicalMoments.scopeAt
namespace AFT.CanonicalMoments.scopeEnding
end AFT.CanonicalMoments.scopeEnding
namespace AFT.CanonicalMoments.scopePrefix
end AFT.CanonicalMoments.scopePrefix
namespace AFT.CanonicalMoments.scopeSuffix
end AFT.CanonicalMoments.scopeSuffix
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color] {power : ℕ}
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h17 (scope : Fin power → Finset Pool) (copy : Fin power) :
    scope copy ∩ _root_.AFT.CanonicalMoments.scopePrefix scope copy.val ∩ _root_.AFT.CanonicalMoments.scopeSuffix scope (copy.val + 1) = _root_.AFT.CanonicalMoments.middleScopes scope copy := by
  ext label
  simp only [_root_.AFT.CanonicalMoments.scopePrefix, _root_.AFT.CanonicalMoments.scopeSuffix, _root_.AFT.CanonicalMoments.middleScopes, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hlabel, before, hbefore, hbeforeLabel⟩, after, hafter, hafterLabel⟩
    exact ⟨hlabel, ⟨before, hbefore, hbeforeLabel⟩, ⟨after, by change copy.val < after.val; omega, hafterLabel⟩⟩
  · rintro ⟨hlabel, ⟨before, hbefore, hbeforeLabel⟩, ⟨after, hafter, hafterLabel⟩⟩
    exact ⟨⟨hlabel, before, hbefore, hbeforeLabel⟩, after, by exact Nat.succ_le_of_lt hafter, hafterLabel⟩
open _root_.P2Mb748e9da renaming h17 → _p2mH17
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype Pool] in
theorem _root_.P2Mb748e9da.h41 (placement : Slot ↪ Pool) (fixed : Finset Pool)
    (hfixed : fixed ⊆ Finset.univ.map placement) : (_root_.AFT.CanonicalMoments.placementFixed placement fixed).card = fixed.card := by
  have heq : (_root_.AFT.CanonicalMoments.placementFixed placement fixed).map placement = fixed := by
    ext label
    constructor
    · intro h
      obtain ⟨slot, hslot, rfl⟩ := Finset.mem_map.mp h
      exact (Finset.mem_filter.mp hslot).2
    · intro h
      obtain ⟨slot, _, heq⟩ := Finset.mem_map.mp (hfixed h)
      refine Finset.mem_map.mpr ⟨slot, ?_, heq⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [heq] using h⟩
  have h := congrArg Finset.card heq
  simpa only [Finset.card_map] using h
open _root_.P2Mb748e9da renaming h41 → _p2mH41
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype Pool] in
theorem _root_.P2Mb748e9da.h32 (pattern : Fin power → Slot ↪ Pool) (hpattern : _root_.AFT.CanonicalMoments.NoSingleton pattern) :
    _root_.AFT.CanonicalMoments.NoSingletonScopes (_root_.AFT.CanonicalMoments.patternScopes pattern) := by
  intro copy label hlabel
  obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp hlabel
  obtain ⟨other, otherSlot, hother, heq⟩ := hpattern copy slot
  exact ⟨other, hother, Finset.mem_map.mpr ⟨otherSlot, Finset.mem_univ _, heq⟩⟩
open _root_.P2Mb748e9da renaming h32 → _p2mH32
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype Pool] in
theorem _root_.P2Mb748e9da.h33 (pattern : Fin power → Slot ↪ Pool) :
    _root_.AFT.CanonicalMoments.scopeUnion (_root_.AFT.CanonicalMoments.patternScopes pattern) = _root_.AFT.CanonicalMoments.usedLabels pattern := by
  ext label
  simp only [_root_.AFT.CanonicalMoments.scopeUnion, _root_.AFT.CanonicalMoments.patternScopes, _root_.AFT.CanonicalMoments.usedLabels, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_map, Finset.mem_image, Prod.exists]
open _root_.P2Mb748e9da renaming h33 → _p2mH33
set_option maxRecDepth 8192
omit [Fintype Color] in
theorem _root_.P2Mb748e9da.h31 (pattern : Fin power → Slot ↪ Pool) (hpattern : _root_.AFT.CanonicalMoments.NoSingleton pattern) :
    (∑ copy, (_root_.AFT.CanonicalMoments.patternFixed pattern copy).card) + 2 * (_root_.AFT.CanonicalMoments.usedLabels pattern).card =
      power * Fintype.card Slot := by
  have hcard (copy : Fin power) : (_root_.AFT.CanonicalMoments.patternFixed pattern copy).card =
      (_root_.AFT.CanonicalMoments.middleScopes (_root_.AFT.CanonicalMoments.patternScopes pattern) copy).card :=
    _p2mH41 (pattern copy) _ (by
      intro label hlabel
      simp only [_root_.AFT.CanonicalMoments.middleScopes, Finset.mem_filter] at hlabel
      exact hlabel.1)
  simp only [hcard]
  have h := _p2mH27 (_root_.AFT.CanonicalMoments.patternScopes pattern) (_p2mH32 pattern hpattern)
  simpa only [_p2mH33, _root_.AFT.CanonicalMoments.patternScopes, Finset.card_map, Finset.card_univ,
    Finset.sum_const, Fintype.card_fin, smul_eq_mul] using h
open _root_.P2Mb748e9da renaming h31 → _p2mH31
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h17 → _p2mH17
open _root_.P2Mb748e9da renaming h31 → _p2mH31
open _root_.P2Mb748e9da renaming h32 → _p2mH32
open _root_.P2Mb748e9da renaming h33 → _p2mH33
open _root_.P2Mb748e9da renaming h41 → _p2mH41
end
open _root_.P2Mb748e9da renaming h17 → _p2mH17
open _root_.P2Mb748e9da renaming h31 → _p2mH31
open _root_.P2Mb748e9da renaming h32 → _p2mH32
open _root_.P2Mb748e9da renaming h33 → _p2mH33
open _root_.P2Mb748e9da renaming h41 → _p2mH41
namespace AFT.CanonicalMoments.patternFixed
end AFT.CanonicalMoments.patternFixed
namespace AFT.CanonicalMoments.patternScopes
end AFT.CanonicalMoments.patternScopes
namespace AFT.CanonicalMoments.scopeUnion
end AFT.CanonicalMoments.scopeUnion
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
variable {Slot Pool Color : Type*} [Fintype Slot] [Fintype Pool] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h21 (equiv : Slot ≃ Pool)
    (reference : Pool → _root_.AFT.FiniteDist Color) (function : (Slot → Color) → ℝ) :
    (_root_.AFT.FiniteDist.independent reference).expectation (fun word => function (word ∘ equiv)) =
      (_root_.AFT.FiniteDist.independent (fun slot => reference (equiv slot))).expectation function := by
  have h := (_root_.AFT.HistogramNormalization.renameWord (Color := Color) equiv).symm.sum_comp
    (fun word => (∏ slot, (reference (equiv slot)).weight (word slot)) * function word)
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
  apply Eq.trans ?_ h
  apply Finset.sum_congr (by ext; simp)
  intro word _
  change (∏ slot, (reference slot).weight (word slot)) * function (word ∘ equiv) =
    (∏ slot, (reference (equiv slot)).weight ((word ∘ equiv) slot)) * function (word ∘ equiv)
  congr 1
  exact (equiv.prod_comp (fun slot => (reference slot).weight (word slot))).symm
open _root_.P2Mb748e9da renaming h21 → _p2mH21
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h20 (reference : Pool → _root_.AFT.FiniteDist Color)
    (placement : Slot ↪ Pool) (function : (Slot → Color) → ℝ) :
    (_root_.AFT.FiniteDist.independent reference).expectation (fun word => function (word ∘ placement)) =
      (_root_.AFT.FiniteDist.independent (fun slot => reference (placement slot))).expectation function := by
  have hr := _root_.AFT.LocalTensors.independent_restriction_expectation reference (Finset.univ.map placement)
    (fun word => function (word ∘ _root_.AFT.CanonicalMoments.placementEquiv placement))
  have he := _p2mH21 (_root_.AFT.CanonicalMoments.placementEquiv placement)
    (fun label : Finset.univ.map placement => reference label) function
  apply Eq.trans ?_ (hr.trans ?_)
  · rfl
  · apply Eq.trans ?_ he
    unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
    apply Finset.sum_congr (by ext; simp)
    intro word _
    rfl
open _root_.P2Mb748e9da renaming h20 → _p2mH20
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h40 (reference : Pool → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool) (fixed : Finset Pool) (word : Pool → Color) :
    _root_.AFT.MixedKernel.fiberSq reference (_root_.AFT.CanonicalMoments.placedKernel kernel placement) fixed word =
      _root_.AFT.MixedKernel.fiberSq (fun slot => reference (placement slot)) kernel
        (_root_.AFT.CanonicalMoments.placementFixed placement fixed) (word ∘ placement) := by
  have hfreeze (integrated : Pool → Color) : _root_.AFT.MixedKernel.freeze fixed word integrated ∘ placement =
      _root_.AFT.MixedKernel.freeze (_root_.AFT.CanonicalMoments.placementFixed placement fixed) (word ∘ placement) (integrated ∘ placement) := by
    funext slot
    simp [_root_.AFT.MixedKernel.freeze, _root_.AFT.CanonicalMoments.placementFixed]
  simp only [_root_.AFT.MixedKernel.fiberSq, _root_.AFT.FiniteDist.l2Sq, _root_.AFT.CanonicalMoments.placedKernel, hfreeze]
  exact _p2mH20 reference placement
    (fun integrated => kernel (_root_.AFT.MixedKernel.freeze (_root_.AFT.CanonicalMoments.placementFixed placement fixed) (word ∘ placement) integrated) ^ 2)
open _root_.P2Mb748e9da renaming h40 → _p2mH40
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h39 [Nonempty Color] (reference : Pool → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (placement : Slot ↪ Pool) (fixed : Finset Pool) :
    _root_.AFT.MixedKernel.fiberNorm reference (_root_.AFT.CanonicalMoments.placedKernel kernel placement) fixed =
      _root_.AFT.MixedKernel.fiberNorm (fun slot => reference (placement slot)) kernel (_root_.AFT.CanonicalMoments.placementFixed placement fixed) := by
  simp only [_root_.AFT.MixedKernel.fiberNorm, _p2mH40]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro word
    exact norm_le_pi_norm (fun word => Real.sqrt (_root_.AFT.MixedKernel.fiberSq (fun slot => reference (placement slot))
      kernel (_root_.AFT.CanonicalMoments.placementFixed placement fixed) word)) (word ∘ placement)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro word
    let extended : Pool → Color := Function.extend placement word (fun _ => Classical.choice inferInstance)
    have heq : extended ∘ placement = word := by
      funext slot
      exact placement.injective.extend_apply word (fun _ : Pool => Classical.choice (inferInstance : Nonempty Color)) slot
    have hh := norm_le_pi_norm (fun values => Real.sqrt (_root_.AFT.MixedKernel.fiberSq (fun slot => reference (placement slot))
      kernel (_root_.AFT.CanonicalMoments.placementFixed placement fixed) (values ∘ placement))) extended
    simpa only [heq] using hh
open _root_.P2Mb748e9da renaming h39 → _p2mH39
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h34 [Nonempty Color] {power : ℕ}
    (reference : Pool → _root_.AFT.FiniteDist Color) (inputReference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (pattern : Fin power → Slot ↪ Pool)
    (hcompatible : ∀ copy slot, reference (pattern copy slot) = inputReference slot) :
    (_root_.AFT.FiniteDist.independent reference).expectation (_root_.AFT.CanonicalMoments.patternProduct kernel pattern) ^ 2 ≤
      ∏ copy, _root_.AFT.MixedKernel.fiberNorm inputReference kernel (_root_.AFT.CanonicalMoments.patternFixed pattern copy) ^ 2 := by
  have hscope (copy : Fin power) : _root_.AFT.Hoeffding.DependsOn (_root_.AFT.CanonicalMoments.patternScopes pattern copy)
      (_root_.AFT.CanonicalMoments.placedKernel kernel (pattern copy)) := by
    intro first second hequal
    unfold _root_.AFT.CanonicalMoments.placedKernel
    congr 1
    funext slot
    exact hequal (pattern copy slot) (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)
  have h := _p2mH10 reference (_root_.AFT.CanonicalMoments.patternScopes pattern)
    (fun copy => _root_.AFT.CanonicalMoments.placedKernel kernel (pattern copy)) hscope
  have hreference (copy : Fin power) : (fun slot => reference (pattern copy slot)) = inputReference :=
    funext (hcompatible copy)
  unfold _root_.AFT.CanonicalMoments.patternProduct
  simpa only [_p2mH17, _p2mH39, hreference, _root_.AFT.CanonicalMoments.patternFixed] using h
open _root_.P2Mb748e9da renaming h34 → _p2mH34
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h20 → _p2mH20
open _root_.P2Mb748e9da renaming h21 → _p2mH21
open _root_.P2Mb748e9da renaming h34 → _p2mH34
open _root_.P2Mb748e9da renaming h39 → _p2mH39
open _root_.P2Mb748e9da renaming h40 → _p2mH40
end
open _root_.P2Mb748e9da renaming h20 → _p2mH20
open _root_.P2Mb748e9da renaming h21 → _p2mH21
open _root_.P2Mb748e9da renaming h34 → _p2mH34
open _root_.P2Mb748e9da renaming h39 → _p2mH39
open _root_.P2Mb748e9da renaming h40 → _p2mH40
namespace AFT.FiniteDist.optional
end AFT.FiniteDist.optional
namespace AFT.GaussianSource.bodyBlur
end AFT.GaussianSource.bodyBlur
namespace AFT.GaussianSource.bodySample
end AFT.GaussianSource.bodySample
namespace AFT.GaussianSource.bodySampleFintype
end AFT.GaussianSource.bodySampleFintype
namespace AFT.GaussianSource.bodyShift
end AFT.GaussianSource.bodyShift
namespace AFT.GaussianSource.extraBlur
end AFT.GaussianSource.extraBlur
namespace AFT.GaussianSource.extraShift
end AFT.GaussianSource.extraShift
namespace AFT.GaussianSource.maxBodyShift
end AFT.GaussianSource.maxBodyShift
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.TrimmedSlice.blurredSafeLaw
end AFT.TrimmedSlice.blurredSafeLaw
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h76 {α : Type*} {source : Fintype α} [target : Fintype α]
    (law : @_root_.AFT.FiniteDist α source) (f : α → ℝ) :
    (_root_.AFT.FiniteDist.retype law).expectation f = @_root_.AFT.FiniteDist.expectation α source law f := by
  cases Subsingleton.elim source target
  rfl
open _root_.P2Mb748e9da renaming h76 → _p2mH76
end
open _root_.P2Mb748e9da renaming h76 → _p2mH76
end AFT.FiniteDist
open _root_.P2Mb748e9da renaming h76 → _p2mH76
end
open _root_.P2Mb748e9da renaming h76 → _p2mH76
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TensorChannel.apply
end AFT.TensorChannel.apply
namespace AFT.TensorChannel.apply.match_1
end AFT.TensorChannel.apply.match_1
section
namespace AFT.TensorChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]
set_option maxRecDepth 8192
omit [Fintype Input] [Fintype Output] in
theorem _root_.P2Mb748e9da.h110 {Source : Type*} [Fintype Source] (source : _root_.AFT.FiniteDist Source)
    (count : ℕ) (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : Source → (Fin count → Input) → ℝ) (output : Fin count → Output) :
    _root_.AFT.TensorChannel.apply count channel (fun word => source.expectation (fun sample => kernel sample word)) output =
      source.expectation (fun sample => _root_.AFT.TensorChannel.apply count channel (kernel sample) output) := by
  have heq : (fun word => source.expectation (fun sample => kernel sample word)) =
      ∑ sample, source.weight sample • kernel sample := by
    funext word
    simp only [_root_.AFT.FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change _root_.AFT.TensorChannel.applyLinear count channel _ output = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.AFT.TensorChannel.applyLinear,
    LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.expectation]
open _root_.P2Mb748e9da renaming h110 → _p2mH110
end
open _root_.P2Mb748e9da renaming h110 → _p2mH110
end AFT.TensorChannel
open _root_.P2Mb748e9da renaming h110 → _p2mH110
end
open _root_.P2Mb748e9da renaming h110 → _p2mH110
namespace AFT.FiniteDist.dependentPairsEquiv
end AFT.FiniteDist.dependentPairsEquiv
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.TensorChannel.applyLinear
end AFT.TensorChannel.applyLinear
namespace AFT.TensorChannel.center
end AFT.TensorChannel.center
section
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Output : Type*} [Fintype Index] [DecidableEq Index]
  {Old : Index → Type*} [∀ i, Fintype (Old i)]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h108
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (kernel : ((i : Index) → Old i) → ℝ)
    (slot : Index)
    (hc : ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0)
    (polynomial : ((i : Index) → Old i) → _root_.AFT.RepresentedPolynomial.Table Output)
    (hp : ∀ first second, (∀ i, i ≠ slot → first i = second i) →
      polynomial first = polynomial second) :
    (∑ word, MvPolynomial.C ((law slot).weight (word slot) * kernel word) * polynomial word) = 0 := by
  classical
  by_cases hn : Nonempty (Old slot)
  · let color₀ : Old slot := Classical.choice hn
    rw [← (Equiv.piSplitAt slot Old).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro tail _
    have he (color : Old slot) : polynomial ((Equiv.piSplitAt slot Old).symm (color,tail)) =
        polynomial ((Equiv.piSplitAt slot Old).symm (color₀,tail)) := by
      apply hp
      intro other ho
      simp [Equiv.piSplitAt,ho]
    simp only [he]
    have hv (color : Old slot) : (Equiv.piSplitAt slot Old).symm (color,tail) slot = color := by
      simp [Equiv.piSplitAt]
    simp only [hv]
    rw [← Finset.sum_mul, ← map_sum, hc, map_zero, zero_mul]
  · haveI : IsEmpty (Old slot) := not_nonempty_iff.mp hn
    haveI : IsEmpty ((i : Index) → Old i) := ⟨fun word => isEmptyElim (word slot)⟩
    simp
open _root_.P2Mb748e9da renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h107
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (forms : ∀ i, Old i → _root_.AFT.RepresentedPolynomial.Table Output)
    (kernel : ((i : Index) → Old i) → ℝ) (slot : Index) (constant : _root_.AFT.RepresentedPolynomial.Table Output)
    (hc : ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0) :
    _root_.AFT.RepresentedPolynomial.dependentPolynomial (Function.update forms slot
      (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant)) kernel =
      _root_.AFT.RepresentedPolynomial.dependentPolynomial forms kernel := by
  classical
  let remaining := fun word : (i : Index) → Old i =>
    ∏ other ∈ Finset.univ.erase slot, forms other (word other)
  have hz := _p2mH108 law kernel slot hc remaining (by
    intro first second h
    apply Finset.prod_congr rfl
    intro other ho
    rw [h other (Finset.mem_erase.mp ho).1])
  have hu (word : (i : Index) → Old i) :
      (fun other => Function.update forms slot
        (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant) other (word other)) =
      Function.update (fun other => forms other (word other)) slot
        (forms slot (word slot)+MvPolynomial.C ((law slot).weight (word slot))*constant) := by
    funext other
    by_cases ho : other=slot
    · subst other; simp
    · simp [Function.update_of_ne ho]
  have he : _root_.AFT.RepresentedPolynomial.dependentPolynomial (Function.update forms slot
      (fun color => forms slot color + MvPolynomial.C ((law slot).weight color)*constant)) kernel =
      _root_.AFT.RepresentedPolynomial.dependentPolynomial forms kernel + constant *
        (∑ word, MvPolynomial.C ((law slot).weight (word slot)*kernel word)*remaining word) := by
    unfold _root_.AFT.RepresentedPolynomial.dependentPolynomial
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro word _
    rw [hu,Finset.prod_update_of_mem (Finset.mem_univ slot),
      ← Finset.mul_prod_erase Finset.univ (fun other => forms other (word other)) (Finset.mem_univ slot)]
    simp only [Finset.sdiff_singleton_eq_erase,map_mul]
    dsimp only [remaining]
    ring
  rw [he,hz,mul_zero,add_zero]
open _root_.P2Mb748e9da renaming h107 → _p2mH107
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h106
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (forms : ∀ i, Old i → _root_.AFT.RepresentedPolynomial.Table Output)
    (constants : Index → _root_.AFT.RepresentedPolynomial.Table Output) (kernel : ((i : Index) → Old i) → ℝ)
    (selected : Finset Index)
    (hc : ∀ slot ∈ selected, ∀ tail : (i : {i // i ≠ slot}) → Old i.val,
      ∑ color, (law slot).weight color *
        kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0) :
    _root_.AFT.RepresentedPolynomial.dependentPolynomial (fun slot color => forms slot color -
      if slot ∈ selected then MvPolynomial.C ((law slot).weight color)*constants slot else 0) kernel =
      _root_.AFT.RepresentedPolynomial.dependentPolynomial forms kernel := by
  classical
  induction selected using Finset.induction_on with
  | empty => simp only [Finset.notMem_empty,if_false,sub_zero]
  | @insert slot selected hs ih =>
    let previous : ∀ i, Old i → _root_.AFT.RepresentedPolynomial.Table Output := fun other color => forms other color -
      if other ∈ selected then MvPolynomial.C ((law other).weight color)*constants other else 0
    have he : (fun other color => forms other color -
        if other ∈ insert slot selected then MvPolynomial.C ((law other).weight color)*constants other else 0) =
        Function.update previous slot
          (fun color => previous slot color+MvPolynomial.C ((law slot).weight color)*(-constants slot)) := by
      funext other color
      by_cases ho : other=slot
      · subst other; simp [previous,hs,sub_eq_add_neg]
      · simp [previous,ho]
    rw [he,_p2mH107 law previous kernel slot (-constants slot)
      (hc slot (Finset.mem_insert_self _ _))]
    exact ih (fun other ho => hc other (Finset.mem_insert_of_mem ho))
open _root_.P2Mb748e9da renaming h106 → _p2mH106
set_option maxRecDepth 8192
omit [Fintype Index] in
theorem _root_.P2Mb748e9da.h109
    (law : ∀ i, _root_.AFT.FiniteDist (Old i)) (kernel : ((i : Index) → Old i) → ℝ)
    (slot : Index)
    (hc : ∀ word, ∑ color, (law slot).weight color *
      kernel (Function.update word slot color) = 0)
    (tail : (i : {i // i ≠ slot}) → Old i.val) :
    ∑ color, (law slot).weight color *
      kernel ((Equiv.piSplitAt slot Old).symm (color,tail)) = 0 := by
  classical
  by_cases hn : Nonempty (Old slot)
  · let color₀ : Old slot := Classical.choice hn
    have he (color : Old slot) :
        Function.update ((Equiv.piSplitAt slot Old).symm (color₀,tail)) slot color =
          (Equiv.piSplitAt slot Old).symm (color,tail) := by
      funext other
      by_cases ho : other=slot
      · subst other; simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt,ho]
    simpa only [he] using hc ((Equiv.piSplitAt slot Old).symm (color₀,tail))
  · haveI : IsEmpty (Old slot) := not_nonempty_iff.mp hn
    simp
open _root_.P2Mb748e9da renaming h109 → _p2mH109
end
open _root_.P2Mb748e9da renaming h106 → _p2mH106
open _root_.P2Mb748e9da renaming h107 → _p2mH107
open _root_.P2Mb748e9da renaming h108 → _p2mH108
open _root_.P2Mb748e9da renaming h109 → _p2mH109
end AFT.RepresentedPolynomial
open _root_.P2Mb748e9da renaming h106 → _p2mH106
open _root_.P2Mb748e9da renaming h107 → _p2mH107
open _root_.P2Mb748e9da renaming h108 → _p2mH108
open _root_.P2Mb748e9da renaming h109 → _p2mH109
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Root Old Output : Type*} [Fintype Old]
end
end AFT.RepresentedPolynomial
end
open _root_.P2Mb748e9da renaming h106 → _p2mH106
open _root_.P2Mb748e9da renaming h107 → _p2mH107
open _root_.P2Mb748e9da renaming h108 → _p2mH108
open _root_.P2Mb748e9da renaming h109 → _p2mH109
namespace AFT.MixedKernel.densityConjugate
end AFT.MixedKernel.densityConjugate
namespace AFT.MixedKernel.productKernel
end AFT.MixedKernel.productKernel
namespace AFT.RepresentedPolynomial.conditionalOldCenter
end AFT.RepresentedPolynomial.conditionalOldCenter
namespace AFT.RepresentedPolynomial.dependentPolynomial
end AFT.RepresentedPolynomial.dependentPolynomial
section
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h95 (reference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (hc : _root_.AFT.Hoeffding.Canonical reference Finset.univ kernel)
    (word : Slot → Color) :
    (∑ point,kernel point*_root_.AFT.MixedKernel.canonicalPointBasis reference point word)=kernel word := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hh := _p2mH106 (Output:=Unit)
    reference (fun slot color => MvPolynomial.C (R:=ℝ) (if word slot=color then 1 else 0))
    (fun _ => 1) kernel Finset.univ (by
      intro slot _ tail
      exact _p2mH109 reference kernel slot
        (hc.2 slot (Finset.mem_univ slot)) tail)
  simp only [Finset.mem_univ,if_true,mul_one,_root_.AFT.RepresentedPolynomial.dependentPolynomial,
    ←map_sub,←map_prod,←map_mul,←map_sum] at hh
  have he := MvPolynomial.C_injective Unit ℝ hh
  have hx := congrFun (_p2mH103 kernel) word
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,_root_.AFT.MixedKernel.productKernel] at hx
  exact he.trans hx.symm
open _root_.P2Mb748e9da renaming h95 → _p2mH95
end
open _root_.P2Mb748e9da renaming h95 → _p2mH95
end AFT.MixedKernel
open _root_.P2Mb748e9da renaming h95 → _p2mH95
end
open _root_.P2Mb748e9da renaming h95 → _p2mH95
namespace AFT.blockTransport
end AFT.blockTransport
namespace AFT.injectionColumn
end AFT.injectionColumn
namespace AFT.pathLoad
end AFT.pathLoad
namespace AFT.pathLoad.match_1
end AFT.pathLoad.match_1
namespace AFT.roundingLoad
end AFT.roundingLoad
namespace AFT.totalCharge
end AFT.totalCharge
namespace AFT.transportBlockMatrix
end AFT.transportBlockMatrix
section
namespace AFT
end AFT
namespace AFT
open scoped BigOperators
end AFT
namespace AFT
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h111 (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : _root_.AFT.totalCharge c = (q : ℤ))
    (x : (Fin n → ZMod q) × ZMod q) :
    x = (_root_.AFT.canonicalEndpointEquiv n q c hc (_root_.AFT.endpointProjection n q c hc x)).val ↔
      _root_.AFT.fiberLabel n q c x = 0 := by
  constructor
  · intro h
    rw [h]
    exact (_root_.AFT.canonicalEndpointEquiv n q c hc (_root_.AFT.endpointProjection n q c hc x)).property
  · intro h
    exact (congrArg Subtype.val
      (_root_.AFT.zeroFiberPullback_endpointProjection n q c hc ⟨x, h⟩)).symm
open _root_.P2Mb748e9da renaming h111 → _p2mH111
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h112 (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : _root_.AFT.totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) :
    _root_.AFT.reduceCoordinates n q x =
      (_root_.AFT.canonicalEndpointEquiv n q c hc
        (_root_.AFT.endpointProjection n q c hc (_root_.AFT.reduceCoordinates n q x))).val ↔
      (q : ℤ) ∣ _root_.AFT.totalCharge (_root_.AFT.canonicalCarry n q (_root_.AFT.roundingLoad n c x)) := by
  rw [_p2mH111, _root_.AFT.fiberLabel_reduceCoordinates n q c hc]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd _ q
open _root_.P2Mb748e9da renaming h112 → _p2mH112
end AFT
open _root_.P2Mb748e9da renaming h111 → _p2mH111
open _root_.P2Mb748e9da renaming h112 → _p2mH112
end
open _root_.P2Mb748e9da renaming h111 → _p2mH111
open _root_.P2Mb748e9da renaming h112 → _p2mH112
namespace AFT.AffinePair
end AFT.AffinePair
namespace AFT.AffinePair.eval
end AFT.AffinePair.eval
namespace AFT.AffinePair.fallback
end AFT.AffinePair.fallback
namespace AFT.AffinePair.mk
end AFT.AffinePair.mk
namespace AFT.endpointIntegralPreimage
end AFT.endpointIntegralPreimage
namespace AFT.endpointLift
end AFT.endpointLift
namespace AFT.endpointProjection
end AFT.endpointProjection
namespace AFT.integerLabel
end AFT.integerLabel
namespace AFT.liftCoordinates
end AFT.liftCoordinates
namespace AFT.reduceCoordinates
end AFT.reduceCoordinates
namespace AFT.zeroFiberPullback
end AFT.zeroFiberPullback
section
set_option backward.isDefEq.respectTransparency false
namespace AFT
open scoped Classical BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h113 (n q : ℕ) [NeZero q]
    (column : Fin (n + 1) → ℤ) (hcolumn : _root_.AFT.totalCharge column = (q : ℤ)) :
    (_root_.AFT.FiniteDist.uniform (_root_.AFT.EndpointHyperplane n q)).map
        (fun endpoint => (_root_.AFT.canonicalEndpointEquiv n q column hcolumn endpoint).val) =
      _root_.AFT.uniformZeroFiber n q column := by
  rw [← _root_.AFT.FiniteDist.map_map]
  rw [_root_.AFT.FiniteDist.uniform_map_equiv]
  rfl
open _root_.P2Mb748e9da renaming h113 → _p2mH113
end AFT
open _root_.P2Mb748e9da renaming h113 → _p2mH113
end
open _root_.P2Mb748e9da renaming h113 → _p2mH113
section
namespace AFT
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h117 {State : Type*}
    (full retained : State → ℝ) (_hfull : ∀ state,0≤ full state)
    (hretained : ∀ state,0≤ retained state) (hle : ∀ state,retained state≤ full state)
    (hfull_sum : Summable full) (hretained_pos : 0<∑' state,retained state) :
    (∑' state,|retained state/(∑' x,retained x)-full state/(∑' x,full x)|)/2≤
      ((∑' state,full state)-(∑' state,retained state))/(∑' state,full state) := by
  let total := ∑' state,full state
  let kept := ∑' state,retained state
  have hs := Summable.of_nonneg_of_le hretained hle hfull_sum
  have htotal : kept≤ total := hs.tsum_le_tsum hle hfull_sum
  have hkpos : 0< kept := hretained_pos
  have htpos : 0< total := hretained_pos.trans_le htotal
  have hp (state : State) :
      |retained state/kept-full state/total|≤
        (full state-retained state)/total+retained state*((total-kept)/(total*kept)) := by
    have ha : retained state/kept-retained state/total≥0 :=
      sub_nonneg.mpr (div_le_div_of_nonneg_left (hretained state) hretained_pos htotal)
    have hb : (retained state-full state)/total≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hle state)) htpos.le
    calc
      _ = |(retained state/kept-retained state/total)+(retained state-full state)/total| := by congr 1; ring
      _ ≤ |retained state/kept-retained state/total|+|(retained state-full state)/total| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg ha,abs_of_nonpos hb]; field_simp [htpos.ne',hkpos.ne']; ring
  have hnorm := ((hs.div_const kept).sub (hfull_sum.div_const total)).norm
  have hmajor := ((hfull_sum.sub hs).div_const total).add (hs.mul_right ((total-kept)/(total*kept)))
  have hsum := hnorm.tsum_le_tsum (fun state => by simpa only [Real.norm_eq_abs] using hp state) hmajor
  simp only [Real.norm_eq_abs] at hsum
  rw [Summable.tsum_add ((hfull_sum.sub hs).div_const total) (hs.mul_right _),tsum_div_const,
    hfull_sum.tsum_sub hs,tsum_mul_right] at hsum
  change (∑' state,|retained state/kept-full state/total|)≤
    (total-kept)/total+kept*((total-kept)/(total*kept)) at hsum
  have he : (total-kept)/total+kept*((total-kept)/(total*kept))=2*((total-kept)/total) := by
    field_simp [htpos.ne',hkpos.ne']; ring
  rw [he] at hsum
  change (∑' state,|retained state/kept-full state/total|)/2≤(total-kept)/total
  linarith
open _root_.P2Mb748e9da renaming h117 → _p2mH117
end AFT
open _root_.P2Mb748e9da renaming h117 → _p2mH117
end
open _root_.P2Mb748e9da renaming h117 → _p2mH117
namespace AFT.FiniteDist.totalVariation
end AFT.FiniteDist.totalVariation
namespace AFT.HistogramNormalization
end AFT.HistogramNormalization
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Source Output : Type*} [Fintype Output]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h71 (first second : Source → ℝ)
    (hf : ∀ source,0 ≤ first source) (hg : ∀ source,0 ≤ second source)
    (hsf : Summable first) (hsg : Summable second)
    (hfone : ∑' source,first source=1) (hgone : ∑' source,second source=1)
    (channel : Source → _root_.AFT.FiniteDist Output) :
    (∑ output,|(_root_.AFT.FiniteDist.countableMix first hf hsf hfone channel).weight output-
      (_root_.AFT.FiniteDist.countableMix second hg hsg hgone channel).weight output|) ≤ ∑' source,|first source-second source| := by
  have hd : Summable (fun source => |first source-second source|) := by
    simpa only [Real.norm_eq_abs] using (hsf.sub hsg).norm
  have hparts (output : Output) := _root_.AFT.FiniteDist.countable_channel_summable (fun source => |first source-second source|) hd channel output
  have hbound (output : Output) :
      |(_root_.AFT.FiniteDist.countableMix first hf hsf hfone channel).weight output-
        (_root_.AFT.FiniteDist.countableMix second hg hsg hgone channel).weight output| ≤
      ∑' source,|first source-second source| *(channel source).weight output := by
    change |(∑' source,first source*(channel source).weight output)-
      (∑' source,second source*(channel source).weight output)| ≤ _
    rw [← (_root_.AFT.FiniteDist.countable_channel_summable first hsf channel output).tsum_sub
      (_root_.AFT.FiniteDist.countable_channel_summable second hsg channel output)]
    have hh := norm_tsum_le_tsum_norm (_root_.AFT.FiniteDist.countable_channel_summable (fun source => first source-second source) (hsf.sub hsg) channel output).norm
    simp_rw [← sub_mul]
    simpa only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (_root_.AFT.FiniteDist.nonneg _ _)] using hh
  apply (Finset.sum_le_sum fun output _ => hbound output).trans_eq
  rw [← tsum_fintype (L := .unconditional Output) (f := fun output : Output => ∑' source,|first source-second source| *(channel source).weight output)]
  have hs : Summable (fun point : Output × Source => |first point.2-second point.2| *(channel point.2).weight point.1) :=
    (summable_prod_of_nonneg (fun point => mul_nonneg (abs_nonneg _) ((channel point.2).nonneg point.1))).mpr
      ⟨hparts,(hasSum_fintype _).summable⟩
  rw [← Summable.tsum_comm hs]
  simp only [tsum_fintype,← Finset.mul_sum,_root_.AFT.FiniteDist.sum_one,mul_one]
open _root_.P2Mb748e9da renaming h71 → _p2mH71
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h72 (first second : Source → ℝ)
    (hf : ∀ source,0 ≤ first source) (hg : ∀ source,0 ≤ second source)
    (hsf : Summable first) (hsg : Summable second)
    (hfone : ∑' source,first source=1) (hgone : ∑' source,second source=1)
    (channel : Source → _root_.AFT.FiniteDist Output) (error : ℝ)
    (herror : (∑' source,|first source-second source|)/2 ≤ error) :
    _root_.AFT.FiniteDist.TVBound (_root_.AFT.FiniteDist.countableMix first hf hsf hfone channel) (_root_.AFT.FiniteDist.countableMix second hg hsg hgone channel) error := by
  apply (_p2mH81 _ _ _).mpr
  rw [totalVariation_eq_half_l1]
  exact (div_le_div_of_nonneg_right (_p2mH71 first second hf hg hsf hsg hfone hgone channel)
    (by norm_num)).trans herror
open _root_.P2Mb748e9da renaming h72 → _p2mH72
end
open _root_.P2Mb748e9da renaming h71 → _p2mH71
open _root_.P2Mb748e9da renaming h72 → _p2mH72
end AFT.FiniteDist
open _root_.P2Mb748e9da renaming h71 → _p2mH71
open _root_.P2Mb748e9da renaming h72 → _p2mH72
end
open _root_.P2Mb748e9da renaming h71 → _p2mH71
open _root_.P2Mb748e9da renaming h72 → _p2mH72
section
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h115 {First Second : Type*}
    (p q : First → ℝ) (r s : Second → ℝ)
    (hp : ∀ x,0 ≤ p x) (hq : ∀ x,0 ≤ q x) (hr : ∀ x,0 ≤ r x) (hs : ∀ x,0 ≤ s x)
    (hps : Summable p) (hqs : Summable q) (hrs : Summable r) (hss : Summable s)
    (hq1 : ∑' x,q x=1) (hr1 : ∑' x,r x=1) :
    (∑' point : First × Second,|p point.1*r point.2-q point.1*s point.2|) ≤
      (∑' x,|p x-q x|)+(∑' x,|r x-s x|) := by
  have hfirst := (hps.sub hqs).norm
  have hsecond := (hrs.sub hss).norm
  simp only [Real.norm_eq_abs] at hfirst hsecond
  have ha := hfirst.mul_of_nonneg hrs (fun _ => abs_nonneg _) hr
  have hb := hqs.mul_of_nonneg hsecond hq (fun _ => abs_nonneg _)
  have hh := ((hps.mul_of_nonneg hrs hp hr).sub (hqs.mul_of_nonneg hss hq hs)).norm
  simp only [Real.norm_eq_abs] at hh
  have hbound (point : First × Second) :
      |p point.1*r point.2-q point.1*s point.2| ≤
        |p point.1-q point.1| *r point.2+q point.1*|r point.2-s point.2| := by
    calc
      _ = |(p point.1-q point.1)*r point.2+q point.1*(r point.2-s point.2)| := by congr 1; ring
      _  ≤  |(p point.1-q point.1)*r point.2|+|q point.1*(r point.2-s point.2)| := abs_add_le _ _
      _ = _ := by rw [abs_mul,abs_mul,abs_of_nonneg (hr _),abs_of_nonneg (hq _)]
  apply (hh.tsum_le_tsum hbound (ha.add hb)).trans_eq
  rw [ha.tsum_add hb,← hfirst.tsum_mul_tsum hrs ha,← hqs.tsum_mul_tsum hsecond hb,hr1,hq1,mul_one,one_mul]
open _root_.P2Mb748e9da renaming h115 → _p2mH115
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h114 {State : Type*} (count : ℕ)
    (first second : Fin count → State → ℝ)
    (hf : ∀ i x,0 ≤ first i x) (hg : ∀ i x,0 ≤ second i x)
    (hfs : ∀ i,Summable (first i)) (hgs : ∀ i,Summable (second i))
    (hf1 : ∀ i,∑' x,first i x=1) (hg1 : ∀ i,∑' x,second i x=1) :
    (∑' word : Fin count → State,|(∏ i,first i (word i))-(∏ i,second i (word i))|) ≤
      ∑ i,∑' x,|first i x-second i x| := by
  induction count with
  | zero => simp
  | succ count ih =>
    have hp := _root_.AFT.countableFiniteProduct_summable_sum count (fun i => first i.succ)
      (fun i => hf i.succ) (fun i => hfs i.succ)
    have hq := _root_.AFT.countableFiniteProduct_summable_sum count (fun i => second i.succ)
      (fun i => hg i.succ) (fun i => hgs i.succ)
    have hp1 : (∑' word : Fin count → State,∏ i : Fin count,first i.succ (word i))=1 := by
      rw [hp.2]; simp only [hf1,Finset.prod_const_one]
    have hh := _p2mH115 (first 0) (second 0)
      (fun word : Fin count → State => ∏ i : Fin count,first i.succ (word i))
      (fun word : Fin count → State => ∏ i : Fin count,second i.succ (word i))
      (hf 0) (hg 0) (fun word => Finset.prod_nonneg fun i _ => hf i.succ (word i))
      (fun word => Finset.prod_nonneg fun i _ => hg i.succ (word i))
      (hfs 0) (hgs 0) hp.1 hq.1 (hg1 0) hp1
    rw [← (Fin.consEquiv (fun _ : Fin (count+1) => State)).tsum_eq]
    simp only [Fin.prod_univ_succ,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]
    apply hh.trans
    rw [Fin.sum_univ_succ]
    exact add_le_add le_rfl (ih (fun i => first i.succ) (fun i => second i.succ)
      (fun i => hf i.succ) (fun i => hg i.succ) (fun i => hfs i.succ) (fun i => hgs i.succ)
      (fun i => hf1 i.succ) (fun i => hg1 i.succ))
open _root_.P2Mb748e9da renaming h114 → _p2mH114
end
open _root_.P2Mb748e9da renaming h114 → _p2mH114
open _root_.P2Mb748e9da renaming h115 → _p2mH115
end AFT
open _root_.P2Mb748e9da renaming h114 → _p2mH114
open _root_.P2Mb748e9da renaming h115 → _p2mH115
end
open _root_.P2Mb748e9da renaming h114 → _p2mH114
open _root_.P2Mb748e9da renaming h115 → _p2mH115
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source Inner Output : Type*} [Fintype Source] [Fintype Inner] [Fintype Output]
set_option maxRecDepth 8192
omit [Fintype Inner] in
theorem _root_.P2Mb748e9da.h79 (law : _root_.AFT.FiniteDist Source) (first second : Source → _root_.AFT.FiniteDist Output)
    (heq : ∀ source,law.weight source≠0 → first source=second source) : law.mix first=law.mix second := by
  apply _root_.AFT.FiniteDist.ext
  intro output
  apply Finset.sum_congr rfl
  intro source _
  by_cases hs : law.weight source=0
  · simp only [hs,zero_mul]
  · rw [heq source hs]
open _root_.P2Mb748e9da renaming h79 → _p2mH79
 set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h78 (first : _root_.AFT.FiniteDist Source) (second : _root_.AFT.FiniteDist Inner)
    (channel : Source → Inner → _root_.AFT.FiniteDist Output) :
    first.mix (fun source => second.mix (channel source))=
      second.mix (fun inner => first.mix (fun source => channel source inner)) := by
  apply _root_.AFT.FiniteDist.ext
  intro output
  simp only [_root_.AFT.FiniteDist.mix_weight,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inner _
  apply Finset.sum_congr rfl
  intro source _
  ring
open _root_.P2Mb748e9da renaming h78 → _p2mH78
set_option maxRecDepth 8192
omit [Fintype Inner] in
theorem _root_.P2Mb748e9da.h68 (law : _root_.AFT.FiniteDist Source) {first second : Source → _root_.AFT.FiniteDist Output}
    {error : ℝ} (hbound : ∀ source,_root_.AFT.FiniteDist.TVBound (first source) (second source) error) :
    _root_.AFT.FiniteDist.TVBound (law.mix first) (law.mix second) error := by
  intro event
  simp only [_p2mH74,← Finset.sum_sub_distrib,← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (law.nonneg _)]
  calc
    _ ≤ ∑ source,law.weight source*error :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hbound source event) (law.nonneg source)
    _ = error := by rw [← Finset.sum_mul,law.sum_one,one_mul]
open _root_.P2Mb748e9da renaming h68 → _p2mH68
end
open _root_.P2Mb748e9da renaming h68 → _p2mH68
open _root_.P2Mb748e9da renaming h78 → _p2mH78
open _root_.P2Mb748e9da renaming h79 → _p2mH79
end AFT.FiniteDist
open _root_.P2Mb748e9da renaming h68 → _p2mH68
open _root_.P2Mb748e9da renaming h78 → _p2mH78
open _root_.P2Mb748e9da renaming h79 → _p2mH79
end
open _root_.P2Mb748e9da renaming h68 → _p2mH68
open _root_.P2Mb748e9da renaming h78 → _p2mH78
open _root_.P2Mb748e9da renaming h79 → _p2mH79
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {State Index : Type*} [Fintype State] [Fintype Index]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h82 (law : _root_.AFT.FiniteDist State) (value : State → ℝ)
    (power : ℕ) (hpower : 0 < power)
    (hmoment : law.expectation (fun point => |value point|^power) ≤ 0)
    (point : State) (hpoint : 0 < law.weight point) : value point = 0 := by
  have ht : law.weight point * |value point|^power ≤ 0 :=
    (Finset.single_le_sum (f := fun x => law.weight x * |value x|^power) (fun x _ => mul_nonneg (law.nonneg x) (pow_nonneg (abs_nonneg (value x)) power))
      (Finset.mem_univ point)).trans hmoment
  have hp : |value point|^power = 0 := le_antisymm (by nlinarith) (by positivity)
  exact abs_eq_zero.mp ((pow_eq_zero_iff hpower.ne').mp hp)
open _root_.P2Mb748e9da renaming h82 → _p2mH82
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h75 (law : _root_.AFT.FiniteDist State) (value : Index → State → ℝ)
    (bound : Index → ℝ) (hbound : ∀ index, 0 ≤ bound index)
    (power : ℕ) (hpower : 0 < power)
    (hmoment : ∀ index, law.expectation (fun point => |value index point|^power) ≤ bound index^power) :
    law.expectation (fun point => |∑ index, value index point|^power) ≤ (∑ index, bound index)^power := by
  let total := ∑ index, bound index
  have htotal : 0 ≤ total := Finset.sum_nonneg fun index _ => hbound index
  have hz (index : Index) (hi : bound index = 0) (point : State) (hp : 0 < law.weight point) :
      value index point = 0 :=
    _p2mH82 law (value index) power hpower (by simpa only [hi, zero_pow hpower.ne'] using hmoment index) point hp
  by_cases ht : total = 0
  · have hall (index : Index) : bound index = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun index _ => hbound index)).mp ht index (Finset.mem_univ _)
    change (∑ point, law.weight point * |∑ index, value index point|^power) ≤ total^power
    rw [ht, zero_pow hpower.ne']
    apply Finset.sum_nonpos
    intro point _
    by_cases hp : law.weight point = 0
    · simp only [hp, zero_mul, le_refl]
    · have hpoint := (law.nonneg point).lt_of_ne' hp
      simp only [hz _ (hall _) point hpoint, Finset.sum_const_zero, abs_zero, zero_pow hpower.ne', mul_zero, le_refl]
  have htpos : 0 < total := lt_of_le_of_ne htotal (Ne.symm ht)
  have hw : ∑ index, bound index / total = 1 := by rw [← Finset.sum_div]; exact div_self ht
  have hnormalize (index : Index) :
      law.expectation (fun point => (|value index point| / bound index)^power) ≤ 1 := by
    by_cases hb : bound index = 0
    · simp only [hb, div_zero, zero_pow hpower.ne', _root_.AFT.FiniteDist.expectation, mul_zero, Finset.sum_const_zero, zero_le_one]
    · unfold _root_.AFT.FiniteDist.expectation
      simp only [div_pow, ← mul_div_assoc, ← Finset.sum_div]
      apply (div_le_one (pow_pos (lt_of_le_of_ne (hbound index) (Ne.symm hb)) power)).mpr
      exact hmoment index
  have hpoint (point : State) :
      law.weight point * |∑ index, value index point|^power ≤
        law.weight point * (total^power * ∑ index, (bound index / total) * (|value index point| / bound index)^power) := by
    by_cases hp : law.weight point = 0
    · simp only [hp, zero_mul, le_refl]
    have hpoint := (law.nonneg point).lt_of_ne' hp
    have heq : (∑ index, (bound index / total) * (|value index point| / bound index)) =
        (∑ index, |value index point|) / total := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro index _
      by_cases hb : bound index = 0
      · simp only [hb, hz index hb point hpoint, abs_zero, zero_div, mul_zero]
      · field_simp
    have hj := Real.pow_arith_mean_le_arith_mean_pow Finset.univ
      (fun index => bound index / total) (fun index => |value index point| / bound index)
      (fun index _ => div_nonneg (hbound index) htpos.le) hw
      (fun index _ => div_nonneg (abs_nonneg _) (hbound index)) power
    rw [heq, div_pow] at hj
    apply mul_le_mul_of_nonneg_left _ (law.nonneg point)
    apply (pow_le_pow_left₀ (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) power).trans
    exact (div_le_iff₀ (pow_pos htpos power)).mp hj |>.trans_eq (by ring)
  unfold _root_.AFT.FiniteDist.expectation
  apply (Finset.sum_le_sum fun point _ => hpoint point).trans
  calc
    _ = total^power * ∑ index, (bound index / total) *
        law.expectation (fun point => (|value index point| / bound index)^power) := by
      unfold _root_.AFT.FiniteDist.expectation
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro index _
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ ≤ total^power * ∑ index, (bound index / total) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg htpos.le power)
      exact Finset.sum_le_sum fun index _ => mul_le_mul_of_nonneg_left (hnormalize index)
        (div_nonneg (hbound index) htpos.le)
    _ = _ := by simp only [mul_one, hw]; rfl
open _root_.P2Mb748e9da renaming h75 → _p2mH75
end
open _root_.P2Mb748e9da renaming h75 → _p2mH75
open _root_.P2Mb748e9da renaming h82 → _p2mH82
end AFT.FiniteDist
open _root_.P2Mb748e9da renaming h75 → _p2mH75
open _root_.P2Mb748e9da renaming h82 → _p2mH82
end
open _root_.P2Mb748e9da renaming h75 → _p2mH75
open _root_.P2Mb748e9da renaming h82 → _p2mH82
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot State Record : Type*} [Fintype Slot] [Fintype State] [Fintype Record]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h77 (law : Slot → _root_.AFT.FiniteDist State) (record : Slot → State → Record) :
    (_root_.AFT.FiniteDist.independent law).map (fun word slot => record slot (word slot)) =
      _root_.AFT.FiniteDist.independent (fun slot => (law slot).map (record slot)) := by
  ext values
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.independent]
  change (∑ word : Slot → State, if (fun slot => record slot (word slot)) = values then ∏ slot, (law slot).weight (word slot) else 0) =
    ∏ slot, ∑ point, if record slot point = values slot then (law slot).weight point else 0
  have he := Fintype.prod_sum (fun slot point => if record slot point = values slot then (law slot).weight point else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]
open _root_.P2Mb748e9da renaming h77 → _p2mH77
end
open _root_.P2Mb748e9da renaming h77 → _p2mH77
end AFT.FiniteDist
open _root_.P2Mb748e9da renaming h77 → _p2mH77
end
open _root_.P2Mb748e9da renaming h77 → _p2mH77
section
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h102 (reference : Slot → _root_.AFT.FiniteDist Color)
    (fixed : Finset Slot) (values word : Slot → Color) :
    (∏ slot ∈ fixed, (reference slot).weight (values slot)) *
      (_root_.AFT.CanonicalMoments.refreshLaw reference fixedᶜ values).weight word ≤
        (_root_.AFT.FiniteDist.independent reference).weight word := by
  rw [← Fintype.prod_ite_mem fixed (fun slot => (reference slot).weight (values slot))]
  change (∏ slot, if slot ∈ fixed then (reference slot).weight (values slot) else 1) *
      (∏ slot, (if slot ∈ fixedᶜ then reference slot else _root_.AFT.CanonicalMoments.pointLaw (values slot)).weight (word slot)) ≤
    ∏ slot, (reference slot).weight (word slot)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  · intro slot _
    exact mul_nonneg (by split_ifs; exact (reference slot).nonneg _; norm_num)
      (_root_.AFT.FiniteDist.nonneg _ _)
  · intro slot _
    by_cases hs : slot ∈ fixed
    · simp only [hs, if_true, Finset.mem_compl, not_true_eq_false, if_false, _root_.AFT.CanonicalMoments.pointLaw]
      by_cases hv : values slot = word slot
      · simp only [hv, if_true, mul_one, le_refl]
      · simp only [if_neg hv, mul_zero]
        exact (reference slot).nonneg _
    · simp only [hs, if_false, Finset.mem_compl, not_false_eq_true, if_true, one_mul, le_refl]
open _root_.P2Mb748e9da renaming h102 → _p2mH102
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h100 (reference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (values : Slot → Color) :
    (∏ slot ∈ fixed, (reference slot).weight (values slot)) * _root_.AFT.MixedKernel.fiberSq reference kernel fixed values ≤
      (_root_.AFT.FiniteDist.independent reference).l2Sq kernel := by
  have heq : _root_.AFT.MixedKernel.fiberSq reference kernel fixed values =
      (_root_.AFT.CanonicalMoments.refreshLaw reference fixedᶜ values).expectation (fun word => kernel word ^ 2) := by
    have hh := _p2mH45 reference fixedᶜ (fun word => kernel word ^ 2) values
    simpa only [_root_.AFT.CanonicalMoments.refresh, compl_compl, _root_.AFT.MixedKernel.fiberSq, _root_.AFT.FiniteDist.l2Sq] using hh.symm
  rw [heq]
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.l2Sq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro word _
  exact (mul_le_mul_of_nonneg_right (_p2mH102 reference fixed values word) (sq_nonneg (kernel word))).trans_eq' (by ring)
open _root_.P2Mb748e9da renaming h100 → _p2mH100
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h98 (reference : Slot → _root_.AFT.FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (values : Slot → Color) :
    _root_.AFT.MixedKernel.fiberSq reference kernel fixed values ≤ (_root_.AFT.FiniteDist.independent reference).l2Sq kernel / lower ^ fixed.card := by
  apply (le_div_iff₀ (pow_pos hlower fixed.card)).mpr
  have hweight : lower ^ fixed.card ≤ ∏ slot ∈ fixed, (reference slot).weight (values slot) := by
    calc
      _ = ∏ _slot ∈ fixed, lower := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hlower.le) (fun slot _ => href slot (values slot))
  exact (mul_le_mul_of_nonneg_right hweight (_p2mH101 reference kernel fixed values)).trans
    (_p2mH100 reference kernel fixed values) |>.trans_eq' (by ring)
open _root_.P2Mb748e9da renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h96 (reference : Slot → _root_.AFT.FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower) (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) :
    _root_.AFT.MixedKernel.fiberNorm reference kernel fixed ≤
      Real.sqrt ((_root_.AFT.FiniteDist.independent reference).l2Sq kernel) / (Real.sqrt lower) ^ fixed.card := by
  have hsqrt (n : ℕ) : Real.sqrt (lower ^ n) = (Real.sqrt lower) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hlower.le n), ih, pow_succ]
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))).mpr
  intro values
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_le_sqrt (_p2mH98 reference lower hlower href kernel fixed values)).trans_eq
    (by rw [Real.sqrt_div (_root_.AFT.FiniteDist.l2Sq_nonneg _ _), hsqrt])
open _root_.P2Mb748e9da renaming h96 → _p2mH96
end
open _root_.P2Mb748e9da renaming h96 → _p2mH96
open _root_.P2Mb748e9da renaming h98 → _p2mH98
open _root_.P2Mb748e9da renaming h100 → _p2mH100
open _root_.P2Mb748e9da renaming h102 → _p2mH102
end AFT.MixedKernel
open _root_.P2Mb748e9da renaming h96 → _p2mH96
open _root_.P2Mb748e9da renaming h98 → _p2mH98
open _root_.P2Mb748e9da renaming h100 → _p2mH100
open _root_.P2Mb748e9da renaming h102 → _p2mH102
end
open _root_.P2Mb748e9da renaming h96 → _p2mH96
open _root_.P2Mb748e9da renaming h98 → _p2mH98
open _root_.P2Mb748e9da renaming h100 → _p2mH100
open _root_.P2Mb748e9da renaming h102 → _p2mH102
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
section Counting
variable {Copy PrimarySlot BodySlot PrimaryPool BodyPool : Type*}
  [Fintype Copy] [Fintype PrimarySlot] [Fintype BodySlot] [Fintype PrimaryPool] [Fintype BodyPool]
end Counting
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h63 (primaryPopulation bodyPopulation primaryOrder bodyOrder power primaryUsed bodyUsed : ℕ)
    (hprimary : 0 < primaryPopulation) (hbody : 0 < bodyPopulation)
    (hprimaryLarge : 2 * primaryOrder ≤ primaryPopulation) (hbodyLarge : 2 * bodyOrder ≤ bodyPopulation)
    (hprimaryUsed : primaryUsed ≤ power * primaryOrder) (hbodyUsed : bodyUsed ≤ power * bodyOrder) :
    ((primaryPopulation.descFactorial primaryUsed : ℝ) * (primaryPopulation : ℝ) ^ (power * primaryOrder - primaryUsed) *
      ((bodyPopulation.descFactorial bodyUsed : ℝ) * (bodyPopulation : ℝ) ^ (power * bodyOrder - bodyUsed))) /
      (((primaryPopulation.descFactorial primaryOrder : ℝ) * (bodyPopulation.descFactorial bodyOrder : ℝ)) ^ power) ≤
      (2 : ℝ) ^ (power * (primaryOrder + bodyOrder)) := by
  have hp := _p2mH2 primaryPopulation primaryOrder power primaryUsed hprimary hprimaryLarge hprimaryUsed
  have hb := _p2mH2 bodyPopulation bodyOrder power bodyUsed hbody hbodyLarge hbodyUsed
  have hmul := mul_le_mul hp hb (by positivity) (by positivity)
  rw [div_mul_div_comm, ← mul_pow, ← pow_add, ← Nat.mul_add] at hmul
  exact hmul
open _root_.P2Mb748e9da renaming h63 → _p2mH63
section Occurrences
variable {Copy Label : Type*} [Fintype Copy] [LinearOrder Copy] [Fintype Label]
end Occurrences
end
open _root_.P2Mb748e9da renaming h63 → _p2mH63
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h63 → _p2mH63
end
open _root_.P2Mb748e9da renaming h63 → _p2mH63
namespace AFT.CanonicalMoments.roleScopes
end AFT.CanonicalMoments.roleScopes
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.AFT.CanonicalMoments.instDecidableEqSum_aFT
section Compatible
variable {Slot Pool Color Copy : Type*}
  [Fintype Slot] [Fintype Pool] [Fintype Color] [Fintype Copy]
set_option maxRecDepth 8192
omit [Fintype Copy] [Fintype Pool] in
theorem _root_.P2Mb748e9da.h38 (reference : Pool → _root_.AFT.FiniteDist Color)
    (inputReference : Slot → _root_.AFT.FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical inputReference Finset.univ kernel)
    (placement : Slot ↪ Pool) (hcompatible : ∀ slot, reference (placement slot) = inputReference slot) :
    _root_.AFT.Hoeffding.Canonical reference (Finset.univ.map placement) (_root_.AFT.CanonicalMoments.placedKernel kernel placement) := by
  constructor
  · intro first second hequal
    unfold _root_.AFT.CanonicalMoments.placedKernel
    congr 1
    funext slot
    exact hequal (placement slot) (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, rfl⟩)
  · intro label hlabel
    obtain ⟨slot, _, rfl⟩ := Finset.mem_map.mp hlabel
    intro word
    have hword (color : Color) :
        (Function.update word (placement slot) color) ∘ placement =
          Function.update (word ∘ placement) slot color := by
      funext other
      by_cases hother : other = slot
      · subst other; simp
      · have hne : placement other ≠ placement slot := fun h => hother (placement.injective h)
        simp [Function.comp_apply, Function.update_of_ne hother, Function.update_of_ne hne]
    simp only [_root_.AFT.CanonicalMoments.placedKernel, hword, hcompatible]
    exact hcanonical.2 slot (Finset.mem_univ _) (word ∘ placement)
open _root_.P2Mb748e9da renaming h38 → _p2mH38
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h35 (reference : Pool → _root_.AFT.FiniteDist Color)
    (inputReference : Slot → _root_.AFT.FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical inputReference Finset.univ kernel)
    (pattern : Copy → Slot ↪ Pool)
    (hcompatible : ∀ copy slot, reference (pattern copy slot) = inputReference slot)
    (singleCopy : Copy) (singleSlot : Slot)
    (hsingle : ∀ copy, copy ≠ singleCopy → ∀ slot,
      pattern copy slot ≠ pattern singleCopy singleSlot) :
    (_root_.AFT.FiniteDist.independent reference).expectation (_root_.AFT.CanonicalMoments.patternProduct kernel pattern) = 0 := by
  let label := pattern singleCopy singleSlot
  let remainder (word : Pool → Color) :=
    ∏ copy ∈ Finset.univ.erase singleCopy, _root_.AFT.CanonicalMoments.placedKernel kernel (pattern copy) word
  have hcentered := (_p2mH38 reference inputReference kernel hcanonical
    (pattern singleCopy) (hcompatible singleCopy)).2 label
    (Finset.mem_map.mpr ⟨singleSlot, Finset.mem_univ _, rfl⟩)
  have hdepends : _root_.AFT.Hoeffding.DependsOn (Finset.univ.erase label) remainder := by
    intro first second hequal
    apply Finset.prod_congr rfl
    intro copy hcopy
    unfold _root_.AFT.CanonicalMoments.placedKernel
    congr 1
    funext slot
    exact hequal (pattern copy slot)
      (Finset.mem_erase.mpr ⟨hsingle copy (Finset.mem_erase.mp hcopy).1 slot, Finset.mem_univ _⟩)
  have h := _root_.AFT.Hoeffding.orthogonal_of_centered reference (Finset.univ.erase label)
    label (by simp) (_root_.AFT.CanonicalMoments.placedKernel kernel (pattern singleCopy)) remainder hcentered hdepends
  have heq : _root_.AFT.CanonicalMoments.patternProduct kernel pattern =
      (fun word => _root_.AFT.CanonicalMoments.placedKernel kernel (pattern singleCopy) word * remainder word) := by
    funext word
    exact (Finset.mul_prod_erase _ _ (Finset.mem_univ singleCopy)).symm
  rw [heq]
  exact h
open _root_.P2Mb748e9da renaming h35 → _p2mH35
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h30 (reference : Pool → _root_.AFT.FiniteDist Color)
    (inputReference : Slot → _root_.AFT.FiniteDist Color) (kernel : (Slot → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical inputReference Finset.univ kernel)
    (pattern : Copy → Slot ↪ Pool)
    (hcompatible : ∀ copy slot, reference (pattern copy slot) = inputReference slot)
    (hne : (_root_.AFT.FiniteDist.independent reference).expectation (_root_.AFT.CanonicalMoments.patternProduct kernel pattern) ≠ 0) :
    _root_.AFT.CanonicalMoments.NoSingleton pattern := by
  by_contra h
  simp only [_root_.AFT.CanonicalMoments.NoSingleton, not_forall, not_exists, not_and] at h
  obtain ⟨copy, slot, hsingle⟩ := h
  apply hne
  apply _p2mH35 reference inputReference kernel hcanonical
    pattern hcompatible copy slot
  intro otherCopy hcopy otherSlot
  exact hsingle otherCopy otherSlot hcopy
open _root_.P2Mb748e9da renaming h30 → _p2mH30
end Compatible
open _root_.P2Mb748e9da renaming h30 → _p2mH30
open _root_.P2Mb748e9da renaming h35 → _p2mH35
open _root_.P2Mb748e9da renaming h38 → _p2mH38
section TwoPools
variable {PS BS PP BP Color Copy : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color] [Fintype Copy]
set_option maxRecDepth 8192
omit [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color] [Fintype Copy] in
theorem _root_.P2Mb748e9da.h55 (pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP)) :
    _root_.AFT.CanonicalMoments.NoSingleton (_root_.AFT.CanonicalMoments.sumPattern pattern) ↔ _root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2 := by
  constructor
  · intro h
    constructor
    · intro copy slot
      obtain ⟨other, otherSlot, hother, heq⟩ := h copy (Sum.inl slot)
      cases otherSlot with
      | inl otherSlot => exact ⟨other, otherSlot, hother, Sum.inl.inj heq⟩
      | inr otherSlot => cases heq
    · intro copy slot
      obtain ⟨other, otherSlot, hother, heq⟩ := h copy (Sum.inr slot)
      cases otherSlot with
      | inl otherSlot => cases heq
      | inr otherSlot => exact ⟨other, otherSlot, hother, Sum.inr.inj heq⟩
  · rintro ⟨hp, hb⟩ copy (slot | slot)
    · obtain ⟨other, otherSlot, hother, heq⟩ := hp copy slot
      exact ⟨other, Sum.inl otherSlot, hother, congrArg Sum.inl heq⟩
    · obtain ⟨other, otherSlot, hother, heq⟩ := hb copy slot
      exact ⟨other, Sum.inr otherSlot, hother, congrArg Sum.inr heq⟩
open _root_.P2Mb748e9da renaming h55 → _p2mH55
set_option maxRecDepth 8192
omit [Fintype Copy] in
theorem _root_.P2Mb748e9da.h60 (primary body : _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ) (power : ℕ) :
    (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => _root_.AFT.CanonicalMoments.twoPoolStatistic kernel word ^ power) =
      (∑ pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP),
        (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
          (_root_.AFT.CanonicalMoments.patternProduct kernel (_root_.AFT.CanonicalMoments.sumPattern pattern))) /
      (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
        ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ)) ^ power := by
  unfold _root_.AFT.CanonicalMoments.twoPoolStatistic _root_.AFT.FiniteDist.expectation _root_.AFT.CanonicalMoments.patternProduct
  simp only [div_pow, Fintype.sum_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have he := (Equiv.arrowProdEquivProdArrow (Fin power) (fun _ => PS ↪ PP) (fun _ => BS ↪ BP)).symm.sum_comp
    (fun pattern : Fin power → (PS ↪ PP) × (BS ↪ BP) =>
      ∑ word, (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).weight word *
        ∏ copy, _root_.AFT.CanonicalMoments.placedKernel kernel ((pattern copy).1.sumMap (pattern copy).2) word)
  exact he.symm
open _root_.P2Mb748e9da renaming h60 → _p2mH60
set_option maxRecDepth 8192
omit [Fintype Copy] in
theorem _root_.P2Mb748e9da.h62 (primary body : _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (power : ℕ) :
    (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => _root_.AFT.CanonicalMoments.twoPoolStatistic kernel word ^ power) =
      (∑ pattern ∈ Finset.univ.filter (fun pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP) =>
          _root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2),
        (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
          (_root_.AFT.CanonicalMoments.patternProduct kernel (_root_.AFT.CanonicalMoments.sumPattern pattern))) /
      (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
        ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ)) ^ power := by
  rw [_p2mH60]
  congr 1
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro pattern _ hnot
  by_contra hne
  apply hnot
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  apply (_p2mH55 pattern).mp
  apply _p2mH30 _ _ kernel hcanonical _ _ hne
  intro copy slot
  cases slot <;> rfl
open _root_.P2Mb748e9da renaming h62 → _p2mH62
end TwoPools
open _root_.P2Mb748e9da renaming h55 → _p2mH55
open _root_.P2Mb748e9da renaming h60 → _p2mH60
open _root_.P2Mb748e9da renaming h62 → _p2mH62
end
open _root_.P2Mb748e9da renaming h30 → _p2mH30
open _root_.P2Mb748e9da renaming h35 → _p2mH35
open _root_.P2Mb748e9da renaming h38 → _p2mH38
open _root_.P2Mb748e9da renaming h55 → _p2mH55
open _root_.P2Mb748e9da renaming h60 → _p2mH60
open _root_.P2Mb748e9da renaming h62 → _p2mH62
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h30 → _p2mH30
open _root_.P2Mb748e9da renaming h35 → _p2mH35
open _root_.P2Mb748e9da renaming h38 → _p2mH38
open _root_.P2Mb748e9da renaming h55 → _p2mH55
open _root_.P2Mb748e9da renaming h60 → _p2mH60
open _root_.P2Mb748e9da renaming h62 → _p2mH62
end
open _root_.P2Mb748e9da renaming h30 → _p2mH30
open _root_.P2Mb748e9da renaming h35 → _p2mH35
open _root_.P2Mb748e9da renaming h38 → _p2mH38
open _root_.P2Mb748e9da renaming h55 → _p2mH55
open _root_.P2Mb748e9da renaming h60 → _p2mH60
open _root_.P2Mb748e9da renaming h62 → _p2mH62
section
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.AFT.CanonicalMoments.instDecidableEqSum_aFT_1
section Weighted
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h9 (reference : Slot → _root_.AFT.FiniteDist Color)
    (kernel : (Slot → Color) → ℝ) (fixed : Finset Slot) (scale : Slot → ℝ)
    (hscale : ∀ slot, 0 < scale slot) :
    _root_.AFT.MixedKernel.fiberNorm reference kernel fixed ≤
      ((∏ slot, scale slot) * (∏ slot ∈ fixed, scale slot)) *
        _root_.AFT.MixedKernel.activity (fun slot => 1 / scale slot) reference kernel := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Finset Slot)))
    (f := fun selected => (∏ slot ∈ selected, 1 / scale slot) * _root_.AFT.MixedKernel.fiberNorm reference kernel selected)
    (fun selected _ => mul_nonneg (Finset.prod_nonneg fun slot _ => (one_div_pos.mpr (hscale slot)).le)
      (_p2mH97 reference kernel selected)) (Finset.mem_univ fixed)
  have hm := mul_le_mul_of_nonneg_left h
    (show 0 ≤ ∏ slot, 1 / scale slot from Finset.prod_nonneg fun slot _ => (one_div_pos.mpr (hscale slot)).le)
  have hraw : (∏ slot, 1 / scale slot) * ((∏ slot ∈ fixed, 1 / scale slot) *
      _root_.AFT.MixedKernel.fiberNorm reference kernel fixed) ≤
      _root_.AFT.MixedKernel.activity (fun slot => 1 / scale slot) reference kernel := hm
  have hh := mul_le_mul_of_nonneg_left hraw (show 0 ≤ (∏ slot, scale slot) * (∏ slot ∈ fixed, scale slot) from
    mul_nonneg (Finset.prod_nonneg fun slot _ => (hscale slot).le)
      (Finset.prod_nonneg fun slot _ => (hscale slot).le))
  have hu : (∏ slot, scale slot) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun slot _ => (hscale slot).ne')
  have hf : (∏ slot ∈ fixed, scale slot) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun slot _ => (hscale slot).ne')
  have heq : ((∏ slot, scale slot) * (∏ slot ∈ fixed, scale slot)) *
      ((∏ slot, 1 / scale slot) * ((∏ slot ∈ fixed, 1 / scale slot) *
        _root_.AFT.MixedKernel.fiberNorm reference kernel fixed)) = _root_.AFT.MixedKernel.fiberNorm reference kernel fixed := by
    simp only [one_div, Finset.prod_inv_distrib]
    field_simp
  rwa [heq] at hh
open _root_.P2Mb748e9da renaming h9 → _p2mH9
end Weighted
open _root_.P2Mb748e9da renaming h9 → _p2mH9
section TwoPools
variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]
  {power : ℕ}
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem _root_.P2Mb748e9da.h56 (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) (label : PP) :
    Sum.inl label ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) copy ↔ label ∈ _root_.AFT.CanonicalMoments.patternScopes pattern.1 copy := by
  simp only [_root_.AFT.CanonicalMoments.patternScopes, Finset.mem_map, Finset.mem_univ, true_and, Sum.exists]
  simp [_root_.AFT.CanonicalMoments.sumPattern]
open _root_.P2Mb748e9da renaming h56 → _p2mH56
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem _root_.P2Mb748e9da.h57 (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) (label : BP) :
    Sum.inr label ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) copy ↔ label ∈ _root_.AFT.CanonicalMoments.patternScopes pattern.2 copy := by
  simp only [_root_.AFT.CanonicalMoments.patternScopes, Finset.mem_map, Finset.mem_univ, true_and, Sum.exists]
  simp [_root_.AFT.CanonicalMoments.sumPattern]
open _root_.P2Mb748e9da renaming h57 → _p2mH57
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem _root_.P2Mb748e9da.h53 (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) :
    (_root_.AFT.CanonicalMoments.patternFixed (_root_.AFT.CanonicalMoments.sumPattern pattern) copy).toLeft = _root_.AFT.CanonicalMoments.patternFixed pattern.1 copy := by
  ext slot
  simp only [Finset.mem_toLeft, _root_.AFT.CanonicalMoments.patternFixed, _root_.AFT.CanonicalMoments.placementFixed, Finset.mem_filter, Finset.mem_univ,
    true_and, _root_.AFT.CanonicalMoments.middleScopes]
  change (_ ∧ (∃ before, before < copy ∧ _) ∧ (∃ after, copy < after ∧ _)) ↔ _
  change (Sum.inl (pattern.1 copy slot) ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) copy ∧
    (∃ before, before < copy ∧ Sum.inl (pattern.1 copy slot) ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) before) ∧
    (∃ after, copy < after ∧ Sum.inl (pattern.1 copy slot) ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) after)) ↔ _
  simp only [_p2mH56]
open _root_.P2Mb748e9da renaming h53 → _p2mH53
set_option maxRecDepth 8192
omit [Fintype Color] [Fintype PP] [Fintype BP] in
theorem _root_.P2Mb748e9da.h54 (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (copy : Fin power) :
    (_root_.AFT.CanonicalMoments.patternFixed (_root_.AFT.CanonicalMoments.sumPattern pattern) copy).toRight = _root_.AFT.CanonicalMoments.patternFixed pattern.2 copy := by
  ext slot
  simp only [Finset.mem_toRight, _root_.AFT.CanonicalMoments.patternFixed, _root_.AFT.CanonicalMoments.placementFixed, Finset.mem_filter, Finset.mem_univ,
    true_and, _root_.AFT.CanonicalMoments.middleScopes]
  change (_ ∧ (∃ before, before < copy ∧ _) ∧ (∃ after, copy < after ∧ _)) ↔ _
  change (Sum.inr (pattern.2 copy slot) ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) copy ∧
    (∃ before, before < copy ∧ Sum.inr (pattern.2 copy slot) ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) before) ∧
    (∃ after, copy < after ∧ Sum.inr (pattern.2 copy slot) ∈ _root_.AFT.CanonicalMoments.patternScopes (_root_.AFT.CanonicalMoments.sumPattern pattern) after)) ↔ _
  simp only [_p2mH57]
open _root_.P2Mb748e9da renaming h54 → _p2mH54
set_option maxRecDepth 8192
omit [Fintype PP] [Fintype BP] in
theorem _root_.P2Mb748e9da.h8 (reference : (PS ⊕ BS) → _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ) (fixed : Finset (PS ⊕ BS))
    (primaryScale bodyScale : ℝ) (hprimary : 0 < primaryScale) (hbody : 0 < bodyScale) :
    _root_.AFT.MixedKernel.fiberNorm reference kernel fixed ≤
      primaryScale ^ (Fintype.card PS + fixed.toLeft.card) *
        bodyScale ^ (Fintype.card BS + fixed.toRight.card) *
          _root_.AFT.MixedKernel.activity (Sum.elim (fun _ : PS => 1 / primaryScale) (fun _ : BS => 1 / bodyScale)) reference kernel := by
  have h := _p2mH9 reference kernel fixed
    (Sum.elim (fun _ : PS => primaryScale) (fun _ : BS => bodyScale)) (by intro slot; cases slot <;> assumption)
  have hr : (fun slot : PS ⊕ BS => 1 / Sum.elim (fun _ : PS => primaryScale) (fun _ : BS => bodyScale) slot) =
      Sum.elim (fun _ : PS => 1 / primaryScale) (fun _ : BS => 1 / bodyScale) := by funext slot; cases slot <;> rfl
  rw [hr, Fintype.prod_sum_type, Finset.prod_sum_eq_prod_toLeft_mul_prod_toRight] at h
  simpa only [Sum.elim_inl, Sum.elim_inr, Finset.prod_const, Finset.card_univ, pow_add,
    mul_assoc, mul_left_comm, mul_comm] using h
open _root_.P2Mb748e9da renaming h8 → _p2mH8
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h65 (primary body : _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP))
    (hpattern : _root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2)
    (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP) :
    |(_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (_root_.AFT.CanonicalMoments.patternProduct kernel (_root_.AFT.CanonicalMoments.sumPattern pattern))| ≤
      (Fintype.card PP : ℝ) ^ (power * Fintype.card PS - (_root_.AFT.CanonicalMoments.usedLabels pattern.1).card) *
        (Fintype.card BP : ℝ) ^ (power * Fintype.card BS - (_root_.AFT.CanonicalMoments.usedLabels pattern.2).card) *
          _root_.AFT.MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
            (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
            (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel ^ power := by
  haveI : Nonempty Color := by
    by_contra h
    haveI : IsEmpty Color := not_nonempty_iff.mp h
    have hh := primary.sum_one
    simp at hh
  have hp : (0 : ℝ) < Fintype.card PP := by exact_mod_cast hprimary
  have hb : (0 : ℝ) < Fintype.card BP := by exact_mod_cast hbody
  have hc := _p2mH34
    (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel (_root_.AFT.CanonicalMoments.sumPattern pattern)
    (by intro copy slot; cases slot <;> rfl)
  rw [Finset.prod_pow] at hc
  have habs := (sq_le_sq₀ (abs_nonneg _) (Finset.prod_nonneg fun copy _ => _p2mH97 _ _ _)).mp
    (by simpa only [sq_abs] using hc)
  apply habs.trans
  have h := Finset.prod_le_prod (fun copy (_ : copy ∈ (Finset.univ : Finset (Fin power))) =>
      _p2mH97 (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel _)
    (fun copy (_ : copy ∈ (Finset.univ : Finset (Fin power))) => _p2mH8
      (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel (_root_.AFT.CanonicalMoments.patternFixed (_root_.AFT.CanonicalMoments.sumPattern pattern) copy)
      (Real.sqrt (Fintype.card PP)) (Real.sqrt (Fintype.card BP)) (Real.sqrt_pos.mpr hp) (Real.sqrt_pos.mpr hb))
  apply h.trans_eq
  simp only [_p2mH53, _p2mH54, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpcount := _p2mH31 pattern.1 hpattern.1
  have hbcount := _p2mH31 pattern.2 hpattern.2
  have hpe : (∑ copy : Fin power, (Fintype.card PS + (_root_.AFT.CanonicalMoments.patternFixed pattern.1 copy).card)) =
      2 * (power * Fintype.card PS - (_root_.AFT.CanonicalMoments.usedLabels pattern.1).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hbe : (∑ copy : Fin power, (Fintype.card BS + (_root_.AFT.CanonicalMoments.patternFixed pattern.2 copy).card)) =
      2 * (power * Fintype.card BS - (_root_.AFT.CanonicalMoments.usedLabels pattern.2).card) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  rw [hpe, hbe, pow_mul, pow_mul, Real.sq_sqrt hp.le, Real.sq_sqrt hb.le]
open _root_.P2Mb748e9da renaming h65 → _p2mH65
end TwoPools
open _root_.P2Mb748e9da renaming h8 → _p2mH8
open _root_.P2Mb748e9da renaming h53 → _p2mH53
open _root_.P2Mb748e9da renaming h54 → _p2mH54
open _root_.P2Mb748e9da renaming h56 → _p2mH56
open _root_.P2Mb748e9da renaming h57 → _p2mH57
open _root_.P2Mb748e9da renaming h65 → _p2mH65
end
open _root_.P2Mb748e9da renaming h8 → _p2mH8
open _root_.P2Mb748e9da renaming h9 → _p2mH9
open _root_.P2Mb748e9da renaming h53 → _p2mH53
open _root_.P2Mb748e9da renaming h54 → _p2mH54
open _root_.P2Mb748e9da renaming h56 → _p2mH56
open _root_.P2Mb748e9da renaming h57 → _p2mH57
open _root_.P2Mb748e9da renaming h65 → _p2mH65
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h8 → _p2mH8
open _root_.P2Mb748e9da renaming h9 → _p2mH9
open _root_.P2Mb748e9da renaming h53 → _p2mH53
open _root_.P2Mb748e9da renaming h54 → _p2mH54
open _root_.P2Mb748e9da renaming h56 → _p2mH56
open _root_.P2Mb748e9da renaming h57 → _p2mH57
open _root_.P2Mb748e9da renaming h65 → _p2mH65
end
open _root_.P2Mb748e9da renaming h8 → _p2mH8
open _root_.P2Mb748e9da renaming h9 → _p2mH9
open _root_.P2Mb748e9da renaming h53 → _p2mH53
open _root_.P2Mb748e9da renaming h54 → _p2mH54
open _root_.P2Mb748e9da renaming h56 → _p2mH56
open _root_.P2Mb748e9da renaming h57 → _p2mH57
open _root_.P2Mb748e9da renaming h65 → _p2mH65
namespace AFT.CanonicalMoments.momentConstant
end AFT.CanonicalMoments.momentConstant
namespace AFT.CanonicalMoments.sumPattern
end AFT.CanonicalMoments.sumPattern
section
set_option maxHeartbeats 800000
namespace AFT.CanonicalMoments
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.AFT.CanonicalMoments.instDecidableEqSum_aFT_2
section Counting
variable {Copy PS BS PP BP : Type*}
  [Fintype Copy] [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h64 (primaryUsed bodyUsed : ℕ) :
    (Finset.univ.filter (fun pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP) =>
      (_root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2) ∧
        ((_root_.AFT.CanonicalMoments.usedLabels pattern.1).card, (_root_.AFT.CanonicalMoments.usedLabels pattern.2).card) = (primaryUsed, bodyUsed))).card ≤
      ((Fintype.card PP).descFactorial primaryUsed *
        (Fintype.card Copy * Fintype.card PS) ^ (Fintype.card Copy * Fintype.card PS)) *
      ((Fintype.card BP).descFactorial bodyUsed *
        (Fintype.card Copy * Fintype.card BS) ^ (Fintype.card Copy * Fintype.card BS)) := by
  have heq : Finset.univ.filter (fun pattern : (Copy → PS ↪ PP) × (Copy → BS ↪ BP) =>
      (_root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2) ∧
        ((_root_.AFT.CanonicalMoments.usedLabels pattern.1).card, (_root_.AFT.CanonicalMoments.usedLabels pattern.2).card) = (primaryUsed, bodyUsed)) =
      (Finset.univ.filter (fun pattern : Copy → PS ↪ PP => _root_.AFT.CanonicalMoments.NoSingleton pattern ∧ (_root_.AFT.CanonicalMoments.usedLabels pattern).card = primaryUsed)).product
        (Finset.univ.filter (fun pattern : Copy → BS ↪ BP => _root_.AFT.CanonicalMoments.NoSingleton pattern ∧ (_root_.AFT.CanonicalMoments.usedLabels pattern).card = bodyUsed)) := by
    ext pattern
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.product_eq_sprod, Finset.mem_product, Prod.mk.injEq]
    tauto
  rw [heq, Finset.product_eq_sprod, Finset.card_product]
  exact Nat.mul_le_mul (_p2mH28 primaryUsed) (_p2mH28 bodyUsed)
open _root_.P2Mb748e9da renaming h64 → _p2mH64
end Counting
open _root_.P2Mb748e9da renaming h64 → _p2mH64
variable {PS BS PP BP Color : Type*}
  [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h61 (primary body : _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (power : ℕ) (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP)
    (hprimaryLarge : 2 * Fintype.card PS ≤ Fintype.card PP)
    (hbodyLarge : 2 * Fintype.card BS ≤ Fintype.card BP) :
    (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => _root_.AFT.CanonicalMoments.twoPoolStatistic kernel word ^ power) ≤
      (_root_.AFT.CanonicalMoments.momentConstant (Fintype.card PS) power * _root_.AFT.CanonicalMoments.momentConstant (Fintype.card BS) power) *
        _root_.AFT.MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
          (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
          (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel ^ power := by
  let lp := power * Fintype.card PS
  let lb := power * Fintype.card BS
  let activity := _root_.AFT.MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
    (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel
  let denominator : ℝ := (((Fintype.card PP).descFactorial (Fintype.card PS) : ℝ) *
    ((Fintype.card BP).descFactorial (Fintype.card BS) : ℝ)) ^ power
  let survivors := Finset.univ.filter (fun pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP) =>
    _root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2)
  let support (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) :=
    ((_root_.AFT.CanonicalMoments.usedLabels pattern.1).card, (_root_.AFT.CanonicalMoments.usedLabels pattern.2).card)
  let term (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) :=
    (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (_root_.AFT.CanonicalMoments.patternProduct kernel (_root_.AFT.CanonicalMoments.sumPattern pattern)) / denominator
  have ha : 0 ≤ activity := _p2mH94 _ _ _ (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
  have hden : 0 < denominator := by
    apply pow_pos
    apply mul_pos
    · exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : Fintype.card PS ≤ Fintype.card PP))
    · exact_mod_cast (Nat.descFactorial_pos.mpr (by omega : Fintype.card BS ≤ Fintype.card BP))
  have hmaps (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) (_ : pattern ∈ survivors) :
      support pattern ∈ (Finset.range (lp + 1)).product (Finset.range (lb + 1)) := by
    have hp := _p2mH66 pattern.1
    have hb := _p2mH66 pattern.2
    simp only [Fintype.card_fin] at hp hb
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp),
      Finset.mem_range.mpr (Nat.lt_succ_of_le hb)⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps term
  have hused (used : ℕ × ℕ) (hused : used ∈ (Finset.range (lp + 1)).product (Finset.range (lb + 1))) :
      (∑ pattern ∈ survivors.filter (fun pattern => support pattern = used), term pattern) ≤
        (2 : ℝ) ^ (power * (Fintype.card PS + Fintype.card BS)) *
          ((lp : ℝ) ^ lp * (lb : ℝ) ^ lb * activity ^ power) := by
    let selected := survivors.filter (fun pattern => support pattern = used)
    have hcount : (selected.card : ℝ) ≤
        (((Fintype.card PP).descFactorial used.1 : ℝ) * (lp : ℝ) ^ lp) *
          (((Fintype.card BP).descFactorial used.2 : ℝ) * (lb : ℝ) ^ lb) := by
      have hh := _p2mH64 (Copy := Fin power) (PS := PS) (BS := BS)
        (PP := PP) (BP := BP) used.1 used.2
      simp only [Fintype.card_fin] at hh
      have hh' : selected.card ≤
          ((Fintype.card PP).descFactorial used.1 * lp ^ lp) *
            ((Fintype.card BP).descFactorial used.2 * lb ^ lb) := by
        convert hh using 1
        congr 1
        ext pattern
        simp only [selected, survivors, support, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.eta]
      exact_mod_cast hh'
    have hterm (pattern : (Fin power → PS ↪ PP) × (Fin power → BS ↪ BP)) (hpattern : pattern ∈ selected) :
        term pattern ≤ (Fintype.card PP : ℝ) ^ (lp - used.1) *
          (Fintype.card BP : ℝ) ^ (lb - used.2) * activity ^ power / denominator := by
      have hm := Finset.mem_filter.mp hpattern
      have hs : _root_.AFT.CanonicalMoments.NoSingleton pattern.1 ∧ _root_.AFT.CanonicalMoments.NoSingleton pattern.2 := (Finset.mem_filter.mp hm.1).2
      have hh := _p2mH65 primary body kernel pattern hs hprimary hbody
      have heqP : (_root_.AFT.CanonicalMoments.usedLabels pattern.1).card = used.1 := congrArg Prod.fst hm.2
      have heqB : (_root_.AFT.CanonicalMoments.usedLabels pattern.2).card = used.2 := congrArg Prod.snd hm.2
      rw [heqP, heqB] at hh
      apply div_le_div_of_nonneg_right _ hden.le
      exact (le_abs_self _).trans hh
    calc
      _ ≤ (selected.card : ℝ) * ((Fintype.card PP : ℝ) ^ (lp - used.1) *
          (Fintype.card BP : ℝ) ^ (lb - used.2) * activity ^ power / denominator) := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul selected term _ hterm
      _ ≤ ((((Fintype.card PP).descFactorial used.1 : ℝ) * (lp : ℝ) ^ lp) *
          (((Fintype.card BP).descFactorial used.2 : ℝ) * (lb : ℝ) ^ lb)) *
          ((Fintype.card PP : ℝ) ^ (lp - used.1) *
            (Fintype.card BP : ℝ) ^ (lb - used.2) * activity ^ power / denominator) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = ((((Fintype.card PP).descFactorial used.1 : ℝ) * (Fintype.card PP : ℝ) ^ (lp - used.1) *
          (((Fintype.card BP).descFactorial used.2 : ℝ) * (Fintype.card BP : ℝ) ^ (lb - used.2))) / denominator) *
          ((lp : ℝ) ^ lp * (lb : ℝ) ^ lb * activity ^ power) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (_p2mH63 (Fintype.card PP) (Fintype.card BP) (Fintype.card PS) (Fintype.card BS)
          power used.1 used.2 hprimary hbody hprimaryLarge hbodyLarge
          (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hused).1))
          (Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hused).2))) (by positivity)
  rw [_p2mH62 primary body kernel hcanonical power]
  change (∑ pattern ∈ survivors, _) / denominator ≤ _
  rw [Finset.sum_div]
  change (∑ pattern ∈ survivors, term pattern) ≤ _
  rw [← hgroup]
  apply (Finset.sum_le_sum hused).trans_eq
  simp only [Finset.sum_const, Finset.product_eq_sprod, Finset.card_product, Finset.card_range, nsmul_eq_mul, _root_.AFT.CanonicalMoments.momentConstant]
  dsimp only [lp, lb, activity]
  rw [Nat.mul_add power (Fintype.card PS) (Fintype.card BS), pow_add]
  push_cast
  ring
open _root_.P2Mb748e9da renaming h61 → _p2mH61
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h59 (primary body : _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (moment : ℕ) (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP)
    (hprimaryLarge : 2 * Fintype.card PS ≤ Fintype.card PP)
    (hbodyLarge : 2 * Fintype.card BS ≤ Fintype.card BP) :
    (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => |_root_.AFT.CanonicalMoments.twoPoolStatistic kernel word| ^ (2 * moment)) ≤
      (_root_.AFT.CanonicalMoments.momentConstant (Fintype.card PS) (2 * moment) * _root_.AFT.CanonicalMoments.momentConstant (Fintype.card BS) (2 * moment)) *
        _root_.AFT.MixedKernel.activity (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP))
          (fun _ : BS => 1 / Real.sqrt (Fintype.card BP)))
          (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel ^ (2 * moment) := by
  simpa only [pow_mul, sq_abs] using _p2mH61
    primary body kernel hcanonical (2 * moment) hprimary hbody hprimaryLarge hbodyLarge
open _root_.P2Mb748e9da renaming h59 → _p2mH59
end
open _root_.P2Mb748e9da renaming h59 → _p2mH59
open _root_.P2Mb748e9da renaming h61 → _p2mH61
open _root_.P2Mb748e9da renaming h64 → _p2mH64
end AFT.CanonicalMoments
open _root_.P2Mb748e9da renaming h59 → _p2mH59
open _root_.P2Mb748e9da renaming h61 → _p2mH61
open _root_.P2Mb748e9da renaming h64 → _p2mH64
end
open _root_.P2Mb748e9da renaming h59 → _p2mH59
open _root_.P2Mb748e9da renaming h61 → _p2mH61
open _root_.P2Mb748e9da renaming h64 → _p2mH64
section
namespace CurrentAFT.Parameters
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h401 (accuracyOrder : ℕ) :
    ((_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder : ℕ) + 1 : ℝ) / 4 =
      (accuracyOrder : ℝ) + 67 := by
  simp [_root_.CurrentAFT.Parameters.calibrationOrder]
  ring
open _root_.P2Mb748e9da renaming h401 → _p2mH401
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h402 (security accuracyOrder : ℕ) :
    (_root_.CurrentAFT.Parameters.modulus security : ℝ) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^
        (-(((_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder : ℕ) + 1 : ℝ) / 4)) ≤
      131072 / (_root_.CurrentAFT.Parameters.base security : ℝ) ^ (accuracyOrder + 3) := by
  have hb : (0 : ℝ) < _root_.CurrentAFT.Parameters.base security := by exact_mod_cast _root_.CurrentAFT.Parameters.base_pos security
  have hm : (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≤ 131072 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_bounds security).2
  rw [_p2mH401]
  have hexp : (accuracyOrder : ℝ) + 67 = ((accuracyOrder + 67 : ℕ) : ℝ) := by norm_num
  rw [hexp, Real.rpow_neg hb.le, Real.rpow_natCast, ← div_eq_mul_inv]
  calc
    _ ≤ (131072 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64) /
        (_root_.CurrentAFT.Parameters.base security : ℝ) ^ (accuracyOrder + 67) := by
      exact div_le_div_of_nonneg_right hm (pow_nonneg hb.le _)
    _ = _ := by
      have hsum : accuracyOrder + 67 = 64 + (accuracyOrder + 3) := by omega
      rw [hsum, pow_add]
      field_simp
open _root_.P2Mb748e9da renaming h402 → _p2mH402
end CurrentAFT.Parameters
open _root_.P2Mb748e9da renaming h401 → _p2mH401
open _root_.P2Mb748e9da renaming h402 → _p2mH402
end
open _root_.P2Mb748e9da renaming h401 → _p2mH401
open _root_.P2Mb748e9da renaming h402 → _p2mH402
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.AffineFlagCalibration
end CurrentAFT.AffineFlagCalibration
namespace CurrentAFT.AffineFlagCalibration.SimultaneousLaw
end CurrentAFT.AffineFlagCalibration.SimultaneousLaw
namespace CurrentAFT.AffineFlagCalibration.SimultaneousLaw.mk
end CurrentAFT.AffineFlagCalibration.SimultaneousLaw.mk
namespace CurrentAFT.AffineFlagCalibration.flagLaw
end CurrentAFT.AffineFlagCalibration.flagLaw
namespace CurrentAFT.AffineFlagCalibration.small_budget
end CurrentAFT.AffineFlagCalibration.small_budget
namespace CurrentAFT.CurrentFlagProgram
end CurrentAFT.CurrentFlagProgram
namespace CurrentAFT.CurrentFlagProgram.RationalModel
end CurrentAFT.CurrentFlagProgram.RationalModel
namespace CurrentAFT.CurrentFlagProgram.RationalModel.mk
end CurrentAFT.CurrentFlagProgram.RationalModel.mk
namespace CurrentAFT.CurrentRationalFlagLaw
end CurrentAFT.CurrentRationalFlagLaw
namespace CurrentAFT.CurrentRationalFlagLaw.RegularCertificate
end CurrentAFT.CurrentRationalFlagLaw.RegularCertificate
namespace CurrentAFT.CurrentRationalFlagLaw.affineFeatures
end CurrentAFT.CurrentRationalFlagLaw.affineFeatures
namespace CurrentAFT.CurrentRationalFlagLaw.affineSafe
end CurrentAFT.CurrentRationalFlagLaw.affineSafe
section
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.legLawModulusNeZero
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.currentModulusPrime
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h202 (security : ℕ) (input : _root_.CurrentAFT.AffineFlagCalibration.ProtectedInput security) :
    (((input.1 : ℤ) : ZMod (_root_.CurrentAFT.Parameters.modulus security)) = 0) ↔ (input.1 : ℤ) = 0 := by
  let zero : _root_.AFT.GaussianSource.Window (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) :=
    _root_.AFT.GaussianSource.windowZero (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)
  constructor
  · intro hc
    have hi := _root_.AFT.BoundaryCalibration.window_cast_injective (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)
      (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.AffineFlagCalibration.leg_input_separation security)
    have hz : input.1 = zero := hi (by simpa only [zero, _root_.AFT.GaussianSource.windowZero, Int.cast_zero] using hc)
    exact congrArg Subtype.val hz
  · intro hc
    rw [hc, Int.cast_zero]
open _root_.P2Mb748e9da renaming h202 → _p2mH202
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h193 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ _root_.CurrentAFT.AffineFlagCalibration.legOffsetBound security)
    (mark : ZMod (_root_.CurrentAFT.Parameters.modulus security)) (atom : ℝ)
    (ha0 : 0 ≤ atom) (haHalf : atom ≤ 1 / 2)
    (point : Bool × _root_.AFT.BoundaryCalibration.Chart (ZMod (_root_.CurrentAFT.Parameters.modulus security)))
    (hweight : (_root_.CurrentAFT.AffineFlagCalibration.currentLaw security baseline hbaseline mark atom ha0 haHalf).joint.weight point ≠ 0) :
    point.2.2.1 ≠ 0 := by
  let model := _root_.CurrentAFT.AffineFlagCalibration.currentLaw security baseline hbaseline mark atom ha0 haHalf
  intro hz
  have hr : model.regular.weight point.2 = 0 := model.regular_support point.2 (by simp [hz])
  have hm : model.marked.weight point.2 = 0 := model.marked_support point.2 (by simp [hz])
  apply hweight
  rw [model.decomposition point, hr, hm]
  split_ifs <;> simp
open _root_.P2Mb748e9da renaming h193 → _p2mH193
end
open _root_.P2Mb748e9da renaming h193 → _p2mH193
open _root_.P2Mb748e9da renaming h202 → _p2mH202
end CurrentAFT.AffineFlagCalibration
open _root_.P2Mb748e9da renaming h193 → _p2mH193
open _root_.P2Mb748e9da renaming h202 → _p2mH202
end
open _root_.P2Mb748e9da renaming h193 → _p2mH193
open _root_.P2Mb748e9da renaming h202 → _p2mH202
namespace CurrentAFT.Parameters
end CurrentAFT.Parameters
namespace CurrentAFT.Parameters.base
end CurrentAFT.Parameters.base
namespace CurrentAFT.Parameters.bodySize
end CurrentAFT.Parameters.bodySize
namespace CurrentAFT.Parameters.calibrationOrder
end CurrentAFT.Parameters.calibrationOrder
namespace CurrentAFT.Parameters.dimension
end CurrentAFT.Parameters.dimension
namespace CurrentAFT.Parameters.leastPrimeWitness
end CurrentAFT.Parameters.leastPrimeWitness
namespace CurrentAFT.Parameters.legCount
end CurrentAFT.Parameters.legCount
namespace CurrentAFT.Parameters.primeThreshold
end CurrentAFT.Parameters.primeThreshold
namespace CurrentAFT.Parameters.scale
end CurrentAFT.Parameters.scale
section
namespace CurrentAFT.ControlCoordinates
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ControlCoordinates.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h235 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := Primary) (Body := Body) r s) :
    _root_.CurrentAFT.ControlCoordinates.kernelMean primary body kernel =
      (_root_.AFT.FiniteDist.independent (fun _ : Fin r => primary)).expectation (fun colors =>
        (_root_.AFT.FiniteDist.independent (fun _ : Fin s => body)).expectation (kernel colors)) := by
  simp only [_root_.CurrentAFT.ControlCoordinates.kernelMean, _root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.prod_weight,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
open _root_.P2Mb748e9da renaming h235 → _p2mH235
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h236 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := Primary) (Body := Body) r s) :
    _root_.CurrentAFT.ControlCoordinates.kernelMean primary body kernel =
      (_root_.AFT.FiniteDist.independent (fun _ : Fin s => body)).expectation (fun centers =>
        (_root_.AFT.FiniteDist.independent (fun _ : Fin r => primary)).expectation (fun colors => kernel colors centers)) := by
  rw [_p2mH235]
  simp only [_root_.AFT.FiniteDist.expectation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro centers _
  apply Finset.sum_congr rfl
  intro colors _
  ring
open _root_.P2Mb748e9da renaming h236 → _p2mH236
end
open _root_.P2Mb748e9da renaming h235 → _p2mH235
open _root_.P2Mb748e9da renaming h236 → _p2mH236
end CurrentAFT.ControlCoordinates
open _root_.P2Mb748e9da renaming h235 → _p2mH235
open _root_.P2Mb748e9da renaming h236 → _p2mH236
end
open _root_.P2Mb748e9da renaming h235 → _p2mH235
open _root_.P2Mb748e9da renaming h236 → _p2mH236
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.pairEnergy
end AFT.BlockDensity.pairEnergy
namespace AFT.BlockDensity.tripleEnergy
end AFT.BlockDensity.tripleEnergy
namespace CurrentAFT.ActualControls
end CurrentAFT.ActualControls
namespace CurrentAFT.ActualControls.bodyResidueReference
end CurrentAFT.ActualControls.bodyResidueReference
namespace CurrentAFT.ActualControls.primaryResidueReference
end CurrentAFT.ActualControls.primaryResidueReference
namespace CurrentAFT.ActualControls.safeResidueEquiv
end CurrentAFT.ActualControls.safeResidueEquiv
namespace CurrentAFT.LocalReferenceEnergy
end CurrentAFT.LocalReferenceEnergy
namespace CurrentAFT.LocalReferenceEnergy.attachmentAt
end CurrentAFT.LocalReferenceEnergy.attachmentAt
namespace CurrentAFT.LocalReferenceEnergy.averagedPair_height
end CurrentAFT.LocalReferenceEnergy.averagedPair_height
namespace CurrentAFT.LocalReferenceEnergy.pairAt
end CurrentAFT.LocalReferenceEnergy.pairAt
namespace CurrentAFT.LocalReferenceEnergy.uniformReference
end CurrentAFT.LocalReferenceEnergy.uniformReference
section
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy InwardAnchor
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.anchorWidthNeZero
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff activation
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h164 (security : ℕ) : (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).weight true = _root_.CurrentAFT.DiffuseProfiles.activation security := rfl
open _root_.P2Mb748e9da renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h163 (security : ℕ) : (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).weight false = 1 - _root_.CurrentAFT.DiffuseProfiles.activation security := rfl
open _root_.P2Mb748e9da renaming h163 → _p2mH163
end
open _root_.P2Mb748e9da renaming h163 → _p2mH163
open _root_.P2Mb748e9da renaming h164 → _p2mH164
end CurrentAFT.ActualPublicLegCharge
open _root_.P2Mb748e9da renaming h163 → _p2mH163
open _root_.P2Mb748e9da renaming h164 → _p2mH164
end
open _root_.P2Mb748e9da renaming h163 → _p2mH163
open _root_.P2Mb748e9da renaming h164 → _p2mH164
section
namespace CurrentAFT
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h457 {weight : ℝ} (hweight : weight ≤ 0) : _root_.CurrentAFT.clip weight = 0 := by
  simp [_root_.CurrentAFT.clip, max_eq_left hweight]
open _root_.P2Mb748e9da renaming h457 → _p2mH457
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h458 {weight : ℝ} (hweight : 2 ≤ weight) : _root_.CurrentAFT.clip weight = 2 := by
  have hnonneg : 0 ≤ weight := by linarith
  simp [_root_.CurrentAFT.clip, max_eq_right hnonneg, min_eq_left hweight]
open _root_.P2Mb748e9da renaming h458 → _p2mH458
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h456 {weight : ℝ} (hweight : weight ∈ Set.Icc (0 : ℝ) 2) :
    _root_.CurrentAFT.clip weight = weight := by
  simp [_root_.CurrentAFT.clip, max_eq_right hweight.1, min_eq_right hweight.2]
open _root_.P2Mb748e9da renaming h456 → _p2mH456
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h455 (weight : ℝ) (moment : ℕ) (hmoment : 1 ≤ moment) :
    |weight - _root_.CurrentAFT.clip weight| ≤ |weight - 1| ^ (2 * moment) := by
  rcases le_total weight 0 with hlow | hlow
  · rw [_p2mH457 hlow]
    have hbase : 1 ≤ |weight - 1| := by
      rw [abs_of_nonpos (by linarith : weight - 1 ≤ 0)]
      linarith
    calc
      |weight - 0| ≤ |weight - 1| := by
        rw [sub_zero, abs_of_nonpos hlow,
          abs_of_nonpos (by linarith : weight - 1 ≤ 0)]
        linarith
      _ = |weight - 1| ^ 1 := by simp
      _ ≤ |weight - 1| ^ (2 * moment) := pow_le_pow_right₀ hbase (by omega)
  · rcases le_total weight 2 with hhigh | hhigh
    · rw [_p2mH456 ⟨hlow, hhigh⟩, sub_self, abs_zero]
      positivity
    · rw [_p2mH458 hhigh]
      have hbase : 1 ≤ |weight - 1| := by
        rw [abs_of_nonneg (by linarith : 0 ≤ weight - 1)]
        linarith
      calc
        |weight - 2| ≤ |weight - 1| := by
          rw [abs_of_nonneg (by linarith : 0 ≤ weight - 2),
            abs_of_nonneg (by linarith : 0 ≤ weight - 1)]
          linarith
        _ = |weight - 1| ^ 1 := by simp
        _ ≤ |weight - 1| ^ (2 * moment) := pow_le_pow_right₀ hbase (by omega)
open _root_.P2Mb748e9da renaming h455 → _p2mH455
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h459 {Index : Type*} [Fintype Index]
    (reference weight : Index → ℝ) (hreference : ∀ index, 0 ≤ reference index)
    (moment : ℕ) (hmoment : 1 ≤ moment) :
    (∑ index, reference index * |weight index - _root_.CurrentAFT.clip (weight index)|) ≤
      ∑ index, reference index * |weight index - 1| ^ (2 * moment) := by
  apply Finset.sum_le_sum
  intro index _
  exact mul_le_mul_of_nonneg_left
    (_p2mH455 (weight index) moment hmoment) (hreference index)
open _root_.P2Mb748e9da renaming h459 → _p2mH459
end CurrentAFT
open _root_.P2Mb748e9da renaming h455 → _p2mH455
open _root_.P2Mb748e9da renaming h456 → _p2mH456
open _root_.P2Mb748e9da renaming h457 → _p2mH457
open _root_.P2Mb748e9da renaming h458 → _p2mH458
open _root_.P2Mb748e9da renaming h459 → _p2mH459
end
open _root_.P2Mb748e9da renaming h455 → _p2mH455
open _root_.P2Mb748e9da renaming h456 → _p2mH456
open _root_.P2Mb748e9da renaming h457 → _p2mH457
open _root_.P2Mb748e9da renaming h458 → _p2mH458
open _root_.P2Mb748e9da renaming h459 → _p2mH459
namespace CurrentAFT.ActualPublicLegCharge
end CurrentAFT.ActualPublicLegCharge
namespace CurrentAFT.ActualPublicLegCharge.PublicSeed
end CurrentAFT.ActualPublicLegCharge.PublicSeed
namespace CurrentAFT.ActualPublicLegCharge.PublicSeed.mk
end CurrentAFT.ActualPublicLegCharge.PublicSeed.mk
namespace CurrentAFT.ActualPublicLegCharge.seedLaw
end CurrentAFT.ActualPublicLegCharge.seedLaw
namespace CurrentAFT.clippingLoss
end CurrentAFT.clippingLoss
namespace CurrentAFT.endpointMass
end CurrentAFT.endpointMass
section
namespace CurrentAFT.ActualPublicLegCharge
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram InwardAnchor
open scoped BigOperators Classical Fin.NatCast
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.chargeFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualPublicLegCharge.chargeModulusNeZero
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h168 (security : ℕ) (shift : ℤ) (color : _root_.CurrentAFT.ActualPublicLegCharge.Palette security)
    (hlower : 0 ≤ (color.val : ℤ) + shift)
    (hupper : (color.val : ℤ) + shift < _root_.CurrentAFT.Parameters.modulus security) :
    ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift color).val : ℤ) = (color.val : ℤ) + shift := by
  let output : _root_.CurrentAFT.ActualPublicLegCharge.Palette security := ⟨((color.val : ℤ) + shift).toNat, by omega⟩
  have houtput : (output.val : ℤ) = (color.val : ℤ) + shift := by dsimp [output]; omega
  have hemb (point : _root_.CurrentAFT.ActualPublicLegCharge.Palette security) : (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) point =
      (point.val : ZMod (_root_.CurrentAFT.Parameters.modulus security)) := _root_.CurrentAFT.ActualPublicLegCharge.finEquiv_natCast _ point
  have hequal : _root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift color = output := by
    apply (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).injective
    change (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security))
      ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).symm
        ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) color + (shift : ZMod (_root_.CurrentAFT.Parameters.modulus security)))) = _
    rw [RingEquiv.apply_symm_apply, hemb, hemb]
    have hcast := congrArg (fun value : ℤ => (value : ZMod (_root_.CurrentAFT.Parameters.modulus security))) houtput
    simpa only [Int.cast_natCast, Int.cast_add] using hcast.symm
  rw [hequal, houtput]
open _root_.P2Mb748e9da renaming h168 → _p2mH168
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h167 (security : ℕ) (primary : _root_.CurrentAFT.ActualPublicLegCharge.Palette security) (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) :
    (_root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary scalar seed).val =
      ((_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 - primary.val + _root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - scalar.val).toNat := by
  have hs := _root_.CurrentAFT.InwardAnchor.integerPoint_safe security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using _root_.CurrentAFT.InwardAnchor.scalar_bound security scalar)
  have hp := _root_.CurrentAFT.InwardAnchor.point_value security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using _root_.CurrentAFT.InwardAnchor.scalar_bound security scalar)
  have hblur := abs_le.mp (_root_.CurrentAFT.ActualPublicLegCharge.blur_bound security seed)
  have hmargin : (_root_.CurrentAFT.Parameters.safeMargin security : ℤ) = 3 * (_root_.CurrentAFT.Parameters.sourceCutoff security : ℤ) := by
    rw [_root_.CurrentAFT.Parameters.safeMargin]
    push_cast
    ring
  have hcut := _root_.CurrentAFT.InwardAnchor.sourceCutoff_pos security
  have hvalue := _p2mH168 security (seed.blur.1.val - seed.blur.2.val)
    (_root_.CurrentAFT.InwardAnchor.point security primary seed.coin seed.anchorIndex (-scalar.val)
      (by simpa only [abs_neg] using _root_.CurrentAFT.InwardAnchor.scalar_bound security scalar))
    (by rw [hp]; omega) (by rw [hp]; omega)
  change (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (seed.blur.1.val - seed.blur.2.val) _).val = _
  apply Int.ofNat_inj.mp
  rw [hvalue, hp]
  have hequal : _root_.CurrentAFT.InwardAnchor.integerPoint security primary seed.coin seed.anchorIndex (-scalar.val) +
      (seed.blur.1.val - seed.blur.2.val) =
      (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 - primary.val + _root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - scalar.val := by
    unfold _root_.CurrentAFT.InwardAnchor.integerPoint _root_.CurrentAFT.ActualPublicLegCharge.publicShift _root_.CurrentAFT.ActualPublicLegCharge.signedOffset
    ring
  rw [← hequal, Int.toNat_of_nonneg]
  omega
open _root_.P2Mb748e9da renaming h167 → _p2mH167
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h166 (security : ℕ) (primary : _root_.CurrentAFT.ActualPublicLegCharge.Palette security) (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (pair : _root_.CurrentAFT.ActualPublicLegCharge.Palette security × _root_.CurrentAFT.ActualPublicLegCharge.Palette security) :
    (_root_.CurrentAFT.ActualPublicLegCharge.markedLaw security primary scalar seed).weight pair =
      if (primary, _root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary scalar seed) = pair then 1 else 0 := by
  simp [_root_.CurrentAFT.ActualPublicLegCharge.markedLaw, _root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.uniform_weight]
open _root_.P2Mb748e9da renaming h166 → _p2mH166
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h165 (security : ℕ) (primary : _root_.CurrentAFT.ActualPublicLegCharge.Palette security) (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (pair : _root_.CurrentAFT.ActualPublicLegCharge.Palette security × _root_.CurrentAFT.ActualPublicLegCharge.Palette security)
    (hweight : (_root_.CurrentAFT.ActualPublicLegCharge.markedLaw security primary scalar seed).weight pair ≠ 0) :
    (pair.1.val : ℤ) + pair.2.val = (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 + _root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - scalar.val := by
  rw [_p2mH166] at hweight
  have hpair : pair = (primary, _root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary scalar seed) := by
    by_contra hne
    simp only [Ne.symm hne, if_false, ne_eq, not_true_eq_false] at hweight
  subst pair
  have hs := _root_.CurrentAFT.InwardAnchor.integerPoint_safe security primary seed.coin seed.anchorIndex (-scalar.val)
    (by simpa only [abs_neg] using _root_.CurrentAFT.InwardAnchor.scalar_bound security scalar)
  have hblur := abs_le.mp (_root_.CurrentAFT.ActualPublicLegCharge.blur_bound security seed)
  have hcut := _root_.CurrentAFT.InwardAnchor.sourceCutoff_pos security
  rw [_p2mH167]
  rw [Int.toNat_of_nonneg]
  · ring
  · unfold _root_.CurrentAFT.InwardAnchor.integerPoint _root_.CurrentAFT.ActualPublicLegCharge.publicShift _root_.CurrentAFT.ActualPublicLegCharge.signedOffset at *
    rw [_root_.CurrentAFT.Parameters.safeMargin] at hs
    push_cast at hs
    omega
open _root_.P2Mb748e9da renaming h165 → _p2mH165
end
open _root_.P2Mb748e9da renaming h165 → _p2mH165
open _root_.P2Mb748e9da renaming h166 → _p2mH166
open _root_.P2Mb748e9da renaming h167 → _p2mH167
open _root_.P2Mb748e9da renaming h168 → _p2mH168
end CurrentAFT.ActualPublicLegCharge
open _root_.P2Mb748e9da renaming h165 → _p2mH165
open _root_.P2Mb748e9da renaming h166 → _p2mH166
open _root_.P2Mb748e9da renaming h167 → _p2mH167
open _root_.P2Mb748e9da renaming h168 → _p2mH168
end
open _root_.P2Mb748e9da renaming h165 → _p2mH165
open _root_.P2Mb748e9da renaming h166 → _p2mH166
open _root_.P2Mb748e9da renaming h167 → _p2mH167
open _root_.P2Mb748e9da renaming h168 → _p2mH168
namespace CurrentAFT.ActualPublicLegCharge.markedLaw
end CurrentAFT.ActualPublicLegCharge.markedLaw
namespace CurrentAFT.CurrentFlagProgram.current
end CurrentAFT.CurrentFlagProgram.current
section
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.pairGraphDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.pairModulusPrime
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h189 (security : ℕ) (shift : ℤ)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (hsum : (second.val : ℤ) = (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 + shift - first.val) :
    _root_.CurrentAFT.AffineFlagCalibration.companion security shift first = second := by
  apply (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).injective
  have he : (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) (_root_.CurrentAFT.AffineFlagCalibration.companion security shift first) =
      -1 + (shift : ZMod (_root_.CurrentAFT.Parameters.modulus security)) -
        (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) first :=
    (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).apply_symm_apply _
  rw [he, _root_.CurrentAFT.ActualPublicLegCharge.finEquiv_natCast, _root_.CurrentAFT.ActualPublicLegCharge.finEquiv_natCast]
  have hc := congrArg (fun n : ℤ => (n : ZMod (_root_.CurrentAFT.Parameters.modulus security))) hsum
  push_cast at hc
  simpa only [ZMod.natCast_self, zero_sub] using hc.symm
open _root_.P2Mb748e9da renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h190 (security : ℕ) (shift : ℤ) (first second : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (hfirst : (first.val : ℤ) ∈ _root_.AFT.TrimmedSlice.slice (_root_.CurrentAFT.Parameters.modulus security) 1 shift) :
    _root_.CurrentAFT.AffineFlagCalibration.companion security shift first = second ↔
      (second.val : ℤ) = (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 + shift - first.val := by
  have hs := (_root_.AFT.TrimmedSlice.mem_slice _ _ _ _).mp hfirst
  let value : ℤ := (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 + shift - first.val
  have hv : 0 ≤ value ∧ value < _root_.CurrentAFT.Parameters.modulus security := by dsimp [value]; omega
  let output : _root_.CurrentAFT.AffineFlagCalibration.Palette security := ⟨value.toNat, by omega⟩
  have hout : (output.val : ℤ) = value := by dsimp [output]; omega
  have hc : _root_.CurrentAFT.AffineFlagCalibration.companion security shift first = output :=
    _p2mH189 security shift first output hout
  rw [hc]
  constructor
  · rintro rfl
    exact hout
  · intro he
    apply Fin.ext
    exact_mod_cast hout.trans he.symm
open _root_.P2Mb748e9da renaming h190 → _p2mH190
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h198 {A B : Type*} [Fintype A] [Fintype B]
    (law : _root_.AFT.FiniteDist A) (f : A → B) (a : A) (b : B) :
    (law.map (fun x => (x, f x))).weight (a, b) =
      law.weight a * (if f a = b then 1 else 0) := by
  simp only [_root_.AFT.FiniteDist.map_weight, Prod.mk.injEq, ite_and,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  split_ifs <;> simp
open _root_.P2Mb748e9da renaming h198 → _p2mH198
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h205 (security : ℕ) (shift : ℤ)
    (hclear : 2 + |shift| < (_root_.CurrentAFT.Parameters.modulus security : ℤ))
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Palette security) :
    ((_root_.AFT.TrimmedSlice.finiteLaw (_root_.CurrentAFT.Parameters.modulus security) 1 shift (by norm_num) hclear).map
      (_root_.CurrentAFT.AffineFlagCalibration.pairProjection security shift)).weight (first, second) =
        _root_.AFT.TrimmedSlice.orderedPairSlice (_root_.CurrentAFT.Parameters.modulus security) 1 shift first second := by
  change ((_root_.AFT.TrimmedSlice.finiteLaw (_root_.CurrentAFT.Parameters.modulus security) 1 shift (by norm_num) hclear).map
    (fun x => (x, _root_.CurrentAFT.AffineFlagCalibration.companion security shift x))).weight (first, second) = _
  rw [_p2mH198, _root_.AFT.TrimmedSlice.finiteLaw_weight]
  unfold _root_.AFT.TrimmedSlice.orderedPairSlice
  by_cases hc : (first.val : ℤ) ∈ _root_.AFT.TrimmedSlice.slice (_root_.CurrentAFT.Parameters.modulus security) 1 shift
  · rw [_p2mH190 security shift first second hc]
    split_ifs <;> rfl
  · simp only [_root_.AFT.TrimmedSlice.law, if_neg hc, zero_mul]
open _root_.P2Mb748e9da renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h196 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ _root_.CurrentAFT.AffineFlagCalibration.legOffsetBound security) (mark : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) (color : _root_.CurrentAFT.AffineFlagCalibration.Palette security) :
    (_root_.CurrentAFT.AffineFlagCalibration.evaluatedPrimary security baseline hbaseline mark first second).weight color =
      if first.val = 0 then
        (1 / 2 : ℝ) * (if color ∈ _root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1
          (baseline - second.val) then
            ((_root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0) +
          (1 / 2 : ℝ) * (if color = mark then 1 else 0)
      else if color ∈ _root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val) then
        ((_root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0 := by
  let input : _root_.CurrentAFT.AffineFlagCalibration.ProtectedInput security := (first, second)
  let model := _root_.CurrentAFT.AffineFlagCalibration.currentLaw security baseline hbaseline
    ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) mark) (1 / 2) (by norm_num) (by norm_num)
  have heq : _root_.CurrentAFT.AffineFlagCalibration.evaluatedPrimary security baseline hbaseline mark first second =
      (model.joint.map (fun point => _root_.AFT.BoundaryCalibration.feature
        ((first.val : ℤ) : ZMod (_root_.CurrentAFT.Parameters.modulus security))
        ((second.val : ℤ) : ZMod (_root_.CurrentAFT.Parameters.modulus security)) point.2)).map
          (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).toEquiv.symm := by
    rw [_root_.AFT.FiniteDist.map_map]
    rfl
  rw [heq, _root_.AFT.FiniteDist.map_equiv_weight]
  change (model.joint.map (fun point => _root_.AFT.BoundaryCalibration.feature
    (_root_.AFT.BoundaryCalibration.protectedInputs (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) input).1
    (_root_.AFT.BoundaryCalibration.protectedInputs (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) input).2 point.2)).weight
      ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) color) = _
  by_cases hf : first.val = 0
  · have hon := model.on_line input ((_p2mH202 security input).mpr hf)
      ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) color)
    rw [hon, if_pos hf]
    simp only [input, _root_.AFT.BoundaryCalibration.protectedPalettes, _root_.AFT.BoundaryCalibration.fieldPalette, Finset.mem_map_equiv,
      Finset.card_map, one_div]
    norm_num
  · have hoff := model.off_line input
      (fun hz => hf ((_p2mH202 security input).mp hz))
      ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) color)
    rw [hoff, if_neg hf]
    simp only [input, _root_.AFT.BoundaryCalibration.protectedPalettes, _root_.AFT.BoundaryCalibration.fieldPalette, Finset.mem_map_equiv,
      Finset.card_map]
    have hsym : (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).symm
        ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) color) = color :=
      (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).symm_apply_apply color
    exact congrArg (fun a : _root_.CurrentAFT.AffineFlagCalibration.Palette security =>
      if a ∈ _root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val) then
        ((_root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0) hsym
open _root_.P2Mb748e9da renaming h196 → _p2mH196
end
open _root_.P2Mb748e9da renaming h189 → _p2mH189
open _root_.P2Mb748e9da renaming h190 → _p2mH190
open _root_.P2Mb748e9da renaming h196 → _p2mH196
open _root_.P2Mb748e9da renaming h198 → _p2mH198
open _root_.P2Mb748e9da renaming h205 → _p2mH205
end CurrentAFT.AffineFlagCalibration
open _root_.P2Mb748e9da renaming h189 → _p2mH189
open _root_.P2Mb748e9da renaming h190 → _p2mH190
open _root_.P2Mb748e9da renaming h196 → _p2mH196
open _root_.P2Mb748e9da renaming h198 → _p2mH198
open _root_.P2Mb748e9da renaming h205 → _p2mH205
end
open _root_.P2Mb748e9da renaming h189 → _p2mH189
open _root_.P2Mb748e9da renaming h190 → _p2mH190
open _root_.P2Mb748e9da renaming h196 → _p2mH196
open _root_.P2Mb748e9da renaming h198 → _p2mH198
open _root_.P2Mb748e9da renaming h205 → _p2mH205
section
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration ActualPublicLegCharge DiffuseProfiles
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h188 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ _root_.CurrentAFT.AffineFlagCalibration.legOffsetBound security) (second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    2 + |baseline - second.val| < (_root_.CurrentAFT.Parameters.modulus security : ℤ) := by
  have hs := _root_.CurrentAFT.InwardAnchor.scalar_bound security second
  have hroom := _root_.CurrentAFT.AffineFlagCalibration.leg_trimmed_room security
  have hB : 0 < _root_.CurrentAFT.Parameters.sourceCutoff security := _root_.CurrentAFT.InwardAnchor.sourceCutoff_pos security
  have ha := (abs_sub baseline second.val).trans (add_le_add hbaseline hs)
  omega
open _root_.P2Mb748e9da renaming h188 → _p2mH188
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h195 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ _root_.CurrentAFT.AffineFlagCalibration.legOffsetBound security) (mark : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) (pair : _root_.CurrentAFT.AffineFlagCalibration.Palette security × _root_.CurrentAFT.AffineFlagCalibration.Palette security) :
    (_root_.CurrentAFT.AffineFlagCalibration.evaluatedPair security baseline hbaseline mark first second).weight pair =
      if first.val = 0 then
        (1 / 2 : ℝ) * _root_.AFT.TrimmedSlice.orderedPairSlice (_root_.CurrentAFT.Parameters.modulus security) 1
          (baseline - second.val) pair.1 pair.2 +
        (1 / 2 : ℝ) * (if _root_.CurrentAFT.AffineFlagCalibration.pairProjection security (baseline - second.val) mark = pair then 1 else 0)
      else _root_.AFT.TrimmedSlice.orderedPairSlice (_root_.CurrentAFT.Parameters.modulus security) 1
        (baseline - second.val) pair.1 pair.2 := by
  let sliceLaw := _root_.AFT.TrimmedSlice.finiteLaw (_root_.CurrentAFT.Parameters.modulus security) 1
    (baseline - second.val) (by norm_num) (_p2mH188 security baseline hbaseline second)
  have hslice (color : _root_.CurrentAFT.AffineFlagCalibration.Palette security) : sliceLaw.weight color =
      if color ∈ _root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val) then
        ((_root_.AFT.TrimmedSlice.paletteSlice (_root_.CurrentAFT.Parameters.modulus security) 1 (baseline - second.val)).card : ℝ)⁻¹ else 0 := by
    dsimp only [sliceLaw, _root_.AFT.TrimmedSlice.finiteLaw, _root_.AFT.FiniteDist.uniformSafe]
    split_ifs <;> rfl
  have hdiffuse := _p2mH205 security (baseline - second.val)
    (_p2mH188 security baseline hbaseline second) pair.1 pair.2
  change (sliceLaw.map (fun x => (x, _root_.CurrentAFT.AffineFlagCalibration.companion security (baseline - second.val) x))).weight
    (pair.1, pair.2) = _ at hdiffuse
  rw [_p2mH198] at hdiffuse
  have hpoint : (if pair.1 = mark then (1 : ℝ) else 0) *
      (if _root_.CurrentAFT.AffineFlagCalibration.companion security (baseline - second.val) pair.1 = pair.2 then 1 else 0) =
      if _root_.CurrentAFT.AffineFlagCalibration.pairProjection security (baseline - second.val) mark = pair then 1 else 0 := by
    rcases pair with ⟨a, b⟩
    by_cases ha : a = mark
    · subst a
      simp only [_root_.CurrentAFT.AffineFlagCalibration.pairProjection, Prod.mk.injEq, true_and]
      split_ifs <;> norm_num
    · simp [ha, _root_.CurrentAFT.AffineFlagCalibration.pairProjection, Ne.symm ha]
  change ((_root_.CurrentAFT.AffineFlagCalibration.evaluatedPrimary security baseline hbaseline mark first second).map
    (fun x => (x, _root_.CurrentAFT.AffineFlagCalibration.companion security (baseline - second.val) x))).weight (pair.1, pair.2) = _
  rw [_p2mH198, _p2mH196]
  rw [hslice pair.1] at hdiffuse
  split_ifs at hdiffuse hpoint ⊢ <;>
    simp only [mul_zero, mul_one, add_zero, zero_add] at * <;> linarith
open _root_.P2Mb748e9da renaming h195 → _p2mH195
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h187 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ _root_.CurrentAFT.AffineFlagCalibration.legOffsetBound security) (mark : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) (pair : _root_.CurrentAFT.AffineFlagCalibration.Palette security × _root_.CurrentAFT.AffineFlagCalibration.Palette security) :
    ((_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (fun first => _root_.CurrentAFT.AffineFlagCalibration.evaluatedPair security baseline hbaseline mark first second)).weight pair =
      (1 - _root_.CurrentAFT.DiffuseProfiles.activation security) * _root_.AFT.TrimmedSlice.orderedPairSlice (_root_.CurrentAFT.Parameters.modulus security) 1
        (baseline - second.val) pair.1 pair.2 +
      _root_.CurrentAFT.DiffuseProfiles.activation security * (if _root_.CurrentAFT.AffineFlagCalibration.pairProjection security (baseline - second.val) mark = pair then 1 else 0) := by
  let zero := _root_.AFT.GaussianSource.windowZero (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)
  have hz (first : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) : first.val = 0 ↔ first = zero := by
    constructor
    · intro he
      exact Subtype.ext he
    · rintro rfl
      rfl
  let d := _root_.AFT.TrimmedSlice.orderedPairSlice (_root_.CurrentAFT.Parameters.modulus security) 1
    (baseline - second.val) pair.1 pair.2
  let m : ℝ := if _root_.CurrentAFT.AffineFlagCalibration.pairProjection security (baseline - second.val) mark = pair then 1 else 0
  have hrow (first : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
      (_root_.CurrentAFT.AffineFlagCalibration.evaluatedPair security baseline hbaseline mark first second).weight pair =
        d + if first = zero then (1 / 2 : ℝ) * (m - d) else 0 := by
    rw [_p2mH195]
    by_cases hf : first.val = 0
    · simp only [if_pos hf, if_pos ((hz first).mp hf)]
      dsimp [d, m]
      ring
    · simp only [if_neg hf, if_neg (mt (hz first).mpr hf), add_zero]
      rfl
  rw [_root_.AFT.FiniteDist.mix_weight]
  simp_rw [hrow, mul_add, mul_ite, mul_zero]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  dsimp only [d, m, zero, _root_.CurrentAFT.DiffuseProfiles.activation]
  split_ifs <;> ring
open _root_.P2Mb748e9da renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h200 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security) (second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) :
    _root_.CurrentAFT.AffineFlagCalibration.pairProjection security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val) primary =
      (primary, _root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary second seed) := by
  have hc := _p2mH165 security primary second seed
    (primary, _root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary second seed)
    (by rw [_p2mH166]; simp)
  have hs : _root_.CurrentAFT.AffineFlagCalibration.companion security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val) primary =
      _root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary second seed := _p2mH189 security _ _ _ (by
        dsimp only at hc
        omega)
  exact congrArg (fun color => (primary, color)) hs
open _root_.P2Mb748e9da renaming h200 → _p2mH200
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h204 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security) (second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) :
    _root_.CurrentAFT.ActualPublicLegCharge.refinedPair security primary second (_root_.CurrentAFT.AffineFlagCalibration.setMarked security seed true) =
      _root_.CurrentAFT.ActualPublicLegCharge.markedLaw security primary second seed := rfl
open _root_.P2Mb748e9da renaming h204 → _p2mH204
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h203 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security) (second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) :
    _root_.CurrentAFT.ActualPublicLegCharge.refinedPair security primary second (_root_.CurrentAFT.AffineFlagCalibration.setMarked security seed false) =
      _root_.CurrentAFT.ActualPublicLegCharge.diffuseLaw security primary second seed := rfl
open _root_.P2Mb748e9da renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h197 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (fun first => _root_.CurrentAFT.AffineFlagCalibration.evaluatedPair security
      (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed)
      (by simpa only [_root_.CurrentAFT.AffineFlagCalibration.legOffsetBound, add_sub_assoc] using _root_.CurrentAFT.ActualPublicLegCharge.publicShift_bound security primary seed)
      primary first second) =
      (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).mix (fun flag =>
        _root_.CurrentAFT.ActualPublicLegCharge.refinedPair security primary second (_root_.CurrentAFT.AffineFlagCalibration.setMarked security seed flag)) := by
  ext pair
  rw [_p2mH187, _root_.AFT.FiniteDist.mix_weight, Fintype.sum_bool]
  simp only [_p2mH204, _p2mH203,
    _p2mH164, _p2mH163]
  rw [_p2mH166, _p2mH200]
  dsimp only [_root_.CurrentAFT.ActualPublicLegCharge.diffuseLaw]
  split_ifs <;> ring
open _root_.P2Mb748e9da renaming h197 → _p2mH197
end
open _root_.P2Mb748e9da renaming h187 → _p2mH187
open _root_.P2Mb748e9da renaming h188 → _p2mH188
open _root_.P2Mb748e9da renaming h195 → _p2mH195
open _root_.P2Mb748e9da renaming h197 → _p2mH197
open _root_.P2Mb748e9da renaming h200 → _p2mH200
open _root_.P2Mb748e9da renaming h203 → _p2mH203
open _root_.P2Mb748e9da renaming h204 → _p2mH204
end CurrentAFT.AffineFlagCalibration
open _root_.P2Mb748e9da renaming h187 → _p2mH187
open _root_.P2Mb748e9da renaming h188 → _p2mH188
open _root_.P2Mb748e9da renaming h195 → _p2mH195
open _root_.P2Mb748e9da renaming h197 → _p2mH197
open _root_.P2Mb748e9da renaming h200 → _p2mH200
open _root_.P2Mb748e9da renaming h203 → _p2mH203
open _root_.P2Mb748e9da renaming h204 → _p2mH204
end
open _root_.P2Mb748e9da renaming h187 → _p2mH187
open _root_.P2Mb748e9da renaming h188 → _p2mH188
open _root_.P2Mb748e9da renaming h195 → _p2mH195
open _root_.P2Mb748e9da renaming h197 → _p2mH197
open _root_.P2Mb748e9da renaming h200 → _p2mH200
open _root_.P2Mb748e9da renaming h203 → _p2mH203
open _root_.P2Mb748e9da renaming h204 → _p2mH204
section
namespace CurrentAFT.PhysicalSynthesis
open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.PhysicalSynthesis.classicalFinDecidableEq
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
  primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw
set_option maxRecDepth 8192
private theorem _root_.P2Mb748e9da.h466 {Input Output : Type*} [Fintype Input] [Fintype Output]
    (count : ℕ) [decision : DecidableEq (Fin count)]
    (input : Fin count → _root_.AFT.FiniteDist Input) (output : Fin count → _root_.AFT.FiniteDist Output)
    (channel : Fin count → (Input → ℝ) →ₗ[ℝ] (Output → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index score, (output index).l2Sq (channel index score) ≤
      bound index ^ 2 * (input index).l2Sq score)
    (kernel : (Fin count → Input) → ℝ) :
    (_root_.AFT.FiniteDist.independent output).l2Sq (_root_.AFT.TensorChannel.apply count channel kernel) ≤
      (∏ index, bound index ^ 2) * (_root_.AFT.FiniteDist.independent input).l2Sq kernel := by
  cases Subsingleton.elim decision (instDecidableEqFin count)
  exact _root_.AFT.TensorChannel.energy_le count input output channel bound hchannel kernel
open _root_.P2Mb748e9da renaming h466 → _p2mH466
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h417 (security : ℕ) (score : _root_.CurrentAFT.PhysicalSynthesis.Palette security → ℝ) :
    (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security).l2Sq (_root_.CurrentAFT.PhysicalSynthesis.pairedChannel security score) ≤
      258 * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).l2Sq score := by
  have hpoint (primary center : _root_.CurrentAFT.PhysicalSynthesis.Palette security) :
      _root_.CurrentAFT.PairedResponse.pairedScore security score primary center ^ 2 ≤
        2 * score primary ^ 2 + 2 * _root_.CurrentAFT.PairedResponse.compensatorScore security score center ^ 2 := by
    unfold _root_.CurrentAFT.PairedResponse.pairedScore
    nlinarith [sq_nonneg (score primary + _root_.CurrentAFT.PairedResponse.compensatorScore security score center)]
  have hsum : (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security).l2Sq (_root_.CurrentAFT.PhysicalSynthesis.pairedChannel security score) ≤
      2 * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).l2Sq score +
        2 * ∑ center, (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center * _root_.CurrentAFT.PairedResponse.compensatorScore security score center ^ 2 := by
    calc
      _ ≤ ∑ primary, ∑ center, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
          (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center *
            (2 * score primary ^ 2 + 2 * _root_.CurrentAFT.PairedResponse.compensatorScore security score center ^ 2) := by
        unfold _root_.AFT.FiniteDist.l2Sq _root_.AFT.FiniteDist.expectation _root_.CurrentAFT.PhysicalSynthesis.groupLaw
        simp only [_root_.AFT.FiniteDist.prod_weight, Fintype.sum_prod_type, _root_.CurrentAFT.PhysicalSynthesis.pairedChannel]
        apply Finset.sum_le_sum
        intro primary _
        apply Finset.sum_le_sum
        intro center _
        exact mul_le_mul_of_nonneg_left (hpoint primary center)
          (mul_nonneg ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg primary) ((_root_.CurrentAFT.ProposalPrimary.centerLaw security).nonneg center))
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [show (∑ primary, ∑ center, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
            (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center * (2 * score primary ^ 2)) =
            2 * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).l2Sq score by
          simp only [_root_.AFT.FiniteDist.l2Sq, _root_.AFT.FiniteDist.expectation]
          simp_rw [show ∀ primary center, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
              (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center * (2 * score primary ^ 2) =
              2 * ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * score primary ^ 2) *
                (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center by intros; ring]
          simp_rw [← Finset.mul_sum, _root_.AFT.FiniteDist.sum_one, mul_one]
          rw [Finset.mul_sum]]
        congr 1
        rw [Finset.sum_comm]
        simp_rw [show ∀ primary center, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
            (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center * (2 * _root_.CurrentAFT.PairedResponse.compensatorScore security score center ^ 2) =
            (2 * ((_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center * _root_.CurrentAFT.PairedResponse.compensatorScore security score center ^ 2)) *
              (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary by intros; ring]
        simp_rw [← Finset.mul_sum, _root_.AFT.FiniteDist.sum_one, mul_one]
        rw [Finset.mul_sum]
  rw [_root_.CurrentAFT.PhysicalSynthesis.compensator_square_mean] at hsum
  have hcomp := _root_.CurrentAFT.PairedResponse.compensator_energy_le security score
  have hin : 0 ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).l2Sq score :=
    by
      unfold _root_.AFT.FiniteDist.l2Sq _root_.AFT.FiniteDist.expectation
      exact Finset.sum_nonneg (fun color _ =>
        mul_nonneg ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg color) (sq_nonneg _))
  have ha := mul_le_mul_of_nonneg_right (_root_.CurrentAFT.DiffuseProfiles.activation_le_half security) hin
  change _ ≤ 258 * ∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * score color ^ 2
  change 0 ≤ ∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * score color ^ 2 at hin
  change _root_.CurrentAFT.DiffuseProfiles.activation security * (∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * score color ^ 2) ≤
    (1 / 2) * (∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * score color ^ 2) at ha
  change _ ≤ 2 * (∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * score color ^ 2) + _ at hsum
  nlinarith only [hsum, hcomp, ha]
open _root_.P2Mb748e9da renaming h417 → _p2mH417
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h418 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.PhysicalSynthesis.Palette security)
      (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s)
    (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin r => _root_.CurrentAFT.PhysicalSynthesis.groupLaw security)).l2Sq
      (fun groups => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s kernel groups centers) ≤
        258 ^ r * (_root_.AFT.FiniteDist.independent (fun _ : Fin r => _root_.CurrentAFT.ProposalPrimary.primaryLaw security)).l2Sq
          (fun colors => kernel colors centers) := by
  have hlocal (index : Fin r) (score : _root_.CurrentAFT.PhysicalSynthesis.Palette security → ℝ) :
      (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security).l2Sq (_root_.CurrentAFT.PhysicalSynthesis.pairedChannel security score) ≤
        Real.sqrt 258 ^ 2 * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).l2Sq score := by
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 258)]
    exact _p2mH417 security score
  have h := _p2mH466 r (fun _ => _root_.CurrentAFT.ProposalPrimary.primaryLaw security) (fun _ => _root_.CurrentAFT.PhysicalSynthesis.groupLaw security)
    (fun _ => _root_.CurrentAFT.PhysicalSynthesis.pairedChannel security) (fun _ => Real.sqrt 258) hlocal (fun colors => kernel colors centers)
  simpa only [_root_.CurrentAFT.PhysicalSynthesis.pairedKernel, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 258),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
open _root_.P2Mb748e9da renaming h418 → _p2mH418
end
open _root_.P2Mb748e9da renaming h417 → _p2mH417
open _root_.P2Mb748e9da renaming h418 → _p2mH418
open _root_.P2Mb748e9da renaming h466 → _p2mH466
end CurrentAFT.PhysicalSynthesis
open _root_.P2Mb748e9da renaming h417 → _p2mH417
open _root_.P2Mb748e9da renaming h418 → _p2mH418
open _root_.P2Mb748e9da renaming h466 → _p2mH466
end
open _root_.P2Mb748e9da renaming h417 → _p2mH417
open _root_.P2Mb748e9da renaming h418 → _p2mH418
namespace AFT.GaussianSource.windowNegate
end AFT.GaussianSource.windowNegate
namespace AFT.RootSlice
end AFT.RootSlice
namespace CurrentAFT.PublicCharge
end CurrentAFT.PublicCharge
namespace CurrentAFT.PublicCharge.assembledEndpoint
end CurrentAFT.PublicCharge.assembledEndpoint
namespace CurrentAFT.PublicCharge.assembledEndpoint.match_1
end CurrentAFT.PublicCharge.assembledEndpoint.match_1
namespace CurrentAFT.PublicCharge.cycleDifference
end CurrentAFT.PublicCharge.cycleDifference
namespace CurrentAFT.PublicCharge.legCompanion
end CurrentAFT.PublicCharge.legCompanion
namespace CurrentAFT.PublicCharge.queueIncrement
end CurrentAFT.PublicCharge.queueIncrement
namespace CurrentAFT.characterFourier
end CurrentAFT.characterFourier
namespace CurrentAFT.coordinateCharacter
end CurrentAFT.coordinateCharacter
namespace CurrentAFT.signedFourier
end CurrentAFT.signedFourier
namespace CurrentAFT.uniformDensity
end CurrentAFT.uniformDensity
namespace CurrentAFT.uniformDeviation
end CurrentAFT.uniformDeviation
section
namespace CurrentAFT.ProtectedCycle
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h425 (body cutoff : ℕ)
    (latent : Fin body → _root_.AFT.GaussianSource.Window cutoff) (vertex : Fin body) :
    |_root_.CurrentAFT.PublicCharge.cycleDifference (fun index => (latent index : ℤ)) vertex| ≤ 2 * (cutoff : ℤ) := by
  have hfirst := Finset.mem_Icc.mp (latent vertex).property
  have hsecond := Finset.mem_Icc.mp (latent ((finRotate body).symm vertex)).property
  dsimp only [_root_.CurrentAFT.PublicCharge.cycleDifference]
  apply abs_le.mpr
  constructor <;> omega
open _root_.P2Mb748e9da renaming h425 → _p2mH425
end
open _root_.P2Mb748e9da renaming h425 → _p2mH425
end CurrentAFT.ProtectedCycle
open _root_.P2Mb748e9da renaming h425 → _p2mH425
end
open _root_.P2Mb748e9da renaming h425 → _p2mH425
namespace AFT.MixedKernel.centered_sum_product_zero
end AFT.MixedKernel.centered_sum_product_zero
namespace CurrentAFT.PhysicalSynthesis
end CurrentAFT.PhysicalSynthesis
namespace CurrentAFT.PhysicalSynthesis.groupLaw
end CurrentAFT.PhysicalSynthesis.groupLaw
namespace CurrentAFT.PhysicalSynthesis.pairedChannel
end CurrentAFT.PhysicalSynthesis.pairedChannel
namespace CurrentAFT.PhysicalSynthesis.pairedKernel
end CurrentAFT.PhysicalSynthesis.pairedKernel
section
namespace CurrentAFT.PhysicalTriangularity
open AFT DiffuseProfiles ProposalPrimary ControlCoordinates PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.PhysicalTriangularity.classicalFinDecidableEq
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h422 (security : ℕ) (color : _root_.CurrentAFT.PhysicalSynthesis.Palette security) :
    (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security).expectation (_root_.CurrentAFT.PhysicalTriangularity.pairedMatrix security color) =
      (1 - _root_.CurrentAFT.DiffuseProfiles.activation security) * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color := by
  change (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security).expectation (_root_.CurrentAFT.PhysicalSynthesis.pairedChannel security (Pi.single color 1)) = _
  rw [_root_.CurrentAFT.PhysicalSynthesis.pairedChannel_mean]
  simp [_root_.AFT.FiniteDist.expectation, Pi.single_apply]
open _root_.P2Mb748e9da renaming h422 → _p2mH422
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h420 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.PhysicalSynthesis.Palette security)
      (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s)
    (groups : Fin r → _root_.CurrentAFT.PhysicalSynthesis.Group security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s kernel groups centers =
      _root_.AFT.MixedKernel.matrixApply (fun _ => _root_.CurrentAFT.PhysicalTriangularity.pairedMatrix security) (fun colors => kernel colors centers) groups := by
  exact _root_.AFT.TensorChannel.apply_formula_instance r (fun _ => _root_.CurrentAFT.PhysicalSynthesis.pairedChannel security)
    (fun colors => kernel colors centers) groups
open _root_.P2Mb748e9da renaming h420 → _p2mH420
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h421 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.AFT.Hoeffding.Canonical (fun _ : Fin r => _root_.CurrentAFT.PhysicalSynthesis.groupLaw security) Finset.univ
      (fun groups => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s kernel.val groups centers) := by
  have hinput : _root_.AFT.Hoeffding.Canonical (fun _ : Fin r => _root_.CurrentAFT.ProposalPrimary.primaryLaw security) Finset.univ
      (fun colors => kernel.val colors centers) := by
    constructor
    · intro first second hequal
      have heq : first = second := funext (fun index => hequal index (Finset.mem_univ _))
      rw [heq]
    · intro index _ colors
      exact kernel.property.1 index colors centers
  have houtput := _root_.AFT.MixedKernel.matrixApply_canonical (fun _ : Fin r => _root_.CurrentAFT.ProposalPrimary.primaryLaw security)
    (fun _ => _root_.CurrentAFT.PhysicalSynthesis.groupLaw security) (fun _ => _root_.CurrentAFT.PhysicalTriangularity.pairedMatrix security) (fun _ => 1 - _root_.CurrentAFT.DiffuseProfiles.activation security)
    (fun _ => _p2mH422 security) (fun colors => kernel.val colors centers) hinput
  have heq : (fun groups => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s kernel.val groups centers) =
      _root_.AFT.MixedKernel.matrixApply (fun _ : Fin r => _root_.CurrentAFT.PhysicalTriangularity.pairedMatrix security) (fun colors => kernel.val colors centers) := by
    funext groups
    exact _p2mH420 security r s kernel.val groups centers
  rw [heq]
  exact houtput
open _root_.P2Mb748e9da renaming h421 → _p2mH421
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h419 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (index : Fin s) (groups : Fin r → _root_.CurrentAFT.PhysicalSynthesis.Group security)
    (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (∑ center, (_root_.CurrentAFT.ActualControls.bodyReference security).weight center *
      _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s kernel.val groups (Function.update centers index center)) = 0 := by
  have hmove := _p2mH110 (_root_.CurrentAFT.ActualControls.bodyReference security) r
    (fun _ => _root_.CurrentAFT.PhysicalSynthesis.pairedChannel security)
    (fun center colors => kernel.val colors (Function.update centers index center)) groups
  have hzero : (fun colors => (_root_.CurrentAFT.ActualControls.bodyReference security).expectation
      (fun center => kernel.val colors (Function.update centers index center))) = 0 := by
    funext colors
    exact kernel.property.2.1 index colors centers
  rw [hzero] at hmove
  have hmapzero : _root_.AFT.TensorChannel.apply r (fun _ => _root_.CurrentAFT.PhysicalSynthesis.pairedChannel security) 0 groups = 0 :=
    congrFun (map_zero (_root_.AFT.TensorChannel.applyLinear r (fun _ => _root_.CurrentAFT.PhysicalSynthesis.pairedChannel security))) groups
  rw [hmapzero] at hmove
  exact hmove.symm
open _root_.P2Mb748e9da renaming h419 → _p2mH419
end
open _root_.P2Mb748e9da renaming h419 → _p2mH419
open _root_.P2Mb748e9da renaming h420 → _p2mH420
open _root_.P2Mb748e9da renaming h421 → _p2mH421
open _root_.P2Mb748e9da renaming h422 → _p2mH422
end CurrentAFT.PhysicalTriangularity
open _root_.P2Mb748e9da renaming h419 → _p2mH419
open _root_.P2Mb748e9da renaming h420 → _p2mH420
open _root_.P2Mb748e9da renaming h421 → _p2mH421
open _root_.P2Mb748e9da renaming h422 → _p2mH422
end
open _root_.P2Mb748e9da renaming h419 → _p2mH419
open _root_.P2Mb748e9da renaming h420 → _p2mH420
open _root_.P2Mb748e9da renaming h421 → _p2mH421
open _root_.P2Mb748e9da renaming h422 → _p2mH422
namespace CurrentAFT.ControlProduct
end CurrentAFT.ControlProduct
namespace CurrentAFT.ControlProduct.disjointTensor
end CurrentAFT.ControlProduct.disjointTensor
namespace CurrentAFT.ControlProduct.finBlockSwap
end CurrentAFT.ControlProduct.finBlockSwap
namespace CurrentAFT.ControlProduct.finDisjointTensor
end CurrentAFT.ControlProduct.finDisjointTensor
namespace CurrentAFT.ControlProduct.finLeftUnit
end CurrentAFT.ControlProduct.finLeftUnit
namespace CurrentAFT.ControlProduct.finRightUnit
end CurrentAFT.ControlProduct.finRightUnit
namespace CurrentAFT.ControlProduct.reindexKernel
end CurrentAFT.ControlProduct.reindexKernel
namespace CurrentAFT.ControlProduct.scalarUnit
end CurrentAFT.ControlProduct.scalarUnit
namespace CurrentAFT.ControlProduct.symmetrize
end CurrentAFT.ControlProduct.symmetrize
namespace CurrentAFT.ControlProduct.truncatedHomogeneousProduct
end CurrentAFT.ControlProduct.truncatedHomogeneousProduct
section
namespace CurrentAFT.ControlNorm
open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ControlNorm.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ControlNorm.classicalSumDecidableEq
variable {Primary Body PS BS PT BT : Type*}
  [Fintype Primary] [Fintype Body] [Fintype PS] [Fintype BS] [Fintype PT] [Fintype BT]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h237 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (hprimary : 0 ≤ primaryFactor) (hbody : 0 ≤ bodyFactor)
    (coefficient : _root_.CurrentAFT.ControlCoordinates.CoefficientSpace primary body order) :
    0 ≤ _root_.CurrentAFT.ControlNorm.coefficientNorm primary body order primaryFactor bodyFactor coefficient := by
  apply add_nonneg (abs_nonneg _)
  apply Finset.sum_nonneg
  intro arity _
  exact mul_nonneg (_root_.CurrentAFT.ControlNorm.gradeWeight_nonneg primaryFactor bodyFactor hprimary hbody _ _)
    (_root_.CurrentAFT.ControlNorm.blockL2_nonneg primary body _)
open _root_.P2Mb748e9da renaming h237 → _p2mH237
end
open _root_.P2Mb748e9da renaming h237 → _p2mH237
end CurrentAFT.ControlNorm
open _root_.P2Mb748e9da renaming h237 → _p2mH237
end
open _root_.P2Mb748e9da renaming h237 → _p2mH237
namespace CurrentAFT.ControlNorm
end CurrentAFT.ControlNorm
namespace CurrentAFT.ControlNorm.blockEnergy
end CurrentAFT.ControlNorm.blockEnergy
namespace CurrentAFT.ControlNorm.blockL2
end CurrentAFT.ControlNorm.blockL2
namespace CurrentAFT.ControlNorm.finite_expectation_square_le
end CurrentAFT.ControlNorm.finite_expectation_square_le
namespace CurrentAFT.ControlNorm.finite_l2_triangle
end CurrentAFT.ControlNorm.finite_l2_triangle
namespace CurrentAFT.ControlNorm.gradeWeight
end CurrentAFT.ControlNorm.gradeWeight
namespace CurrentAFT.ControlNorm.slotWordEquiv
end CurrentAFT.ControlNorm.slotWordEquiv
namespace CurrentAFT.PhysicalTriangularity
end CurrentAFT.PhysicalTriangularity
section
namespace CurrentAFT.SafeControlGroups
open AFT DiffuseProfiles ProposalPrimary PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.SafeControlGroups.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.SafeControlGroups.classicalSumDecidableEq
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw centerLaw
set_option maxRecDepth 8192
private theorem _root_.P2Mb748e9da.h467 {Left Right Color : Type*}
    [Fintype Left] [Fintype Right] [Fintype Color]
    (first : Left → _root_.AFT.FiniteDist Color) (second : Right → _root_.AFT.FiniteDist Color)
    (test : (Left ⊕ Right → Color) → ℝ) :
    (_root_.AFT.FiniteDist.independent (Sum.elim first second)).expectation test =
      (_root_.AFT.FiniteDist.independent first).expectation (fun left =>
        (_root_.AFT.FiniteDist.independent second).expectation (fun right => test (Sum.elim left right))) := by
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
  rw [← (Equiv.sumArrowEquivProdArrow Left Right Color).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk, Fintype.prod_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  ring
open _root_.P2Mb748e9da renaming h467 → _p2mH467
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h438 (security : ℕ) (test : _root_.CurrentAFT.PhysicalSynthesis.Palette security → ℝ) :
    (_root_.CurrentAFT.ActualControls.bodyReference security).expectation (fun center => test center.val) =
      (_root_.CurrentAFT.ProposalPrimary.centerLaw security).expectation test := by
  exact _root_.CurrentAFT.ActualControls.supportedLaw_expectation (_root_.CurrentAFT.ProposalPrimary.centerLaw security) (_root_.CurrentAFT.InwardAnchor.SafeColor security)
    (fun color hunsafe => by
      simpa only [_root_.CurrentAFT.ProposalPrimary.centerLaw] using _root_.CurrentAFT.ProposalPrimary.centerProfile_zero_outside security color hunsafe) test
open _root_.P2Mb748e9da renaming h438 → _p2mH438
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h445 (security : ℕ) (test : _root_.CurrentAFT.PhysicalSynthesis.Group security → ℝ) :
    (_root_.CurrentAFT.SafeControlGroups.reference security).expectation (fun group => test (_root_.CurrentAFT.SafeControlGroups.unwrap security group)) =
      (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security).expectation test := by
  rw [_root_.CurrentAFT.SafeControlGroups.reference, _root_.CurrentAFT.PhysicalSynthesis.groupLaw, _root_.AFT.FiniteDist.expectation_prod, _root_.AFT.FiniteDist.expectation_prod]
  congr 1
  funext primary
  exact _p2mH438 security (fun center => test (primary, center))
open _root_.P2Mb748e9da renaming h445 → _p2mH445
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h444 (security : ℕ) (test : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    (_root_.CurrentAFT.SafeControlGroups.reference security).expectation (fun group => test group.2) =
      (_root_.CurrentAFT.ActualControls.bodyReference security).expectation test := by
  rw [_root_.CurrentAFT.SafeControlGroups.reference, _root_.AFT.FiniteDist.expectation_prod]
  exact _root_.AFT.FiniteDist.expectation_const (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
    ((_root_.CurrentAFT.ActualControls.bodyReference security).expectation test)
open _root_.P2Mb748e9da renaming h444 → _p2mH444
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h446 (security : ℕ) (group : _root_.CurrentAFT.SafeControlGroups.SafeGroup security) :
    1 / (4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) ^ 2) ≤ (_root_.CurrentAFT.SafeControlGroups.reference security).weight group := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hp : 1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight group.1 := by
    simpa only [_root_.CurrentAFT.ProposalPrimary.primaryLaw] using _root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security group.1
  have hb := _root_.CurrentAFT.ActualControls.bodyReference_lower security group.2
  calc
    _ = (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) *
        (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) := by ring
    _ ≤ (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight group.1 * (_root_.CurrentAFT.ActualControls.bodyReference security).weight group.2 :=
      mul_le_mul hp hb (by positivity) ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).nonneg _)
    _ = _ := rfl
open _root_.P2Mb748e9da renaming h446 → _p2mH446
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h448 (security : ℕ) :
    (_root_.CurrentAFT.SafeControlGroups.reference security).map (_root_.CurrentAFT.SafeControlGroups.unwrap security) = _root_.CurrentAFT.PhysicalSynthesis.groupLaw security := by
  ext output
  have h := _p2mH445 security (fun group => if group = output then 1 else 0)
  have hmap := _root_.AFT.FiniteDist.expectation_map (_root_.CurrentAFT.SafeControlGroups.reference security) (_root_.CurrentAFT.SafeControlGroups.unwrap security)
    (fun group => if group = output then 1 else 0)
  have hh := hmap.trans h
  simpa only [_root_.AFT.FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hh
open _root_.P2Mb748e9da renaming h448 → _p2mH448
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h447 (security : ℕ) :
    (_root_.CurrentAFT.SafeControlGroups.reference security).map Prod.snd = _root_.CurrentAFT.ActualControls.bodyReference security := by
  ext output
  have h := _p2mH444 security (fun center => if center = output then 1 else 0)
  have hmap := _root_.AFT.FiniteDist.expectation_map (_root_.CurrentAFT.SafeControlGroups.reference security) Prod.snd
    (fun center => if center = output then 1 else 0)
  have hh := hmap.trans h
  simpa only [_root_.AFT.FiniteDist.expectation, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] using hh
open _root_.P2Mb748e9da renaming h447 → _p2mH447
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h442 (security r s : ℕ)
    (input : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.AFT.Hoeffding.Canonical (fun _ : Fin r ⊕ Fin s => _root_.CurrentAFT.SafeControlGroups.reference security) Finset.univ
      (_root_.CurrentAFT.SafeControlGroups.kernel security r s input) := by
  constructor
  · intro first second hequal
    have heq : first = second := funext (fun index => hequal index (Finset.mem_univ _))
    rw [heq]
  · intro index _ word
    cases index with
    | inl index =>
      have hupdate (group : _root_.CurrentAFT.SafeControlGroups.SafeGroup security) : _root_.CurrentAFT.SafeControlGroups.kernel security r s input
          (Function.update word (Sum.inl index) group) =
          _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
            (Function.update (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl slot))) index (_root_.CurrentAFT.SafeControlGroups.unwrap security group))
            (fun slot => (word (Sum.inr slot)).2) := by
        unfold _root_.CurrentAFT.SafeControlGroups.kernel
        congr 1
        · funext slot
          by_cases heq : slot = index <;> simp [heq, Function.update]
        · funext slot
          simp [Function.update]
      simp_rw [hupdate]
      change (_root_.CurrentAFT.SafeControlGroups.reference security).expectation (fun group => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
        (Function.update (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl slot))) index (_root_.CurrentAFT.SafeControlGroups.unwrap security group))
        (fun slot => (word (Sum.inr slot)).2)) = 0
      rw [_p2mH445 security (fun group => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
        (Function.update (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl slot))) index group)
        (fun slot => (word (Sum.inr slot)).2))]
      exact (_p2mH421 security r s input
        (fun slot => (word (Sum.inr slot)).2)).2 index (Finset.mem_univ _) _
    | inr index =>
      have hupdate (group : _root_.CurrentAFT.SafeControlGroups.SafeGroup security) : _root_.CurrentAFT.SafeControlGroups.kernel security r s input
          (Function.update word (Sum.inr index) group) =
          _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
            (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl slot)))
            (Function.update (fun slot => (word (Sum.inr slot)).2) index group.2) := by
        unfold _root_.CurrentAFT.SafeControlGroups.kernel
        congr 1
        · funext slot
          simp [Function.update]
        · funext slot
          by_cases heq : slot = index <;> simp [heq, Function.update]
      simp_rw [hupdate]
      change (_root_.CurrentAFT.SafeControlGroups.reference security).expectation (fun group => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
        (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl slot)))
        (Function.update (fun slot => (word (Sum.inr slot)).2) index group.2)) = 0
      rw [_p2mH444 security (fun center => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
        (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl slot)))
        (Function.update (fun slot => (word (Sum.inr slot)).2) index center))]
      exact _p2mH419 security r s input index _ _
open _root_.P2Mb748e9da renaming h442 → _p2mH442
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h441 {Slot : Type*} [Fintype Slot]
    (security : ℕ) (test : (Slot → _root_.CurrentAFT.PhysicalSynthesis.Group security) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun _ : Slot => _root_.CurrentAFT.SafeControlGroups.reference security)).expectation
      (fun word => test (fun slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word slot))) =
        (_root_.AFT.FiniteDist.independent (fun _ : Slot => _root_.CurrentAFT.PhysicalSynthesis.groupLaw security)).expectation test := by
  have hmap := _p2mH77 (fun _ : Slot => _root_.CurrentAFT.SafeControlGroups.reference security)
    (fun _ => _root_.CurrentAFT.SafeControlGroups.unwrap security)
  simp only [_p2mH448] at hmap
  have h := _root_.AFT.FiniteDist.expectation_map (_root_.AFT.FiniteDist.independent (fun _ : Slot => _root_.CurrentAFT.SafeControlGroups.reference security))
    (fun word slot => _root_.CurrentAFT.SafeControlGroups.unwrap security (word slot)) test
  rw [hmap] at h
  exact h.symm
open _root_.P2Mb748e9da renaming h441 → _p2mH441
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h440 {Slot : Type*} [Fintype Slot]
    (security : ℕ) (test : (Slot → _root_.CurrentAFT.ActualControls.SafePalette security) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun _ : Slot => _root_.CurrentAFT.SafeControlGroups.reference security)).expectation
      (fun word => test (fun slot => (word slot).2)) =
        (_root_.AFT.FiniteDist.independent (fun _ : Slot => _root_.CurrentAFT.ActualControls.bodyReference security)).expectation test := by
  have hmap := _p2mH77 (fun _ : Slot => _root_.CurrentAFT.SafeControlGroups.reference security)
    (fun _ => Prod.snd)
  simp only [_p2mH447] at hmap
  have h := _root_.AFT.FiniteDist.expectation_map (_root_.AFT.FiniteDist.independent (fun _ : Slot => _root_.CurrentAFT.SafeControlGroups.reference security))
    (fun word slot => (word slot).2) test
  rw [hmap] at h
  exact h.symm
open _root_.P2Mb748e9da renaming h440 → _p2mH440
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h439 (security primaryPool bodyPool : ℕ)
    (test : (Fin primaryPool → _root_.CurrentAFT.PhysicalSynthesis.Group security) →
      (Fin bodyPool → _root_.CurrentAFT.ActualControls.SafePalette security) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin primaryPool ⊕ Fin bodyPool => _root_.CurrentAFT.SafeControlGroups.reference security)).expectation
      (fun word => test (fun index => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl index)))
        (fun index => (word (Sum.inr index)).2)) =
      _root_.CurrentAFT.ControlCoordinates.kernelMean (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) test := by
  rw [_p2mH235]
  have hreference : (fun _ : Fin primaryPool ⊕ Fin bodyPool => _root_.CurrentAFT.SafeControlGroups.reference security) =
      Sum.elim (fun _ : Fin primaryPool => _root_.CurrentAFT.SafeControlGroups.reference security) (fun _ : Fin bodyPool => _root_.CurrentAFT.SafeControlGroups.reference security) := by
    funext index
    cases index <;> rfl
  rw [hreference]
  rw [_p2mH467]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hbody (groups : Fin primaryPool → _root_.CurrentAFT.SafeControlGroups.SafeGroup security) :
      (_root_.AFT.FiniteDist.independent (fun _ : Fin bodyPool => _root_.CurrentAFT.SafeControlGroups.reference security)).expectation
        (fun centers => test (fun index => _root_.CurrentAFT.SafeControlGroups.unwrap security (groups index)) (fun index => (centers index).2)) =
      (_root_.AFT.FiniteDist.independent (fun _ : Fin bodyPool => _root_.CurrentAFT.ActualControls.bodyReference security)).expectation
        (fun centers => test (fun index => _root_.CurrentAFT.SafeControlGroups.unwrap security (groups index)) centers) :=
    _p2mH440 security (test (fun index => _root_.CurrentAFT.SafeControlGroups.unwrap security (groups index)))
  simp_rw [hbody]
  exact _p2mH441 security (fun groups =>
    (_root_.AFT.FiniteDist.independent (fun _ : Fin bodyPool => _root_.CurrentAFT.ActualControls.bodyReference security)).expectation (test groups))
open _root_.P2Mb748e9da renaming h439 → _p2mH439
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h443 (security r s : ℕ)
    (input : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin r ⊕ Fin s => _root_.CurrentAFT.SafeControlGroups.reference security)).l2Sq
      (_root_.CurrentAFT.SafeControlGroups.kernel security r s input) ≤
        258 ^ r * _root_.CurrentAFT.ControlNorm.blockEnergy (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) input.val := by
  change (_root_.AFT.FiniteDist.independent (fun _ : Fin r ⊕ Fin s => _root_.CurrentAFT.SafeControlGroups.reference security)).expectation
    (fun word => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val
      (fun index => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl index))) (fun index => (word (Sum.inr index)).2) ^ 2) ≤ _
  rw [_p2mH439 security r s (fun groups centers => _root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val groups centers ^ 2)]
  have heq : _root_.CurrentAFT.ControlNorm.blockEnergy (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) input.val =
      _root_.CurrentAFT.ControlCoordinates.kernelMean (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
        (fun colors centers => input.val colors centers ^ 2) := rfl
  rw [heq, _p2mH236, _p2mH236]
  calc
    _ ≤ (_root_.AFT.FiniteDist.independent (fun _ : Fin s => _root_.CurrentAFT.ActualControls.bodyReference security)).expectation
        (fun centers => 258 ^ r *
          (_root_.AFT.FiniteDist.independent (fun _ : Fin r => _root_.CurrentAFT.ProposalPrimary.primaryLaw security)).l2Sq
            (fun colors => input.val colors centers)) := by
      unfold _root_.AFT.FiniteDist.expectation
      apply Finset.sum_le_sum
      intro centers _
      exact mul_le_mul_of_nonneg_left (_p2mH418 security r s input.val centers)
        ((_root_.AFT.FiniteDist.independent (fun _ : Fin s => _root_.CurrentAFT.ActualControls.bodyReference security)).nonneg centers)
    _ = _ := by rw [_root_.AFT.FiniteDist.expectation_const_mul]; rfl
open _root_.P2Mb748e9da renaming h443 → _p2mH443
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h449 (security r s primaryPool bodyPool : ℕ)
    (input : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : (Fin primaryPool ⊕ Fin bodyPool) → _root_.CurrentAFT.SafeControlGroups.SafeGroup security) :
    _root_.AFT.CanonicalMoments.twoPoolStatistic (_root_.CurrentAFT.SafeControlGroups.kernel security r s input) word =
      _root_.CurrentAFT.ControlCoordinates.twoPoolUStatistic primaryPool bodyPool (_root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val)
        (fun index => _root_.CurrentAFT.SafeControlGroups.unwrap security (word (Sum.inl index))) (fun index => (word (Sum.inr index)).2) := by
  unfold _root_.AFT.CanonicalMoments.twoPoolStatistic _root_.CurrentAFT.ControlCoordinates.twoPoolUStatistic
  simp only [Fintype.card_fin]
  congr 1
open _root_.P2Mb748e9da renaming h449 → _p2mH449
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h450 (security r s primaryPool bodyPool power : ℕ)
    (input : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin primaryPool ⊕ Fin bodyPool => _root_.CurrentAFT.SafeControlGroups.reference security)).expectation
      (fun word => |_root_.AFT.CanonicalMoments.twoPoolStatistic (_root_.CurrentAFT.SafeControlGroups.kernel security r s input) word| ^ power) =
      _root_.CurrentAFT.ControlCoordinates.kernelMean (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
        (fun groups centers => |_root_.CurrentAFT.ControlCoordinates.twoPoolUStatistic primaryPool bodyPool
          (_root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val) groups centers| ^ power) := by
  simp_rw [_p2mH449]
  exact _p2mH439 security primaryPool bodyPool (fun groups centers =>
    |_root_.CurrentAFT.ControlCoordinates.twoPoolUStatistic primaryPool bodyPool (_root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val) groups centers| ^ power)
open _root_.P2Mb748e9da renaming h450 → _p2mH450
end
open _root_.P2Mb748e9da renaming h438 → _p2mH438
open _root_.P2Mb748e9da renaming h439 → _p2mH439
open _root_.P2Mb748e9da renaming h440 → _p2mH440
open _root_.P2Mb748e9da renaming h441 → _p2mH441
open _root_.P2Mb748e9da renaming h442 → _p2mH442
open _root_.P2Mb748e9da renaming h443 → _p2mH443
open _root_.P2Mb748e9da renaming h444 → _p2mH444
open _root_.P2Mb748e9da renaming h445 → _p2mH445
open _root_.P2Mb748e9da renaming h446 → _p2mH446
open _root_.P2Mb748e9da renaming h447 → _p2mH447
open _root_.P2Mb748e9da renaming h448 → _p2mH448
open _root_.P2Mb748e9da renaming h449 → _p2mH449
open _root_.P2Mb748e9da renaming h450 → _p2mH450
open _root_.P2Mb748e9da renaming h467 → _p2mH467
end CurrentAFT.SafeControlGroups
open _root_.P2Mb748e9da renaming h438 → _p2mH438
open _root_.P2Mb748e9da renaming h439 → _p2mH439
open _root_.P2Mb748e9da renaming h440 → _p2mH440
open _root_.P2Mb748e9da renaming h441 → _p2mH441
open _root_.P2Mb748e9da renaming h442 → _p2mH442
open _root_.P2Mb748e9da renaming h443 → _p2mH443
open _root_.P2Mb748e9da renaming h444 → _p2mH444
open _root_.P2Mb748e9da renaming h445 → _p2mH445
open _root_.P2Mb748e9da renaming h446 → _p2mH446
open _root_.P2Mb748e9da renaming h447 → _p2mH447
open _root_.P2Mb748e9da renaming h448 → _p2mH448
open _root_.P2Mb748e9da renaming h449 → _p2mH449
open _root_.P2Mb748e9da renaming h450 → _p2mH450
open _root_.P2Mb748e9da renaming h467 → _p2mH467
end
open _root_.P2Mb748e9da renaming h438 → _p2mH438
open _root_.P2Mb748e9da renaming h439 → _p2mH439
open _root_.P2Mb748e9da renaming h440 → _p2mH440
open _root_.P2Mb748e9da renaming h441 → _p2mH441
open _root_.P2Mb748e9da renaming h442 → _p2mH442
open _root_.P2Mb748e9da renaming h443 → _p2mH443
open _root_.P2Mb748e9da renaming h444 → _p2mH444
open _root_.P2Mb748e9da renaming h445 → _p2mH445
open _root_.P2Mb748e9da renaming h446 → _p2mH446
open _root_.P2Mb748e9da renaming h447 → _p2mH447
open _root_.P2Mb748e9da renaming h448 → _p2mH448
open _root_.P2Mb748e9da renaming h449 → _p2mH449
open _root_.P2Mb748e9da renaming h450 → _p2mH450
namespace CurrentAFT.PositivePublicChannels
end CurrentAFT.PositivePublicChannels
namespace CurrentAFT.PositivePublicChannels.quadGiven
end CurrentAFT.PositivePublicChannels.quadGiven
namespace CurrentAFT.PositivePublicChannels.tripleGiven
end CurrentAFT.PositivePublicChannels.tripleGiven
section
namespace CurrentAFT.TensorPublicProjection
open AFT JointTaggedPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TensorPublicProjection.finDecEq
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h451 {Index Color : Type*} [Fintype Index] [Fintype Color]
    (first second : DecidableEq Index) (law : Index → _root_.AFT.FiniteDist Color) (value : (Index → Color) → ℝ) :
    @_root_.AFT.FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) first _ (fun _ => inferInstance))
      (@_root_.AFT.FiniteDist.independent Color Index _ _ first law) value =
    @_root_.AFT.FiniteDist.expectation (Index → Color) (@Pi.instFintype Index (fun _ => Color) second _ (fun _ => inferInstance))
      (@_root_.AFT.FiniteDist.independent Color Index _ _ second law) value := by
  cases Subsingleton.elim first second
  rfl
open _root_.P2Mb748e9da renaming h451 → _p2mH451
section Generic
variable {Index Primary Body : Type*} [Fintype Index] [Fintype Primary] [Fintype Body]
  [DecidableEq Index]
end Generic
section TwoPools
variable {Primary Body Public : Type*} [Fintype Primary] [Fintype Body] [Fintype Public]
end TwoPools
end
open _root_.P2Mb748e9da renaming h451 → _p2mH451
end CurrentAFT.TensorPublicProjection
open _root_.P2Mb748e9da renaming h451 → _p2mH451
end
open _root_.P2Mb748e9da renaming h451 → _p2mH451
namespace CurrentAFT.ControlProduct.homogeneousProduct
end CurrentAFT.ControlProduct.homogeneousProduct
namespace CurrentAFT.GradedControlAlgebra
end CurrentAFT.GradedControlAlgebra
namespace CurrentAFT.GradedControlAlgebra.coefficientsToFamily
end CurrentAFT.GradedControlAlgebra.coefficientsToFamily
namespace CurrentAFT.GradedControlAlgebra.familyProduct
end CurrentAFT.GradedControlAlgebra.familyProduct
namespace CurrentAFT.GradedControlAlgebra.positiveArity
end CurrentAFT.GradedControlAlgebra.positiveArity
namespace CurrentAFT.GradedControlAlgebra.scalarAt
end CurrentAFT.GradedControlAlgebra.scalarAt
namespace CurrentAFT.GradedControlAlgebra.scalarKernel
end CurrentAFT.GradedControlAlgebra.scalarKernel
namespace CurrentAFT.GradedControlAlgebra.transportKernel
end CurrentAFT.GradedControlAlgebra.transportKernel
namespace CurrentAFT.GradedControlAlgebra.zeroArity
end CurrentAFT.GradedControlAlgebra.zeroArity
section
namespace CurrentAFT.GradedControlNorm
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.GradedControlNorm.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h378 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (coefficient : _root_.CurrentAFT.ControlCoordinates.CoefficientSpace primary body order) :
    _root_.CurrentAFT.GradedControlNorm.familyNorm primary body order primaryFactor bodyFactor (_root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily primary body order coefficient) =
      _root_.CurrentAFT.ControlNorm.coefficientNorm primary body order primaryFactor bodyFactor coefficient := by
  unfold _root_.CurrentAFT.GradedControlNorm.familyNorm
  rw [← (_root_.CurrentAFT.GradedControlNorm.aritySplit order).sum_comp, Fintype.sum_sum_type, Fintype.sum_unique]
  change _root_.CurrentAFT.ControlNorm.gradeWeight primaryFactor bodyFactor 0 0 *
      _root_.CurrentAFT.ControlNorm.blockL2 primary body (_root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily primary body order coefficient (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)).val +
      (∑ arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order,
        _root_.CurrentAFT.ControlNorm.gradeWeight primaryFactor bodyFactor arity.val.1.val arity.val.2.val *
          _root_.CurrentAFT.ControlNorm.blockL2 primary body (_root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily primary body order coefficient (_root_.CurrentAFT.GradedControlAlgebra.positiveArity order arity)).val) = _
  simp only [_root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily_zero, _root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily_positive,
    _root_.CurrentAFT.ControlNorm.gradeWeight, pow_zero, one_mul, _root_.CurrentAFT.ControlNorm.coefficientNorm]
  rw [_root_.CurrentAFT.GradedControlNorm.blockL2_scalarKernel]
open _root_.P2Mb748e9da renaming h378 → _p2mH378
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h377 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily primary body order (_root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv primary body order family) = family := by
  apply _root_.CurrentAFT.GradedControlAlgebra.familyToCoefficients_injective primary body order
  apply Prod.ext
  · change _root_.CurrentAFT.GradedControlAlgebra.scalarAt primary body
        (_root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily primary body order (_root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv primary body order family) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) =
      _root_.CurrentAFT.GradedControlAlgebra.scalarAt primary body (family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order))
    rw [_root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily_zero]
    rfl
  · funext arity
    exact _root_.CurrentAFT.GradedControlAlgebra.coefficientsToFamily_positive primary body order _ arity
open _root_.P2Mb748e9da renaming h377 → _p2mH377
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h379 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (primaryFactor bodyFactor : ℝ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.GradedControlNorm.familyNorm primary body order primaryFactor bodyFactor family =
      _root_.CurrentAFT.ControlNorm.coefficientNorm primary body order primaryFactor bodyFactor (_root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv primary body order family) := by
  rw [← _p2mH378, _p2mH377]
open _root_.P2Mb748e9da renaming h379 → _p2mH379
end
open _root_.P2Mb748e9da renaming h377 → _p2mH377
open _root_.P2Mb748e9da renaming h378 → _p2mH378
open _root_.P2Mb748e9da renaming h379 → _p2mH379
end CurrentAFT.GradedControlNorm
open _root_.P2Mb748e9da renaming h377 → _p2mH377
open _root_.P2Mb748e9da renaming h378 → _p2mH378
open _root_.P2Mb748e9da renaming h379 → _p2mH379
end
open _root_.P2Mb748e9da renaming h377 → _p2mH377
open _root_.P2Mb748e9da renaming h378 → _p2mH378
open _root_.P2Mb748e9da renaming h379 → _p2mH379
section
namespace CurrentAFT.GradedInverse
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h380 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hfirst : _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order 1 family) (power : ℕ) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order power (family ^ power) := by
  induction power with
  | zero => exact _root_.CurrentAFT.GradedInverse.vanishesBelow_zero primary body order _
  | succ power ih =>
    rw [pow_succ]
    exact _root_.CurrentAFT.GradedInverse.vanishesBelow_mul primary body order power 1 _ family ih hfirst
open _root_.P2Mb748e9da renaming h380 → _p2mH380
end
open _root_.P2Mb748e9da renaming h380 → _p2mH380
end CurrentAFT.GradedInverse
open _root_.P2Mb748e9da renaming h380 → _p2mH380
end
open _root_.P2Mb748e9da renaming h380 → _p2mH380
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
section
namespace CurrentAFT.FiniteAtomMoments
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h345 (reference : Slot → _root_.AFT.FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower)
    (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (rate : Slot → ℝ) (hrate : ∀ slot, 0 ≤ rate slot) (kernel : (Slot → Color) → ℝ) :
    _root_.AFT.MixedKernel.activity rate reference kernel ≤
      (∏ slot, rate slot) * (∏ slot, (1 + rate slot / Real.sqrt lower)) *
        Real.sqrt ((_root_.AFT.FiniteDist.independent reference).l2Sq kernel) := by
  have hexp : (∑ fixed : Finset Slot, ∏ slot ∈ fixed, rate slot / Real.sqrt lower) =
      ∏ slot, (1 + rate slot / Real.sqrt lower) := by
    have h := Fintype.prod_add (fun slot : Slot => rate slot / Real.sqrt lower) (fun _ => (1 : ℝ))
    simpa only [Finset.prod_const, one_pow, mul_one, add_comm] using h.symm
  unfold _root_.AFT.MixedKernel.activity
  calc
    _ ≤ (∏ slot, rate slot) * ∑ fixed : Finset Slot,
        (∏ slot ∈ fixed, rate slot) *
          (Real.sqrt ((_root_.AFT.FiniteDist.independent reference).l2Sq kernel) / Real.sqrt lower ^ fixed.card) := by
      apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun slot _ => hrate slot)
      apply Finset.sum_le_sum
      intro fixed _
      exact mul_le_mul_of_nonneg_left
        (_p2mH96 reference lower hlower href kernel fixed)
        (Finset.prod_nonneg fun slot _ => hrate slot)
    _ = (∏ slot, rate slot) *
        ((∑ fixed : Finset Slot, ∏ slot ∈ fixed, rate slot / Real.sqrt lower) *
          Real.sqrt ((_root_.AFT.FiniteDist.independent reference).l2Sq kernel)) := by
      rw [Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro fixed _
      rw [Finset.prod_div_distrib, Finset.prod_const]
      ring
    _ = _ := by rw [hexp]; ring
open _root_.P2Mb748e9da renaming h345 → _p2mH345
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h346 (reference : Slot → _root_.AFT.FiniteDist Color)
    (lower : ℝ) (hlower : 0 < lower)
    (href : ∀ slot color, lower ≤ (reference slot).weight color)
    (rate : Slot → ℝ) (hrate : ∀ slot, 0 ≤ rate slot)
    (ratio : ℝ) (_hratio : 0 ≤ ratio) (hcompare : ∀ slot, rate slot / Real.sqrt lower ≤ ratio)
    (kernel : (Slot → Color) → ℝ) :
    _root_.AFT.MixedKernel.activity rate reference kernel ≤
      (1 + ratio) ^ Fintype.card Slot * (∏ slot, rate slot) *
        Real.sqrt ((_root_.AFT.FiniteDist.independent reference).l2Sq kernel) := by
  apply (_p2mH345 reference lower hlower href rate hrate kernel).trans
  have hproduct : (∏ slot, (1 + rate slot / Real.sqrt lower)) ≤ (1 + ratio) ^ Fintype.card Slot := by
    calc
      _ ≤ ∏ _slot : Slot, (1 + ratio) := by
        exact Finset.prod_le_prod
          (fun slot _ => add_nonneg zero_le_one (div_nonneg (hrate slot) (Real.sqrt_nonneg _)))
          (fun slot _ => by linarith [hcompare slot])
      _ = _ := by simp
  have hrates : 0 ≤ ∏ slot, rate slot := Finset.prod_nonneg fun slot _ => hrate slot
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hproduct hrates)
    (Real.sqrt_nonneg ((_root_.AFT.FiniteDist.independent reference).l2Sq kernel))
  exact h.trans_eq (by ring)
open _root_.P2Mb748e9da renaming h346 → _p2mH346
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h352 (primaryOrder bodyOrder moment : ℕ) (ratio : ℝ) (hratio : 0 ≤ ratio) :
    0 ≤ _root_.CurrentAFT.FiniteAtomMoments.momentFactor primaryOrder bodyOrder moment ratio := by
  unfold _root_.CurrentAFT.FiniteAtomMoments.momentFactor _root_.AFT.CanonicalMoments.momentConstant
  positivity
open _root_.P2Mb748e9da renaming h352 → _p2mH352
variable {PS BS PP BP : Type*} [Fintype PS] [Fintype BS] [Fintype PP] [Fintype BP]
attribute [local instance] _root_.CurrentAFT.FiniteAtomMoments.instDecidableEqSum_currentAFT
attribute [local instance] _root_.CurrentAFT.FiniteAtomMoments.instDecidableEqSum_currentAFT_1
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h353 (primary body : _root_.AFT.FiniteDist Color)
    (kernel : ((PS ⊕ BS) → Color) → ℝ)
    (hcanonical : _root_.AFT.Hoeffding.Canonical (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) Finset.univ kernel)
    (lower : ℝ) (hlower : 0 < lower)
    (hprimaryAtoms : ∀ color, lower ≤ primary.weight color)
    (hbodyAtoms : ∀ color, lower ≤ body.weight color)
    (ratio : ℝ) (hratio : 0 ≤ ratio)
    (hprimaryRatio : (1 / Real.sqrt (Fintype.card PP : ℝ)) / Real.sqrt lower ≤ ratio)
    (hbodyRatio : (1 / Real.sqrt (Fintype.card BP : ℝ)) / Real.sqrt lower ≤ ratio)
    (moment : ℕ) (hmoment : 1 ≤ moment)
    (hprimary : 0 < Fintype.card PP) (hbody : 0 < Fintype.card BP)
    (hprimaryLarge : 2 * Fintype.card PS ≤ Fintype.card PP)
    (hbodyLarge : 2 * Fintype.card BS ≤ Fintype.card BP) :
    (_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PP => primary) (fun _ : BP => body))).expectation
      (fun word => |_root_.AFT.CanonicalMoments.twoPoolStatistic kernel word| ^ (2 * moment)) ≤
      (_root_.CurrentAFT.FiniteAtomMoments.momentFactor (Fintype.card PS) (Fintype.card BS) moment ratio *
        ((1 / Real.sqrt (Fintype.card PP : ℝ)) ^ Fintype.card PS *
          (1 / Real.sqrt (Fintype.card BP : ℝ)) ^ Fintype.card BS) *
        Real.sqrt ((_root_.AFT.FiniteDist.independent (Sum.elim (fun _ : PS => primary) (fun _ : BS => body))).l2Sq kernel)) ^
          (2 * moment) := by
  have ha := _p2mH346
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) lower hlower
    (by intro slot color; cases slot with
        | inl _ => exact hprimaryAtoms color
        | inr _ => exact hbodyAtoms color)
    (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP : ℝ))
      (fun _ : BS => 1 / Real.sqrt (Fintype.card BP : ℝ)))
    (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _)) ratio hratio
    (by intro slot; cases slot with
        | inl _ => exact hprimaryRatio
        | inr _ => exact hbodyRatio) kernel
  simp only [Fintype.card_sum, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.prod_const, Finset.card_univ] at ha
  have h := _p2mH59
    (PP := PP) (BP := BP) primary body kernel hcanonical moment hprimary hbody hprimaryLarge hbodyLarge
  apply h.trans
  let combinatorial := _root_.AFT.CanonicalMoments.momentConstant (Fintype.card PS) (2 * moment) *
    _root_.AFT.CanonicalMoments.momentConstant (Fintype.card BS) (2 * moment)
  have hcomb : 0 ≤ combinatorial := by dsimp [combinatorial, _root_.AFT.CanonicalMoments.momentConstant]; positivity
  have hcombPower : combinatorial ≤ (combinatorial + 1) ^ (2 * moment) := by
    apply (by linarith : combinatorial ≤ combinatorial + 1).trans
    exact le_self_pow₀ (by linarith) (by omega)
  have hactivityNonneg := _p2mH94
    (Sum.elim (fun _ : PS => 1 / Real.sqrt (Fintype.card PP : ℝ))
      (fun _ : BS => 1 / Real.sqrt (Fintype.card BP : ℝ)))
    (Sum.elim (fun _ : PS => primary) (fun _ : BS => body)) kernel
    (by intro slot; cases slot <;> exact one_div_nonneg.mpr (Real.sqrt_nonneg _))
  have hpow := pow_le_pow_left₀ hactivityNonneg ha (2 * moment)
  have hbound := mul_le_mul hcombPower hpow (pow_nonneg hactivityNonneg _) (pow_nonneg (by linarith : 0 ≤ combinatorial + 1) _)
  apply hbound.trans_eq
  simp only [_root_.CurrentAFT.FiniteAtomMoments.momentFactor, combinatorial, mul_pow]
  ring
open _root_.P2Mb748e9da renaming h353 → _p2mH353
end
open _root_.P2Mb748e9da renaming h345 → _p2mH345
open _root_.P2Mb748e9da renaming h346 → _p2mH346
open _root_.P2Mb748e9da renaming h352 → _p2mH352
open _root_.P2Mb748e9da renaming h353 → _p2mH353
end CurrentAFT.FiniteAtomMoments
open _root_.P2Mb748e9da renaming h345 → _p2mH345
open _root_.P2Mb748e9da renaming h346 → _p2mH346
open _root_.P2Mb748e9da renaming h352 → _p2mH352
open _root_.P2Mb748e9da renaming h353 → _p2mH353
end
open _root_.P2Mb748e9da renaming h345 → _p2mH345
open _root_.P2Mb748e9da renaming h346 → _p2mH346
open _root_.P2Mb748e9da renaming h352 → _p2mH352
open _root_.P2Mb748e9da renaming h353 → _p2mH353
namespace CurrentAFT.BackgroundRates
end CurrentAFT.BackgroundRates
namespace CurrentAFT.BackgroundRates.radius
end CurrentAFT.BackgroundRates.radius
namespace CurrentAFT.FiniteAtomMoments
end CurrentAFT.FiniteAtomMoments
namespace CurrentAFT.FiniteAtomMoments.momentFactor
end CurrentAFT.FiniteAtomMoments.momentFactor
section
namespace CurrentAFT.FiniteAtomMoments
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount BackgroundRates.ordinaryPool
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h347 (security : ℕ) : 0 < _root_.CurrentAFT.FiniteAtomMoments.currentAtomLower security := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  unfold _root_.CurrentAFT.FiniteAtomMoments.currentAtomLower
  positivity
open _root_.P2Mb748e9da renaming h347 → _p2mH347
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h348 (security : ℕ) :
    Real.sqrt (_root_.CurrentAFT.FiniteAtomMoments.currentAtomLower security) = 1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  unfold _root_.CurrentAFT.FiniteAtomMoments.currentAtomLower
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one,
    show 4 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) ^ 2 = (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
open _root_.P2Mb748e9da renaming h348 → _p2mH348
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h350 (security population : ℕ)
    (hpopulation : _root_.CurrentAFT.Parameters.base security ^ 128 ≤ population) :
    (1 / Real.sqrt (population : ℝ)) / Real.sqrt (_root_.CurrentAFT.FiniteAtomMoments.currentAtomLower security) ≤ 262144 := by
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hpop : (0 : ℝ) < population := by
    exact_mod_cast (pow_pos (_root_.CurrentAFT.Parameters.base_pos security) 128).trans_le hpopulation
  have hsqrt : (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64 ≤ Real.sqrt (population : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    have hh : (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 128 ≤ population := by exact_mod_cast hpopulation
    convert hh using 1; ring
  have hqu : (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≤ 131072 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64 := by
    exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_bounds security).2
  rw [_p2mH348]
  have hequal : (1 / Real.sqrt (population : ℝ)) / (1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ))) =
      2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) / Real.sqrt (population : ℝ) := by field_simp
  rw [hequal]
  calc
    _ ≤ 2 * (131072 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64) / Real.sqrt (population : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    _ ≤ 2 * (131072 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64) / (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 64 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hb 64) hsqrt
    _ = _ := by field_simp; norm_num
open _root_.P2Mb748e9da renaming h350 → _p2mH350
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h351 (security : ℕ) :
    (1 / Real.sqrt (_root_.CurrentAFT.Parameters.legCount security : ℝ)) / Real.sqrt (_root_.CurrentAFT.FiniteAtomMoments.currentAtomLower security) ≤ 262144 :=
  _p2mH350 security _ (by rw [_root_.CurrentAFT.Parameters.legCount_eq])
open _root_.P2Mb748e9da renaming h351 → _p2mH351
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h349 (security : ℕ) :
    (1 / Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ)) / Real.sqrt (_root_.CurrentAFT.FiniteAtomMoments.currentAtomLower security) ≤ 262144 := by
  apply _p2mH350
  exact (Nat.pow_le_pow_right (by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega) (by omega)).trans
    (_root_.CurrentAFT.BackgroundRates.ordinaryPool_lower security)
open _root_.P2Mb748e9da renaming h349 → _p2mH349
end
open _root_.P2Mb748e9da renaming h347 → _p2mH347
open _root_.P2Mb748e9da renaming h348 → _p2mH348
open _root_.P2Mb748e9da renaming h349 → _p2mH349
open _root_.P2Mb748e9da renaming h350 → _p2mH350
open _root_.P2Mb748e9da renaming h351 → _p2mH351
end CurrentAFT.FiniteAtomMoments
open _root_.P2Mb748e9da renaming h347 → _p2mH347
open _root_.P2Mb748e9da renaming h348 → _p2mH348
open _root_.P2Mb748e9da renaming h349 → _p2mH349
open _root_.P2Mb748e9da renaming h350 → _p2mH350
open _root_.P2Mb748e9da renaming h351 → _p2mH351
end
open _root_.P2Mb748e9da renaming h347 → _p2mH347
open _root_.P2Mb748e9da renaming h348 → _p2mH348
open _root_.P2Mb748e9da renaming h349 → _p2mH349
open _root_.P2Mb748e9da renaming h350 → _p2mH350
open _root_.P2Mb748e9da renaming h351 → _p2mH351
namespace CurrentAFT.PhysicalFockHilbert
end CurrentAFT.PhysicalFockHilbert
namespace CurrentAFT.PhysicalFockHilbert.channel
end CurrentAFT.PhysicalFockHilbert.channel
namespace CurrentAFT.PhysicalFockHilbert.vector
end CurrentAFT.PhysicalFockHilbert.vector
namespace CurrentAFT.UniformTaggedOutput
end CurrentAFT.UniformTaggedOutput
namespace CurrentAFT.UniformTaggedOutput.choiceLaw
end CurrentAFT.UniformTaggedOutput.choiceLaw
section
namespace CurrentAFT.CoefficientOutputFock
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy ActualBlockFock ActualBlockMean
  ActualCycleMeanMGF ConditionalHistogramMean PhysicalFockRates ActualFockBound
  TaggedOutputFock UniformTaggedOutput ControlCoordinates ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  BackgroundRates.radius BackgroundRates.ordinaryPool
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h221 (order : ℕ) (multiple : ℝ) : 0 ≤ _root_.CurrentAFT.CoefficientOutputFock.normConstant order multiple := by
  unfold _root_.CurrentAFT.CoefficientOutputFock.normConstant
  positivity
open _root_.P2Mb748e9da renaming h221 → _p2mH221
end
open _root_.P2Mb748e9da renaming h221 → _p2mH221
end CurrentAFT.CoefficientOutputFock
open _root_.P2Mb748e9da renaming h221 → _p2mH221
end
open _root_.P2Mb748e9da renaming h221 → _p2mH221
section
namespace CurrentAFT
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h461 (dimension modulus : ℕ) [NeZero modulus]
    (endpoint : _root_.CurrentAFT.EndpointSpace dimension modulus) :
    (_root_.CurrentAFT.uniformZeroSum dimension modulus).weight endpoint =
      if (∑ index, endpoint index) = 0 then ((modulus : ℝ) ^ dimension)⁻¹ else 0 := by
  by_cases hcharge : (∑ index, endpoint index) = 0
  · let target : _root_.CurrentAFT.ZeroSumSpace dimension modulus := ⟨endpoint, hcharge⟩
    have heq (source : _root_.CurrentAFT.ZeroSumSpace dimension modulus) :
        source.val = endpoint ↔ source = target := by
      constructor
      · intro heq
        exact Subtype.ext heq
      · intro heq
        exact congrArg Subtype.val heq
    simp [_root_.CurrentAFT.uniformZeroSum, _root_.AFT.FiniteDist.map_weight, heq, _root_.AFT.FiniteDist.uniform_weight,
      _root_.CurrentAFT.zeroSumSpace_card, hcharge]
  · have hne (source : _root_.CurrentAFT.ZeroSumSpace dimension modulus) : source.val ≠ endpoint := by
      intro heq
      apply hcharge
      rw [← heq]
      exact source.property
    simp [_root_.CurrentAFT.uniformZeroSum, _root_.AFT.FiniteDist.map_weight, hne, hcharge]
open _root_.P2Mb748e9da renaming h461 → _p2mH461
end
open _root_.P2Mb748e9da renaming h461 → _p2mH461
end CurrentAFT
open _root_.P2Mb748e9da renaming h461 → _p2mH461
end
open _root_.P2Mb748e9da renaming h461 → _p2mH461
namespace CurrentAFT.ActualPhysicalTail
end CurrentAFT.ActualPhysicalTail
namespace CurrentAFT.ActualPhysicalTail.coefficient
end CurrentAFT.ActualPhysicalTail.coefficient
namespace CurrentAFT.PublicSignedOutput
end CurrentAFT.PublicSignedOutput
section
namespace CurrentAFT.ActualPublicCharge
open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy ActualBlockFock
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean PublicOutputExperiment
  PublicCoefficientOutput PublicSignedOutput
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw centerLaw safeLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h162 (security : ℕ) (test : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ) :
    (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation test =
      (_root_.CurrentAFT.PublicOutputExperiment.reference security).expectation
        (fun controls => (_root_.CurrentAFT.ActualPublicCharge.auxiliaryLaw security controls).expectation test) := by
  unfold _root_.CurrentAFT.ActualPublicCharge.proposal _root_.CurrentAFT.ActualPublicCharge.auxiliaryLaw _root_.CurrentAFT.ActualPublicCharge.localSeedsLaw _root_.CurrentAFT.ActualPublicCharge.bodyPermutationLaw _root_.CurrentAFT.ActualPublicCharge.endpointPermutationLaw
  simp only [_root_.AFT.FiniteDist.expectation_map, Function.comp_def, _root_.AFT.FiniteDist.expectation_prod]
open _root_.P2Mb748e9da renaming h162 → _p2mH162
end
open _root_.P2Mb748e9da renaming h162 → _p2mH162
end CurrentAFT.ActualPublicCharge
open _root_.P2Mb748e9da renaming h162 → _p2mH162
end
open _root_.P2Mb748e9da renaming h162 → _p2mH162
namespace CurrentAFT.ActualPublicCharge
end CurrentAFT.ActualPublicCharge
namespace CurrentAFT.ActualPublicCharge.Core
end CurrentAFT.ActualPublicCharge.Core
namespace CurrentAFT.ActualPublicCharge.Core.mk
end CurrentAFT.ActualPublicCharge.Core.mk
namespace CurrentAFT.ActualPublicCharge.centerAt
end CurrentAFT.ActualPublicCharge.centerAt
namespace CurrentAFT.ActualPublicCharge.centerAt.match_1
end CurrentAFT.ActualPublicCharge.centerAt.match_1
namespace CurrentAFT.ActualPublicCharge.queueSet
end CurrentAFT.ActualPublicCharge.queueSet
namespace CurrentAFT.AffineFlagCalibration.evaluatedPair
end CurrentAFT.AffineFlagCalibration.evaluatedPair
namespace CurrentAFT.AffineFlagCalibration.legOffsetBound
end CurrentAFT.AffineFlagCalibration.legOffsetBound
namespace CurrentAFT.AffineFlagCalibration.pairProjection
end CurrentAFT.AffineFlagCalibration.pairProjection
section
namespace CurrentAFT.AffineFlagCalibration
open AFT ActualPublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h201 (security order : ℕ)
    (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (bits : Fin (_root_.CurrentAFT.Parameters.legCount security) → Bool) :
    _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits) =
      _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient core := rfl
open _root_.P2Mb748e9da renaming h201 → _p2mH201
end
open _root_.P2Mb748e9da renaming h201 → _p2mH201
end CurrentAFT.AffineFlagCalibration
open _root_.P2Mb748e9da renaming h201 → _p2mH201
end
open _root_.P2Mb748e9da renaming h201 → _p2mH201
namespace AFT.RootTensor
end AFT.RootTensor
section
namespace CurrentAFT.PublicAuxiliaryFubini
open AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h427 {Index Color : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
    (law : Index → _root_.AFT.FiniteDist Color) (factor : Index → Color → ℝ) :
    (_root_.AFT.FiniteDist.independent law).expectation (fun word => ∏ index, factor index (word index)) =
      ∏ index, (law index).expectation (factor index) := by
  unfold _root_.AFT.FiniteDist.expectation _root_.AFT.FiniteDist.independent
  simp only [← Finset.prod_mul_distrib]
  rw [Fintype.prod_sum]
open _root_.P2Mb748e9da renaming h427 → _p2mH427
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h426 {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : _root_.AFT.FiniteDist Source) (channel : Source → _root_.AFT.FiniteDist Output) (test : Output → ℝ) :
    (law.mix channel).expectation test =
      law.expectation (fun source => (channel source).expectation test) := by
  unfold _root_.AFT.FiniteDist.expectation
  simp only [_root_.AFT.FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro output _
  ring
open _root_.P2Mb748e9da renaming h426 → _p2mH426
end
open _root_.P2Mb748e9da renaming h426 → _p2mH426
open _root_.P2Mb748e9da renaming h427 → _p2mH427
end CurrentAFT.PublicAuxiliaryFubini
open _root_.P2Mb748e9da renaming h426 → _p2mH426
open _root_.P2Mb748e9da renaming h427 → _p2mH427
end
open _root_.P2Mb748e9da renaming h426 → _p2mH426
open _root_.P2Mb748e9da renaming h427 → _p2mH427
namespace CurrentAFT.PublicAuxiliaryFubini
end CurrentAFT.PublicAuxiliaryFubini
namespace CurrentAFT.RefinedPublicOutput
end CurrentAFT.RefinedPublicOutput
namespace CurrentAFT.RefinedPublicOutput.blockCharge
end CurrentAFT.RefinedPublicOutput.blockCharge
namespace CurrentAFT.RefinedPublicOutput.blocks
end CurrentAFT.RefinedPublicOutput.blocks
namespace CurrentAFT.RefinedPublicOutput.blocks.match_1
end CurrentAFT.RefinedPublicOutput.blocks.match_1
section
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration ActualPublicLegCharge ActualPublicCharge DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.completionFinDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.completionPrime
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h199 {A B O : Type*} [Fintype A] [Fintype B] [Fintype O]
    (first : _root_.AFT.FiniteDist A) (second : _root_.AFT.FiniteDist B) (value : A → B → O) :
    first.mix (fun a => second.map (value a)) =
      second.mix (fun b => first.map (fun a => value a b)) := by
  ext output
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_weight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring
open _root_.P2Mb748e9da renaming h199 → _p2mH199
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h194 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security) (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    _root_.CurrentAFT.AffineFlagCalibration.evaluatedPair security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed)
      (by simpa only [_root_.CurrentAFT.AffineFlagCalibration.legOffsetBound, add_sub_assoc] using _root_.CurrentAFT.ActualPublicLegCharge.publicShift_bound security primary seed)
      primary first second =
      (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security primary seed).map (fun chart =>
        _root_.CurrentAFT.AffineFlagCalibration.pairProjection security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val)
          (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second)) := by
  rw [_root_.CurrentAFT.AffineFlagCalibration.evaluatedPair, _root_.CurrentAFT.AffineFlagCalibration.evaluatedPrimary, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2Mb748e9da renaming h194 → _p2mH194
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h192 (security : ℕ) (root : ℤ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicCharge.LegCore security) :
    _root_.CurrentAFT.AffineFlagCalibration.completedTriple security root primary seed =
      (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (fun second => (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (fun first =>
        (_root_.CurrentAFT.AffineFlagCalibration.evaluatedPair security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed.1)
          (by simpa only [_root_.CurrentAFT.AffineFlagCalibration.legOffsetBound, add_sub_assoc] using _root_.CurrentAFT.ActualPublicLegCharge.publicShift_bound security primary seed.1)
          primary first second).map (fun pair =>
            _root_.AFT.PhysicalBlockTensors.tripleEquiv.symm
              (pair, _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root + second.val) seed.2)))) := by
  unfold _root_.CurrentAFT.AffineFlagCalibration.completedTriple
  rw [_p2mH78]
  simp_rw [_p2mH199 (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security primary seed.1) (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security)]
  rw [_p2mH78]
  apply congrArg (_root_.AFT.FiniteDist.mix (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security))
  funext second
  apply congrArg (_root_.AFT.FiniteDist.mix (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security))
  funext first
  rw [_p2mH194, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2Mb748e9da renaming h192 → _p2mH192
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h191 (security : ℕ) (root : ℤ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicCharge.LegCore security) :
    _root_.CurrentAFT.AffineFlagCalibration.completedTriple security root primary seed =
      (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).mix (fun flag =>
        _root_.CurrentAFT.RefinedPublicOutput.triple security root primary
          (_root_.CurrentAFT.AffineFlagCalibration.setMarked security seed.1 flag, seed.2)) := by
  rw [_p2mH192]
  trans (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (fun second =>
    (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).mix (fun flag =>
      (_root_.CurrentAFT.ActualPublicLegCharge.refinedPair security primary second (_root_.CurrentAFT.AffineFlagCalibration.setMarked security seed.1 flag)).map
        (fun pair => _root_.AFT.PhysicalBlockTensors.tripleEquiv.symm
          (pair, _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root + second.val) seed.2))))
  · apply congrArg (_root_.AFT.FiniteDist.mix (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security))
    funext second
    rw [← _root_.AFT.FiniteDist.map_mix, _p2mH197, _root_.AFT.FiniteDist.map_mix]
  · rw [_p2mH78]
    rfl
open _root_.P2Mb748e9da renaming h191 → _p2mH191
end
open _root_.P2Mb748e9da renaming h191 → _p2mH191
open _root_.P2Mb748e9da renaming h192 → _p2mH192
open _root_.P2Mb748e9da renaming h194 → _p2mH194
open _root_.P2Mb748e9da renaming h199 → _p2mH199
end CurrentAFT.AffineFlagCalibration
open _root_.P2Mb748e9da renaming h191 → _p2mH191
open _root_.P2Mb748e9da renaming h192 → _p2mH192
open _root_.P2Mb748e9da renaming h194 → _p2mH194
open _root_.P2Mb748e9da renaming h199 → _p2mH199
end
open _root_.P2Mb748e9da renaming h191 → _p2mH191
open _root_.P2Mb748e9da renaming h192 → _p2mH192
open _root_.P2Mb748e9da renaming h194 → _p2mH194
open _root_.P2Mb748e9da renaming h199 → _p2mH199
namespace CurrentAFT.AffineFlagCalibration.evaluatedPrimary
end CurrentAFT.AffineFlagCalibration.evaluatedPrimary
section
namespace CurrentAFT.ActualAffineCompletedOutput
open AFT AffineFlagCalibration ActualPublicCharge DiffuseProfiles ProposalPrimary
  ActualBlockFock ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean
  PublicOutputExperiment PublicCoefficientOutput PublicAuxiliaryFubini
open HistogramNormalization PhysicalSynthesis
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualAffineCompletedOutput.completedOutputFinDecidableEq
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h122 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (queue : ℤ) (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security) :
    (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).mix (fun bits =>
      _root_.CurrentAFT.RefinedPublicOutput.conditionalLaw security layout (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits) queue latent) =
      _root_.CurrentAFT.ActualAffineCompletedOutput.conditionalLaw security layout core queue latent := by
  ext word
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.CurrentAFT.RefinedPublicOutput.conditionalLaw, _root_.CurrentAFT.ActualAffineCompletedOutput.conditionalLaw,
    _root_.AFT.FiniteDist.retype_weight, _root_.AFT.BlockProducts.blockLaw, _root_.AFT.BlockProducts.blockMass,
    Fintype.prod_sum_type, _root_.CurrentAFT.RefinedPublicOutput.blocks, _root_.CurrentAFT.ActualAffineCompletedOutput.blocks]
  change (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).expectation (fun bits =>
      (∏ leg, (_root_.CurrentAFT.RefinedPublicOutput.triple security
        (_root_.CurrentAFT.ActualBlockMean.attachmentRoots security layout core.bodyPermutation latent leg)
        (core.controls (.inl leg)).1 (_root_.CurrentAFT.AffineFlagCalibration.setMarked security (core.legs leg).1 (bits leg), (core.legs leg).2)).weight
          (fun slot => word ⟨.inl leg, slot⟩)) *
      ((∏ center, (_root_.CurrentAFT.RefinedPublicOutput.singleton security
        (_root_.CurrentAFT.ActualBlockMean.centerRoots security layout core.bodyPermutation latent center)
        (core.controls ((_root_.CurrentAFT.UniformTaggedOutput.centerSplit security).symm center)).2.val).weight
          (fun slot => word ⟨.inr (.inl center), slot⟩)) *
       ∏ point, (_root_.CurrentAFT.RefinedPublicOutput.singleton security
        (_root_.CurrentAFT.ActualBlockMean.queueRoots security layout core.bodyPermutation latent point + queue) (core.queueBaselines point)).weight
          (fun slot => word ⟨.inr (.inr point), slot⟩))) = _
  rw [_root_.AFT.FiniteDist.expectation_mul_const]
  apply congrArg₂ (· * ·) _ rfl
  trans ∏ leg : Fin (_root_.CurrentAFT.Parameters.legCount security),
    (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).expectation (fun flag =>
      (_root_.CurrentAFT.RefinedPublicOutput.triple security (_root_.CurrentAFT.ActualBlockMean.attachmentRoots security layout core.bodyPermutation latent leg)
        (core.controls (.inl leg)).1 (_root_.CurrentAFT.AffineFlagCalibration.setMarked security (core.legs leg).1 flag, (core.legs leg).2)).weight
          (fun slot => word ⟨.inl leg, slot⟩))
  · exact _p2mH427 (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) =>
      _root_.CurrentAFT.ActualPublicLegCharge.activationLaw security) (fun leg flag =>
        (_root_.CurrentAFT.RefinedPublicOutput.triple security (_root_.CurrentAFT.ActualBlockMean.attachmentRoots security layout core.bodyPermutation latent leg)
          (core.controls (.inl leg)).1 (_root_.CurrentAFT.AffineFlagCalibration.setMarked security (core.legs leg).1 flag, (core.legs leg).2)).weight
            (fun slot => word ⟨.inl leg, slot⟩))
  apply Finset.prod_congr rfl
  intro leg _
  have hl := congrArg (fun law => law.weight (fun slot => word ⟨.inl leg, slot⟩))
    (_p2mH191 security (_root_.CurrentAFT.ActualBlockMean.attachmentRoots security layout core.bodyPermutation latent leg)
      (core.controls (.inl leg)).1 (core.legs leg))
  exact hl.symm
open _root_.P2Mb748e9da renaming h122 → _p2mH122
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h121 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).mix (fun bits =>
      _root_.CurrentAFT.RefinedPublicOutput.lawGiven security layout (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits)) =
        _root_.CurrentAFT.ActualAffineCompletedOutput.lawGiven security layout core := by
  unfold _root_.CurrentAFT.RefinedPublicOutput.lawGiven _root_.CurrentAFT.ActualAffineCompletedOutput.lawGiven
  rw [_p2mH78]
  apply congrArg (_root_.AFT.FiniteDist.mix (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security))
  funext queue
  rw [_p2mH78]
  apply congrArg (_root_.AFT.FiniteDist.mix (_root_.AFT.FiniteDist.retype (_root_.CurrentAFT.ActualFockBound.latentLaw security)))
  funext latent
  change (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).mix (fun bits =>
    (_root_.CurrentAFT.RefinedPublicOutput.conditionalLaw security layout (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits)
      queue.val latent).map (fun word => _root_.AFT.relabel (_root_.AFT.HistogramNormalization.renameWord (_root_.CurrentAFT.PublicCoefficientOutput.flatten security) word) core.endpointPermutation)) = _
  rw [← _root_.AFT.FiniteDist.map_mix, _p2mH122]
open _root_.P2Mb748e9da renaming h121 → _p2mH121
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h123 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).mix (fun bits =>
      _root_.CurrentAFT.RefinedPublicOutput.mappedChannel security layout (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits)) =
        _root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel security layout core := by
  unfold _root_.CurrentAFT.RefinedPublicOutput.mappedChannel _root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel
  rw [← _root_.AFT.FiniteDist.map_mix, _p2mH121]
open _root_.P2Mb748e9da renaming h123 → _p2mH123
end
open _root_.P2Mb748e9da renaming h121 → _p2mH121
open _root_.P2Mb748e9da renaming h122 → _p2mH122
open _root_.P2Mb748e9da renaming h123 → _p2mH123
end CurrentAFT.ActualAffineCompletedOutput
open _root_.P2Mb748e9da renaming h121 → _p2mH121
open _root_.P2Mb748e9da renaming h122 → _p2mH122
open _root_.P2Mb748e9da renaming h123 → _p2mH123
end
open _root_.P2Mb748e9da renaming h121 → _p2mH121
open _root_.P2Mb748e9da renaming h122 → _p2mH122
open _root_.P2Mb748e9da renaming h123 → _p2mH123
namespace CurrentAFT.LeadingEvaluation
end CurrentAFT.LeadingEvaluation
namespace CurrentAFT.LeadingEvaluation.kernelPolynomial
end CurrentAFT.LeadingEvaluation.kernelPolynomial
section
namespace CurrentAFT.LeadingEvaluation
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.LeadingEvaluation.familyFinDecidableEq
variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h381 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ)
    (bodyForm : Body → MvPolynomial Variable ℝ) (order : ℕ)
    (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForm bodyForm order family =
      ∑ arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order,
        _root_.CurrentAFT.TruncatedOutput.quotientMap order
          (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForm bodyForm (family arity).val) := by
  simp only [_root_.CurrentAFT.LeadingEvaluation.familyLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, _root_.CurrentAFT.LeadingEvaluation.homogeneousLinear, Submodule.subtype_apply]
  rfl
open _root_.P2Mb748e9da renaming h381 → _p2mH381
end
open _root_.P2Mb748e9da renaming h381 → _p2mH381
end CurrentAFT.LeadingEvaluation
open _root_.P2Mb748e9da renaming h381 → _p2mH381
end
open _root_.P2Mb748e9da renaming h381 → _p2mH381
namespace CurrentAFT.LeadingEvaluation.familyLinear
end CurrentAFT.LeadingEvaluation.familyLinear
namespace CurrentAFT.LeadingEvaluation.homogeneousLinear
end CurrentAFT.LeadingEvaluation.homogeneousLinear
section
namespace CurrentAFT.Augmentation
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.Augmentation.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h213 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (first second : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) :
    first (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = second (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) ↔
      _root_.CurrentAFT.Augmentation.scalarHom primary body order first = _root_.CurrentAFT.Augmentation.scalarHom primary body order second := by
  exact (_root_.CurrentAFT.GradedControlAlgebra.scalarAt_injective primary body).eq_iff.symm
open _root_.P2Mb748e9da renaming h213 → _p2mH213
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h212 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) {Index : Type*} (terms : Finset Index)
    (atoms : Index → _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hzero : ∀ index ∈ terms, atoms index (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0) :
    (∏ index ∈ terms, (1 + atoms index)) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) =
      (1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  apply (_p2mH213 primary body order _ _).mpr
  rw [map_prod, map_one]
  apply Finset.prod_eq_one
  intro index hindex
  rw [map_add, map_one]
  have hscalar : _root_.CurrentAFT.Augmentation.scalarHom primary body order (atoms index) = 0 := by
    change _root_.CurrentAFT.GradedControlAlgebra.scalarAt primary body (atoms index (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) = 0
    rw [hzero index hindex]
    rfl
  rw [hscalar, add_zero]
open _root_.P2Mb748e9da renaming h212 → _p2mH212
end
open _root_.P2Mb748e9da renaming h212 → _p2mH212
open _root_.P2Mb748e9da renaming h213 → _p2mH213
end CurrentAFT.Augmentation
open _root_.P2Mb748e9da renaming h212 → _p2mH212
open _root_.P2Mb748e9da renaming h213 → _p2mH213
end
open _root_.P2Mb748e9da renaming h212 → _p2mH212
open _root_.P2Mb748e9da renaming h213 → _p2mH213
namespace CurrentAFT.ActualBackground
end CurrentAFT.ActualBackground
namespace CurrentAFT.ActualBackground.background
end CurrentAFT.ActualBackground.background
namespace CurrentAFT.ActualBackground.fixedQueueBackground
end CurrentAFT.ActualBackground.fixedQueueBackground
namespace CurrentAFT.ActualBackground.numericalThreshold
end CurrentAFT.ActualBackground.numericalThreshold
namespace CurrentAFT.Augmentation
end CurrentAFT.Augmentation
namespace CurrentAFT.GradedControlAlgebra.familyUnit
end CurrentAFT.GradedControlAlgebra.familyUnit
namespace CurrentAFT.GradedInverseNorm
end CurrentAFT.GradedInverseNorm
section
namespace CurrentAFT.ActualBackgroundInverse
open AFT GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  Augmentation RoleProduct DiffuseProfiles ProposalPrimary ActualControls BackgroundRates BackgroundFamilies
  BackgroundLinear LegBackgroundFamilies BackgroundScalarZero BackgroundPopulationBounds ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  ActualBackground.background ActualBackground.fixedQueueBackground
attribute [local instance] _root_.CurrentAFT.ActualBackgroundInverse.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h125 (security order : ℕ) (horder : 2 ≤ order) (queueShift : ℤ) :
    _root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queueShift (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) =
      (1 : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  let atoms := _root_.CurrentAFT.RoleProduct.roleAtoms (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (_root_.CurrentAFT.BackgroundPopulationBounds.freeCount security) (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.legCount security)
    (_root_.CurrentAFT.BackgroundFamilies.freeCertificate security order (by omega)) (_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order (by omega) queueShift)
    (_root_.CurrentAFT.LegBackgroundFamilies.completeLegAtom security order horder)
  have hzero (index : _root_.CurrentAFT.RoleProduct.RoleIndex (_root_.CurrentAFT.BackgroundPopulationBounds.freeCount security) (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.legCount security)) :
      atoms index (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
    rcases index with index | index
    · exact _root_.CurrentAFT.BackgroundScalarZero.freeCertificate_zero security order (by omega)
    · rcases index with index | index
      · exact _root_.CurrentAFT.BackgroundScalarZero.translationCertificate_zero security order (by omega) queueShift
      · exact _root_.CurrentAFT.BackgroundScalarZero.completeLegAtom_zero security order horder
  have h := _p2mH212 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order Finset.univ atoms (fun index _ => hzero index)
  change (∏ index, (1 + _root_.CurrentAFT.RoleProduct.roleAtoms (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (_root_.CurrentAFT.BackgroundPopulationBounds.freeCount security) (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.Parameters.legCount security)
    (_root_.CurrentAFT.BackgroundFamilies.freeCertificate security order (by omega)) (_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order (by omega) queueShift)
    (_root_.CurrentAFT.LegBackgroundFamilies.completeLegAtom security order horder) index)) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = _ at h
  rw [_root_.CurrentAFT.RoleProduct.roleAtoms_product] at h
  unfold _root_.CurrentAFT.ActualBackground.fixedQueueBackground
  exact h
open _root_.P2Mb748e9da renaming h125 → _p2mH125
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h124 (security order : ℕ) (horder : 2 ≤ order) :
    _root_.CurrentAFT.ActualBackground.background security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  simp only [_root_.CurrentAFT.ActualBackground.background, Finset.sum_apply, Pi.smul_apply, _p2mH125]
  rw [← Finset.sum_smul, _root_.AFT.FiniteDist.sum_one, one_smul]
open _root_.P2Mb748e9da renaming h124 → _p2mH124
end
open _root_.P2Mb748e9da renaming h124 → _p2mH124
open _root_.P2Mb748e9da renaming h125 → _p2mH125
end CurrentAFT.ActualBackgroundInverse
open _root_.P2Mb748e9da renaming h124 → _p2mH124
open _root_.P2Mb748e9da renaming h125 → _p2mH125
end
open _root_.P2Mb748e9da renaming h124 → _p2mH124
open _root_.P2Mb748e9da renaming h125 → _p2mH125
namespace CurrentAFT.LocalCoefficientFamily
end CurrentAFT.LocalCoefficientFamily
namespace CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
end CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
namespace CurrentAFT.LocalCoefficientFamily.selectedDensity
end CurrentAFT.LocalCoefficientFamily.selectedDensity
namespace CurrentAFT.LocalCoefficientFamily.selectedKernel
end CurrentAFT.LocalCoefficientFamily.selectedKernel
namespace CurrentAFT.PrimaryTensorInverse
end CurrentAFT.PrimaryTensorInverse
namespace CurrentAFT.PrimaryTensorInverse.referenceWeight
end CurrentAFT.PrimaryTensorInverse.referenceWeight
section
namespace CurrentAFT.LocalCoefficientEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open LocalCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.LocalCoefficientEvaluation.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h389 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (forms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (degree : ℕ) (density : (Fin degree → Primary) → ℝ) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body forms bodyForms (fun colors (_ : Fin 0 → Body) => density colors) =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary forms degree density := by
  simp only [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial, _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial, Fin.prod_univ_zero, Fintype.sum_unique, mul_one]
open _root_.P2Mb748e9da renaming h389 → _p2mH389
end
open _root_.P2Mb748e9da renaming h389 → _p2mH389
end CurrentAFT.LocalCoefficientEvaluation
open _root_.P2Mb748e9da renaming h389 → _p2mH389
end
open _root_.P2Mb748e9da renaming h389 → _p2mH389
namespace CurrentAFT.FirstHistogram
end CurrentAFT.FirstHistogram
namespace CurrentAFT.FirstHistogram.completeHistogramResponse
end CurrentAFT.FirstHistogram.completeHistogramResponse
namespace CurrentAFT.IndependentPairedReference
end CurrentAFT.IndependentPairedReference
namespace CurrentAFT.IndependentPairedReference.independentSignedMass
end CurrentAFT.IndependentPairedReference.independentSignedMass
namespace CurrentAFT.IndependentPairedReference.profileEnergy_add
end CurrentAFT.IndependentPairedReference.profileEnergy_add
namespace CurrentAFT.LocalCoefficientEvaluation
end CurrentAFT.LocalCoefficientEvaluation
namespace CurrentAFT.LocalCoefficientEvaluation.densityPolynomial
end CurrentAFT.LocalCoefficientEvaluation.densityPolynomial
namespace CurrentAFT.LocalCoefficientEvaluation.evaluation
end CurrentAFT.LocalCoefficientEvaluation.evaluation
namespace CurrentAFT.LocalCoefficientEvaluation.primaryForm
end CurrentAFT.LocalCoefficientEvaluation.primaryForm
section
namespace CurrentAFT.NormalizedLocalPolynomial
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.NormalizedLocalPolynomial.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h395 (security order : ℕ) (law : _root_.AFT.FiniteDist (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security)) :
    _root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order law (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  rw [_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily, _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily_zeroArity, law.sum_one, one_smul]
open _root_.P2Mb748e9da renaming h395 → _p2mH395
end
open _root_.P2Mb748e9da renaming h395 → _p2mH395
end CurrentAFT.NormalizedLocalPolynomial
open _root_.P2Mb748e9da renaming h395 → _p2mH395
end
open _root_.P2Mb748e9da renaming h395 → _p2mH395
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace CurrentAFT.BackgroundFamilies
end CurrentAFT.BackgroundFamilies
namespace CurrentAFT.BackgroundFamilies.bodyArity
end CurrentAFT.BackgroundFamilies.bodyArity
namespace CurrentAFT.BackgroundFamilies.bodyCoefficient
end CurrentAFT.BackgroundFamilies.bodyCoefficient
namespace CurrentAFT.BackgroundFamilies.bodyFamily
end CurrentAFT.BackgroundFamilies.bodyFamily
namespace CurrentAFT.BackgroundFamilies.bodyKernel
end CurrentAFT.BackgroundFamilies.bodyKernel
namespace CurrentAFT.BackgroundFamilies.freeCertificate
end CurrentAFT.BackgroundFamilies.freeCertificate
namespace CurrentAFT.BackgroundFamilies.primaryArity
end CurrentAFT.BackgroundFamilies.primaryArity
namespace CurrentAFT.BackgroundFamilies.primaryCoefficient
end CurrentAFT.BackgroundFamilies.primaryCoefficient
namespace CurrentAFT.BackgroundFamilies.primaryFamily
end CurrentAFT.BackgroundFamilies.primaryFamily
namespace CurrentAFT.BackgroundFamilies.primaryKernel
end CurrentAFT.BackgroundFamilies.primaryKernel
namespace CurrentAFT.BackgroundFamilies.translationCertificate
end CurrentAFT.BackgroundFamilies.translationCertificate
namespace CurrentAFT.NormalizedLocalPolynomial
end CurrentAFT.NormalizedLocalPolynomial
namespace CurrentAFT.NormalizedLocalPolynomial.positiveFamily
end CurrentAFT.NormalizedLocalPolynomial.positiveFamily
section
namespace CurrentAFT.LocalRaisingFirst
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily NormalizedLocalPolynomial BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.LocalRaisingFirst.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LocalRaisingFirst.classicalSubtypeDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
section Filtration
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h390 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (background : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hzero : background (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order 1 (_root_.CurrentAFT.GradedInverse.backgroundInverse primary body order background - 1) := by
  have hbase : (1 - background : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
    change (1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) - background (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0
    rw [hzero, sub_self]
  have hfirst := _root_.CurrentAFT.GradedInverse.vanishesBelow_one_of_zero primary body order (1 - background) hbase
  have hsplit : _root_.CurrentAFT.GradedInverse.backgroundInverse primary body order background - 1 =
      ∑ power ∈ (Finset.range (order + 1)).erase 0, (1 - background) ^ power := by
    unfold _root_.CurrentAFT.GradedInverse.backgroundInverse
    have hsum := Finset.sum_erase_add (Finset.range (order + 1))
      (fun power => (1 - background) ^ power) (by simp : 0 ∈ Finset.range (order + 1))
    simp only [pow_zero] at hsum
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  rw [hsplit]
  apply _root_.CurrentAFT.LocalRaisingFirst.vanishesBelow_sum
  intro power hpower arity hdegree
  have hpositive : 0 < power := Nat.pos_of_ne_zero (Finset.mem_erase.mp hpower).1
  exact _p2mH380 primary body order (1 - background) hfirst power arity (by omega)
open _root_.P2Mb748e9da renaming h390 → _p2mH390
end Filtration
open _root_.P2Mb748e9da renaming h390 → _p2mH390
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h393 (security order : ℕ)
    (positive : _root_.AFT.FiniteDist (Fin 4 → _root_.CurrentAFT.LocalRaisingFirst.Palette security)) (mass : (Fin 4 → _root_.CurrentAFT.LocalRaisingFirst.Palette security) → ℝ)
    (hmass : ∑ word, mass word = 0) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily security order positive mass - _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order mass) := by
  have hequal : _root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily security order positive mass - _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order mass =
      _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order mass *
        (_root_.CurrentAFT.GradedInverse.backgroundInverse (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
          (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order positive) - 1) := by
    unfold _root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily
    rw [mul_sub, mul_one]
  rw [hequal]
  exact _root_.CurrentAFT.GradedInverse.vanishesBelow_mul (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 1 1 _ _
    (_root_.CurrentAFT.LocalRaisingFirst.completeFamily_vanishes_one security order mass hmass)
    (_p2mH390 _ _ order _ (_p2mH395 security order positive))
open _root_.P2Mb748e9da renaming h393 → _p2mH393
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h391 (security order : ℕ) (score : _root_.CurrentAFT.LocalRaisingFirst.Palette security → ℝ)
    (hcentered : (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation score = 0) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order score -
        _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order (_root_.CurrentAFT.IndependentPairedReference.independentSignedMass security score)) :=
  _p2mH393 security order _ _
    (_root_.CurrentAFT.IndependentPairedReference.independentSigned_mass_zero security score hcentered)
open _root_.P2Mb748e9da renaming h391 → _p2mH391
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h392 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.LocalRaisingFirst.Palette security → ℝ) (hcentered : (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation score = 0) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.LocalRaisingFirst.localRaising security order horder score hcentered) := by
  have hsplit : _root_.CurrentAFT.LocalRaisingFirst.localRaising security order horder score hcentered =
      (_root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order score -
        _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order (_root_.CurrentAFT.IndependentPairedReference.independentSignedMass security score)) +
      (_root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order (_root_.CurrentAFT.IndependentPairedReference.independentSignedMass security score) -
        _root_.CurrentAFT.BackgroundFamilies.primaryFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder score hcentered) := by
    unfold _root_.CurrentAFT.LocalRaisingFirst.localRaising
    abel
  rw [hsplit]
  exact _root_.CurrentAFT.LocalRaisingFirst.vanishesBelow_add _ _ order 2 _ _
    (_p2mH391 security order score hcentered)
    (_root_.CurrentAFT.LocalRaisingFirst.independentComplete_sub_primary_raises security order horder score hcentered)
open _root_.P2Mb748e9da renaming h392 → _p2mH392
end
open _root_.P2Mb748e9da renaming h390 → _p2mH390
open _root_.P2Mb748e9da renaming h391 → _p2mH391
open _root_.P2Mb748e9da renaming h392 → _p2mH392
open _root_.P2Mb748e9da renaming h393 → _p2mH393
end CurrentAFT.LocalRaisingFirst
open _root_.P2Mb748e9da renaming h390 → _p2mH390
open _root_.P2Mb748e9da renaming h391 → _p2mH391
open _root_.P2Mb748e9da renaming h392 → _p2mH392
open _root_.P2Mb748e9da renaming h393 → _p2mH393
end
open _root_.P2Mb748e9da renaming h390 → _p2mH390
open _root_.P2Mb748e9da renaming h391 → _p2mH391
open _root_.P2Mb748e9da renaming h392 → _p2mH392
open _root_.P2Mb748e9da renaming h393 → _p2mH393
namespace CurrentAFT.LocalRaisingFirst
end CurrentAFT.LocalRaisingFirst
namespace CurrentAFT.LocalRaisingFirst.primaryProjection
end CurrentAFT.LocalRaisingFirst.primaryProjection
namespace CurrentAFT.LocalRaisingFirst.sum_nonempty_singletons
end CurrentAFT.LocalRaisingFirst.sum_nonempty_singletons
section
namespace CurrentAFT.LocalRaisingLinear
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily NormalizedLocalPolynomial LocalRaisingFirst
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.LocalRaisingLinear.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LocalRaisingLinear.classicalSubtypeDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h394 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.LocalRaisingLinear.centeredScores security) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.LocalRaisingLinear.localRaisingLinear security order horder score) :=
  _p2mH392 security order horder score.val score.property
open _root_.P2Mb748e9da renaming h394 → _p2mH394
end
open _root_.P2Mb748e9da renaming h394 → _p2mH394
end CurrentAFT.LocalRaisingLinear
open _root_.P2Mb748e9da renaming h394 → _p2mH394
end
open _root_.P2Mb748e9da renaming h394 → _p2mH394
section
namespace CurrentAFT.CanonicalReconstruction
open AFT ControlCoordinates ControlProduct
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CanonicalReconstruction.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h218 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∑ sourcePrimary, ∑ sourceBody,
      kernel.val sourcePrimary sourceBody *
        _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors *
          _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers) =
      kernel.val colors centers := by
  have hprimary (fixed : Fin s → Body) :
      _root_.AFT.Hoeffding.Canonical (fun _ : Fin r => primary) Finset.univ (fun word => kernel.val word fixed) := by
    constructor
    · intro first second hequal
      have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
      rw [hword]
    · intro index _ word
      exact kernel.property.1 index word fixed
  have hbody (fixed : Fin r → Primary) :
      _root_.AFT.Hoeffding.Canonical (fun _ : Fin s => body) Finset.univ (kernel.val fixed) := by
    constructor
    · intro first second hequal
      have hword : first = second := funext fun index => hequal index (Finset.mem_univ index)
      rw [hword]
    · intro index _ word
      exact kernel.property.2.1 index fixed word
  have hp := _p2mH95 (fun _ : Fin r => primary)
    (fun word => kernel.val word centers) (hprimary centers) colors
  have hb (source : Fin r → Primary) := _p2mH95
    (fun _ : Fin s => body) (kernel.val source) (hbody source) centers
  calc
    _ = ∑ sourcePrimary,
        (∑ sourceBody, kernel.val sourcePrimary sourceBody *
          _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin s => body) sourceBody centers) *
          _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Fin r => primary) sourcePrimary colors := by
      apply Finset.sum_congr rfl
      intro source _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro other _
      ring
    _ = _ := by simp only [hb]; exact hp
open _root_.P2Mb748e9da renaming h218 → _p2mH218
set_option maxRecDepth 8192
private theorem _root_.P2Mb748e9da.h462 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) (source output : Color) :
    law.weight source * _root_.AFT.Hoeffding.centeredAtom law source output =
      (if output = source then 1 else 0) - law.weight source := by
  by_cases hequal : source = output
  · subst output
    simp only [_root_.AFT.Hoeffding.centeredAtom, if_true, mul_sub, mul_one,
      mul_inv_cancel₀ (hpositive source).ne']
  · simp only [_root_.AFT.Hoeffding.centeredAtom, hequal, Ne.symm hequal, if_false, zero_sub, mul_neg, mul_one]
open _root_.P2Mb748e9da renaming h462 → _p2mH462
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h220 {Color : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, 0 < law.weight color) {Index : Type*} [Fintype Index] [DecidableEq Index]
    (source output : Index → Color) :
    (∏ index, law.weight (source index)) *
        (∏ index, _root_.AFT.Hoeffding.centeredAtom law (source index) (output index)) =
      _root_.AFT.MixedKernel.canonicalPointBasis (fun _ : Index => law) source output := by
  rw [← Finset.prod_mul_distrib]
  simp only [_p2mH462 law hpositive, _root_.AFT.MixedKernel.canonicalPointBasis]
open _root_.P2Mb748e9da renaming h220 → _p2mH220
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h219 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s)
    (colors : Fin r → Primary) (centers : Fin s → Body) :
    (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) *
          _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody colors centers) =
      kernel.val colors centers := by
  rw [← _p2mH218 primary body kernel colors centers]
  apply Finset.sum_congr rfl
  intro sourcePrimary _
  apply Finset.sum_congr rfl
  intro sourceBody _
  rw [← _p2mH220 primary hprimary, ← _p2mH220 body hbody]
  unfold _root_.CurrentAFT.CanonicalReconstruction.pointTensor
  ring
open _root_.P2Mb748e9da renaming h219 → _p2mH219
end
open _root_.P2Mb748e9da renaming h218 → _p2mH218
open _root_.P2Mb748e9da renaming h219 → _p2mH219
open _root_.P2Mb748e9da renaming h220 → _p2mH220
open _root_.P2Mb748e9da renaming h462 → _p2mH462
end CurrentAFT.CanonicalReconstruction
open _root_.P2Mb748e9da renaming h218 → _p2mH218
open _root_.P2Mb748e9da renaming h219 → _p2mH219
open _root_.P2Mb748e9da renaming h220 → _p2mH220
open _root_.P2Mb748e9da renaming h462 → _p2mH462
end
open _root_.P2Mb748e9da renaming h218 → _p2mH218
open _root_.P2Mb748e9da renaming h219 → _p2mH219
open _root_.P2Mb748e9da renaming h220 → _p2mH220
namespace AFT.MixedKernel.canonicalPointBasis
end AFT.MixedKernel.canonicalPointBasis
namespace CurrentAFT.CanonicalReconstruction
end CurrentAFT.CanonicalReconstruction
namespace CurrentAFT.CanonicalReconstruction.atomProduct_centered
end CurrentAFT.CanonicalReconstruction.atomProduct_centered
namespace CurrentAFT.CanonicalReconstruction.pointKernel
end CurrentAFT.CanonicalReconstruction.pointKernel
namespace CurrentAFT.CanonicalReconstruction.pointTensor
end CurrentAFT.CanonicalReconstruction.pointTensor
namespace CurrentAFT.LocalRaisingBounds
end CurrentAFT.LocalRaisingBounds
namespace CurrentAFT.LocalRaisingBounds.base_ge_one
end CurrentAFT.LocalRaisingBounds.base_ge_one
namespace CurrentAFT.LocalRaisingBounds.coefficientNorm
end CurrentAFT.LocalRaisingBounds.coefficientNorm
section
namespace CurrentAFT.GlobalRaising
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.GlobalRaising.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h375 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.GlobalRaising.Palette security) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 1 (_root_.CurrentAFT.GlobalRaising.primaryPoint security order horder source) := by
  apply _root_.CurrentAFT.GradedInverse.vanishesBelow_one_of_zero
  unfold _root_.CurrentAFT.GlobalRaising.primaryPoint _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear _root_.CurrentAFT.BackgroundFamilies.primaryFamily
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega
open _root_.P2Mb748e9da renaming h375 → _p2mH375
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h374 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 1 (_root_.CurrentAFT.GlobalRaising.bodyPoint security order horder source) := by
  apply _root_.CurrentAFT.GradedInverse.vanishesBelow_one_of_zero
  unfold _root_.CurrentAFT.GlobalRaising.bodyPoint _root_.CurrentAFT.BackgroundFamilies.bodyFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.2.val) hequal
  change 0 = 1 at h
  omega
open _root_.P2Mb748e9da renaming h374 → _p2mH374
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h376 (security order : ℕ) (horder : 1 ≤ order) (source : _root_.CurrentAFT.GlobalRaising.Palette security) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2 (_root_.CurrentAFT.GlobalRaising.raisedPoint security order horder source) :=
  _p2mH394 security order horder _
open _root_.P2Mb748e9da renaming h376 → _p2mH376
section Filtration
variable {Primary Body Index : Type*} [Fintype Primary] [Fintype Body]
end Filtration
end
open _root_.P2Mb748e9da renaming h374 → _p2mH374
open _root_.P2Mb748e9da renaming h375 → _p2mH375
open _root_.P2Mb748e9da renaming h376 → _p2mH376
end CurrentAFT.GlobalRaising
open _root_.P2Mb748e9da renaming h374 → _p2mH374
open _root_.P2Mb748e9da renaming h375 → _p2mH375
open _root_.P2Mb748e9da renaming h376 → _p2mH376
end
open _root_.P2Mb748e9da renaming h374 → _p2mH374
open _root_.P2Mb748e9da renaming h375 → _p2mH375
open _root_.P2Mb748e9da renaming h376 → _p2mH376
namespace CurrentAFT.BackgroundEvaluation
end CurrentAFT.BackgroundEvaluation
namespace CurrentAFT.BackgroundEvaluation.bodyForm
end CurrentAFT.BackgroundEvaluation.bodyForm
section
namespace CurrentAFT.BackgroundFirstEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation
  LocalCoefficientFamily LocalCoefficientEvaluation FringeCertificate BackgroundTranslations
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
attribute [local instance] _root_.CurrentAFT.BackgroundFirstEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h215 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms (_root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body density hcenter).val =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary primaryForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) :=
  _p2mH389 primary body primaryForms bodyForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)
open _root_.P2Mb748e9da renaming h215 → _p2mH215
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h214 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.familyHom primary body primaryForms bodyForms hprimary hbody order
      (_root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder density hcenter) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary primaryForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms
    (_root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body density hcenter).val) = _
  rw [_p2mH215]
open _root_.P2Mb748e9da renaming h214 → _p2mH214
end
open _root_.P2Mb748e9da renaming h214 → _p2mH214
open _root_.P2Mb748e9da renaming h215 → _p2mH215
end CurrentAFT.BackgroundFirstEvaluation
open _root_.P2Mb748e9da renaming h214 → _p2mH214
open _root_.P2Mb748e9da renaming h215 → _p2mH215
end
open _root_.P2Mb748e9da renaming h214 → _p2mH214
open _root_.P2Mb748e9da renaming h215 → _p2mH215
namespace CurrentAFT.BackgroundFirstEvaluation
end CurrentAFT.BackgroundFirstEvaluation
namespace CurrentAFT.GlobalRaising
end CurrentAFT.GlobalRaising
namespace CurrentAFT.GlobalRaising.bodyPoint
end CurrentAFT.GlobalRaising.bodyPoint
namespace CurrentAFT.GlobalRaising.homogeneousCorrectionLinear
end CurrentAFT.GlobalRaising.homogeneousCorrectionLinear
namespace CurrentAFT.GlobalRaising.primaryPoint
end CurrentAFT.GlobalRaising.primaryPoint
namespace CurrentAFT.GlobalRaising.raisedPoint
end CurrentAFT.GlobalRaising.raisedPoint
namespace CurrentAFT.GlobalRaising.raisingLinear
end CurrentAFT.GlobalRaising.raisingLinear
namespace CurrentAFT.GlobalRaising.responseInverse
end CurrentAFT.GlobalRaising.responseInverse
namespace CurrentAFT.GlobalRaising.responseLinear
end CurrentAFT.GlobalRaising.responseLinear
namespace CurrentAFT.GlobalRaising.selectedCorrection
end CurrentAFT.GlobalRaising.selectedCorrection
namespace CurrentAFT.GlobalRaising.selectedCorrectionLinear
end CurrentAFT.GlobalRaising.selectedCorrectionLinear
namespace CurrentAFT.GlobalRaising.selectedPointProduct
end CurrentAFT.GlobalRaising.selectedPointProduct
namespace CurrentAFT.PrimaryMassFamilies
end CurrentAFT.PrimaryMassFamilies
namespace CurrentAFT.PrimaryMassFamilies.massCertificateFamily
end CurrentAFT.PrimaryMassFamilies.massCertificateFamily
namespace CurrentAFT.PrimaryMassFamilies.massLiftKernel
end CurrentAFT.PrimaryMassFamilies.massLiftKernel
namespace CurrentAFT.PrimaryMassFamilies.oneWordProfile
end CurrentAFT.PrimaryMassFamilies.oneWordProfile
namespace CurrentAFT.PrimaryMassFamilies.pairWordProfile
end CurrentAFT.PrimaryMassFamilies.pairWordProfile
namespace CurrentAFT.PrimaryMassFamilies.primaryArity
end CurrentAFT.PrimaryMassFamilies.primaryArity
section
namespace CurrentAFT.OrdinaryRaising
open AFT DiffuseProfiles ProposalPrimary ActualControls FringeCertificate BackgroundCertificates
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse GradedInverseNorm LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.OrdinaryRaising.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h398 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.OrdinaryRaising.positiveAtom security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
  unfold _root_.CurrentAFT.OrdinaryRaising.positiveAtom _root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega
open _root_.P2Mb748e9da renaming h398 → _p2mH398
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h399 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.OrdinaryRaising.positiveFamily security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  change (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) + _root_.CurrentAFT.OrdinaryRaising.positiveAtom security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = _
  rw [_p2mH398, add_zero]
open _root_.P2Mb748e9da renaming h399 → _p2mH399
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h397 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (hcentered : (_root_.CurrentAFT.ActualControls.bodyReference security).expectation score = 0) :
    _root_.CurrentAFT.OrdinaryRaising.normalizedFamily security order horder score hcentered =
      _root_.CurrentAFT.BackgroundFamilies.bodyFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder score hcentered +
        _root_.CurrentAFT.OrdinaryRaising.raisingFamily security order horder score hcentered := by
  unfold _root_.CurrentAFT.OrdinaryRaising.normalizedFamily _root_.CurrentAFT.OrdinaryRaising.raisingFamily
  rw [mul_sub, mul_one]
  abel
open _root_.P2Mb748e9da renaming h397 → _p2mH397
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h400 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (hcentered : (_root_.CurrentAFT.ActualControls.bodyReference security).expectation score = 0) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.OrdinaryRaising.raisingFamily security order horder score hcentered) := by
  apply _root_.CurrentAFT.GradedInverse.vanishesBelow_mul _ _ order 1 1
  · apply _root_.CurrentAFT.GradedInverse.vanishesBelow_one_of_zero
    unfold _root_.CurrentAFT.BackgroundFamilies.bodyFamily
    rw [Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.2.val) hequal
    change 0 = 1 at h
    omega
  · exact _p2mH390 _ _ order _ (_p2mH399 security order horder)
open _root_.P2Mb748e9da renaming h400 → _p2mH400
end
open _root_.P2Mb748e9da renaming h397 → _p2mH397
open _root_.P2Mb748e9da renaming h398 → _p2mH398
open _root_.P2Mb748e9da renaming h399 → _p2mH399
open _root_.P2Mb748e9da renaming h400 → _p2mH400
end CurrentAFT.OrdinaryRaising
open _root_.P2Mb748e9da renaming h397 → _p2mH397
open _root_.P2Mb748e9da renaming h398 → _p2mH398
open _root_.P2Mb748e9da renaming h399 → _p2mH399
open _root_.P2Mb748e9da renaming h400 → _p2mH400
end
open _root_.P2Mb748e9da renaming h397 → _p2mH397
open _root_.P2Mb748e9da renaming h398 → _p2mH398
open _root_.P2Mb748e9da renaming h399 → _p2mH399
open _root_.P2Mb748e9da renaming h400 → _p2mH400
namespace CurrentAFT.OrdinaryRaising
end CurrentAFT.OrdinaryRaising
namespace CurrentAFT.OrdinaryRaising.deviation
end CurrentAFT.OrdinaryRaising.deviation
section
namespace CurrentAFT.CompleteRaising
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.CompleteRaising.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.CompleteRaising.classicalSumDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h224 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (selected : Finset (Fin r ⊕ Fin s)) (sourcePrimary : Fin r → _root_.CurrentAFT.CompleteRaising.Palette security) (sourceBody : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (r + s + selected.card)
      (_root_.CurrentAFT.CompleteRaising.selectedPointProduct security order horder selected sourcePrimary sourceBody) := by
  have h := _root_.CurrentAFT.GlobalRaising.vanishesBelow_prod (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (Finset.univ : Finset (Fin r ⊕ Fin s)) (fun slot => if slot ∈ selected then 2 else 1)
    (fun slot => if slot ∈ selected then _root_.CurrentAFT.CompleteRaising.slotRaised security order horder sourcePrimary sourceBody slot
      else _root_.CurrentAFT.CompleteRaising.slotLeading security order horder sourcePrimary sourceBody slot) (fun slot _ => by
        split_ifs
        · cases slot with
          | inl index => exact _p2mH376 security order horder _
          | inr index => exact _p2mH400 security order horder _ _
        · cases slot with
          | inl index => exact _p2mH375 security order horder _
          | inr index => exact _p2mH374 security order horder _)
  have hcount : (∑ slot : Fin r ⊕ Fin s, if slot ∈ selected then 2 else 1) = r + s + selected.card := by
    have hpoint (slot : Fin r ⊕ Fin s) : (if slot ∈ selected then 2 else 1) =
        1 + (if slot ∈ selected then 1 else 0) := by split_ifs <;> omega
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib]
  simpa only [hcount, _root_.CurrentAFT.CompleteRaising.selectedPointProduct] using h
open _root_.P2Mb748e9da renaming h224 → _p2mH224
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h222 (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (r + s + 1)
      (_root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel) := by
  simp only [_root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  apply _root_.CurrentAFT.LocalRaisingFirst.vanishesBelow_sum
  intro selected hselected
  change _root_.CurrentAFT.GradedInverse.VanishesBelow _ _ order (r + s + 1) (_root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder selected kernel)
  unfold _root_.CurrentAFT.CompleteRaising.selectedCorrection
  apply _root_.CurrentAFT.LocalRaisingFirst.vanishesBelow_sum
  intro sourcePrimary _
  apply _root_.CurrentAFT.LocalRaisingFirst.vanishesBelow_sum
  intro sourceBody _
  apply _root_.CurrentAFT.GlobalRaising.vanishesBelow_smul
  intro arity hdegree
  have hpositive : 0 < selected.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
  exact _p2mH224 security order horder selected sourcePrimary sourceBody arity (by omega)
open _root_.P2Mb748e9da renaming h222 → _p2mH222
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h223 (security order : ℕ) (horder : 1 ≤ order) (degree : ℕ)
    (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order)
    (hfamily : _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order degree family) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (degree + 1)
      (_root_.CurrentAFT.CompleteRaising.raisingLinear security order horder family) := by
  change _root_.CurrentAFT.GradedInverse.VanishesBelow _ _ order (degree + 1) (∑ arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order,
    _root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder arity.val.1.val arity.val.2.val (family arity))
  apply _root_.CurrentAFT.LocalRaisingFirst.vanishesBelow_sum
  intro arity _
  by_cases hsmall : arity.val.1.val + arity.val.2.val < degree
  · rw [hfamily arity hsmall, map_zero]
    intro output _
    rfl
  · intro output hdegree
    exact _p2mH222 security order horder _ _ (family arity) output (by omega)
open _root_.P2Mb748e9da renaming h223 → _p2mH223
end
open _root_.P2Mb748e9da renaming h222 → _p2mH222
open _root_.P2Mb748e9da renaming h223 → _p2mH223
open _root_.P2Mb748e9da renaming h224 → _p2mH224
end CurrentAFT.CompleteRaising
open _root_.P2Mb748e9da renaming h222 → _p2mH222
open _root_.P2Mb748e9da renaming h223 → _p2mH223
open _root_.P2Mb748e9da renaming h224 → _p2mH224
end
open _root_.P2Mb748e9da renaming h222 → _p2mH222
open _root_.P2Mb748e9da renaming h223 → _p2mH223
open _root_.P2Mb748e9da renaming h224 → _p2mH224
section
namespace CurrentAFT.BodyChannelEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation
  MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference MarkedPairLeading.bodyConvolution
attribute [local instance] _root_.CurrentAFT.BodyChannelEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h217 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms (_root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body density hcenter).val =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial body bodyForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) := by
  simp only [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial, _root_.CurrentAFT.BackgroundFamilies.bodyKernel, _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial, _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile, Fin.prod_univ_zero,
    Fintype.sum_unique, one_mul]
open _root_.P2Mb748e9da renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h216 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.familyHom primary body primaryForms bodyForms hprimary hbody order
      (_root_.CurrentAFT.BackgroundFamilies.bodyFamily primary body order horder density hcenter) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial body bodyForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms
    (_root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body density hcenter).val) = _
  rw [_p2mH217]
open _root_.P2Mb748e9da renaming h216 → _p2mH216
end
open _root_.P2Mb748e9da renaming h216 → _p2mH216
open _root_.P2Mb748e9da renaming h217 → _p2mH217
end CurrentAFT.BodyChannelEvaluation
open _root_.P2Mb748e9da renaming h216 → _p2mH216
open _root_.P2Mb748e9da renaming h217 → _p2mH217
end
open _root_.P2Mb748e9da renaming h216 → _p2mH216
open _root_.P2Mb748e9da renaming h217 → _p2mH217
namespace CurrentAFT.ActualRootResponse
end CurrentAFT.ActualRootResponse
section
namespace CurrentAFT.ActualRootDefect
open AFT ActualBlockFock TaggedSelection PairedRootPlacement ControlCoordinates
  GradedControlAlgebra LocalCoefficientFamily GradedInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootDefect.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootDefect.classicalSumDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h169 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.ActualRootDefect.selectedDefect order horder queue selection layout kernel) := by
  intro arity hsmall
  simp only [_root_.CurrentAFT.ActualRootDefect.selectedDefect, LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro tagged htagged
  have hlower := (Finset.mem_filter.mp htagged).2
  have hdegree := _root_.CurrentAFT.PairedRootDegrees.tags_le_degree selection tagged
  exact _root_.CurrentAFT.ActualRootResponse.response_degree order horder queue selection tagged layout kernel arity (by omega)
open _root_.P2Mb748e9da renaming h169 → _p2mH169
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h170 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    (_root_.CurrentAFT.ActualRootDefect.selectedDefect order horder queue selection layout kernel) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 :=
  _p2mH169 order horder queue selection layout kernel (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) (by
    change 0 + 0 < 2
    omega)
open _root_.P2Mb748e9da renaming h170 → _p2mH170
end
open _root_.P2Mb748e9da renaming h169 → _p2mH169
open _root_.P2Mb748e9da renaming h170 → _p2mH170
end CurrentAFT.ActualRootDefect
open _root_.P2Mb748e9da renaming h169 → _p2mH169
open _root_.P2Mb748e9da renaming h170 → _p2mH170
end
open _root_.P2Mb748e9da renaming h169 → _p2mH169
open _root_.P2Mb748e9da renaming h170 → _p2mH170
namespace CurrentAFT.ActualRootDefectNorm
end CurrentAFT.ActualRootDefectNorm
section
namespace CurrentAFT.ActualRootFamily
open AFT ActualBlockFock TaggedSelection UniformTaggedOutput ControlCoordinates ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  LocalCoefficientFamily BackgroundRates
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootFamily.finDecEq
attribute [local instance] _root_.CurrentAFT.ActualRootFamily.sumDecEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h171 (security order : ℕ) (horder : 1 ≤ order) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    (_root_.CurrentAFT.ActualRootFamily.rootLinear security order horder hroom queue layout family) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
  rw [_root_.CurrentAFT.ActualRootFamily.rootLinear_apply]
  simp_rw [_root_.CurrentAFT.ActualRootFamily.selectedAverage_apply]
  simp only [Finset.sum_apply, Pi.smul_apply,
    _p2mH170, smul_zero, Finset.sum_const_zero]
open _root_.P2Mb748e9da renaming h171 → _p2mH171
end
open _root_.P2Mb748e9da renaming h171 → _p2mH171
end CurrentAFT.ActualRootFamily
open _root_.P2Mb748e9da renaming h171 → _p2mH171
end
open _root_.P2Mb748e9da renaming h171 → _p2mH171
namespace CurrentAFT.ActualBackground.stabilityConstant
end CurrentAFT.ActualBackground.stabilityConstant
namespace CurrentAFT.ActualBackgroundInverse
end CurrentAFT.ActualBackgroundInverse
namespace CurrentAFT.ActualBackgroundInverse.inverse
end CurrentAFT.ActualBackgroundInverse.inverse
namespace CurrentAFT.ActualRootDefect
end CurrentAFT.ActualRootDefect
namespace CurrentAFT.ActualRootDefect.selectedDefect
end CurrentAFT.ActualRootDefect.selectedDefect
namespace CurrentAFT.ActualRootFamily
end CurrentAFT.ActualRootFamily
namespace CurrentAFT.ActualRootFamily.rootLinear
end CurrentAFT.ActualRootFamily.rootLinear
namespace CurrentAFT.ActualRootFamily.selectedAverage
end CurrentAFT.ActualRootFamily.selectedAverage
namespace CurrentAFT.CompleteRaisingStability
end CurrentAFT.CompleteRaisingStability
namespace CurrentAFT.RaisingPatternNorm
end CurrentAFT.RaisingPatternNorm
namespace CurrentAFT.RaisingPatternNorm.homogeneousCorrection
end CurrentAFT.RaisingPatternNorm.homogeneousCorrection
section
namespace CurrentAFT.ActualCompleteStability
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalCoefficientFamily
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm
  BackgroundRates BackgroundLinear ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualCompleteStability.classicalFinDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference BackgroundRates.ordinaryPool
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h149 (order : ℕ) : 0 ≤ _root_.CurrentAFT.ActualCompleteStability.independentConstant order := by
  unfold _root_.CurrentAFT.ActualCompleteStability.independentConstant _root_.CurrentAFT.ActualBackground.stabilityConstant
  exact add_nonneg (by positivity) (mul_nonneg (by norm_num) (_root_.CurrentAFT.CompleteRaisingStability.stabilityConstant_nonneg order))
open _root_.P2Mb748e9da renaming h149 → _p2mH149
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h155 (order : ℕ) : 0 ≤ _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order :=
  add_nonneg (_p2mH149 order)
    (mul_nonneg (by norm_num) (_root_.CurrentAFT.ActualRootDefectNorm.stabilityConstant_nonneg order))
open _root_.P2Mb748e9da renaming h155 → CurrentAFT.ActualCompleteStability.stabilityConstant_nonneg
open _root_.P2Mb748e9da renaming h155 → _p2mH155
end
open _root_.P2Mb748e9da renaming h149 → _p2mH149
open _root_.P2Mb748e9da renaming h155 → CurrentAFT.ActualCompleteStability.stabilityConstant_nonneg
open _root_.P2Mb748e9da renaming h155 → _p2mH155
end CurrentAFT.ActualCompleteStability
open _root_.P2Mb748e9da renaming h149 → _p2mH149
open _root_.P2Mb748e9da renaming h155 → CurrentAFT.ActualCompleteStability.stabilityConstant_nonneg
open _root_.P2Mb748e9da renaming h155 → _p2mH155
end
open _root_.P2Mb748e9da renaming h149 → _p2mH149
open _root_.P2Mb748e9da renaming h155 → CurrentAFT.ActualCompleteStability.stabilityConstant_nonneg
open _root_.P2Mb748e9da renaming h155 → _p2mH155
namespace CurrentAFT.ActualCompleteStability
end CurrentAFT.ActualCompleteStability
namespace CurrentAFT.ActualCompleteStability.rootCorrection
end CurrentAFT.ActualCompleteStability.rootCorrection
section
namespace CurrentAFT.ActualCompleteStability
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalCoefficientFamily ControlCoordinates
  GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverseNorm Augmentation
  BackgroundRates BackgroundLinear ActualBackground
open Filter
open scoped BigOperators Classical Topology
noncomputable section
attribute [local instance] _root_.CurrentAFT.ActualCompleteStability.solutionFinDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference BackgroundRates.ordinaryPool
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h151 (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualCompleteStability.rootCorrection security order horder hroom layout family) = 0 := by
  have hroot (queue : ℤ) : _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
      (_root_.CurrentAFT.ActualRootFamily.rootLinear security order (by omega) hroom queue layout family) = 0 := by
    change _root_.CurrentAFT.GradedControlAlgebra.scalarAt _ _ ((_root_.CurrentAFT.ActualRootFamily.rootLinear security order (by omega) hroom queue layout family) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) = 0
    rw [_p2mH171]
    rfl
  simp only [_root_.CurrentAFT.ActualCompleteStability.rootCorrection, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, map_mul, hroot,
    mul_zero, smul_zero, Finset.sum_const_zero]
open _root_.P2Mb748e9da renaming h151 → _p2mH151
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h150 (security order : ℕ) (horder : 2 ≤ order) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualCompleteStability.independentResponse security order horder family) =
      _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order family := by
  have hbackground : _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualBackground.background security order horder) = 1 := by
    have h := (_p2mH213 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order _ _).mp
      (_p2mH124 security order horder)
    simpa only [map_one] using h
  have hraising : _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
      (_root_.CurrentAFT.CompleteRaising.raisingLinear security order (by omega) family) = 0 := by
    have h := _p2mH223 security order (by omega) 0 family (_root_.CurrentAFT.GradedInverse.vanishesBelow_zero _ _ order family)
    have hz := h (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) (by change 0 + 0 < 0 + 1; omega)
    change _root_.CurrentAFT.GradedControlAlgebra.scalarAt _ _ ((_root_.CurrentAFT.CompleteRaising.raisingLinear security order (by omega) family) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) = 0
    rw [hz]
    rfl
  change _root_.CurrentAFT.Augmentation.scalarHom _ _ order (_root_.CurrentAFT.ActualBackground.background security order horder * (family + _)) = _
  rw [map_mul, map_add, hbackground, hraising, add_zero, one_mul]
open _root_.P2Mb748e9da renaming h150 → _p2mH150
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h148 (security order : ℕ) (horder : 2 ≤ order) (hroom : 2 * order ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualCompleteStability.fullResponse security order horder hroom layout family) =
      _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order family := by
  change _root_.CurrentAFT.Augmentation.scalarHom _ _ order (_root_.CurrentAFT.ActualCompleteStability.independentResponse security order horder family + _root_.CurrentAFT.ActualCompleteStability.rootCorrection security order horder hroom layout family) = _
  rw [map_add, _p2mH150, _p2mH151, add_zero]
open _root_.P2Mb748e9da renaming h148 → _p2mH148
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h152 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.ActualCompleteStability.fullResponse security order horder (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) layout (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity layout) = 1 :=
  (Classical.choose_spec (_root_.CurrentAFT.ActualCompleteStability.calibration_existsUnique security order horder hsecurity layout 1)).1
open _root_.P2Mb748e9da renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h154 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity layout - 1) ≤
      2 * _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 := by
  have hs := _root_.CurrentAFT.ActualCompleteStability.stable security order horder hsecurity layout
  have hnorm : _root_.CurrentAFT.LocalRaisingBounds.coefficientNorm security order (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) = 1 := _root_.CurrentAFT.GradedInverseNorm.familyNorm_one _ _ _ _ _
  have href := hs.2 1
  rw [hnorm, mul_one] at href
  have hbound := (Classical.choose_spec (_root_.CurrentAFT.ActualCompleteStability.calibration_existsUnique security order horder hsecurity layout 1)).2.2 1
  apply hbound.trans
  have hgap : 0 < 1 - _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 := by linarith [hs.1]
  apply (div_le_div_of_nonneg_right href hgap.le).trans
  apply (div_le_iff₀ hgap).mpr
  have hnonneg : 0 ≤ _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 :=
    div_nonneg (_p2mH155 order) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hs.1 hnonneg
  rw [show 2 * _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 =
    2 * (_root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6) by ring]
  nlinarith only [hmul]
open _root_.P2Mb748e9da renaming h154 → _p2mH154
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h153 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity layout) = 1 := by
  rw [← _p2mH148 security order horder (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) layout, _p2mH152, map_one]
open _root_.P2Mb748e9da renaming h153 → _p2mH153
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h146 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout).1 = 1 := _p2mH153 security order horder hsecurity layout
open _root_.P2Mb748e9da renaming h146 → _p2mH146
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h145 (security order : ℕ) :
    _root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) = (1, 0) := by
  apply Prod.ext
  · change _root_.CurrentAFT.Augmentation.scalarHom (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) = 1
    exact map_one _
  · funext arity
    change (_root_.CurrentAFT.GradedControlAlgebra.familyUnit (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order) (_root_.CurrentAFT.GradedControlAlgebra.positiveArity order arity) = 0
    rw [_root_.CurrentAFT.GradedControlAlgebra.familyUnit, Pi.single_eq_of_ne]
    intro hequal
    have h := congrArg (fun output : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => output.val.1.val + output.val.2.val) hequal
    have hpositive := arity.property.1
    change arity.val.1.val + arity.val.2.val = 0 + 0 at h
    omega
open _root_.P2Mb748e9da renaming h145 → _p2mH145
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h147 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security)
      (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout - (1, 0)) ≤ 2 * _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 := by
  rw [← _p2mH145]
  change _root_.CurrentAFT.ControlNorm.coefficientNorm _ _ order _ _
    (_root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity layout) -
      _root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 1) ≤ _
  have hequal := (_root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order).map_sub
    (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity layout) 1
  calc
    _ = _root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security)
        (_root_.CurrentAFT.GradedControlAlgebra.familyCoefficientEquiv (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity layout - 1)) :=
      (congrArg (_root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security)) hequal).symm
    _ ≤ _ := by
      rw [← _p2mH379]
      exact _p2mH154 security order horder hsecurity layout
open _root_.P2Mb748e9da renaming h147 → _p2mH147
end
open _root_.P2Mb748e9da renaming h145 → _p2mH145
open _root_.P2Mb748e9da renaming h146 → _p2mH146
open _root_.P2Mb748e9da renaming h147 → _p2mH147
open _root_.P2Mb748e9da renaming h148 → _p2mH148
open _root_.P2Mb748e9da renaming h150 → _p2mH150
open _root_.P2Mb748e9da renaming h151 → _p2mH151
open _root_.P2Mb748e9da renaming h152 → _p2mH152
open _root_.P2Mb748e9da renaming h153 → _p2mH153
open _root_.P2Mb748e9da renaming h154 → _p2mH154
end CurrentAFT.ActualCompleteStability
open _root_.P2Mb748e9da renaming h145 → _p2mH145
open _root_.P2Mb748e9da renaming h146 → _p2mH146
open _root_.P2Mb748e9da renaming h147 → _p2mH147
open _root_.P2Mb748e9da renaming h148 → _p2mH148
open _root_.P2Mb748e9da renaming h150 → _p2mH150
open _root_.P2Mb748e9da renaming h151 → _p2mH151
open _root_.P2Mb748e9da renaming h152 → _p2mH152
open _root_.P2Mb748e9da renaming h153 → _p2mH153
open _root_.P2Mb748e9da renaming h154 → _p2mH154
end
open _root_.P2Mb748e9da renaming h145 → _p2mH145
open _root_.P2Mb748e9da renaming h146 → _p2mH146
open _root_.P2Mb748e9da renaming h147 → _p2mH147
open _root_.P2Mb748e9da renaming h148 → _p2mH148
open _root_.P2Mb748e9da renaming h150 → _p2mH150
open _root_.P2Mb748e9da renaming h151 → _p2mH151
open _root_.P2Mb748e9da renaming h152 → _p2mH152
open _root_.P2Mb748e9da renaming h153 → _p2mH153
open _root_.P2Mb748e9da renaming h154 → _p2mH154
namespace CurrentAFT.SafeControlGroups
end CurrentAFT.SafeControlGroups
namespace CurrentAFT.SafeControlGroups.reference
end CurrentAFT.SafeControlGroups.reference
section
namespace CurrentAFT.PhysicalMoments
open AFT DiffuseProfiles ProposalPrimary PhysicalSynthesis ControlCoordinates ControlNorm
  BackgroundRates FiniteAtomMoments
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.PhysicalMoments.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PhysicalMoments.classicalSumDecidableEq
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
  BackgroundRates.ordinaryPool ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference SafeControlGroups.reference SafeControlGroups.kernel
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h404 (primaryOrder bodyOrder moment : ℕ) :
    0 ≤ _root_.CurrentAFT.PhysicalMoments.blockFactor primaryOrder bodyOrder moment :=
  mul_nonneg (_p2mH352 _ _ _ _ (by norm_num)) (by positivity)
open _root_.P2Mb748e9da renaming h404 → _p2mH404
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h406 (order moment : ℕ) : 0 < _root_.CurrentAFT.PhysicalMoments.coefficientFactor order moment := by
  unfold _root_.CurrentAFT.PhysicalMoments.coefficientFactor
  have hsum : 0 ≤ ∑ arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order,
      _root_.CurrentAFT.PhysicalMoments.blockFactor arity.val.1.val arity.val.2.val moment :=
    Finset.sum_nonneg fun arity _ => _p2mH404 _ _ _
  linarith
open _root_.P2Mb748e9da renaming h406 → _p2mH406
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h403 (order moment : ℕ) (arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order) :
    _root_.CurrentAFT.PhysicalMoments.blockFactor arity.val.1.val arity.val.2.val moment ≤ _root_.CurrentAFT.PhysicalMoments.coefficientFactor order moment := by
  have h := Finset.single_le_sum
    (fun arity (_ : arity ∈ (Finset.univ : Finset (_root_.CurrentAFT.ControlCoordinates.PositiveArity order))) => _p2mH404 arity.val.1.val arity.val.2.val moment)
    (Finset.mem_univ arity)
  unfold _root_.CurrentAFT.PhysicalMoments.coefficientFactor
  linarith
open _root_.P2Mb748e9da renaming h403 → _p2mH403
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h409 (security : ℕ) : 1 ≤ _root_.CurrentAFT.BackgroundRates.radius security := by
  apply Real.one_le_rpow
  · exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.base security by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega)
  · norm_num
open _root_.P2Mb748e9da renaming h409 → _p2mH409
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h408 (security r s : ℕ) :
    (1 / Real.sqrt (_root_.CurrentAFT.Parameters.legCount security : ℝ)) ^ r *
        (1 / Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ)) ^ s ≤
      _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) r s := by
  have hbodyRate : 1 / Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ) ≤ _root_.CurrentAFT.BackgroundRates.bodyFactor security := by
    have h := mul_le_mul_of_nonneg_right (_p2mH409 security)
      (inv_nonneg.mpr (Real.sqrt_nonneg (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ)))
    simpa only [_root_.CurrentAFT.BackgroundRates.bodyFactor, one_div, one_mul] using h
  unfold _root_.CurrentAFT.ControlNorm.gradeWeight _root_.CurrentAFT.BackgroundRates.primaryFactor
  simp only [one_div]
  have hbodyPower : (Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ))⁻¹ ^ s ≤ _root_.CurrentAFT.BackgroundRates.bodyFactor security ^ s := by
    simpa only [one_div] using pow_le_pow_left₀ (by positivity) hbodyRate s
  exact mul_le_mul_of_nonneg_left
    hbodyPower (by positivity)
open _root_.P2Mb748e9da renaming h408 → _p2mH408
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h410 (security r s : ℕ)
    (input : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    Real.sqrt ((_root_.AFT.FiniteDist.independent
      (fun _ : Fin r ⊕ Fin s => _root_.CurrentAFT.SafeControlGroups.reference security)).l2Sq
      (_root_.CurrentAFT.SafeControlGroups.kernel security r s input)) ≤
      17 ^ r * _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) input.val := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by positivity) (_root_.CurrentAFT.ControlNorm.blockL2_nonneg _ _ _)
  · have hpower : (258 : ℝ) ^ r ≤ ((17 : ℝ) ^ r) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm r 2, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) r
    calc
      _ ≤ 258 ^ r * _root_.CurrentAFT.ControlNorm.blockEnergy (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) input.val :=
        _p2mH443 security r s input
      _ ≤ (17 ^ r) ^ 2 * _root_.CurrentAFT.ControlNorm.blockEnergy (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) input.val :=
        mul_le_mul_of_nonneg_right hpower (_root_.CurrentAFT.ControlNorm.blockEnergy_nonneg _ _ _)
      _ = _ := by rw [mul_pow, _root_.CurrentAFT.ControlNorm.blockL2_sq]
open _root_.P2Mb748e9da renaming h410 → _p2mH410
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h405 (security r s moment : ℕ) (hmoment : 1 ≤ moment)
    (hprimaryRoom : 2 * r ≤ _root_.CurrentAFT.Parameters.legCount security)
    (hbodyRoom : 2 * s ≤ _root_.CurrentAFT.BackgroundRates.ordinaryPool security)
    (input : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ControlCoordinates.kernelMean (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (fun groups centers => |_root_.CurrentAFT.ControlCoordinates.twoPoolUStatistic (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.BackgroundRates.ordinaryPool security)
        (_root_.CurrentAFT.PhysicalSynthesis.pairedKernel security r s input.val) groups centers| ^ (2 * moment)) ≤
      (_root_.CurrentAFT.PhysicalMoments.blockFactor r s moment * _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) r s *
        _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) input.val) ^ (2 * moment) := by
  have hinput : Sum.elim (fun _ : Fin r => _root_.CurrentAFT.SafeControlGroups.reference security)
      (fun _ : Fin s => _root_.CurrentAFT.SafeControlGroups.reference security) =
        (fun _ : Fin r ⊕ Fin s => _root_.CurrentAFT.SafeControlGroups.reference security) := by funext slot; cases slot <;> rfl
  have hpool : Sum.elim (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.SafeControlGroups.reference security)
      (fun _ : Fin (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) => _root_.CurrentAFT.SafeControlGroups.reference security) =
        (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) ⊕ Fin (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) => _root_.CurrentAFT.SafeControlGroups.reference security) := by
    funext slot
    cases slot <;> rfl
  have hcanonical : _root_.AFT.Hoeffding.Canonical
      (Sum.elim (fun _ : Fin r => _root_.CurrentAFT.SafeControlGroups.reference security)
        (fun _ : Fin s => _root_.CurrentAFT.SafeControlGroups.reference security)) Finset.univ
      (_root_.CurrentAFT.SafeControlGroups.kernel security r s input) := by
    rw [hinput]
    exact _p2mH442 security r s input
  have h := _p2mH353
    (PS := Fin r) (BS := Fin s) (PP := Fin (_root_.CurrentAFT.Parameters.legCount security)) (BP := Fin (_root_.CurrentAFT.BackgroundRates.ordinaryPool security))
    (_root_.CurrentAFT.SafeControlGroups.reference security) (_root_.CurrentAFT.SafeControlGroups.reference security)
    (_root_.CurrentAFT.SafeControlGroups.kernel security r s input) hcanonical (_root_.CurrentAFT.FiniteAtomMoments.currentAtomLower security)
    (_p2mH347 security) (_p2mH446 security)
    (_p2mH446 security) 262144 (by norm_num)
    (by simpa only [Fintype.card_fin] using _p2mH351 security)
    (by simpa only [Fintype.card_fin] using _p2mH349 security) moment hmoment
    (by simpa only [Fintype.card_fin, _root_.CurrentAFT.Parameters.legCount_eq] using pow_pos (_root_.CurrentAFT.Parameters.base_pos security) 128)
    (by simpa only [Fintype.card_fin] using _root_.CurrentAFT.BackgroundRates.ordinaryPool_pos security)
    (by simpa only [Fintype.card_fin] using hprimaryRoom) (by simpa only [Fintype.card_fin] using hbodyRoom)
  rw [hinput, hpool, _p2mH450] at h
  simp only [Fintype.card_fin] at h
  apply h.trans
  apply pow_le_pow_left₀
  · exact mul_nonneg (mul_nonneg (_p2mH352 _ _ _ _ (by norm_num)) (by positivity)) (Real.sqrt_nonneg _)
  · have hnorm := _p2mH410 security r s input
    have hscaleNonneg : 0 ≤ _root_.CurrentAFT.FiniteAtomMoments.momentFactor r s moment 262144 *
        ((1 / Real.sqrt (_root_.CurrentAFT.Parameters.legCount security : ℝ)) ^ r *
          (1 / Real.sqrt (_root_.CurrentAFT.BackgroundRates.ordinaryPool security : ℝ)) ^ s) :=
      mul_nonneg (_p2mH352 _ _ _ _ (by norm_num)) (by positivity)
    have hnormScaled := mul_le_mul_of_nonneg_left hnorm
      hscaleNonneg
    apply hnormScaled.trans
    have hgrade := mul_le_mul_of_nonneg_left (_p2mH408 security r s)
      (_p2mH404 r s moment)
    have hh := mul_le_mul_of_nonneg_right hgrade (_root_.CurrentAFT.ControlNorm.blockL2_nonneg (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.ActualControls.bodyReference security) input.val)
    convert hh using 1
    unfold _root_.CurrentAFT.PhysicalMoments.blockFactor
    ring
open _root_.P2Mb748e9da renaming h405 → _p2mH405
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h407 (security order moment : ℕ) (hmoment : 1 ≤ moment)
    (hsecurity : 2 * order ≤ security) (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order) :
    _root_.CurrentAFT.ControlCoordinates.kernelMean (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (fun groups centers => |_root_.CurrentAFT.PhysicalSynthesis.coefficientWeight security order (_root_.CurrentAFT.Parameters.legCount security)
        (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) coefficient groups centers - coefficient.1| ^ (2 * moment)) ≤
      (_root_.CurrentAFT.PhysicalMoments.coefficientFactor order moment * _root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
        order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) (0, coefficient.2)) ^ (2 * moment) := by
  let law := (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.PhysicalSynthesis.groupLaw security)).prod
    (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) => _root_.CurrentAFT.ActualControls.bodyReference security))
  let summand := fun (arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order)
      (inputs : (Fin (_root_.CurrentAFT.Parameters.legCount security) → _root_.CurrentAFT.PhysicalSynthesis.Group security) ×
        (Fin (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) → _root_.CurrentAFT.ActualControls.SafePalette security)) =>
    _root_.CurrentAFT.ControlCoordinates.twoPoolUStatistic (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.BackgroundRates.ordinaryPool security)
      (_root_.CurrentAFT.PhysicalSynthesis.pairedKernel security arity.val.1.val arity.val.2.val (coefficient.2 arity).val) inputs.1 inputs.2
  let size := fun arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order =>
    _root_.CurrentAFT.ControlNorm.gradeWeight (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) arity.val.1.val arity.val.2.val *
      _root_.CurrentAFT.ControlNorm.blockL2 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (coefficient.2 arity).val
  have hsize (arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order) : 0 ≤ size arity :=
    mul_nonneg (_root_.CurrentAFT.ControlNorm.gradeWeight_nonneg _ _ (by unfold _root_.CurrentAFT.BackgroundRates.primaryFactor; positivity)
      (by unfold _root_.CurrentAFT.BackgroundRates.bodyFactor _root_.CurrentAFT.BackgroundRates.radius; positivity) _ _) (_root_.CurrentAFT.ControlNorm.blockL2_nonneg _ _ _)
  have hterm (arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order) :
      law.expectation (fun inputs => |summand arity inputs| ^ (2 * moment)) ≤
        (_root_.CurrentAFT.PhysicalMoments.coefficientFactor order moment * size arity) ^ (2 * moment) := by
    have hroom := _root_.CurrentAFT.FiniteAtomMoments.current_pool_room security order hsecurity _ _ arity.property.2
    have h := _p2mH405 security _ _ moment hmoment hroom.1 hroom.2 (coefficient.2 arity)
    change law.expectation (fun inputs => |summand arity inputs| ^ (2 * moment)) ≤ _ at h
    rw [mul_assoc] at h
    change law.expectation (fun inputs => |summand arity inputs| ^ (2 * moment)) ≤
      (_root_.CurrentAFT.PhysicalMoments.blockFactor arity.val.1.val arity.val.2.val moment * size arity) ^ (2 * moment) at h
    apply h.trans
    apply pow_le_pow_left₀ (mul_nonneg (_p2mH404 _ _ _) (hsize arity))
    exact mul_le_mul_of_nonneg_right (_p2mH403 order moment arity) (hsize arity)
  have hsum := _p2mH75 law summand
    (fun arity => _root_.CurrentAFT.PhysicalMoments.coefficientFactor order moment * size arity)
    (fun arity => mul_nonneg (_p2mH406 order moment).le (hsize arity))
    (2 * moment) (by omega) hterm
  have hweight (inputs : (Fin (_root_.CurrentAFT.Parameters.legCount security) → _root_.CurrentAFT.PhysicalSynthesis.Group security) ×
      (Fin (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) → _root_.CurrentAFT.ActualControls.SafePalette security)) :
      _root_.CurrentAFT.PhysicalSynthesis.coefficientWeight security order (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.BackgroundRates.ordinaryPool security)
        coefficient inputs.1 inputs.2 - coefficient.1 = ∑ arity, summand arity inputs := by
    unfold _root_.CurrentAFT.PhysicalSynthesis.coefficientWeight
    ring
  change law.expectation _ ≤ _
  simp_rw [hweight]
  apply hsum.trans_eq
  rw [← Finset.mul_sum]
  congr 2
  unfold _root_.CurrentAFT.ControlNorm.coefficientNorm
  simp only [abs_zero, zero_add]
  rfl
open _root_.P2Mb748e9da renaming h407 → _p2mH407
end
open _root_.P2Mb748e9da renaming h403 → _p2mH403
open _root_.P2Mb748e9da renaming h404 → _p2mH404
open _root_.P2Mb748e9da renaming h405 → _p2mH405
open _root_.P2Mb748e9da renaming h406 → _p2mH406
open _root_.P2Mb748e9da renaming h407 → _p2mH407
open _root_.P2Mb748e9da renaming h408 → _p2mH408
open _root_.P2Mb748e9da renaming h409 → _p2mH409
open _root_.P2Mb748e9da renaming h410 → _p2mH410
end CurrentAFT.PhysicalMoments
open _root_.P2Mb748e9da renaming h403 → _p2mH403
open _root_.P2Mb748e9da renaming h404 → _p2mH404
open _root_.P2Mb748e9da renaming h405 → _p2mH405
open _root_.P2Mb748e9da renaming h406 → _p2mH406
open _root_.P2Mb748e9da renaming h407 → _p2mH407
open _root_.P2Mb748e9da renaming h408 → _p2mH408
open _root_.P2Mb748e9da renaming h409 → _p2mH409
open _root_.P2Mb748e9da renaming h410 → _p2mH410
end
open _root_.P2Mb748e9da renaming h403 → _p2mH403
open _root_.P2Mb748e9da renaming h404 → _p2mH404
open _root_.P2Mb748e9da renaming h405 → _p2mH405
open _root_.P2Mb748e9da renaming h406 → _p2mH406
open _root_.P2Mb748e9da renaming h407 → _p2mH407
open _root_.P2Mb748e9da renaming h408 → _p2mH408
open _root_.P2Mb748e9da renaming h409 → _p2mH409
open _root_.P2Mb748e9da renaming h410 → _p2mH410
namespace AFT.BlockProducts
end AFT.BlockProducts
namespace AFT.BlockProducts.blockLaw
end AFT.BlockProducts.blockLaw
namespace AFT.BlockProducts.blockMass
end AFT.BlockProducts.blockMass
namespace CurrentAFT.BackgroundRates.bodyFactor
end CurrentAFT.BackgroundRates.bodyFactor
namespace CurrentAFT.PhysicalMoments
end CurrentAFT.PhysicalMoments
namespace CurrentAFT.PublicOutputExperiment
end CurrentAFT.PublicOutputExperiment
namespace CurrentAFT.PublicOutputExperiment.conditionalBlocks
end CurrentAFT.PublicOutputExperiment.conditionalBlocks
namespace CurrentAFT.PublicOutputExperiment.conditionalBlocks.match_1
end CurrentAFT.PublicOutputExperiment.conditionalBlocks.match_1
namespace CurrentAFT.PublicOutputExperiment.ordinaryWord
end CurrentAFT.PublicOutputExperiment.ordinaryWord
namespace CurrentAFT.PublicOutputExperiment.pairedWord
end CurrentAFT.PublicOutputExperiment.pairedWord
namespace CurrentAFT.PublicOutputExperiment.physicalFactor
end CurrentAFT.PublicOutputExperiment.physicalFactor
namespace CurrentAFT.PublicOutputExperiment.physicalFactor.match_1
end CurrentAFT.PublicOutputExperiment.physicalFactor.match_1
namespace CurrentAFT.PublicOutputExperiment.placedEmbedding
end CurrentAFT.PublicOutputExperiment.placedEmbedding
namespace CurrentAFT.PublicOutputExperiment.queueFactor
end CurrentAFT.PublicOutputExperiment.queueFactor
namespace CurrentAFT.SafeControlGroups.unwrap
end CurrentAFT.SafeControlGroups.unwrap
namespace CurrentAFT.UniformTaggedOutput.compensatorPosition
end CurrentAFT.UniformTaggedOutput.compensatorPosition
namespace CurrentAFT.UniformTaggedOutput.ordinaryPosition
end CurrentAFT.UniformTaggedOutput.ordinaryPosition
namespace CurrentAFT.clip
end CurrentAFT.clip
section
namespace CurrentAFT.PublicWeightMoments
open AFT PublicOutputExperiment PhysicalSynthesis ControlCoordinates ControlNorm BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h429 (security order : ℕ) (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order)
    (test : ℝ → ℝ) :
    (_root_.CurrentAFT.PublicOutputExperiment.reference security).expectation (fun controls => test (_root_.CurrentAFT.PublicOutputExperiment.actualWeight security order coefficient controls)) =
      _root_.CurrentAFT.ControlCoordinates.kernelMean (_root_.CurrentAFT.PhysicalSynthesis.groupLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
        (fun groups centers => test (_root_.CurrentAFT.PhysicalSynthesis.coefficientWeight security order (_root_.CurrentAFT.Parameters.legCount security)
          (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) coefficient groups centers)) := by
  have h := _p2mH439 security (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.BackgroundRates.ordinaryPool security)
    (fun groups centers => test (_root_.CurrentAFT.PhysicalSynthesis.coefficientWeight security order (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.BackgroundRates.ordinaryPool security) coefficient groups centers))
  unfold _root_.CurrentAFT.PublicOutputExperiment.reference _root_.CurrentAFT.PublicOutputExperiment.actualWeight
  exact (_p2mH451 _ _ _ _).trans h
open _root_.P2Mb748e9da renaming h429 → _p2mH429
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h428 (security order moment : ℕ) (hmoment : 1 ≤ moment)
    (hsecurity : 2 * order ≤ security) (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order) :
    (_root_.CurrentAFT.PublicOutputExperiment.reference security).expectation (fun controls => |_root_.CurrentAFT.PublicOutputExperiment.actualWeight security order coefficient controls - coefficient.1| ^ (2 * moment)) ≤
      (_root_.CurrentAFT.PhysicalMoments.coefficientFactor order moment *
        _root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
          order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) (0, coefficient.2)) ^ (2 * moment) := by
  rw [_p2mH429 security order coefficient (fun value => |value - coefficient.1| ^ (2 * moment))]
  exact _p2mH407 security order moment hmoment hsecurity coefficient
open _root_.P2Mb748e9da renaming h428 → _p2mH428
end
open _root_.P2Mb748e9da renaming h428 → _p2mH428
open _root_.P2Mb748e9da renaming h429 → _p2mH429
end CurrentAFT.PublicWeightMoments
open _root_.P2Mb748e9da renaming h428 → _p2mH428
open _root_.P2Mb748e9da renaming h429 → _p2mH429
end
open _root_.P2Mb748e9da renaming h428 → _p2mH428
open _root_.P2Mb748e9da renaming h429 → _p2mH429
namespace CurrentAFT.ActualCompleteStability.fullResponse
end CurrentAFT.ActualCompleteStability.fullResponse
namespace CurrentAFT.ActualCompleteStability.solution
end CurrentAFT.ActualCompleteStability.solution
namespace CurrentAFT.ActualCompleteStability.threshold
end CurrentAFT.ActualCompleteStability.threshold
namespace CurrentAFT.PublicWeightMoments
end CurrentAFT.PublicWeightMoments
section
namespace CurrentAFT.ActualCalibrationMoments
open AFT ActualCompleteStability PublicOutputExperiment BackgroundRates ControlNorm
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  ordinaryPool ProposalPrimary.primaryLaw ActualControls.bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h131 (order moment : ℕ) : 0 ≤ _root_.CurrentAFT.ActualCalibrationMoments.momentConstant order moment :=
  mul_nonneg (mul_nonneg (by norm_num) (_p2mH406 order moment).le)
    (_p2mH155 order)
open _root_.P2Mb748e9da renaming h131 → _p2mH131
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h132 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    _root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security)
      (0, (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout).2) ≤
        2 * _root_.CurrentAFT.ActualCompleteStability.stabilityConstant order / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 := by
  have h := _p2mH147 security order horder hsecurity layout
  change _root_.CurrentAFT.ControlNorm.coefficientNorm _ _ order _ _
    ((_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout).1 - 1,
      (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout).2 - 0) ≤ _ at h
  rwa [_p2mH146, sub_self, sub_zero] at h
open _root_.P2Mb748e9da renaming h132 → _p2mH132
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h130 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (moment : ℕ) (hmoment : 1 ≤ moment) :
    (_root_.CurrentAFT.PublicOutputExperiment.reference security).expectation (fun controls =>
      |_root_.CurrentAFT.PublicOutputExperiment.actualWeight security order (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout) controls - 1| ^ (2 * moment)) ≤
      (_root_.CurrentAFT.ActualCalibrationMoments.momentConstant order moment / (_root_.CurrentAFT.Parameters.base security : ℝ)^6) ^ (2 * moment) := by
  have h := _p2mH428 security order moment hmoment
    (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout)
  rw [_p2mH146] at h
  apply h.trans
  have hnorm := _p2mH132 security order horder hsecurity layout
  have hnonneg : 0 ≤ _root_.CurrentAFT.ControlNorm.coefficientNorm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      order (_root_.CurrentAFT.BackgroundRates.primaryFactor security) (_root_.CurrentAFT.BackgroundRates.bodyFactor security) (0, (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout).2) :=
    _p2mH237 _ _ order _ _ (_root_.CurrentAFT.RaisingPatternBudget.primaryFactor_pos security).le
      (_root_.CurrentAFT.RaisingPatternBudget.bodyFactor_pos security).le _
  apply (pow_le_pow_left₀ (mul_nonneg (_p2mH406 order moment).le hnonneg)
    (mul_le_mul_of_nonneg_left hnorm (_p2mH406 order moment).le) (2 * moment)).trans_eq
  congr 1
  unfold _root_.CurrentAFT.ActualCalibrationMoments.momentConstant
  ring
open _root_.P2Mb748e9da renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h129 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (moment : ℕ) (hmoment : 1 ≤ moment) :
    (_root_.CurrentAFT.PublicOutputExperiment.reference security).expectation (fun controls =>
      |_root_.CurrentAFT.PublicOutputExperiment.actualWeight security order (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout) controls -
        _root_.CurrentAFT.clip (_root_.CurrentAFT.PublicOutputExperiment.actualWeight security order (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout) controls)|) ≤
      (_root_.CurrentAFT.ActualCalibrationMoments.momentConstant order moment / (_root_.CurrentAFT.Parameters.base security : ℝ)^6) ^ (2 * moment) := by
  exact (_p2mH459 (_root_.CurrentAFT.PublicOutputExperiment.reference security).weight
    (_root_.CurrentAFT.PublicOutputExperiment.actualWeight security order (_root_.CurrentAFT.ActualCompleteStability.coefficients security order horder hsecurity layout))
    (_root_.CurrentAFT.PublicOutputExperiment.reference security).nonneg moment hmoment).trans
      (_p2mH130 security order horder hsecurity layout moment hmoment)
open _root_.P2Mb748e9da renaming h129 → _p2mH129
end
open _root_.P2Mb748e9da renaming h129 → _p2mH129
open _root_.P2Mb748e9da renaming h130 → _p2mH130
open _root_.P2Mb748e9da renaming h131 → _p2mH131
open _root_.P2Mb748e9da renaming h132 → _p2mH132
end CurrentAFT.ActualCalibrationMoments
open _root_.P2Mb748e9da renaming h129 → _p2mH129
open _root_.P2Mb748e9da renaming h130 → _p2mH130
open _root_.P2Mb748e9da renaming h131 → _p2mH131
open _root_.P2Mb748e9da renaming h132 → _p2mH132
end
open _root_.P2Mb748e9da renaming h129 → _p2mH129
open _root_.P2Mb748e9da renaming h130 → _p2mH130
open _root_.P2Mb748e9da renaming h131 → _p2mH131
open _root_.P2Mb748e9da renaming h132 → _p2mH132
section
namespace CurrentAFT
open Filter
open scoped Topology
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h460 (order : ℕ) (constant : ℝ)
    (hconstant : 0 ≤ constant) :
    ∀ᶠ security : ℕ in atTop,
      constant * (_root_.CurrentAFT.Parameters.modulus security : ℝ) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^
          (-(((_root_.CurrentAFT.Parameters.calibrationOrder order : ℕ) + 1 : ℝ) / 4)) ≤
        _root_.CurrentAFT.inversePower security (order + 2) := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (131072 * constant)
  filter_upwards [eventually_ge_atTop threshold] with security hsecurity
  have hbase : (0 : ℝ) < _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast _root_.CurrentAFT.Parameters.base_pos security
  have hlarge : 131072 * constant ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) := by
    apply hthreshold.trans
    exact_mod_cast (show threshold ≤ _root_.CurrentAFT.Parameters.base security by
      dsimp [_root_.CurrentAFT.Parameters.base]
      omega)
  calc
    _ = constant * ((_root_.CurrentAFT.Parameters.modulus security : ℝ) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^
        (-(((_root_.CurrentAFT.Parameters.calibrationOrder order : ℕ) + 1 : ℝ) / 4))) := by ring
    _ ≤ constant * (131072 / (_root_.CurrentAFT.Parameters.base security : ℝ) ^ (order + 3)) :=
      mul_le_mul_of_nonneg_left (_p2mH402 security order) hconstant
    _ = (131072 * constant) / (_root_.CurrentAFT.Parameters.base security : ℝ) ^ (order + 3) := by ring
    _ ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) /
        (_root_.CurrentAFT.Parameters.base security : ℝ) ^ (order + 3) :=
      div_le_div_of_nonneg_right hlarge (pow_nonneg hbase.le _)
    _ = _root_.CurrentAFT.inversePower security (order + 2) := by
      have hexponent : order + 3 = (order + 2) + 1 := by omega
      rw [hexponent, pow_succ]
      unfold _root_.CurrentAFT.inversePower
      field_simp
open _root_.P2Mb748e9da renaming h460 → _p2mH460
end CurrentAFT
open _root_.P2Mb748e9da renaming h460 → _p2mH460
end
open _root_.P2Mb748e9da renaming h460 → _p2mH460
namespace CurrentAFT.ActualCalibrationMoments
end CurrentAFT.ActualCalibrationMoments
namespace CurrentAFT.inversePower
end CurrentAFT.inversePower
section
namespace CurrentAFT.ActualCalibrationClipping
open AFT ActualCompleteStability ActualCalibrationMoments PublicOutputExperiment
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h127 (security order : ℕ) (horder : 2 ≤ order) (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    0 ≤ _root_.CurrentAFT.ActualCalibrationClipping.loss security order horder hsecurity layout := by
  unfold _root_.CurrentAFT.ActualCalibrationClipping.loss _root_.AFT.FiniteDist.expectation
  exact Finset.sum_nonneg (fun controls _ => mul_nonneg ((_root_.CurrentAFT.PublicOutputExperiment.reference security).nonneg controls) (abs_nonneg _))
open _root_.P2Mb748e9da renaming h127 → _p2mH127
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h126 (order : ℕ) (horder : 2 ≤ order) (decayOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff, ∀ hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security,
      ∀ layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security,
      (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.ActualCalibrationClipping.loss security order horder hsecurity layout ≤
        _root_.CurrentAFT.inversePower security decayOrder := by
  let moment := decayOrder + 66
  obtain ⟨constantCutoff, hconstantCutoff⟩ := exists_nat_ge (_root_.CurrentAFT.ActualCalibrationMoments.momentConstant order moment)
  refine ⟨max constantCutoff 131072, ?_⟩
  intro security hlarge hsecurity layout
  have hb : (0 : ℝ) < _root_.CurrentAFT.Parameters.base security := _root_.CurrentAFT.FirstResponse.base_pos security
  have hb1 : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.base security from (by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega))
  have hconstant : _root_.CurrentAFT.ActualCalibrationMoments.momentConstant order moment ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) :=
    hconstantCutoff.trans (Nat.cast_le.mpr (by unfold _root_.CurrentAFT.Parameters.base; omega))
  have hlargeBase : (131072 : ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show 131072 ≤ _root_.CurrentAFT.Parameters.base security by unfold _root_.CurrentAFT.Parameters.base; omega)
  have hmodulus : (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≤ (_root_.CurrentAFT.Parameters.base security : ℝ)^65 := by
    have hbound : (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≤ 131072 * (_root_.CurrentAFT.Parameters.base security : ℝ)^64 := by
      exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_bounds security).2
    apply hbound.trans
    calc
      _ ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) * (_root_.CurrentAFT.Parameters.base security : ℝ)^64 :=
        mul_le_mul_of_nonneg_right hlargeBase (pow_nonneg hb.le _)
      _ = _ := by rw [pow_succ]; ring
  have hratio : _root_.CurrentAFT.ActualCalibrationMoments.momentConstant order moment / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 ≤
      1 / (_root_.CurrentAFT.Parameters.base security : ℝ)^5 := by
    calc
      _ ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) / (_root_.CurrentAFT.Parameters.base security : ℝ)^6 :=
        div_le_div_of_nonneg_right hconstant (pow_nonneg hb.le _)
      _ = _ := by rw [show (6 : ℕ) = 5 + 1 by omega, pow_succ]; field_simp
  have hloss := _p2mH129 security order horder hsecurity layout moment (by dsimp [moment]; omega)
  have hlossBound : _root_.CurrentAFT.ActualCalibrationClipping.loss security order horder hsecurity layout ≤
      (1 / (_root_.CurrentAFT.Parameters.base security : ℝ)^5)^(2 * moment) :=
    hloss.trans (pow_le_pow_left₀
      (div_nonneg (_p2mH131 order moment) (pow_nonneg hb.le _)) hratio _)
  calc
    _ ≤ (_root_.CurrentAFT.Parameters.base security : ℝ)^65 * (1 / (_root_.CurrentAFT.Parameters.base security : ℝ)^5)^(2 * moment) :=
      mul_le_mul hmodulus hlossBound (_p2mH127 security order horder hsecurity layout) (pow_nonneg hb.le _)
    _ = (_root_.CurrentAFT.Parameters.base security : ℝ)^65 / (_root_.CurrentAFT.Parameters.base security : ℝ)^(5 * (2 * moment)) := by
      rw [div_pow, one_pow, ← pow_mul]
      ring
    _ ≤ _root_.CurrentAFT.inversePower security decayOrder := by
      unfold _root_.CurrentAFT.inversePower
      apply (div_le_div_iff₀ (pow_pos hb _) (pow_pos hb _)).mpr
      rw [← pow_add, one_mul]
      exact pow_le_pow_right₀ hb1 (by dsimp [moment]; omega)
open _root_.P2Mb748e9da renaming h126 → _p2mH126
end
open _root_.P2Mb748e9da renaming h126 → _p2mH126
open _root_.P2Mb748e9da renaming h127 → _p2mH127
end CurrentAFT.ActualCalibrationClipping
open _root_.P2Mb748e9da renaming h126 → _p2mH126
open _root_.P2Mb748e9da renaming h127 → _p2mH127
end
open _root_.P2Mb748e9da renaming h126 → _p2mH126
open _root_.P2Mb748e9da renaming h127 → _p2mH127
namespace CurrentAFT.LocalRaisingBounds.positiveInverse
end CurrentAFT.LocalRaisingBounds.positiveInverse
namespace CurrentAFT.PairedOutputProduct
end CurrentAFT.PairedOutputProduct
namespace CurrentAFT.PairedOutputProduct.remaining
end CurrentAFT.PairedOutputProduct.remaining
namespace CurrentAFT.PairedOutputProduct.selectedBodies
end CurrentAFT.PairedOutputProduct.selectedBodies
namespace CurrentAFT.PairedOutputProduct.selectedPairs
end CurrentAFT.PairedOutputProduct.selectedPairs
namespace CurrentAFT.PairedRootInput
end CurrentAFT.PairedRootInput
namespace CurrentAFT.PairedRootInput.controlReference
end CurrentAFT.PairedRootInput.controlReference
namespace CurrentAFT.PairedRootInput.controlReference.match_1
end CurrentAFT.PairedRootInput.controlReference.match_1
namespace CurrentAFT.PairedRootInput.reference
end CurrentAFT.PairedRootInput.reference
namespace CurrentAFT.RootGroupedSourceFormula
end CurrentAFT.RootGroupedSourceFormula
namespace CurrentAFT.RootGroupedSourceFormula.completedTest
end CurrentAFT.RootGroupedSourceFormula.completedTest
namespace CurrentAFT.RootGroupedSourceFormula.controlWeightedTest
end CurrentAFT.RootGroupedSourceFormula.controlWeightedTest
namespace CurrentAFT.RootLocalDenominators
end CurrentAFT.RootLocalDenominators
namespace CurrentAFT.RootLocalDenominators.ordinaryPolynomial
end CurrentAFT.RootLocalDenominators.ordinaryPolynomial
namespace CurrentAFT.RootUnselectedBlockChannel
end CurrentAFT.RootUnselectedBlockChannel
namespace CurrentAFT.RootUnselectedBlockChannel.channel
end CurrentAFT.RootUnselectedBlockChannel.channel
namespace CurrentAFT.RootUnselectedBlockChannel.channel.match_1
end CurrentAFT.RootUnselectedBlockChannel.channel.match_1
namespace CurrentAFT.RootUnselectedBlockChannel.positivePolynomial
end CurrentAFT.RootUnselectedBlockChannel.positivePolynomial
section
namespace CurrentAFT.TypedTaggedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection TaggedOutputFock
  JointTaggedPhysicalFock PairedOutputPlacement LocalReferenceEnergy
  RootBackgroundPolynomial BackgroundPolynomialEvaluation RootLocalDenominators
  CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.classicalSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.actualGroupDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
section Generic
variable {Index Color : Type*} [Fintype Index] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h453 (slots : Index → Type*) [∀ index, Fintype (slots index)]
    (reference : Color → ℝ) (mass : (index : Index) → (slots index → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference
      (fun word : Sigma slots → Color => ∏ index, mass index (fun slot => word ⟨index, slot⟩)) =
      ∏ index, _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference (mass index) := by
  have hequiv := (Equiv.piCurry (fun index (_ : slots index) => Color)).sum_comp
    (fun word => ∏ index, MvPolynomial.C (mass index (word index)) *
      ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index slot))
  unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eq_C_mul,
    map_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma slots → Color,
        ∏ index, (MvPolynomial.C (mass index (fun slot => word ⟨index, slot⟩)) *
          ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word ⟨index, slot⟩)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → slots index → Color,
        ∏ index, (MvPolynomial.C (mass index (word index)) *
          ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index slot)) := hequiv
    _ = _ := (Fintype.prod_sum (fun index (word : slots index → Color) =>
      MvPolynomial.C (mass index word) * ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word slot))).symm
open _root_.P2Mb748e9da renaming h453 → _p2mH453
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h454 {Left Right : Type*} [Fintype Left] [Fintype Right]
    (reference : Color → ℝ) (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference
      (fun word : Left ⊕ Right → Color => first (word ∘ Sum.inl) * second (word ∘ Sum.inr)) =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference first * _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference second := by
  unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eq_C_mul]
  rw [← (Equiv.sumArrowEquivProdArrow Left Right Color).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk,
    Fintype.prod_sum_type, Function.comp_def, Sum.elim_inl, Sum.elim_inr, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro firstWord _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secondWord _
  ring
open _root_.P2Mb748e9da renaming h454 → _p2mH454
end Generic
open _root_.P2Mb748e9da renaming h453 → _p2mH453
open _root_.P2Mb748e9da renaming h454 → _p2mH454
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h452 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedTaggedPhysical.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue roots kernel =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.TypedTaggedPhysical.selectedMass selection roots kernel) *
        ∏ index : selection.kept, _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue roots index.val) := by
  unfold _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial _root_.CurrentAFT.TypedTaggedPhysical.conditionalMass _root_.AFT.BlockProducts.taggedBlockMass
  rw [_p2mH454]
  congr 1
  unfold _root_.AFT.BlockProducts.blockMass
  rw [_p2mH453]
  apply Finset.prod_congr rfl
  intro index _
  exact _root_.CurrentAFT.RootLocalDenominators.generating_eq_block security _
open _root_.P2Mb748e9da renaming h452 → _p2mH452
end
open _root_.P2Mb748e9da renaming h452 → _p2mH452
open _root_.P2Mb748e9da renaming h453 → _p2mH453
open _root_.P2Mb748e9da renaming h454 → _p2mH454
end CurrentAFT.TypedTaggedPhysical
open _root_.P2Mb748e9da renaming h452 → _p2mH452
open _root_.P2Mb748e9da renaming h453 → _p2mH453
open _root_.P2Mb748e9da renaming h454 → _p2mH454
end
open _root_.P2Mb748e9da renaming h452 → _p2mH452
open _root_.P2Mb748e9da renaming h453 → _p2mH453
open _root_.P2Mb748e9da renaming h454 → _p2mH454
namespace CurrentAFT.ActualLayouts
end CurrentAFT.ActualLayouts
namespace CurrentAFT.LocalRaisingLinear
end CurrentAFT.LocalRaisingLinear
namespace CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear
end CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear
namespace CurrentAFT.RootSelectedZeroTag
end CurrentAFT.RootSelectedZeroTag
namespace CurrentAFT.TypedTaggedPhysical
end CurrentAFT.TypedTaggedPhysical
section
namespace CurrentAFT.RootConditionalResidues
open AFT ActualBlockFock TaggedSelection JointTaggedPhysicalFock TaggedPhysicalFock
  OrdinaryPhysicalFock TypedTaggedPhysical RootBackgroundPolynomial ActualLayouts
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootConditionalResidues.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalResidues.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalResidues.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h431 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))
    (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue
      (fun block => _root_.CurrentAFT.ActualBlockMean.rootAt security permutation latent (_root_.CurrentAFT.ActualLayouts.blockLayout layout block)) kernel =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.TaggedOutputFock.conditionalMass security r s selection layout queue permutation latent kernel) := rfl
open _root_.P2Mb748e9da renaming h431 → _p2mH431
end
open _root_.P2Mb748e9da renaming h431 → _p2mH431
end CurrentAFT.RootConditionalResidues
open _root_.P2Mb748e9da renaming h431 → _p2mH431
end
open _root_.P2Mb748e9da renaming h431 → _p2mH431
namespace CurrentAFT.ActualRootDefectPhysical
end CurrentAFT.ActualRootDefectPhysical
namespace CurrentAFT.JointTaggedPhysicalFock
end CurrentAFT.JointTaggedPhysicalFock
namespace CurrentAFT.JointTaggedPhysicalFock.ordinaryChannel
end CurrentAFT.JointTaggedPhysicalFock.ordinaryChannel
namespace CurrentAFT.JointTaggedPhysicalFock.primaryChannel
end CurrentAFT.JointTaggedPhysicalFock.primaryChannel
namespace CurrentAFT.JointTaggedPhysicalFock.roleChannel
end CurrentAFT.JointTaggedPhysicalFock.roleChannel
namespace CurrentAFT.JointTaggedPhysicalFock.roleSlots
end CurrentAFT.JointTaggedPhysicalFock.roleSlots
namespace CurrentAFT.JointTaggedPhysicalFock.roleSlots.match_1
end CurrentAFT.JointTaggedPhysicalFock.roleSlots.match_1
namespace CurrentAFT.OrdinaryPhysicalFock
end CurrentAFT.OrdinaryPhysicalFock
namespace CurrentAFT.OrdinaryPhysicalFock.bodyChannel
end CurrentAFT.OrdinaryPhysicalFock.bodyChannel
namespace CurrentAFT.RootConditionalResidues
end CurrentAFT.RootConditionalResidues
namespace CurrentAFT.TypedTaggedPhysical.blockLaw
end CurrentAFT.TypedTaggedPhysical.blockLaw
section
namespace CurrentAFT.RootActualOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts ActualRootDefectPhysical
  LocalReferenceEnergy RootBackgroundPolynomial ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootActualOutputPolynomial.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootActualOutputPolynomial.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootActualOutputPolynomial.vertexDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
section Generic
variable {Source Target Value : Type*} [Fintype Source] [Fintype Target]
  [AddCommGroup Value] [Module ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h430 {Output : Type*} [Fintype Output]
    (channel : (Output → ℝ) →ₗ[ℝ] Value) (law : _root_.AFT.FiniteDist Source) (mass : Source → Output → ℝ) :
    channel (fun output => law.expectation (fun source => mass source output)) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear law (fun source => channel (mass source)) := by
  have hmass : (fun output => law.expectation (fun source => mass source output)) =
      ∑ source, law.weight source • mass source := by
    funext output
    simp only [_root_.AFT.FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, _root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
open _root_.P2Mb748e9da renaming h430 → _p2mH430
end Generic
open _root_.P2Mb748e9da renaming h430 → _p2mH430
end
open _root_.P2Mb748e9da renaming h430 → _p2mH430
end CurrentAFT.RootActualOutputPolynomial
open _root_.P2Mb748e9da renaming h430 → _p2mH430
end
open _root_.P2Mb748e9da renaming h430 → _p2mH430
section
namespace CurrentAFT.PointPolynomial
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
  CanonicalReconstruction LeadingEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PointPolynomial.classicalFinDecidableEq
variable {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h424 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s : ℕ} (sourcePrimary : Fin r → Primary) (sourceBody : Fin s → Body) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForm bodyForm (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody) =
      (∏ index, _root_.CurrentAFT.PointPolynomial.atomForm primary primaryForm (sourcePrimary index)) *
        ∏ index, _root_.CurrentAFT.PointPolynomial.atomForm body bodyForm (sourceBody index) := by
  unfold _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial
  calc
    _ = ∑ colors : Fin r → Primary, ∑ centers : Fin s → Body,
        (∏ index, MvPolynomial.C (primary.weight (colors index) *
          _root_.AFT.Hoeffding.centeredAtom primary (sourcePrimary index) (colors index)) * primaryForm (colors index)) *
        (∏ index, MvPolynomial.C (body.weight (centers index) *
          _root_.AFT.Hoeffding.centeredAtom body (sourceBody index) (centers index)) * bodyForm (centers index)) := by
      apply Finset.sum_congr rfl
      intro colors _
      apply Finset.sum_congr rfl
      intro centers _
      simp only [_root_.CurrentAFT.CanonicalReconstruction.pointTensor, map_mul, map_prod, Finset.prod_mul_distrib]
      ring
    _ = (∑ colors : Fin r → Primary,
        ∏ index, MvPolynomial.C (primary.weight (colors index) *
          _root_.AFT.Hoeffding.centeredAtom primary (sourcePrimary index) (colors index)) * primaryForm (colors index)) *
        (∑ centers : Fin s → Body,
        ∏ index, MvPolynomial.C (body.weight (centers index) *
          _root_.AFT.Hoeffding.centeredAtom body (sourceBody index) (centers index)) * bodyForm (centers index)) := by
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ = _ := by
      apply congrArg₂ (· * ·)
      · exact (Fintype.prod_sum (fun (index : Fin r) (output : Primary) =>
          MvPolynomial.C (primary.weight output * _root_.AFT.Hoeffding.centeredAtom primary (sourcePrimary index) output) *
            primaryForm output)).symm
      · exact (Fintype.prod_sum (fun (index : Fin s) (output : Body) =>
          MvPolynomial.C (body.weight output * _root_.AFT.Hoeffding.centeredAtom body (sourceBody index) output) *
            bodyForm output)).symm
open _root_.P2Mb748e9da renaming h424 → _p2mH424
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h423 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (hprimary : ∀ color, 0 < primary.weight color) (hbody : ∀ color, 0 < body.weight color)
    (primaryForm : Primary → MvPolynomial Variable ℝ) (bodyForm : Body → MvPolynomial Variable ℝ)
    {r s : ℕ} (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body r s) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForm bodyForm kernel.val =
      ∑ sourcePrimary, ∑ sourceBody,
        ((∏ index, primary.weight (sourcePrimary index)) *
          (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          ((∏ index, _root_.CurrentAFT.PointPolynomial.atomForm primary primaryForm (sourcePrimary index)) *
            ∏ index, _root_.CurrentAFT.PointPolynomial.atomForm body bodyForm (sourceBody index)) := by
  have hraw : (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          _root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody) = kernel.val := by
    funext colors centers
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact _p2mH219 primary body hprimary hbody kernel colors centers
  have h := congrArg (_root_.CurrentAFT.LeadingEvaluation.kernelLinear primary body primaryForm bodyForm) hraw
  simp only [map_sum, map_smul] at h
  change (∑ sourcePrimary, ∑ sourceBody,
      ((∏ index, primary.weight (sourcePrimary index)) *
        (∏ index, body.weight (sourceBody index)) * kernel.val sourcePrimary sourceBody) •
          _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForm bodyForm (_root_.CurrentAFT.CanonicalReconstruction.pointTensor primary body sourcePrimary sourceBody)) =
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForm bodyForm kernel.val at h
  simp only [_p2mH424] at h
  exact h.symm
open _root_.P2Mb748e9da renaming h423 → _p2mH423
end
open _root_.P2Mb748e9da renaming h423 → _p2mH423
open _root_.P2Mb748e9da renaming h424 → _p2mH424
end CurrentAFT.PointPolynomial
open _root_.P2Mb748e9da renaming h423 → _p2mH423
open _root_.P2Mb748e9da renaming h424 → _p2mH424
end
open _root_.P2Mb748e9da renaming h423 → _p2mH423
open _root_.P2Mb748e9da renaming h424 → _p2mH424
namespace CurrentAFT.BodyChannelEvaluation
end CurrentAFT.BodyChannelEvaluation
namespace CurrentAFT.BodyChannelEvaluation.bodyDensityChannel
end CurrentAFT.BodyChannelEvaluation.bodyDensityChannel
namespace CurrentAFT.BodyChannelEvaluation.bodyTensorMass
end CurrentAFT.BodyChannelEvaluation.bodyTensorMass
namespace CurrentAFT.BodyChannelEvaluation.safeMass
end CurrentAFT.BodyChannelEvaluation.safeMass
namespace CurrentAFT.CompleteRaising
end CurrentAFT.CompleteRaising
namespace CurrentAFT.CompleteRaising.homogeneousCorrectionLinear
end CurrentAFT.CompleteRaising.homogeneousCorrectionLinear
namespace CurrentAFT.CompleteRaising.selectedCorrection
end CurrentAFT.CompleteRaising.selectedCorrection
namespace CurrentAFT.CompleteRaising.selectedCorrectionLinear
end CurrentAFT.CompleteRaising.selectedCorrectionLinear
namespace CurrentAFT.CompleteRaising.selectedPointProduct
end CurrentAFT.CompleteRaising.selectedPointProduct
namespace CurrentAFT.CompleteRaising.slotLeading
end CurrentAFT.CompleteRaising.slotLeading
namespace CurrentAFT.CompleteRaising.slotRaised
end CurrentAFT.CompleteRaising.slotRaised
namespace CurrentAFT.PointPolynomial
end CurrentAFT.PointPolynomial
section
namespace CurrentAFT.CompleteRaisingEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalRaisingFirst LocalRaisingLinear
  BackgroundFamilies GlobalRaising CompleteRaising LeadingEvaluation PointPolynomial
  LocalCoefficientEvaluation BackgroundEvaluation PrimaryMassFamilies
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CompleteRaisingEvaluation.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.CompleteRaisingEvaluation.classicalSumDecidableEq
attribute [local irreducible] Parameters.base primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h226 {Color Variable : Type*} [Fintype Color]
    (law : _root_.AFT.FiniteDist Color) (forms : Color → MvPolynomial Variable ℝ) (source : Color) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial law forms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_root_.AFT.Hoeffding.centeredAtom law source)) =
      _root_.CurrentAFT.PointPolynomial.atomForm law forms source := by
  unfold _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial _root_.CurrentAFT.PointPolynomial.atomForm
  simp only [_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile, Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word : Fin 1 → Color =>
      MvPolynomial.C (law.weight (word 0) * _root_.AFT.Hoeffding.centeredAtom law source (word 0)) * forms (word 0))).symm
open _root_.P2Mb748e9da renaming h226 → _p2mH226
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h233 (security order : ℕ) (horder : 1 ≤ order)
    (source : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.GlobalRaising.primaryPoint security order horder source) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.PointPolynomial.atomForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) source) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyHom _ _ _ _ (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security) _ (_root_.CurrentAFT.BackgroundFamilies.primaryFamily _ _ _ _ _ _) = _
  rw [_p2mH214]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order
    (_root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial _ _ 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_root_.AFT.Hoeffding.centeredAtom _ source))) = _
  rw [_p2mH226]
open _root_.P2Mb748e9da renaming h233 → _p2mH233
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h225 (security order : ℕ) (horder : 1 ≤ order)
    (source : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.GlobalRaising.bodyPoint security order horder source) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.PointPolynomial.atomForm (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) source) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyHom _ _ _ _ (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security) _ (_root_.CurrentAFT.BackgroundFamilies.bodyFamily _ _ _ _ _ _) = _
  rw [_p2mH216, _p2mH226]
open _root_.P2Mb748e9da renaming h225 → _p2mH225
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h228 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.CompleteRaising.selectedPointProduct security order horder ∅ colors centers) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        ((∏ index, _root_.CurrentAFT.PointPolynomial.atomForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (colors index)) *
          ∏ index, _root_.CurrentAFT.PointPolynomial.atomForm (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) (centers index)) := by
  simp [_root_.CurrentAFT.CompleteRaising.selectedPointProduct,
    _root_.CurrentAFT.CompleteRaising.slotLeading, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, map_mul, map_prod,
    _p2mH233, _p2mH225]
open _root_.P2Mb748e9da renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h227 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder ∅ kernel) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
        (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) kernel.val) := by
  rw [_p2mH423 _ _ (_root_.CurrentAFT.ActualControls.primaryReference_positive security) (_root_.CurrentAFT.ActualControls.bodyReference_positive security)]
  simp only [_root_.CurrentAFT.CompleteRaising.selectedCorrection, map_sum, map_smul, _p2mH228]
open _root_.P2Mb748e9da renaming h227 → _p2mH227
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h232 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security)
    (slot : Fin r ⊕ Fin s) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedSlot security order horder colors centers slot =
      _root_.CurrentAFT.CompleteRaising.slotLeading security order horder colors centers slot + _root_.CurrentAFT.CompleteRaising.slotRaised security order horder colors centers slot := by
  cases slot with
  | inl index =>
    change _root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order _ =
      _root_.CurrentAFT.GlobalRaising.primaryPoint security order horder _ + _root_.CurrentAFT.GlobalRaising.raisedPoint security order horder _
    change _ = _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder _ +
      (_root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order _ - _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder _)
    abel
  | inr index =>
    exact _p2mH397 security order horder _ _
open _root_.P2Mb748e9da renaming h232 → _p2mH232
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h234 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (colors : Fin r → _root_.CurrentAFT.ActualControls.Palette security) (centers : Fin s → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (∏ slot, _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedSlot security order horder colors centers slot) =
      ∑ selected, _root_.CurrentAFT.CompleteRaising.selectedPointProduct security order horder selected colors centers := by
  simp_rw [_p2mH232, add_comm (_root_.CurrentAFT.CompleteRaising.slotLeading security order horder colors centers _)]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro selected _
  simp [_root_.CurrentAFT.CompleteRaising.selectedPointProduct, Finset.prod_ite, ← Finset.mem_compl]
open _root_.P2Mb748e9da renaming h234 → _p2mH234
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h230 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel =
      ∑ selected, _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder selected kernel := by
  unfold _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint _root_.CurrentAFT.CompleteRaising.selectedCorrection
  simp_rw [_p2mH234, Finset.smul_sum]
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2
    ext colors
    rw [Finset.sum_comm]
open _root_.P2Mb748e9da renaming h230 → _p2mH230
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h229 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel =
      _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder ∅ kernel +
        _root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder r s kernel := by
  rw [_p2mH230]
  simp only [_root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear, LinearMap.sum_apply]
  change _ = _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder ∅ kernel +
    ∑ selected ∈ (Finset.univ : Finset (Finset (Fin r ⊕ Fin s))).erase ∅,
      _root_.CurrentAFT.CompleteRaising.selectedCorrection security order horder selected kernel
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ ∅)).symm
open _root_.P2Mb748e9da renaming h229 → _p2mH229
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h231 (security order : ℕ) (horder : 1 ≤ order)
    (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedResponse security order horder family) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (family + _root_.CurrentAFT.CompleteRaising.raisingLinear security order horder family) := by
  unfold _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedResponse
  simp_rw [map_sum, _p2mH229, map_add, _p2mH227]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · exact (_p2mH381 _ _ _ _ _ family).symm
  · change _ = _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (∑ arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order,
        _root_.CurrentAFT.CompleteRaising.homogeneousCorrectionLinear security order horder
          arity.val.1.val arity.val.2.val (family arity))
    rw [map_sum]
open _root_.P2Mb748e9da renaming h231 → _p2mH231
end
open _root_.P2Mb748e9da renaming h225 → _p2mH225
open _root_.P2Mb748e9da renaming h226 → _p2mH226
open _root_.P2Mb748e9da renaming h227 → _p2mH227
open _root_.P2Mb748e9da renaming h228 → _p2mH228
open _root_.P2Mb748e9da renaming h229 → _p2mH229
open _root_.P2Mb748e9da renaming h230 → _p2mH230
open _root_.P2Mb748e9da renaming h231 → _p2mH231
open _root_.P2Mb748e9da renaming h232 → _p2mH232
open _root_.P2Mb748e9da renaming h233 → _p2mH233
open _root_.P2Mb748e9da renaming h234 → _p2mH234
end CurrentAFT.CompleteRaisingEvaluation
open _root_.P2Mb748e9da renaming h225 → _p2mH225
open _root_.P2Mb748e9da renaming h226 → _p2mH226
open _root_.P2Mb748e9da renaming h227 → _p2mH227
open _root_.P2Mb748e9da renaming h228 → _p2mH228
open _root_.P2Mb748e9da renaming h229 → _p2mH229
open _root_.P2Mb748e9da renaming h230 → _p2mH230
open _root_.P2Mb748e9da renaming h231 → _p2mH231
open _root_.P2Mb748e9da renaming h232 → _p2mH232
open _root_.P2Mb748e9da renaming h233 → _p2mH233
open _root_.P2Mb748e9da renaming h234 → _p2mH234
end
open _root_.P2Mb748e9da renaming h225 → _p2mH225
open _root_.P2Mb748e9da renaming h226 → _p2mH226
open _root_.P2Mb748e9da renaming h227 → _p2mH227
open _root_.P2Mb748e9da renaming h228 → _p2mH228
open _root_.P2Mb748e9da renaming h229 → _p2mH229
open _root_.P2Mb748e9da renaming h230 → _p2mH230
open _root_.P2Mb748e9da renaming h231 → _p2mH231
open _root_.P2Mb748e9da renaming h232 → _p2mH232
open _root_.P2Mb748e9da renaming h233 → _p2mH233
open _root_.P2Mb748e9da renaming h234 → _p2mH234
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
namespace CurrentAFT.ActualWeightedFourier
end CurrentAFT.ActualWeightedFourier
namespace CurrentAFT.ActualWeightedFourier.signedOutputMass
end CurrentAFT.ActualWeightedFourier.signedOutputMass
namespace CurrentAFT.CoefficientOutputFock
end CurrentAFT.CoefficientOutputFock
namespace CurrentAFT.CoefficientOutputFock.familyMass
end CurrentAFT.CoefficientOutputFock.familyMass
namespace CurrentAFT.CycleRootExpansion
end CurrentAFT.CycleRootExpansion
namespace CurrentAFT.CycleRootExpansion.componentResponse
end CurrentAFT.CycleRootExpansion.componentResponse
namespace CurrentAFT.CycleRootExpansion.expectationLinear
end CurrentAFT.CycleRootExpansion.expectationLinear
namespace CurrentAFT.CycleRootExpansion.rootLaw
end CurrentAFT.CycleRootExpansion.rootLaw
section
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial HistogramNormalization GradedControlAlgebra
  ControlCoordinates CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h415 {Slot OtherSlot Color : Type*}
    [Fintype Slot] [Fintype OtherSlot] [Fintype Color]
    (reference : Color → ℝ) (equiv : Slot ≃ OtherSlot) (mass : (Slot → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference (_root_.AFT.HistogramNormalization.renamedMass equiv mass) =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference mass := by
  unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← (_root_.AFT.HistogramNormalization.renameWord equiv).sum_comp]
  apply Finset.sum_congr rfl
  intro word _
  have hword : _root_.AFT.HistogramNormalization.renamedMass equiv mass (_root_.AFT.HistogramNormalization.renameWord equiv word) = mass word := by
    simp only [_root_.AFT.HistogramNormalization.renamedMass, _root_.AFT.HistogramNormalization.renameWord, Equiv.coe_fn_mk, Function.comp_def, Equiv.symm_apply_apply]
  rw [hword]
  congr 1
  exact Equiv.prod_comp equiv.symm (fun slot => _root_.AFT.RepresentedPolynomial.centeredFactor reference (word slot))
open _root_.P2Mb748e9da renaming h415 → _p2mH415
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h413 {Source Slot Color : Type*}
    [Fintype Source] [Fintype Slot] [Fintype Color]
    (reference : Color → ℝ) (law : _root_.AFT.FiniteDist Source) (mass : Source → (Slot → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference (fun word => law.expectation (fun source => mass source word)) =
      ∑ source, law.weight source • _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference (mass source) := by
  have hmass : (fun word => law.expectation (fun source => mass source word)) =
      ∑ source, law.weight source • mass source := by
    funext word
    simp only [_root_.AFT.FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul]
open _root_.P2Mb748e9da renaming h413 → _p2mH413
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h412 {First Second Value : Type*} [Fintype First] [Fintype Second]
    [AddCommGroup Value] [Module ℝ Value] (first : _root_.AFT.FiniteDist First) (second : _root_.AFT.FiniteDist Second)
    (test : First × Second → Value) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (first.prod second) test =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear first (fun left => _root_.CurrentAFT.CycleRootExpansion.expectationLinear second (fun right => test (left, right))) := by
  simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, Fintype.sum_prod_type,
    _root_.AFT.FiniteDist.prod_weight, Finset.smul_sum, smul_smul]
open _root_.P2Mb748e9da renaming h412 → _p2mH412
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h411 (order : ℕ) : Function.Bijective (_root_.CurrentAFT.PhysicalPolynomialAverages.arityOptionMap order) := by
  constructor
  · intro left right hequal
    cases left with
    | none =>
      cases right with
      | none => rfl
      | some arity =>
        have h := congrArg (fun a : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change 0 + 0 = arity.val.1.val + arity.val.2.val at h
        omega
    | some arity =>
      cases right with
      | none =>
        have h := congrArg (fun a : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change arity.val.1.val + arity.val.2.val = 0 + 0 at h
        omega
      | some other =>
        apply congrArg some
        apply Subtype.ext
        exact congrArg (fun a : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => a.val) hequal
  · intro arity
    by_cases hzero : arity.val.1.val + arity.val.2.val = 0
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · change 0 = arity.val.1.val
        omega
      · change 0 = arity.val.2.val
        omega
    · exact ⟨some ⟨arity.val, ⟨by omega, arity.property⟩⟩, rfl⟩
open _root_.P2Mb748e9da renaming h411 → _p2mH411
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h416 {Value : Type*} [AddCommMonoid Value] (order : ℕ)
    (test : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order → Value) :
    (∑ arity, test arity) = test (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) +
      ∑ arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order, test (_root_.CurrentAFT.GradedControlAlgebra.positiveArity order arity) := by
  rw [← (Equiv.ofBijective (_root_.CurrentAFT.PhysicalPolynomialAverages.arityOptionMap order) (_p2mH411 order)).sum_comp]
  exact Fintype.sum_option _
open _root_.P2Mb748e9da renaming h416 → _p2mH416
end
open _root_.P2Mb748e9da renaming h411 → _p2mH411
open _root_.P2Mb748e9da renaming h412 → _p2mH412
open _root_.P2Mb748e9da renaming h413 → _p2mH413
open _root_.P2Mb748e9da renaming h415 → _p2mH415
open _root_.P2Mb748e9da renaming h416 → _p2mH416
end CurrentAFT.PhysicalPolynomialAverages
open _root_.P2Mb748e9da renaming h411 → _p2mH411
open _root_.P2Mb748e9da renaming h412 → _p2mH412
open _root_.P2Mb748e9da renaming h413 → _p2mH413
open _root_.P2Mb748e9da renaming h415 → _p2mH415
open _root_.P2Mb748e9da renaming h416 → _p2mH416
end
open _root_.P2Mb748e9da renaming h411 → _p2mH411
open _root_.P2Mb748e9da renaming h412 → _p2mH412
open _root_.P2Mb748e9da renaming h413 → _p2mH413
open _root_.P2Mb748e9da renaming h415 → _p2mH415
open _root_.P2Mb748e9da renaming h416 → _p2mH416
namespace CurrentAFT.ActualFockBound
end CurrentAFT.ActualFockBound
namespace CurrentAFT.ActualFockBound.latentLaw
end CurrentAFT.ActualFockBound.latentLaw
namespace CurrentAFT.CompleteRaisingEvaluation
end CurrentAFT.CompleteRaisingEvaluation
namespace CurrentAFT.CompleteRaisingEvaluation.normalizedSlot
end CurrentAFT.CompleteRaisingEvaluation.normalizedSlot
namespace CurrentAFT.OrdinaryRaising.normalizedFamily
end CurrentAFT.OrdinaryRaising.normalizedFamily
namespace CurrentAFT.PhysicalPolynomialAverages
end CurrentAFT.PhysicalPolynomialAverages
namespace CurrentAFT.PhysicalPolynomialAverages.arityOptionMap
end CurrentAFT.PhysicalPolynomialAverages.arityOptionMap
namespace CurrentAFT.RaisingPatternBudget
end CurrentAFT.RaisingPatternBudget
namespace CurrentAFT.RaisingPatternBudget.roleReference
end CurrentAFT.RaisingPatternBudget.roleReference
namespace CurrentAFT.RaisingPatternBudget.roleReference.match_1
end CurrentAFT.RaisingPatternBudget.roleReference.match_1
namespace CurrentAFT.RootActualOutputPolynomial
end CurrentAFT.RootActualOutputPolynomial
namespace CurrentAFT.RootIndependentSelectedPhysical
end CurrentAFT.RootIndependentSelectedPhysical
namespace CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
end CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
namespace CurrentAFT.RootIndependentSelectedPhysical.meanLinear
end CurrentAFT.RootIndependentSelectedPhysical.meanLinear
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
end CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedActive.match_1
end CurrentAFT.RootIndependentSelectedPhysical.normalizedActive.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint
end CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint.match_1
end CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedRole
end CurrentAFT.RootIndependentSelectedPhysical.normalizedRole
namespace CurrentAFT.TaggedOutputFock
end CurrentAFT.TaggedOutputFock
namespace CurrentAFT.TaggedOutputFock.outputMass
end CurrentAFT.TaggedOutputFock.outputMass
section
namespace CurrentAFT.ActualCompletePhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.finDecEq
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.sumDecEq
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.vertexDecEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.selected_physical_legacy {security r s : ℕ} (order : ℕ) (horder : 2 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order
      (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.TaggedOutputFock.outputMass security r s selection layout queue permutation kernel.val))) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
          (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order (by omega) kernel +
            _root_.CurrentAFT.ActualRootDefect.selectedDefect order (by omega) queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel)) := by
  exact _root_.CurrentAFT.ActualCompletePhysical.selected_physical_explicit_order order horder (by omega) queue selection layout kernel

set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h143 (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security) (queue : ℤ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.ActualCompletePhysical.selectedGenerating security order hroom queue layout arity kernel) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
          (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order (by omega) kernel +
            _root_.CurrentAFT.ActualRootFamily.selectedAverage security order (by omega) hroom queue (_root_.CurrentAFT.ActualLayouts.blockLayout layout) arity kernel)) := by
  simp only [_root_.CurrentAFT.ActualCompletePhysical.selectedGenerating, map_sum, map_smul]
  simp_rw [_root_.P2Mb748e9da.selected_physical_legacy order horder]
  calc
    _ = _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (∑ choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security arity.val.1.val arity.val.2.val,
          (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security arity.val.1.val arity.val.2.val
            (_root_.CurrentAFT.ActualRootFamily.primary_room security order hroom arity)
            (_root_.CurrentAFT.ActualRootFamily.body_room security order hroom arity)).weight choice •
          (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
            (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order (by omega) kernel +
              _root_.CurrentAFT.ActualRootDefect.selectedDefect order (by omega) queue
                (_root_.CurrentAFT.UniformTaggedOutput.selection security arity.val.1.val arity.val.2.val choice) (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel))) := by
      simp only [map_sum, map_smul]
    _ = _ := by
      congr 1
      simp only [mul_add, smul_add, Finset.sum_add_distrib, _root_.CurrentAFT.ActualRootFamily.selectedAverage_apply]
      rw [← Finset.sum_smul, _root_.AFT.FiniteDist.sum_one, one_smul]
      simp only [Finset.mul_sum, mul_smul_comm]
open _root_.P2Mb748e9da renaming h143 → _p2mH143
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h140 (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security) (queue : ℤ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.ActualCompletePhysical.familyGenerating security order hroom queue layout family) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
          (family + _root_.CurrentAFT.CompleteRaising.raisingLinear security order (by omega) family +
            _root_.CurrentAFT.ActualRootFamily.rootLinear security order (by omega) hroom queue (_root_.CurrentAFT.ActualLayouts.blockLayout layout) family)) := by
  simp only [_root_.CurrentAFT.ActualCompletePhysical.familyGenerating, map_sum]
  simp_rw [_p2mH143 security order horder]
  rw [← map_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [_root_.CurrentAFT.ActualRootFamily.rootLinear_apply security order (by omega) hroom queue (_root_.CurrentAFT.ActualLayouts.blockLayout layout) family]
  have hnormalized := _p2mH231 security order (by omega) family
  unfold _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedResponse at hnormalized
  simp only [map_mul, map_add]
  rw [hnormalized, map_add]
open _root_.P2Mb748e9da renaming h140 → _p2mH140
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h138 (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order
      (∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
        _root_.CurrentAFT.ActualCompletePhysical.familyGenerating security order hroom scalar.val layout family) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualCompleteStability.fullResponse security order horder hroom (_root_.CurrentAFT.ActualLayouts.blockLayout layout) family) := by
  simp only [map_sum, map_smul]
  simp_rw [_p2mH140 security order horder]
  calc
    _ = _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
          (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder scalar.val *
            (family + _root_.CurrentAFT.CompleteRaising.raisingLinear security order (by omega) family +
              _root_.CurrentAFT.ActualRootFamily.rootLinear security order (by omega) hroom scalar.val (_root_.CurrentAFT.ActualLayouts.blockLayout layout) family))) := by
      simp only [map_sum, map_smul]
    _ = _ := by
      congr 1
      simp only [_root_.CurrentAFT.ActualCompleteStability.fullResponse, LinearMap.add_apply,
        _root_.CurrentAFT.ActualCompleteStability.independentResponse, _root_.CurrentAFT.ActualCompleteStability.rootCorrection,
        LinearMap.coe_mk, AddHom.coe_mk, _root_.CurrentAFT.ActualBackground.background,
        mul_add, smul_add, Finset.sum_add_distrib, Finset.sum_mul, smul_mul_assoc]
open _root_.P2Mb748e9da renaming h138 → _p2mH138
end
open _root_.P2Mb748e9da renaming h138 → _p2mH138
open _root_.P2Mb748e9da renaming h140 → _p2mH140
open _root_.P2Mb748e9da renaming h143 → _p2mH143
end CurrentAFT.ActualCompletePhysical
open _root_.P2Mb748e9da renaming h138 → _p2mH138
open _root_.P2Mb748e9da renaming h140 → _p2mH140
open _root_.P2Mb748e9da renaming h143 → _p2mH143
end
open _root_.P2Mb748e9da renaming h138 → _p2mH138
open _root_.P2Mb748e9da renaming h140 → _p2mH140
open _root_.P2Mb748e9da renaming h143 → _p2mH143
section
namespace CurrentAFT.ActualFamilyPolynomial
open AFT AFT.RepresentedPolynomial PhysicalPolynomialAverages CoefficientOutputFock
  UniformTaggedOutput ActualFockBound ConditionalHistogramMean ActualCycleMeanMGF
  LocalReferenceEnergy CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualFamilyPolynomial.finDecEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h156 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (queue : ℤ) (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.CoefficientOutputFock.baselineMass security layout queue permutation) =
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight :=
  _p2mH415 _ _ _
open _root_.P2Mb748e9da renaming h156 → _p2mH156
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h158 (security r s : ℕ) (hprimary : r ≤ _root_.CurrentAFT.Parameters.legCount security)
    (hbody : s ≤ _root_.CurrentAFT.BackgroundRates.ordinaryPool security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel
      (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.UniformTaggedOutput.uMass security r s hprimary hbody layout queue permutation kernel) =
      ∑ choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security r s, (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security r s hprimary hbody).weight choice •
        _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.TaggedOutputFock.outputMass security r s (_root_.CurrentAFT.UniformTaggedOutput.selection security r s choice)
            layout queue permutation kernel) := by
  unfold _root_.CurrentAFT.UniformTaggedOutput.uMass
  rw [_p2mH413]
  simp_rw [_root_.CurrentAFT.UniformTaggedOutput.flatMass, _p2mH415]
open _root_.P2Mb748e9da renaming h158 → _p2mH158
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h157 (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))
    (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.CoefficientOutputFock.familyMass security order hroom layout queue permutation coefficient) =
      coefficient.1 • _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight +
      ∑ arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order,
        ∑ choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security arity.val.1.val arity.val.2.val,
          (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security arity.val.1.val arity.val.2.val
            (_root_.CurrentAFT.CoefficientOutputFock.primary_room security order hroom arity) (_root_.CurrentAFT.CoefficientOutputFock.body_room security order hroom arity)).weight choice •
          _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
            (_root_.CurrentAFT.TaggedOutputFock.outputMass security arity.val.1.val arity.val.2.val
              (_root_.CurrentAFT.UniformTaggedOutput.selection security arity.val.1.val arity.val.2.val choice) layout queue permutation
              (coefficient.2 arity).val) := by
  have hmass : _root_.CurrentAFT.CoefficientOutputFock.familyMass security order hroom layout queue permutation coefficient =
      coefficient.1 • _root_.CurrentAFT.CoefficientOutputFock.baselineMass security layout queue permutation +
        ∑ arity : _root_.CurrentAFT.ControlCoordinates.PositiveArity order,
          _root_.CurrentAFT.UniformTaggedOutput.uMass security arity.val.1.val arity.val.2.val
            (_root_.CurrentAFT.CoefficientOutputFock.primary_room security order hroom arity) (_root_.CurrentAFT.CoefficientOutputFock.body_room security order hroom arity)
            layout queue permutation (coefficient.2 arity).val := by
    funext word
    simp only [_root_.CurrentAFT.CoefficientOutputFock.familyMass, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [hmass, map_add, map_smul, map_sum, _p2mH156]
  simp_rw [_p2mH158]
open _root_.P2Mb748e9da renaming h157 → _p2mH157
end
open _root_.P2Mb748e9da renaming h156 → _p2mH156
open _root_.P2Mb748e9da renaming h157 → _p2mH157
open _root_.P2Mb748e9da renaming h158 → _p2mH158
end CurrentAFT.ActualFamilyPolynomial
open _root_.P2Mb748e9da renaming h156 → _p2mH156
open _root_.P2Mb748e9da renaming h157 → _p2mH157
open _root_.P2Mb748e9da renaming h158 → _p2mH158
end
open _root_.P2Mb748e9da renaming h156 → _p2mH156
open _root_.P2Mb748e9da renaming h157 → _p2mH157
open _root_.P2Mb748e9da renaming h158 → _p2mH158
section
namespace CurrentAFT.RootScalarOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  ActualCycleMeanMGF TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts
  LocalReferenceEnergy ControlCoordinates GradedControlAlgebra RootActualOutputPolynomial
  RootBackgroundPolynomial RootLocalDenominators
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootScalarOutputPolynomial.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h437 {security : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security 0 0) :
    selection.kept = Finset.univ := by
  have hremoved : selection.removed = ∅ := by
    haveI : IsEmpty (_root_.CurrentAFT.TaggedSelection.RemovedLabel 0 0) := inferInstance
    simp only [_root_.CurrentAFT.TaggedSelection.Selection.removed, Finset.univ_eq_empty, Finset.map_empty]
  simp only [_root_.CurrentAFT.TaggedSelection.Selection.kept, hremoved, Finset.sdiff_empty]
open _root_.P2Mb748e9da renaming h437 → _p2mH437
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h432 (security : ℕ) (queue : ℤ) (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ) :
    _root_.CurrentAFT.RootScalarOutputPolynomial.blockPolynomial security queue roots =
      ∏ block, _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue roots block) := by
  change _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
    (_root_.AFT.BlockProducts.blockMass (_root_.CurrentAFT.ActualBlockFock.Slots security) (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue roots)) = _
  unfold _root_.AFT.BlockProducts.blockMass
  have h := _p2mH453 (_root_.CurrentAFT.ActualBlockFock.Slots security) (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
    (fun block => (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue roots block).weight)
  simp_rw [_root_.CurrentAFT.RootLocalDenominators.generating_eq_block] at h
  refine Eq.trans ?_ h
  simp only [_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear, LinearMap.coe_mk, AddHom.coe_mk]
open _root_.P2Mb748e9da renaming h432 → _p2mH432
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h433 {security : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security 0 0)
    (queue : ℤ) (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ) (scalar : ℝ) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue roots
      (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val =
      scalar • _root_.CurrentAFT.RootScalarOutputPolynomial.blockPolynomial security queue roots := by
  rw [_p2mH452]
  have hselected : _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.TypedTaggedPhysical.selectedMass selection roots
        (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val) =
        scalar • (1 : MvPolynomial (_root_.CurrentAFT.ActualControls.Palette security) ℝ) := by
    unfold _root_.CurrentAFT.TypedTaggedPhysical.selectedMass
    haveI : IsEmpty (Sigma (_root_.CurrentAFT.JointTaggedPhysicalFock.physicalSlots 0 0)) :=
      ⟨fun point => Fin.elim0 point.fst⟩
    unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear _root_.CurrentAFT.JointTaggedPhysicalFock.jointMass _root_.AFT.JointPhysicalChannel.mass
    simp [_root_.CurrentAFT.JointTaggedPhysicalFock.finiteKernel, _root_.CurrentAFT.JointTaggedPhysicalFock.unpairedKernel, _root_.CurrentAFT.GradedControlAlgebra.scalarKernel]
  rw [hselected, smul_mul_assoc, one_mul, _p2mH432]
  congr 1
  rw [← Finset.prod_subtype selection.kept (fun _ => Iff.rfl)
    (fun block => _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue roots block)), _p2mH437]
open _root_.P2Mb748e9da renaming h433 → _p2mH433
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h434 (security : ℕ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.ActualFockBound.latentLaw security) (fun latent => _root_.CurrentAFT.RootScalarOutputPolynomial.blockPolynomial security queue
        (fun block => _root_.CurrentAFT.ActualBlockMean.rootAt security permutation latent (_root_.CurrentAFT.ActualLayouts.blockLayout layout block))) := by
  change _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
    (fun output => (_root_.CurrentAFT.ActualFockBound.latentLaw security).expectation (fun latent =>
      _root_.AFT.BlockProducts.blockMass (_root_.CurrentAFT.ActualBlockFock.Slots security) (_root_.CurrentAFT.ActualBlockMean.rootedLaw security layout queue permutation latent) output)) = _
  rw [_p2mH430]
  rfl
open _root_.P2Mb748e9da renaming h434 → _p2mH434
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h436 {security : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security 0 0)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (queue : ℤ)
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) (scalar : ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.TaggedOutputFock.outputMass security 0 0 selection layout queue permutation
        (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val) =
      scalar • _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight := by
  letI : DecidableEq (_root_.CurrentAFT.TaggedOutputFock.OutputIndex selection) := Classical.decEq _
  change _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
    (fun output => (_root_.CurrentAFT.ActualFockBound.latentLaw security).expectation (fun latent =>
      _root_.CurrentAFT.TaggedOutputFock.conditionalMass security 0 0 selection layout queue permutation latent
        (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val output)) = _
  rw [_p2mH430 (Output := _root_.CurrentAFT.TaggedOutputFock.OutputIndex selection → _root_.CurrentAFT.ActualControls.Palette security)
    (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight) (_root_.CurrentAFT.ActualFockBound.latentLaw security)
    (fun latent => _root_.CurrentAFT.TaggedOutputFock.conditionalMass security 0 0 selection layout queue permutation latent
      (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val),
    _p2mH434]
  have hlocal (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security) :
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.TaggedOutputFock.conditionalMass security 0 0 selection layout queue permutation latent
          (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val) =
      scalar • _root_.CurrentAFT.RootScalarOutputPolynomial.blockPolynomial security queue (fun block => _root_.CurrentAFT.ActualBlockMean.rootAt security permutation latent (_root_.CurrentAFT.ActualLayouts.blockLayout layout block)) := by
    rw [← _p2mH431, _p2mH433]
  simp_rw [hlocal]
  exact (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.ActualFockBound.latentLaw security)).map_smul scalar _
open _root_.P2Mb748e9da renaming h436 → _p2mH436
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h435 {security : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security 0 0)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (queue : ℤ) (scalar : ℝ) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
      (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.TaggedOutputFock.outputMass security 0 0 selection layout queue permutation
          (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) scalar).val)) =
      scalar • _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight) := by
  simp_rw [_p2mH436]
  exact (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))).map_smul scalar _
open _root_.P2Mb748e9da renaming h435 → _p2mH435
end
open _root_.P2Mb748e9da renaming h432 → _p2mH432
open _root_.P2Mb748e9da renaming h433 → _p2mH433
open _root_.P2Mb748e9da renaming h434 → _p2mH434
open _root_.P2Mb748e9da renaming h435 → _p2mH435
open _root_.P2Mb748e9da renaming h436 → _p2mH436
open _root_.P2Mb748e9da renaming h437 → _p2mH437
end CurrentAFT.RootScalarOutputPolynomial
open _root_.P2Mb748e9da renaming h432 → _p2mH432
open _root_.P2Mb748e9da renaming h433 → _p2mH433
open _root_.P2Mb748e9da renaming h434 → _p2mH434
open _root_.P2Mb748e9da renaming h435 → _p2mH435
open _root_.P2Mb748e9da renaming h436 → _p2mH436
open _root_.P2Mb748e9da renaming h437 → _p2mH437
end
open _root_.P2Mb748e9da renaming h432 → _p2mH432
open _root_.P2Mb748e9da renaming h433 → _p2mH433
open _root_.P2Mb748e9da renaming h434 → _p2mH434
open _root_.P2Mb748e9da renaming h435 → _p2mH435
open _root_.P2Mb748e9da renaming h436 → _p2mH436
open _root_.P2Mb748e9da renaming h437 → _p2mH437
section
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial CycleRootExpansion
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h414 {Slot Color : Type*} [Fintype Color]
    (first second : Fintype Slot) (reference : Color → ℝ) (mass : (Slot → Color) → ℝ) :
    @_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear Slot Color first _ reference mass =
      @_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear Slot Color second _ reference mass := by
  cases Subsingleton.elim first second
  rfl
open _root_.P2Mb748e9da renaming h414 → _p2mH414
end
open _root_.P2Mb748e9da renaming h414 → _p2mH414
end CurrentAFT.PhysicalPolynomialAverages
open _root_.P2Mb748e9da renaming h414 → _p2mH414
end
open _root_.P2Mb748e9da renaming h414 → _p2mH414
namespace CurrentAFT.ActualCompletePhysical
end CurrentAFT.ActualCompletePhysical
namespace CurrentAFT.ActualCompletePhysical.familyGenerating
end CurrentAFT.ActualCompletePhysical.familyGenerating
namespace CurrentAFT.ActualCompletePhysical.selectedGenerating
end CurrentAFT.ActualCompletePhysical.selectedGenerating
namespace CurrentAFT.ActualCompleteStability.independentResponse
end CurrentAFT.ActualCompleteStability.independentResponse
namespace CurrentAFT.ActualFamilyPolynomial
end CurrentAFT.ActualFamilyPolynomial
namespace CurrentAFT.RootScalarOutputPolynomial
end CurrentAFT.RootScalarOutputPolynomial
namespace CurrentAFT.UniformTaggedOutput.flatMass
end CurrentAFT.UniformTaggedOutput.flatMass
section
namespace CurrentAFT.ActualCompletePhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.pgfFinDecEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h144 (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) 0 0) :
    _root_.CurrentAFT.ActualCompletePhysical.selectedGenerating security order hroom queue layout (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) kernel =
      _root_.CurrentAFT.GradedControlAlgebra.scalarAt (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel •
        _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
          (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
            (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight) := by
  unfold _root_.CurrentAFT.ActualCompletePhysical.selectedGenerating
  dsimp only [_root_.CurrentAFT.GradedControlAlgebra.zeroArity]
  have hkernel := _root_.CurrentAFT.GradedControlAlgebra.scalarKernel_scalarAt (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel
  conv_lhs => rw [← hkernel]
  have hlocal (choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security 0 0) := _p2mH435
    (_root_.CurrentAFT.UniformTaggedOutput.selection security 0 0 choice) layout queue
    (_root_.CurrentAFT.GradedControlAlgebra.scalarAt (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel)
  have hmean (choice : _root_.CurrentAFT.UniformTaggedOutput.Choice security 0 0) :
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.TaggedOutputFock.outputMass security 0 0 (_root_.CurrentAFT.UniformTaggedOutput.selection security 0 0 choice) layout queue permutation
            (_root_.CurrentAFT.GradedControlAlgebra.scalarKernel (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
              (_root_.CurrentAFT.GradedControlAlgebra.scalarAt (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel)).val)) =
        _root_.CurrentAFT.GradedControlAlgebra.scalarAt (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) kernel •
          _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
            (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
              (_root_.CurrentAFT.ActualFockBound.outputLaw security layout queue permutation).weight) := hlocal choice
  have hweights := (_root_.CurrentAFT.UniformTaggedOutput.choiceLaw security 0 0 (_root_.CurrentAFT.ActualRootFamily.primary_room security order hroom (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order))
    (_root_.CurrentAFT.ActualRootFamily.body_room security order hroom (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order))).sum_one
  conv_rhs => rw [← one_smul ℝ (_root_.CurrentAFT.GradedControlAlgebra.scalarAt _ _ kernel • _), ← hweights, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro choice _
  congr 1
  refine Eq.trans ?_ (hmean choice)
  unfold _root_.CurrentAFT.CycleRootExpansion.expectationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.uniform_weight, Fintype.card_eq_nat_card]
  apply Finset.sum_congr (by ext permutation; simp)
  intro permutation _
  apply congrArg (fun polynomial => ((Nat.card (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) : ℝ))⁻¹ • polynomial)
  exact _p2mH414 _ _ _ _
open _root_.P2Mb748e9da renaming h144 → _p2mH144
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h139 (security order : ℕ) (hroom : 2 * order ≤ security)
    (queue : ℤ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.ActualCompletePhysical.familyGenerating security order hroom queue layout family =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.CoefficientOutputFock.familyMass security order hroom layout queue permutation
            (_root_.CurrentAFT.GradedControlAlgebra.familyToCoefficients (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order family))) := by
  rw [_root_.CurrentAFT.ActualCompletePhysical.familyGenerating, _p2mH416, _p2mH144]
  simp_rw [_p2mH157]
  simp only [_root_.CurrentAFT.GradedControlAlgebra.familyToCoefficients, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, smul_add, Finset.smul_sum,
    Finset.sum_add_distrib, _root_.CurrentAFT.ActualCompletePhysical.selectedGenerating, _root_.AFT.FiniteDist.uniform_weight, Fintype.card_eq_nat_card]
  apply congrArg₂ (· + ·)
  · simp only [smul_smul]
    apply Finset.sum_congr (by ext permutation; simp)
    intro permutation _
    rw [mul_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr (by ext permutation; simp)
    intro arity _
    rw [Finset.sum_comm]
    apply Finset.sum_congr (by ext permutation; simp)
    intro permutation _
    apply Finset.sum_congr (by ext choice; simp)
    intro choice _
    simp only [_root_.CurrentAFT.GradedControlAlgebra.positiveArity, smul_smul, mul_comm]
open _root_.P2Mb748e9da renaming h139 → _p2mH139
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h142 (security order : ℕ) (hroom : 2 * order ≤ security)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.ActualWeightedFourier.mixedMass security order hroom layout
        (_root_.CurrentAFT.GradedControlAlgebra.familyToCoefficients (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order family)) =
      ∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
        _root_.CurrentAFT.ActualCompletePhysical.familyGenerating security order hroom scalar.val layout family := by
  unfold _root_.CurrentAFT.ActualWeightedFourier.mixedMass
  rw [_p2mH430, _root_.CurrentAFT.ActualWeightedFourier.randomizationLaw, _p2mH412]
  simp_rw [← _p2mH139]
  rfl
open _root_.P2Mb748e9da renaming h142 → _p2mH142
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h141 (security order : ℕ) (horder : 2 ≤ order)
    (hroom : 2 * order ≤ security) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (family : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order
      (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.ActualWeightedFourier.mixedMass security order hroom layout
          (_root_.CurrentAFT.GradedControlAlgebra.familyToCoefficients (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order family))) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualCompleteStability.fullResponse security order horder hroom (_root_.CurrentAFT.ActualLayouts.blockLayout layout) family) := by
  rw [_p2mH142, _p2mH138]
open _root_.P2Mb748e9da renaming h141 → _p2mH141
end
open _root_.P2Mb748e9da renaming h139 → _p2mH139
open _root_.P2Mb748e9da renaming h141 → _p2mH141
open _root_.P2Mb748e9da renaming h142 → _p2mH142
open _root_.P2Mb748e9da renaming h144 → _p2mH144
end CurrentAFT.ActualCompletePhysical
open _root_.P2Mb748e9da renaming h139 → _p2mH139
open _root_.P2Mb748e9da renaming h141 → _p2mH141
open _root_.P2Mb748e9da renaming h142 → _p2mH142
open _root_.P2Mb748e9da renaming h144 → _p2mH144
end
open _root_.P2Mb748e9da renaming h139 → _p2mH139
open _root_.P2Mb748e9da renaming h141 → _p2mH141
open _root_.P2Mb748e9da renaming h142 → _p2mH142
open _root_.P2Mb748e9da renaming h144 → _p2mH144
namespace CurrentAFT.ActualCalibrationClipping
end CurrentAFT.ActualCalibrationClipping
namespace CurrentAFT.ActualCalibrationFourier
end CurrentAFT.ActualCalibrationFourier
namespace CurrentAFT.ActualCompleteStability.coefficients
end CurrentAFT.ActualCompleteStability.coefficients
section
namespace CurrentAFT.ActualCalibrationRates
open ActualCalibrationFourier ActualCalibrationClipping
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h136 (order : ℕ) : 0 ≤ _root_.CurrentAFT.ActualCalibrationRates.fourierConstant order :=
  mul_nonneg (mul_nonneg (by norm_num) (_p2mH221 order 1))
    (pow_nonneg (Real.sqrt_nonneg _) _)
open _root_.P2Mb748e9da renaming h136 → _p2mH136
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h133 (security : ℕ) : 0 < _root_.CurrentAFT.ActualPhysicalTail.analysisRadius security := by
  unfold _root_.CurrentAFT.ActualPhysicalTail.analysisRadius _root_.CurrentAFT.BackgroundRates.radius
  exact div_pos (Real.rpow_pos_of_pos (_root_.CurrentAFT.FirstResponse.base_pos security) _) (Real.sqrt_pos.mpr (Real.exp_pos 1))
open _root_.P2Mb748e9da renaming h133 → _p2mH133
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h137 (security order : ℕ) :
    _root_.CurrentAFT.ActualCalibrationRates.fourierError security order = _root_.CurrentAFT.ActualCalibrationRates.fourierConstant order * (_root_.CurrentAFT.Parameters.base security : ℝ)^(-((order + 1 : ℕ) : ℝ) / 4) := by
  have hb := _root_.CurrentAFT.FirstResponse.base_pos security
  have hr := _p2mH133 security
  have hc : 0 ≤ 2 * _root_.CurrentAFT.CoefficientOutputFock.normConstant order 1 :=
    mul_nonneg (by norm_num) (_p2mH221 order 1)
  have hpower : _root_.CurrentAFT.ActualPhysicalTail.analysisRadius security^(2 * (order + 1)) =
      (_root_.CurrentAFT.ActualPhysicalTail.analysisRadius security^(order + 1))^2 := by rw [← pow_mul, Nat.mul_comm]
  unfold _root_.CurrentAFT.ActualCalibrationRates.fourierError _root_.CurrentAFT.ActualCalibrationFourier.energyBudget
  rw [hpower, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hc, Real.sqrt_sq (pow_nonneg hr.le _)]
  have hradius : _root_.CurrentAFT.BackgroundRates.radius security^(order + 1) =
      (_root_.CurrentAFT.Parameters.base security : ℝ)^(((order + 1 : ℕ) : ℝ) / 4) := by
    unfold _root_.CurrentAFT.BackgroundRates.radius
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
    congr 1
    ring
  rw [_root_.CurrentAFT.ActualPhysicalTail.analysisRadius, div_pow, hradius, div_div_eq_mul_div]
  rw [show -((order + 1 : ℕ) : ℝ) / 4 = -(((order + 1 : ℕ) : ℝ) / 4) by ring, Real.rpow_neg hb.le]
  unfold _root_.CurrentAFT.ActualCalibrationRates.fourierConstant
  rw [div_eq_mul_inv]
open _root_.P2Mb748e9da renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h135 (accuracyOrder : ℕ) :
    ∀ᶠ security : ℕ in atTop,
      (_root_.CurrentAFT.Parameters.modulus security : ℝ) * _root_.CurrentAFT.ActualCalibrationRates.fourierError security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) ≤
        _root_.CurrentAFT.inversePower security (accuracyOrder + 2) := by
  filter_upwards [_p2mH460 accuracyOrder
    (_root_.CurrentAFT.ActualCalibrationRates.fourierConstant (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)) (_p2mH136 _)] with security hbound
  rw [_p2mH137]
  simpa only [Nat.cast_add, Nat.cast_one, neg_div, mul_assoc, mul_comm, mul_left_comm] using hbound
open _root_.P2Mb748e9da renaming h135 → _p2mH135
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h134 (accuracyOrder : ℕ) : 2 ≤ _root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder := by
  unfold _root_.CurrentAFT.Parameters.calibrationOrder
  omega
open _root_.P2Mb748e9da renaming h134 → _p2mH134
end
open _root_.P2Mb748e9da renaming h133 → _p2mH133
open _root_.P2Mb748e9da renaming h134 → _p2mH134
open _root_.P2Mb748e9da renaming h135 → _p2mH135
open _root_.P2Mb748e9da renaming h136 → _p2mH136
open _root_.P2Mb748e9da renaming h137 → _p2mH137
end CurrentAFT.ActualCalibrationRates
open _root_.P2Mb748e9da renaming h133 → _p2mH133
open _root_.P2Mb748e9da renaming h134 → _p2mH134
open _root_.P2Mb748e9da renaming h135 → _p2mH135
open _root_.P2Mb748e9da renaming h136 → _p2mH136
open _root_.P2Mb748e9da renaming h137 → _p2mH137
end
open _root_.P2Mb748e9da renaming h133 → _p2mH133
open _root_.P2Mb748e9da renaming h134 → _p2mH134
open _root_.P2Mb748e9da renaming h135 → _p2mH135
open _root_.P2Mb748e9da renaming h136 → _p2mH136
open _root_.P2Mb748e9da renaming h137 → _p2mH137
namespace AFT.SignedConditioning
end AFT.SignedConditioning
namespace AFT.SignedConditioning.restricted
end AFT.SignedConditioning.restricted
namespace CurrentAFT.clippedPublicCoreWeight
end CurrentAFT.clippedPublicCoreWeight
namespace CurrentAFT.positiveEndpointLaw
end CurrentAFT.positiveEndpointLaw
namespace CurrentAFT.positivePublicCoreLaw
end CurrentAFT.positivePublicCoreLaw
section
namespace CurrentAFT.FiniteZeroSum
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index] [Nonempty Index] (modulus : ℕ) [NeZero modulus]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h357 (word : Index → ZMod modulus) :
    (_root_.CurrentAFT.FiniteZeroSum.uniformLaw modulus).weight word =
      if ∑ index, word index = 0 then (modulus : ℝ) / (Fintype.card (Index → ZMod modulus) : ℝ) else 0 := by
  by_cases hzero : (∑ index, word index) = 0 <;>
    simp [_root_.CurrentAFT.FiniteZeroSum.uniformLaw, _root_.AFT.FiniteDist.condition, _root_.CurrentAFT.FiniteZeroSum.uniform_charge_mass, _root_.AFT.FiniteDist.uniform_weight,
      hzero, div_eq_mul_inv, mul_comm]
open _root_.P2Mb748e9da renaming h357 → _p2mH357
end
open _root_.P2Mb748e9da renaming h357 → _p2mH357
end CurrentAFT.FiniteZeroSum
open _root_.P2Mb748e9da renaming h357 → _p2mH357
end
open _root_.P2Mb748e9da renaming h357 → _p2mH357
namespace CurrentAFT.ActualCalibratedPublic
end CurrentAFT.ActualCalibratedPublic
namespace CurrentAFT.ActualCalibratedPublic.mass
end CurrentAFT.ActualCalibratedPublic.mass
namespace CurrentAFT.ActualCalibratedPublic.weight
end CurrentAFT.ActualCalibratedPublic.weight
namespace CurrentAFT.ActualCalibrationFourier.calibratedCoefficients
end CurrentAFT.ActualCalibrationFourier.calibratedCoefficients
namespace CurrentAFT.ActualWeightedFourier.randomizationLaw
end CurrentAFT.ActualWeightedFourier.randomizationLaw
namespace CurrentAFT.GradedControlAlgebra.familyToCoefficients
end CurrentAFT.GradedControlAlgebra.familyToCoefficients
section
namespace CurrentAFT.ActualCalibrationExact
open AFT ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCompletePhysical ActualLayouts ConditionalHistogramMean ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualCalibrationExact.exactFinDecEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h128 (security order : ℕ) (horder : 2 ≤ order)
    (hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold order horder ≤ security) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    _root_.CurrentAFT.ActualCalibratedPublic.Calibrated security order horder hsecurity layout := by
  have h := _p2mH141 security order horder (_root_.CurrentAFT.ActualCompleteStability.room security order horder hsecurity) layout
    (_root_.CurrentAFT.ActualCompleteStability.solution security order horder hsecurity (_root_.CurrentAFT.ActualLayouts.blockLayout layout))
  rw [_p2mH152, map_one] at h
  exact h
open _root_.P2Mb748e9da renaming h128 → _p2mH128
end
open _root_.P2Mb748e9da renaming h128 → _p2mH128
end CurrentAFT.ActualCalibrationExact
open _root_.P2Mb748e9da renaming h128 → _p2mH128
end
open _root_.P2Mb748e9da renaming h128 → _p2mH128
section
namespace CurrentAFT.GaussianWindowProtection
open AFT GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h366 (width : ℝ) (hwidth : 0 < width) (point : ℤ) :
    _root_.AFT.GaussianSource.integerMass width point = (_root_.AFT.GaussianSource.integerGaussian width hwidth point).toReal :=
  (_p2mH86 width hwidth point).symm
open _root_.P2Mb748e9da renaming h366 → _p2mH366
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h367 (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) (point : ℤ) :
    0 ≤ _root_.CurrentAFT.GaussianWindowProtection.protectedMass width cutoff point :=
  div_nonneg (_p2mH90 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hwidth) cutoff point)
    (_p2mH92 width cutoff hwidth).le
open _root_.P2Mb748e9da renaming h367 → _p2mH367
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h369 (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    Summable (_root_.CurrentAFT.GaussianWindowProtection.protectedMass width cutoff) :=
  (Summable.of_nonneg_of_le (_p2mH90 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hwidth) cutoff)
    (_p2mH89 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hwidth) cutoff) (_root_.AFT.GaussianSource.summable_integerMass width hwidth)).div_const _
open _root_.P2Mb748e9da renaming h369 → _p2mH369
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h368 (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    (∑' point, _root_.CurrentAFT.GaussianWindowProtection.protectedMass width cutoff point) = 1 := by
  unfold _root_.CurrentAFT.GaussianWindowProtection.protectedMass
  rw [tsum_div_const, _p2mH91,
    div_self (_p2mH92 width cutoff hwidth).ne']
open _root_.P2Mb748e9da renaming h368 → _p2mH368
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h370 (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) (point : ℤ) :
    _root_.CurrentAFT.GaussianWindowProtection.protectedMass width cutoff point =
      if hpoint : point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then
        (_root_.AFT.GaussianSource.windowGaussian width cutoff).weight ⟨point, hpoint⟩ else 0 := by
  by_cases hpoint : point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · rw [dif_pos hpoint]
    change (if point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) then _root_.AFT.GaussianSource.integerMass width point else 0) /
      _root_.AFT.GaussianSource.retainedFraction width cutoff = _
    rw [if_pos hpoint]
    change (_root_.AFT.GaussianSource.weight width point / _root_.AFT.GaussianSource.realNormalizer width) /
      (_root_.AFT.GaussianSource.windowNormalizer width cutoff / _root_.AFT.GaussianSource.realNormalizer width) = _root_.AFT.GaussianSource.weight width point / _root_.AFT.GaussianSource.windowNormalizer width cutoff
    field_simp [(zero_lt_one.trans_le (_root_.AFT.GaussianSource.realNormalizer_ge_one width hwidth)).ne',
      (zero_lt_one.trans_le (_root_.AFT.GaussianSource.windowNormalizer_ge_one width cutoff)).ne']
  · simp only [_root_.CurrentAFT.GaussianWindowProtection.protectedMass, _root_.AFT.GaussianSource.restrictWindow, if_neg hpoint, dif_neg hpoint, zero_div]
open _root_.P2Mb748e9da renaming h370 → _p2mH370
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h371 (width : ℝ) (cutoff : ℕ) (point : ℤ)
    (hpoint : point ∉ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)) :
    _root_.CurrentAFT.GaussianWindowProtection.protectedMass width cutoff point = 0 := by simp only [_root_.CurrentAFT.GaussianWindowProtection.protectedMass, _root_.AFT.GaussianSource.restrictWindow, if_neg hpoint, zero_div]
open _root_.P2Mb748e9da renaming h371 → _p2mH371
set_option maxRecDepth 8192
private theorem _root_.P2Mb748e9da.h465 (cutoff : ℕ) (point : ℤ) :
    ((cutoff + 1 : ℕ) : ℝ) ≤ |(point : ℝ)| ↔
      point ∉ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ) := by
  have hcast : ((cutoff + 1 : ℕ) : ℝ) ≤ |(point : ℝ)| ↔ (cutoff : ℤ) + 1 ≤ |point| := by
    rw [← Int.cast_abs]
    norm_cast
  rw [hcast, Finset.mem_Icc, ← abs_le]
  omega
open _root_.P2Mb748e9da renaming h465 → CurrentAFT.GaussianWindowProtection.outside_window_iff
open _root_.P2Mb748e9da renaming h465 → _p2mH465
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h372 (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    1 - _root_.AFT.GaussianSource.retainedFraction width cutoff = _root_.AFT.GaussianSource.clippingProbability width (cutoff + 1 : ℕ) hwidth := by
  rw [← _p2mH88 width cutoff hwidth]
  unfold _root_.AFT.GaussianSource.clippingProbability
  apply tsum_congr
  intro point
  rw [← _p2mH366 width hwidth point]
  by_cases hpoint : point ∈ Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)
  · rw [if_neg (fun hout => (_p2mH465 cutoff point).mp hout hpoint)]
    simp only [_root_.AFT.GaussianSource.restrictWindow, if_pos hpoint, sub_self]
  · rw [if_pos ((_p2mH465 cutoff point).mpr hpoint)]
    simp only [_root_.AFT.GaussianSource.restrictWindow, if_neg hpoint, sub_zero]
open _root_.P2Mb748e9da renaming h372 → _p2mH372
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h373 (width : ℝ) (cutoff : ℕ) (hwidth : 0 < width) :
    (∑' point, |_root_.AFT.GaussianSource.integerMass width point - _root_.CurrentAFT.GaussianWindowProtection.protectedMass width cutoff point|) / 2 ≤
      _root_.AFT.GaussianSource.clippingProbability width (cutoff + 1 : ℕ) hwidth := by
  have hretained : 0 < ∑' point, _root_.AFT.GaussianSource.restrictWindow (_root_.AFT.GaussianSource.integerMass width) cutoff point := by
    rw [_p2mH91]
    exact _p2mH92 width cutoff hwidth
  have hh := _p2mH117 (_root_.AFT.GaussianSource.integerMass width) (_root_.AFT.GaussianSource.restrictWindow (_root_.AFT.GaussianSource.integerMass width) cutoff)
    (_root_.AFT.GaussianSource.integerMass_nonneg width hwidth) (_p2mH90 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hwidth) cutoff)
    (_p2mH89 _ (_root_.AFT.GaussianSource.integerMass_nonneg width hwidth) cutoff) (_root_.AFT.GaussianSource.summable_integerMass width hwidth) hretained
  rw [_p2mH91, _root_.AFT.GaussianSource.integerMass_sum width hwidth] at hh
  simp only [div_one] at hh
  rw [← _p2mH372 width cutoff hwidth]
  convert hh using 1
  congr 1
  apply tsum_congr
  intro point
  exact abs_sub_comm _ _
open _root_.P2Mb748e9da renaming h373 → _p2mH373
end
open _root_.P2Mb748e9da renaming h366 → _p2mH366
open _root_.P2Mb748e9da renaming h367 → _p2mH367
open _root_.P2Mb748e9da renaming h368 → _p2mH368
open _root_.P2Mb748e9da renaming h369 → _p2mH369
open _root_.P2Mb748e9da renaming h370 → _p2mH370
open _root_.P2Mb748e9da renaming h371 → _p2mH371
open _root_.P2Mb748e9da renaming h372 → _p2mH372
open _root_.P2Mb748e9da renaming h373 → _p2mH373
open _root_.P2Mb748e9da renaming h465 → CurrentAFT.GaussianWindowProtection.outside_window_iff
open _root_.P2Mb748e9da renaming h465 → _p2mH465
end CurrentAFT.GaussianWindowProtection
open _root_.P2Mb748e9da renaming h366 → _p2mH366
open _root_.P2Mb748e9da renaming h367 → _p2mH367
open _root_.P2Mb748e9da renaming h368 → _p2mH368
open _root_.P2Mb748e9da renaming h369 → _p2mH369
open _root_.P2Mb748e9da renaming h370 → _p2mH370
open _root_.P2Mb748e9da renaming h371 → _p2mH371
open _root_.P2Mb748e9da renaming h372 → _p2mH372
open _root_.P2Mb748e9da renaming h373 → _p2mH373
open _root_.P2Mb748e9da renaming h465 → CurrentAFT.GaussianWindowProtection.outside_window_iff
open _root_.P2Mb748e9da renaming h465 → _p2mH465
end
open _root_.P2Mb748e9da renaming h366 → _p2mH366
open _root_.P2Mb748e9da renaming h367 → _p2mH367
open _root_.P2Mb748e9da renaming h368 → _p2mH368
open _root_.P2Mb748e9da renaming h369 → _p2mH369
open _root_.P2Mb748e9da renaming h370 → _p2mH370
open _root_.P2Mb748e9da renaming h371 → _p2mH371
open _root_.P2Mb748e9da renaming h372 → _p2mH372
open _root_.P2Mb748e9da renaming h373 → _p2mH373
namespace AFT.DependentTensorChannel
end AFT.DependentTensorChannel
namespace AFT.DependentTensorChannel.apply
end AFT.DependentTensorChannel.apply
namespace AFT.DependentTensorChannel.applyFin
end AFT.DependentTensorChannel.applyFin
namespace AFT.DependentTensorChannel.applyFin.match_1
end AFT.DependentTensorChannel.applyFin.match_1
namespace CurrentAFT.GaussianWindowProtection
end CurrentAFT.GaussianWindowProtection
namespace CurrentAFT.GaussianWindowProtection.outside_window_iff
end CurrentAFT.GaussianWindowProtection.outside_window_iff
namespace CurrentAFT.GaussianWindowProtection.protectedMass
end CurrentAFT.GaussianWindowProtection.protectedMass
section
namespace CurrentAFT.GaussianProductProtection
open AFT GaussianSource GaussianWindowProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h360 (width : ℝ) (hwidth : 0 < width) {count : ℕ}
    (cutoff : Fin count → ℕ) (word : Fin count → ℤ) : 0 ≤ _root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff word :=
  Finset.prod_nonneg (fun index _ => _p2mH367 width (cutoff index) hwidth _)
open _root_.P2Mb748e9da renaming h360 → _p2mH360
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h363 (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ) :
    Summable (_root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff) :=
  (_root_.AFT.countableFiniteProduct_summable_sum count (fun index => _root_.CurrentAFT.GaussianWindowProtection.protectedMass width (cutoff index))
    (fun index => _p2mH367 width (cutoff index) hwidth)
    (fun index => _p2mH369 width (cutoff index) hwidth)).1
open _root_.P2Mb748e9da renaming h363 → _p2mH363
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h362 (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ) :
    (∑' word, _root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff word) = 1 := by
  unfold _root_.CurrentAFT.GaussianProductProtection.protectedMass
  rw [(_root_.AFT.countableFiniteProduct_summable_sum count (fun index => _root_.CurrentAFT.GaussianWindowProtection.protectedMass width (cutoff index))
    (fun index => _p2mH367 width (cutoff index) hwidth)
    (fun index => _p2mH369 width (cutoff index) hwidth)).2]
  simp only [_p2mH368 width _ hwidth, Finset.prod_const_one]
open _root_.P2Mb748e9da renaming h362 → _p2mH362
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h359 (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ) :
    (∑' word, |_root_.CurrentAFT.GaussianProductProtection.fullMass width count word - _root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff word|) / 2 ≤
      ∑ index, _root_.AFT.GaussianSource.clippingProbability width (cutoff index + 1 : ℕ) hwidth := by
  have hproduct := _p2mH114 count (fun _ => _root_.AFT.GaussianSource.integerMass width)
    (fun index => _root_.CurrentAFT.GaussianWindowProtection.protectedMass width (cutoff index))
    (fun _ => _root_.AFT.GaussianSource.integerMass_nonneg width hwidth)
    (fun index => _p2mH367 width (cutoff index) hwidth)
    (fun _ => _root_.AFT.GaussianSource.summable_integerMass width hwidth)
    (fun index => _p2mH369 width (cutoff index) hwidth)
    (fun _ => _root_.AFT.GaussianSource.integerMass_sum width hwidth)
    (fun index => _p2mH368 width (cutoff index) hwidth)
  apply (div_le_div_of_nonneg_right hproduct (by norm_num : (0 : ℝ) ≤ 2)).trans
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun index _ => _p2mH373 width (cutoff index) hwidth)
open _root_.P2Mb748e9da renaming h359 → _p2mH359
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h361 (width : ℝ) (hwidth : 0 < width) {count : ℕ}
    (cutoff : Fin count → ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord cutoff) :
    _root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding cutoff word) = (_root_.CurrentAFT.GaussianProductProtection.protectedLaw width cutoff).weight word := by
  apply Finset.prod_congr rfl
  intro index _
  change _root_.CurrentAFT.GaussianWindowProtection.protectedMass width (cutoff index) (word index).val = _
  rw [_p2mH370 width (cutoff index) hwidth (word index).val,
    dif_pos (word index).property]
open _root_.P2Mb748e9da renaming h361 → _p2mH361
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h364 (width : ℝ) {count : ℕ} (cutoff : Fin count → ℕ)
    (word : Fin count → ℤ) (hword : word ∉ Finset.univ.image (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding cutoff)) :
    _root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff word = 0 := by
  have hsome : ∃ index, word index ∉ Finset.Icc (-(cutoff index : ℤ)) (cutoff index : ℤ) := by
    by_contra hnone
    have hinside (index : Fin count) : word index ∈ Finset.Icc (-(cutoff index : ℤ)) (cutoff index : ℤ) :=
      not_not.mp (not_exists.mp hnone index)
    apply hword
    exact Finset.mem_image.mpr ⟨(fun index => ⟨word index, hinside index⟩), Finset.mem_univ _, rfl⟩
  obtain ⟨index, hindex⟩ := hsome
  exact Finset.prod_eq_zero (Finset.mem_univ index)
    (_p2mH371 width (cutoff index) (word index) hindex)
open _root_.P2Mb748e9da renaming h364 → _p2mH364
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h365 {Output : Type*} [Fintype Output]
    (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ)
    (channel : (Fin count → ℤ) → _root_.AFT.FiniteDist Output) :
    _root_.AFT.FiniteDist.countableMix (_root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff) (_p2mH360 width hwidth cutoff)
      (_p2mH363 width hwidth cutoff) (_p2mH362 width hwidth cutoff) channel =
        (_root_.CurrentAFT.GaussianProductProtection.protectedLaw width cutoff).mix (fun word => channel (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding cutoff word)) := by
  apply _root_.AFT.FiniteDist.ext
  intro output
  change (∑' word, _root_.CurrentAFT.GaussianProductProtection.protectedMass width cutoff word * (channel word).weight output) = _
  rw [tsum_eq_sum (s := Finset.univ.image (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding cutoff))
    (fun word hword => by rw [_p2mH364 width cutoff word hword, zero_mul])]
  rw [Finset.sum_image (fun first _ second _ hequal => (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding cutoff).injective hequal)]
  apply Finset.sum_congr rfl
  intro word _
  rw [_p2mH361 width hwidth cutoff word]
open _root_.P2Mb748e9da renaming h365 → _p2mH365
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h358 {Output : Type*} [Fintype Output]
    (width : ℝ) (hwidth : 0 < width) {count : ℕ} (cutoff : Fin count → ℕ)
    (channel : (Fin count → ℤ) → _root_.AFT.FiniteDist Output) :
    _root_.AFT.FiniteDist.TVBound
      (_root_.AFT.FiniteDist.countableMix (_root_.CurrentAFT.GaussianProductProtection.fullMass width count) (_root_.CurrentAFT.GaussianProductProtection.fullMass_nonneg width hwidth count)
        (_root_.CurrentAFT.GaussianProductProtection.fullMass_summable width hwidth count) (_root_.CurrentAFT.GaussianProductProtection.fullMass_sum width hwidth count) channel)
      ((_root_.CurrentAFT.GaussianProductProtection.protectedLaw width cutoff).mix (fun word => channel (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding cutoff word)))
      (∑ index, _root_.AFT.GaussianSource.clippingProbability width (cutoff index + 1 : ℕ) hwidth) := by
  rw [← _p2mH365 width hwidth cutoff channel]
  exact _p2mH72 _ _ (_root_.CurrentAFT.GaussianProductProtection.fullMass_nonneg width hwidth count)
    (_p2mH360 width hwidth cutoff) (_root_.CurrentAFT.GaussianProductProtection.fullMass_summable width hwidth count)
    (_p2mH363 width hwidth cutoff) (_root_.CurrentAFT.GaussianProductProtection.fullMass_sum width hwidth count)
    (_p2mH362 width hwidth cutoff) channel _ (_p2mH359 width hwidth cutoff)
open _root_.P2Mb748e9da renaming h358 → _p2mH358
end
open _root_.P2Mb748e9da renaming h358 → _p2mH358
open _root_.P2Mb748e9da renaming h359 → _p2mH359
open _root_.P2Mb748e9da renaming h360 → _p2mH360
open _root_.P2Mb748e9da renaming h361 → _p2mH361
open _root_.P2Mb748e9da renaming h362 → _p2mH362
open _root_.P2Mb748e9da renaming h363 → _p2mH363
open _root_.P2Mb748e9da renaming h364 → _p2mH364
open _root_.P2Mb748e9da renaming h365 → _p2mH365
end CurrentAFT.GaussianProductProtection
open _root_.P2Mb748e9da renaming h358 → _p2mH358
open _root_.P2Mb748e9da renaming h359 → _p2mH359
open _root_.P2Mb748e9da renaming h360 → _p2mH360
open _root_.P2Mb748e9da renaming h361 → _p2mH361
open _root_.P2Mb748e9da renaming h362 → _p2mH362
open _root_.P2Mb748e9da renaming h363 → _p2mH363
open _root_.P2Mb748e9da renaming h364 → _p2mH364
open _root_.P2Mb748e9da renaming h365 → _p2mH365
end
open _root_.P2Mb748e9da renaming h358 → _p2mH358
open _root_.P2Mb748e9da renaming h359 → _p2mH359
open _root_.P2Mb748e9da renaming h360 → _p2mH360
open _root_.P2Mb748e9da renaming h361 → _p2mH361
open _root_.P2Mb748e9da renaming h362 → _p2mH362
open _root_.P2Mb748e9da renaming h363 → _p2mH363
open _root_.P2Mb748e9da renaming h364 → _p2mH364
open _root_.P2Mb748e9da renaming h365 → _p2mH365
namespace CurrentAFT.GaussianProductProtection
end CurrentAFT.GaussianProductProtection
namespace CurrentAFT.InwardAnchor
end CurrentAFT.InwardAnchor
namespace CurrentAFT.InwardAnchor.fixedCoinLaw
end CurrentAFT.InwardAnchor.fixedCoinLaw
namespace CurrentAFT.InwardAnchor.integerPoint
end CurrentAFT.InwardAnchor.integerPoint
namespace CurrentAFT.InwardAnchor.integer_fiber_sum_le_one
end CurrentAFT.InwardAnchor.integer_fiber_sum_le_one
namespace CurrentAFT.InwardAnchor.point
end CurrentAFT.InwardAnchor.point
namespace CurrentAFT.InwardAnchor.positiveDirection
end CurrentAFT.InwardAnchor.positiveDirection
namespace CurrentAFT.InwardAnchor.shiftedAnchorLaw
end CurrentAFT.InwardAnchor.shiftedAnchorLaw
namespace CurrentAFT.InwardAnchor.smoothedAnchorLaw
end CurrentAFT.InwardAnchor.smoothedAnchorLaw
namespace CurrentAFT.InwardAnchor.zero_shift_bound
end CurrentAFT.InwardAnchor.zero_shift_bound
namespace CurrentAFT.ProtectedCycle
end CurrentAFT.ProtectedCycle
namespace CurrentAFT.ProtectedCycle.gaussianCycleLaw
end CurrentAFT.ProtectedCycle.gaussianCycleLaw
namespace CurrentAFT.ProtectedCycle.scalarFourier
end CurrentAFT.ProtectedCycle.scalarFourier
section
namespace CurrentAFT.CurrentSourceProtection
open AFT GaussianSource GaussianWindowProtection GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h319 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceProtection.budget security = ∑ index : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security),
      _root_.AFT.GaussianSource.clippingProbability (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.cutoff security index + 1 : ℕ) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) := by
  symm
  unfold _root_.CurrentAFT.CurrentSourceProtection.sourceCount
  rw [Fin.sum_univ_add]
  have hb (index : Fin (_root_.CurrentAFT.Parameters.bodySize security)) :
      _root_.CurrentAFT.CurrentSourceProtection.cutoff security (index.castAdd (_root_.CurrentAFT.Parameters.legCount security * 2 + 1)) =
        _root_.CurrentAFT.DiffuseProfiles.edgeCutoff security := _root_.CurrentAFT.CurrentSourceProtection.cutoff_body security index
  have ha (index : Fin (_root_.CurrentAFT.Parameters.legCount security * 2 + 1)) :
      _root_.CurrentAFT.CurrentSourceProtection.cutoff security (Fin.natAdd (_root_.CurrentAFT.Parameters.bodySize security) index) =
        _root_.CurrentAFT.Parameters.sourceCutoff security - 1 := _root_.CurrentAFT.CurrentSourceProtection.cutoff_aux security index
  simp only [hb, ha,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rfl
open _root_.P2Mb748e9da renaming h319 → _p2mH319
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h320 (security : ℕ) : 0 ≤ _root_.CurrentAFT.CurrentSourceProtection.budget security := by
  rw [_p2mH319]
  apply Finset.sum_nonneg
  intro index _
  exact tsum_nonneg (fun point => by
    split_ifs
    · exact ENNReal.toReal_nonneg
    · rfl)
open _root_.P2Mb748e9da renaming h320 → _p2mH320
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h324 (security : ℕ) : 0 < _root_.CurrentAFT.Parameters.sourceCutoff security :=
  pow_pos (_root_.CurrentAFT.Parameters.base_pos security) _
open _root_.P2Mb748e9da renaming h324 → CurrentAFT.CurrentSourceProtection.sourceCutoff_pos
open _root_.P2Mb748e9da renaming h324 → _p2mH324
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h321 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (index : Fin (_root_.CurrentAFT.Parameters.legCount security * 2 + 1)) :
    |(_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word index : ℤ)| < _root_.CurrentAFT.Parameters.sourceCutoff security := by
  have h := Finset.mem_Icc.mp (_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word index).property
  have hp := _p2mH324 security
  exact lt_of_le_of_lt (abs_le.mpr h) (by omega)
open _root_.P2Mb748e9da renaming h321 → _p2mH321
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h322 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (permutation : Equiv.Perm (Fin (_root_.CurrentAFT.Parameters.bodySize security))) (vertex : Fin (_root_.CurrentAFT.Parameters.bodySize security)) :
    |_root_.CurrentAFT.PublicCharge.cycleDifference (fun index => (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word (permutation.symm index) : ℤ)) vertex| <
      _root_.CurrentAFT.Parameters.sourceCutoff security := by
  have hh := _p2mH425 (_root_.CurrentAFT.Parameters.bodySize security)
    (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) (fun index => _root_.CurrentAFT.CurrentSourceProtection.protectedBody security word (permutation.symm index)) vertex
  have hp := _p2mH324 security
  have hcut : 2 * (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security : ℤ) < _root_.CurrentAFT.Parameters.sourceCutoff security := by
    unfold _root_.CurrentAFT.DiffuseProfiles.edgeCutoff
    omega
  exact hh.trans_lt hcut
open _root_.P2Mb748e9da renaming h322 → _p2mH322
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h323 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (permutation : Equiv.Perm (Fin (_root_.CurrentAFT.Parameters.bodySize security))) (vertex : Fin (_root_.CurrentAFT.Parameters.bodySize security))
    (index : Fin (_root_.CurrentAFT.Parameters.legCount security * 2 + 1)) :
    |_root_.CurrentAFT.PublicCharge.cycleDifference (fun point => (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word (permutation.symm point) : ℤ)) vertex +
      (_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word index : ℤ)| < _root_.CurrentAFT.Parameters.safeMargin security := by
  have hb := _p2mH322 security word permutation vertex
  have ha := _p2mH321 security word index
  have hp := _p2mH324 security
  have htriangle := abs_add_le
    (_root_.CurrentAFT.PublicCharge.cycleDifference (fun point => (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word (permutation.symm point) : ℤ)) vertex)
    (_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word index : ℤ)
  unfold _root_.CurrentAFT.Parameters.safeMargin
  push_cast
  omega
open _root_.P2Mb748e9da renaming h323 → _p2mH323
end
open _root_.P2Mb748e9da renaming h319 → _p2mH319
open _root_.P2Mb748e9da renaming h320 → _p2mH320
open _root_.P2Mb748e9da renaming h321 → _p2mH321
open _root_.P2Mb748e9da renaming h322 → _p2mH322
open _root_.P2Mb748e9da renaming h323 → _p2mH323
open _root_.P2Mb748e9da renaming h324 → CurrentAFT.CurrentSourceProtection.sourceCutoff_pos
open _root_.P2Mb748e9da renaming h324 → _p2mH324
end CurrentAFT.CurrentSourceProtection
open _root_.P2Mb748e9da renaming h319 → _p2mH319
open _root_.P2Mb748e9da renaming h320 → _p2mH320
open _root_.P2Mb748e9da renaming h321 → _p2mH321
open _root_.P2Mb748e9da renaming h322 → _p2mH322
open _root_.P2Mb748e9da renaming h323 → _p2mH323
open _root_.P2Mb748e9da renaming h324 → CurrentAFT.CurrentSourceProtection.sourceCutoff_pos
open _root_.P2Mb748e9da renaming h324 → _p2mH324
end
open _root_.P2Mb748e9da renaming h319 → _p2mH319
open _root_.P2Mb748e9da renaming h320 → _p2mH320
open _root_.P2Mb748e9da renaming h321 → _p2mH321
open _root_.P2Mb748e9da renaming h322 → _p2mH322
open _root_.P2Mb748e9da renaming h323 → _p2mH323
open _root_.P2Mb748e9da renaming h324 → CurrentAFT.CurrentSourceProtection.sourceCutoff_pos
open _root_.P2Mb748e9da renaming h324 → _p2mH324
namespace AFT.GaussianSource.clippingProbability
end AFT.GaussianSource.clippingProbability
namespace AFT.Negligible
end AFT.Negligible
namespace CurrentAFT.CurrentSourceProtection
end CurrentAFT.CurrentSourceProtection
section
namespace CurrentAFT.CurrentSourceTail
open AFT GaussianSource CurrentSourceProtection
open Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h331 (security : ℕ) : 0 ≤ _root_.CurrentAFT.CurrentSourceTail.envelope security := by
  unfold _root_.CurrentAFT.CurrentSourceTail.envelope
  positivity
open _root_.P2Mb748e9da renaming h331 → _p2mH331
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h330 (security cutoff : ℕ)
    (hcutoff : (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / 2 ≤ (cutoff + 1 : ℕ)) :
    _root_.AFT.GaussianSource.clippingProbability (_root_.CurrentAFT.CurrentSourceProtection.width security) (cutoff + 1 : ℕ) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) ≤
      _root_.CurrentAFT.CurrentSourceTail.envelope security := by
  have hb : (0 : ℝ) < _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast _root_.CurrentAFT.Parameters.base_pos security
  have hsquare := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (Parameters.base security : ℝ) ^ 2 / 2) hcutoff 2
  have hratio : Real.pi / 8 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 ≤
      Real.pi * (cutoff + 1 : ℕ) ^ 2 / (2 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity :
      (0 : ℝ) < 2 * (Parameters.base security : ℝ) ^ 2)).mpr
    calc
      _ = Real.pi * ((_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / 2) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsquare Real.pi_pos.le
  have hexponent :
      -Real.pi * (cutoff + 1 : ℕ) ^ 2 / (2 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2) ≤
        -(Real.pi / 8) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 := by
    calc
      _ = -(Real.pi * (cutoff + 1 : ℕ) ^ 2 /
        (2 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2)) := by ring
      _ ≤ -(Real.pi / 8 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2) := neg_le_neg hratio
      _ = _ := by ring
  have htail := _p2mH85 (_root_.CurrentAFT.CurrentSourceProtection.width security) (cutoff + 1 : ℕ)
    (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) (by positivity)
  change _root_.AFT.GaussianSource.clippingProbability _ _ _ ≤
    Real.exp (-Real.pi * (cutoff + 1 : ℕ) ^ 2 / (2 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2)) *
      (1 + 4 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / Real.pi) at htail
  exact htail.trans ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexponent)
    (by positivity)).trans_eq (by unfold _root_.CurrentAFT.CurrentSourceTail.envelope; ring))
open _root_.P2Mb748e9da renaming h330 → _p2mH330
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h326 (security : ℕ) :
    (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / 2 ≤
      (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security + 1 : ℕ) := by
  have hn : _root_.CurrentAFT.Parameters.sourceCutoff security ≤ 2 * (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security + 1) := by
    unfold _root_.CurrentAFT.DiffuseProfiles.edgeCutoff
    omega
  have hr : (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 ≤
      2 * (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security + 1 : ℕ) := by
    exact_mod_cast hn
  linarith
open _root_.P2Mb748e9da renaming h326 → _p2mH326
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h325 (security : ℕ) :
    (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / 2 ≤
      (_root_.CurrentAFT.Parameters.sourceCutoff security - 1 + 1 : ℕ) := by
  have hpositive := _p2mH324 security
  have heq : _root_.CurrentAFT.Parameters.sourceCutoff security - 1 + 1 = _root_.CurrentAFT.Parameters.sourceCutoff security := by omega
  rw [heq]
  change (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / 2 ≤ ((_root_.CurrentAFT.Parameters.base security) ^ 2 : ℕ)
  push_cast
  nlinarith [sq_nonneg (_root_.CurrentAFT.Parameters.base security : ℝ)]
open _root_.P2Mb748e9da renaming h325 → _p2mH325
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h327 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceProtection.budget security ≤ _root_.CurrentAFT.CurrentSourceProtection.sourceCount security * _root_.CurrentAFT.CurrentSourceTail.envelope security := by
  unfold _root_.CurrentAFT.CurrentSourceProtection.budget
  have hb := mul_le_mul_of_nonneg_left
    (_p2mH330 security (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) (_p2mH326 security))
    (Nat.cast_nonneg (_root_.CurrentAFT.Parameters.bodySize security) : (0 : ℝ) ≤ _root_.CurrentAFT.Parameters.bodySize security)
  have ha := mul_le_mul_of_nonneg_left
    (_p2mH330 security (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_p2mH325 security))
    (Nat.cast_nonneg (_root_.CurrentAFT.Parameters.legCount security * 2 + 1) :
      (0 : ℝ) ≤ (_root_.CurrentAFT.Parameters.legCount security * 2 + 1 : ℕ))
  exact (add_le_add hb ha).trans_eq (by unfold _root_.CurrentAFT.CurrentSourceProtection.sourceCount; push_cast; ring)
open _root_.P2Mb748e9da renaming h327 → _p2mH327
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h332 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceProtection.sourceCount security = _root_.CurrentAFT.Parameters.dimension security + 1 := by
  unfold _root_.CurrentAFT.CurrentSourceProtection.sourceCount _root_.CurrentAFT.Parameters.dimension
  omega
open _root_.P2Mb748e9da renaming h332 → _p2mH332
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h333 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceProtection.sourceCount security ≤ 131075 * _root_.CurrentAFT.Parameters.base security ^ 160 := by
  have hd := (_root_.CurrentAFT.Parameters.dimension_bounds security).2
  have hp : 1 ≤ _root_.CurrentAFT.Parameters.base security ^ 160 :=
    Nat.one_le_pow _ _ (by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega)
  rw [_p2mH332]
  omega
open _root_.P2Mb748e9da renaming h333 → _p2mH333
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h329 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceProtection.budget security ≤ (131075 * (1 + 4 / Real.pi)) *
      (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 162 *
        Real.exp (-(Real.pi / 8) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2) := by
  have hb : (1 : ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show 1 ≤ _root_.CurrentAFT.Parameters.base security by have := _root_.CurrentAFT.Parameters.base_ge_two security; omega)
  have hsquare : (1 : ℝ) ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 := one_le_pow₀ hb
  have hpref : 1 + 4 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / Real.pi ≤
      (1 + 4 / Real.pi) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 := by
    calc
      _ ≤ (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 +
        4 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2 / Real.pi := add_le_add hsquare le_rfl
      _ = _ := by ring
  have hc : (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security : ℝ) ≤ 131075 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 160 := by
    exact_mod_cast _p2mH333 security
  calc
    _ ≤ (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security : ℝ) * _root_.CurrentAFT.CurrentSourceTail.envelope security := _p2mH327 security
    _ ≤ (131075 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 160) * _root_.CurrentAFT.CurrentSourceTail.envelope security :=
      mul_le_mul_of_nonneg_right hc (_p2mH331 security)
    _ ≤ (131075 * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 160) *
        (((1 + 4 / Real.pi) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2) *
          Real.exp (-(Real.pi / 8) * (_root_.CurrentAFT.Parameters.base security : ℝ) ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le
    _ = _ := by rw [show (162 : ℕ) = 160 + 2 by rfl, pow_add]; ring
open _root_.P2Mb748e9da renaming h329 → _p2mH329
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h328 : _root_.AFT.Negligible _root_.CurrentAFT.CurrentSourceProtection.budget := by
  have hmain := (_p2mH116
    (131075 * (1 + 4 / Real.pi)) 162 2 (Real.pi / 8)
    (by positivity) (by norm_num) (by positivity)).comp_add 2
  apply hmain.of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (_p2mH320 security), abs_of_nonneg (by positivity)]
  simpa only [_root_.CurrentAFT.Parameters.base, Nat.cast_add, Nat.cast_ofNat, Real.rpow_two] using
    _p2mH329 security
open _root_.P2Mb748e9da renaming h328 → _p2mH328
end
open _root_.P2Mb748e9da renaming h325 → _p2mH325
open _root_.P2Mb748e9da renaming h326 → _p2mH326
open _root_.P2Mb748e9da renaming h327 → _p2mH327
open _root_.P2Mb748e9da renaming h328 → _p2mH328
open _root_.P2Mb748e9da renaming h329 → _p2mH329
open _root_.P2Mb748e9da renaming h330 → _p2mH330
open _root_.P2Mb748e9da renaming h331 → _p2mH331
open _root_.P2Mb748e9da renaming h332 → _p2mH332
open _root_.P2Mb748e9da renaming h333 → _p2mH333
end CurrentAFT.CurrentSourceTail
open _root_.P2Mb748e9da renaming h325 → _p2mH325
open _root_.P2Mb748e9da renaming h326 → _p2mH326
open _root_.P2Mb748e9da renaming h327 → _p2mH327
open _root_.P2Mb748e9da renaming h328 → _p2mH328
open _root_.P2Mb748e9da renaming h329 → _p2mH329
open _root_.P2Mb748e9da renaming h330 → _p2mH330
open _root_.P2Mb748e9da renaming h331 → _p2mH331
open _root_.P2Mb748e9da renaming h332 → _p2mH332
open _root_.P2Mb748e9da renaming h333 → _p2mH333
end
open _root_.P2Mb748e9da renaming h325 → _p2mH325
open _root_.P2Mb748e9da renaming h326 → _p2mH326
open _root_.P2Mb748e9da renaming h327 → _p2mH327
open _root_.P2Mb748e9da renaming h328 → _p2mH328
open _root_.P2Mb748e9da renaming h329 → _p2mH329
open _root_.P2Mb748e9da renaming h330 → _p2mH330
open _root_.P2Mb748e9da renaming h331 → _p2mH331
open _root_.P2Mb748e9da renaming h332 → _p2mH332
open _root_.P2Mb748e9da renaming h333 → _p2mH333
namespace CurrentAFT.LobsterIncidence
end CurrentAFT.LobsterIncidence
namespace CurrentAFT.LobsterIncidence.bodyResidual
end CurrentAFT.LobsterIncidence.bodyResidual
namespace CurrentAFT.LobsterIncidence.firstEdge
end CurrentAFT.LobsterIncidence.firstEdge
namespace CurrentAFT.LobsterIncidence.load
end CurrentAFT.LobsterIncidence.load
namespace CurrentAFT.LobsterIncidence.load.match_1
end CurrentAFT.LobsterIncidence.load.match_1
namespace CurrentAFT.LobsterIncidence.secondEdge
end CurrentAFT.LobsterIncidence.secondEdge
namespace CurrentAFT.PublicCharge.attachmentIncrement
end CurrentAFT.PublicCharge.attachmentIncrement
section
namespace CurrentAFT.LobsterCoordinates
open AFT PublicCharge LobsterIncidence
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h386 (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) (index : Fin (bodyEdges + (legs + legs) + 1)) :
    (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling input).val index =
      _root_.CurrentAFT.LobsterIncidence.load placement attachment (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input)
        ((_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).symm (relabeling.symm index)) := rfl
open _root_.P2Mb748e9da renaming h386 → _p2mH386
end
open _root_.P2Mb748e9da renaming h386 → _p2mH386
end CurrentAFT.LobsterCoordinates
open _root_.P2Mb748e9da renaming h386 → _p2mH386
end
open _root_.P2Mb748e9da renaming h386 → _p2mH386
namespace CurrentAFT.LegMixer
end CurrentAFT.LegMixer
namespace CurrentAFT.LegMixer.blockCoordinateMixer
end CurrentAFT.LegMixer.blockCoordinateMixer
namespace CurrentAFT.LegMixer.coordinateMixer
end CurrentAFT.LegMixer.coordinateMixer
namespace CurrentAFT.LegMixer.inverseMixer
end CurrentAFT.LegMixer.inverseMixer
namespace CurrentAFT.LegMixer.legIncidence
end CurrentAFT.LegMixer.legIncidence
namespace CurrentAFT.LobsterCoordinates
end CurrentAFT.LobsterCoordinates
section
namespace CurrentAFT.LobsterMixerMatrix
open AFT LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Scalar : Type*} [CommRing Scalar]
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h388 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : Fin (bodyEdges + (legs + legs)) → Scalar)
    (index : Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) :
    (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs index) =
      (_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix bodyEdges legs scale shear).mulVec (input ∘ _root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs) index := by
  simp only [_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs)]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]
open _root_.P2Mb748e9da renaming h388 → _p2mH388
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h387 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) → Scalar) :
    (_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix bodyEdges legs scale shear).mulVec input =
      Sum.elim (fun vertex => input (.inl vertex))
        (Sum.elim (fun leg => scale leg * input (.inr (.inl leg)) + shear leg * input (.inr (.inr leg)))
          (fun leg => input (.inr (.inr leg)))) := by
  ext index
  rcases index with vertex | (leg | leg) <;>
    simp [_root_.CurrentAFT.LobsterMixerMatrix.blockMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.diagonal_apply]
open _root_.P2Mb748e9da renaming h387 → _p2mH387
end
open _root_.P2Mb748e9da renaming h387 → _p2mH387
open _root_.P2Mb748e9da renaming h388 → _p2mH388
end CurrentAFT.LobsterMixerMatrix
open _root_.P2Mb748e9da renaming h387 → _p2mH387
open _root_.P2Mb748e9da renaming h388 → _p2mH388
end
open _root_.P2Mb748e9da renaming h387 → _p2mH387
open _root_.P2Mb748e9da renaming h388 → _p2mH388
namespace CurrentAFT.AffineBaseline
end CurrentAFT.AffineBaseline
namespace CurrentAFT.AffineBaseline.baseline
end CurrentAFT.AffineBaseline.baseline
namespace CurrentAFT.AffineBaseline.baseline.match_1
end CurrentAFT.AffineBaseline.baseline.match_1
namespace CurrentAFT.AffineBaseline.closure
end CurrentAFT.AffineBaseline.closure
namespace CurrentAFT.AffineBaseline.offset
end CurrentAFT.AffineBaseline.offset
section
namespace CurrentAFT.AffineRealization
open AFT LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h208 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    _root_.AFT.pathLoad _ (_root_.CurrentAFT.AffineRealization.extensionCorrection bodyEdges legs modulus queues relabeling) =
      _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling - _root_.AFT.injectionColumn _ modulus :=
  (Classical.choose_spec (_root_.AFT.exists_extension_correction _
    (_root_.AFT.injectionColumn _ modulus) (_root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling)
    ((_root_.CurrentAFT.AffineRealization.queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (_root_.AFT.totalCharge_injectionColumn _ modulus (_root_.CurrentAFT.AffineRealization.queue_modulus_le bodyEdges legs modulus queues)).symm))).1
open _root_.P2Mb748e9da renaming h208 → _p2mH208
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h209 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input) =
      (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling
        ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
          input.2 • _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling :=
  _p2mH120 _ _ _ _ _ _
    (_p2mH208 bodyEdges legs modulus queues relabeling) input
open _root_.P2Mb748e9da renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h211 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : _root_.CurrentAFT.PublicCharge.PublicChargeTest modulus centers shift) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
        _root_.CurrentAFT.AffineBaseline.numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling :=
  (Classical.choose_spec (_root_.CurrentAFT.AffineBaseline.offset_integral_preimage bodyEdges legs modulus (NeZero.ne modulus)
    (_root_.AFT.injectionColumn _ modulus) (_root_.AFT.totalCharge_injectionColumn _ modulus (_root_.CurrentAFT.AffineRealization.queue_modulus_le bodyEdges legs modulus queues))
    centers shift intercept placement closureScalar relabeling hcharge)).1
open _root_.P2Mb748e9da renaming h211 → _p2mH211
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h206 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (closureScalar : ℤ) (hcharge : _root_.CurrentAFT.PublicCharge.PublicChargeTest modulus centers shift)
    (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input +
        _root_.CurrentAFT.AffineRealization.offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
      (_root_.CurrentAFT.LobsterCoordinates.relabeledBasis bodyEdges legs placement attachment relabeling
        ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
        input.2 • _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling +
        _root_.CurrentAFT.AffineBaseline.numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling := by
  have hadd (n : ℕ) (column : Fin (n + 1) → ℤ) (first second : (Fin n → ℤ) × ℤ) :
      _root_.AFT.roundingLoad n column (first + second) = _root_.AFT.roundingLoad n column first + _root_.AFT.roundingLoad n column second := by
    simp only [_root_.AFT.roundingLoad, Prod.fst_add, Prod.snd_add, _root_.AFT.pathLoad_add, add_smul]
    abel
  rw [hadd, _p2mH209, _p2mH211]
open _root_.P2Mb748e9da renaming h206 → _p2mH206
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h207 (count : ℕ) (basis : (Fin count → ℤ) ≃ₗ[ℤ] _root_.AFT.zeroSumLattice count)
    (input : Fin count → ℤ) :
    (_root_.AFT.edgeBasisChangeMatrix count basis).mulVec input = _root_.AFT.edgeBasisChange count basis input := by
  have hrepr (v : Fin count → ℤ) : ⇑((Pi.basisFun ℤ (Fin count)).repr v) = v := by
    funext i
    exact Pi.basisFun_repr ℤ (Fin count) v i
  simpa only [_root_.AFT.edgeBasisChangeMatrix, hrepr, LinearEquiv.coe_coe] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℤ (Fin count)) (Pi.basisFun ℤ (Fin count))
      (_root_.AFT.edgeBasisChange count basis).toLinearMap input
open _root_.P2Mb748e9da renaming h207 → _p2mH207
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h210 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    (_root_.CurrentAFT.AffineRealization.matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).mulVec
      (Sum.elim input.1 (fun _ : Unit => input.2)) =
      Sum.elim (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).1
        (fun _ : Unit => (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).2) := by
  rw [_root_.CurrentAFT.AffineRealization.matrix, _root_.AFT.transportBlockMatrix, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, ← Matrix.mulVec_mulVec, _p2mH207,
    _root_.CurrentAFT.AffineRealization.linearPart, _root_.AFT.blockTransport, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
  congr 1
  ext index
  simp [Matrix.mulVec, dotProduct, mul_comm]
open _root_.P2Mb748e9da renaming h210 → _p2mH210
end
open _root_.P2Mb748e9da renaming h206 → _p2mH206
open _root_.P2Mb748e9da renaming h207 → _p2mH207
open _root_.P2Mb748e9da renaming h208 → _p2mH208
open _root_.P2Mb748e9da renaming h209 → _p2mH209
open _root_.P2Mb748e9da renaming h210 → _p2mH210
open _root_.P2Mb748e9da renaming h211 → _p2mH211
end CurrentAFT.AffineRealization
open _root_.P2Mb748e9da renaming h206 → _p2mH206
open _root_.P2Mb748e9da renaming h207 → _p2mH207
open _root_.P2Mb748e9da renaming h208 → _p2mH208
open _root_.P2Mb748e9da renaming h209 → _p2mH209
open _root_.P2Mb748e9da renaming h210 → _p2mH210
open _root_.P2Mb748e9da renaming h211 → _p2mH211
end
open _root_.P2Mb748e9da renaming h206 → _p2mH206
open _root_.P2Mb748e9da renaming h207 → _p2mH207
open _root_.P2Mb748e9da renaming h208 → _p2mH208
open _root_.P2Mb748e9da renaming h209 → _p2mH209
open _root_.P2Mb748e9da renaming h210 → _p2mH210
open _root_.P2Mb748e9da renaming h211 → _p2mH211
namespace CurrentAFT.ActualBlockFock
end CurrentAFT.ActualBlockFock
namespace CurrentAFT.ActualBlockFock.blockLawAt
end CurrentAFT.ActualBlockFock.blockLawAt
namespace CurrentAFT.ActualBlockFock.blockLawAt.match_1
end CurrentAFT.ActualBlockFock.blockLawAt.match_1
namespace CurrentAFT.ActualBlockFock.primaryLawAt
end CurrentAFT.ActualBlockFock.primaryLawAt
namespace CurrentAFT.ActualBlockMean
end CurrentAFT.ActualBlockMean
namespace CurrentAFT.ActualBlockMean.attachmentRoots
end CurrentAFT.ActualBlockMean.attachmentRoots
namespace CurrentAFT.ActualBlockMean.blockVector
end CurrentAFT.ActualBlockMean.blockVector
namespace CurrentAFT.ActualBlockMean.bodyVector
end CurrentAFT.ActualBlockMean.bodyVector
namespace CurrentAFT.ActualBlockMean.centerRoots
end CurrentAFT.ActualBlockMean.centerRoots
namespace CurrentAFT.ActualBlockMean.queueRoots
end CurrentAFT.ActualBlockMean.queueRoots
namespace CurrentAFT.ActualBlockMean.rootAt
end CurrentAFT.ActualBlockMean.rootAt
namespace CurrentAFT.ActualBlockMean.rootedLaw
end CurrentAFT.ActualBlockMean.rootedLaw
namespace CurrentAFT.ActualCycleMeanMGF
end CurrentAFT.ActualCycleMeanMGF
namespace CurrentAFT.ActualCycleMeanMGF.realizedResponse
end CurrentAFT.ActualCycleMeanMGF.realizedResponse
section
namespace CurrentAFT.CyclePathClosure
open AFT PublicCharge AffineBaseline
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h342 (count : ℕ) (edges : Fin count → ℤ) :
    _root_.AFT.pathLoad count edges = Fin.snoc edges 0 - Fin.cons 0 edges := by
  induction count with
  | zero =>
    funext index
    have hi : index = (0 : Fin 1) := Fin.eq_zero index
    subst index
    simp [_root_.AFT.pathLoad, Fin.snoc_zero]
  | succ count ih =>
    have he : edges = Fin.cons (edges 0) (Fin.tail edges) := (Fin.cons_self_tail edges).symm
    conv_rhs => rw [he, ← Fin.cons_snoc_eq_snoc_cons]
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp [_root_.AFT.pathLoad]
    · simp only [_root_.AFT.pathLoad, Fin.cons_succ, Pi.sub_apply, ih]
      refine Fin.cases ?_ (fun next => ?_) rest <;> simp
open _root_.P2Mb748e9da renaming h342 → _p2mH342
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h343 (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) (index : Fin (count + 1)) :
    (@Fin.snoc count (fun _ => ℤ) edges scalar) ((finRotate (count + 1)).symm index) =
      (@Fin.cons count (fun _ => ℤ) scalar edges) index := by
  rw [Fin.snoc_eq_cons_rotate]
  simp only [Equiv.apply_symm_apply]
open _root_.P2Mb748e9da renaming h343 → _p2mH343
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h344 (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) (index : Fin (count + 1)) :
    (@Fin.snoc count (fun _ => ℤ) edges scalar) index =
      (@Fin.snoc count (fun _ => ℤ) edges 0) index + if index = Fin.last count then scalar else 0 := by
  refine Fin.lastCases ?_ (fun rest => ?_) index <;> simp
open _root_.P2Mb748e9da renaming h344 → _p2mH344
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h340 (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) (index : Fin (count + 1)) :
    (@Fin.cons count (fun _ => ℤ) scalar edges) index =
      (@Fin.cons count (fun _ => ℤ) 0 edges) index + if index = 0 then scalar else 0 := by
  refine Fin.cases ?_ (fun rest => ?_) index <;> simp
open _root_.P2Mb748e9da renaming h340 → _p2mH340
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h341 (count : ℕ) (edges : Fin count → ℤ) (scalar : ℤ) :
    _root_.CurrentAFT.PublicCharge.cycleDifference (Fin.snoc edges scalar) = _root_.AFT.pathLoad count edges + _root_.CurrentAFT.AffineBaseline.closure count scalar := by
  funext index
  rw [_root_.CurrentAFT.PublicCharge.cycleDifference, _p2mH343, _p2mH342]
  simp only [Pi.add_apply, Pi.sub_apply, _root_.CurrentAFT.AffineBaseline.closure]
  rw [_p2mH344, _p2mH340]
  ring
open _root_.P2Mb748e9da renaming h341 → _p2mH341
end
open _root_.P2Mb748e9da renaming h340 → _p2mH340
open _root_.P2Mb748e9da renaming h341 → _p2mH341
open _root_.P2Mb748e9da renaming h342 → _p2mH342
open _root_.P2Mb748e9da renaming h343 → _p2mH343
open _root_.P2Mb748e9da renaming h344 → _p2mH344
end CurrentAFT.CyclePathClosure
open _root_.P2Mb748e9da renaming h340 → _p2mH340
open _root_.P2Mb748e9da renaming h341 → _p2mH341
open _root_.P2Mb748e9da renaming h342 → _p2mH342
open _root_.P2Mb748e9da renaming h343 → _p2mH343
open _root_.P2Mb748e9da renaming h344 → _p2mH344
end
open _root_.P2Mb748e9da renaming h340 → _p2mH340
open _root_.P2Mb748e9da renaming h341 → _p2mH341
open _root_.P2Mb748e9da renaming h342 → _p2mH342
open _root_.P2Mb748e9da renaming h343 → _p2mH343
open _root_.P2Mb748e9da renaming h344 → _p2mH344
namespace AFT.edgeBasisChangeMatrix
end AFT.edgeBasisChangeMatrix
namespace CurrentAFT.AffineRealization
end CurrentAFT.AffineRealization
namespace CurrentAFT.AffineRealization.linearPart
end CurrentAFT.AffineRealization.linearPart
namespace CurrentAFT.AffineRealization.matrix
end CurrentAFT.AffineRealization.matrix
namespace CurrentAFT.AffineRealization.queueColumn
end CurrentAFT.AffineRealization.queueColumn
namespace CurrentAFT.CyclePathClosure
end CurrentAFT.CyclePathClosure
namespace CurrentAFT.PublicEndpointPlacement
end CurrentAFT.PublicEndpointPlacement
namespace CurrentAFT.PublicEndpointPlacement.toAssembly
end CurrentAFT.PublicEndpointPlacement.toAssembly
namespace CurrentAFT.PublicEndpointPlacement.toAssembly.match_1
end CurrentAFT.PublicEndpointPlacement.toAssembly.match_1
namespace CurrentAFT.PublicEndpointPlacement.toPhysical
end CurrentAFT.PublicEndpointPlacement.toPhysical
namespace CurrentAFT.PublicEndpointPlacement.toPhysical.match_3
end CurrentAFT.PublicEndpointPlacement.toPhysical.match_3
section
namespace CurrentAFT.CurrentAffineGeometry
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  LobsterCoordinates AffineRealization PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h241 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex)) =
      core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex) := by
  simp [_root_.CurrentAFT.CurrentAffineGeometry.relabeling]
open _root_.P2Mb748e9da renaming h241 → _p2mH241
end
open _root_.P2Mb748e9da renaming h241 → _p2mH241
end CurrentAFT.CurrentAffineGeometry
open _root_.P2Mb748e9da renaming h241 → _p2mH241
end
open _root_.P2Mb748e9da renaming h241 → _p2mH241
namespace CurrentAFT.CurrentAffineGeometry
end CurrentAFT.CurrentAffineGeometry
namespace CurrentAFT.CurrentAffineGeometry.relabeling
end CurrentAFT.CurrentAffineGeometry.relabeling
namespace CurrentAFT.CurrentSourcePublicTransport
end CurrentAFT.CurrentSourcePublicTransport
section
namespace CurrentAFT.CurrentSourceLayout
open AFT CurrentSourceProtection GaussianProductProtection CurrentAffineGeometry
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h314 (security : ℕ) (path : Fin (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security)) :
    _root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security
      (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inl path))))) =
        _root_.CurrentAFT.CurrentSourceProtection.bodyPosition security ((_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security).symm path.castSucc) := by
  simp [_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering, _root_.CurrentAFT.CurrentSourceLayout.moveClosure, _root_.CurrentAFT.CurrentSourceLayout.bodyNumbering, _root_.CurrentAFT.CurrentSourceProtection.bodyPosition, _root_.CurrentAFT.CurrentAffineGeometry.unitToFinOne]
  rfl
open _root_.P2Mb748e9da renaming h314 → _p2mH314
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h313 (security : ℕ) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    _root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security
      (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inl leg)))))) =
        _root_.CurrentAFT.CurrentSourceProtection.auxPosition security (Fin.cast (by omega)
          ((leg.castAdd (_root_.CurrentAFT.Parameters.legCount security)).castAdd 1)) := by
  apply Fin.ext
  simp [_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering, _root_.CurrentAFT.CurrentSourceLayout.moveClosure, _root_.CurrentAFT.CurrentSourceLayout.auxNumbering, _root_.CurrentAFT.CurrentSourceProtection.auxPosition, _root_.CurrentAFT.CurrentAffineGeometry.unitToFinOne]
  rfl
open _root_.P2Mb748e9da renaming h313 → _p2mH313
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h316 (security : ℕ) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    _root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security
      (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inr leg)))))) =
        _root_.CurrentAFT.CurrentSourceProtection.auxPosition security (Fin.cast (by omega)
          ((Fin.natAdd (_root_.CurrentAFT.Parameters.legCount security) leg).castAdd 1)) := by
  apply Fin.ext
  simp [_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering, _root_.CurrentAFT.CurrentSourceLayout.moveClosure, _root_.CurrentAFT.CurrentSourceLayout.auxNumbering, _root_.CurrentAFT.CurrentSourceProtection.auxPosition, _root_.CurrentAFT.CurrentAffineGeometry.unitToFinOne]
  rfl
open _root_.P2Mb748e9da renaming h316 → _p2mH316
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h315 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inr ()))) =
      _root_.CurrentAFT.CurrentSourceProtection.auxPosition security (Fin.last (_root_.CurrentAFT.Parameters.legCount security * 2)) := by
  apply Fin.ext
  simp [_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering, _root_.CurrentAFT.CurrentSourceLayout.moveClosure, _root_.CurrentAFT.CurrentSourceLayout.auxNumbering, _root_.CurrentAFT.CurrentSourceProtection.auxPosition, _root_.CurrentAFT.CurrentAffineGeometry.unitToFinOne]
  rfl
open _root_.P2Mb748e9da renaming h315 → _p2mH315
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h309 (security : ℕ) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) :
    (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1).1 =
        Fin.init (fun index => _root_.CurrentAFT.CurrentSourceLayout.bodyLatent security word ((_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security).symm index)) := by
  funext index
  change word (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security
    (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inl index)))))) = _
  rw [_p2mH314]
  rfl
open _root_.P2Mb748e9da renaming h309 → _p2mH309
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h310 (security : ℕ) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) :
    (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1).2.1 = _root_.CurrentAFT.CurrentSourceLayout.firstInput security word := by
  funext index
  change word (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security
    (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inl index))))))) = _
  rw [_p2mH313]
  rfl
open _root_.P2Mb748e9da renaming h310 → _p2mH310
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h312 (security : ℕ) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) :
    (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1).2.2 = _root_.CurrentAFT.CurrentSourceLayout.secondInput security word := by
  funext index
  change word (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security
    (.inl (_root_.CurrentAFT.LobsterCoordinates.edgeIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (.inr (.inr index))))))) = _
  rw [_p2mH316]
  rfl
open _root_.P2Mb748e9da renaming h312 → _p2mH312
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h311 (security : ℕ) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) :
    (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).2 = _root_.CurrentAFT.CurrentSourceLayout.queueInput security word := by
  change word (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inl (_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security (.inr ())))) = _
  rw [_p2mH315]
  rfl
open _root_.P2Mb748e9da renaming h311 → _p2mH311
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h308 (security : ℕ) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) :
    Fin.snoc (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1).1 (_root_.CurrentAFT.CurrentSourceLayout.closureScalar security word) =
        fun index => _root_.CurrentAFT.CurrentSourceLayout.bodyLatent security word ((_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security).symm index) := by
  rw [_p2mH309]
  have hclosure : _root_.CurrentAFT.CurrentSourceLayout.closureScalar security word =
      _root_.CurrentAFT.CurrentSourceLayout.bodyLatent security word ((_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security).symm (Fin.last (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security))) := by
    unfold _root_.CurrentAFT.CurrentSourceLayout.closureScalar
    rw [_root_.CurrentAFT.CurrentSourceLayout.numbering_closure]
    rfl
  rw [hclosure, Fin.snoc_init_self]
open _root_.P2Mb748e9da renaming h308 → _p2mH308
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h318 (security : ℕ) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) :
    _root_.CurrentAFT.GaussianProductProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word =
      _root_.CurrentAFT.GaussianProductProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) (_root_.CurrentAFT.CurrentSourceLayout.hiddenWord security word) *
        _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security)
          (_root_.CurrentAFT.CurrentSourceLayout.closureScalar security word) := by
  unfold _root_.CurrentAFT.GaussianProductProtection.protectedMass
  rw [← Equiv.prod_comp (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security)]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique, _root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff, _root_.CurrentAFT.CurrentSourceLayout.hiddenWord,
    _root_.CurrentAFT.CurrentSourceLayout.closureScalar]
  change _ * _root_.CurrentAFT.GaussianWindowProtection.protectedMass _
    (_root_.CurrentAFT.CurrentSourceProtection.cutoff security (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inr ()))) _ = _
  rw [_root_.CurrentAFT.CurrentSourceLayout.cutoff_closure]
open _root_.P2Mb748e9da renaming h318 → _p2mH318
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h317 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) :
    (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security).weight word =
      (_root_.CurrentAFT.GaussianProductProtection.protectedLaw (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security)).weight
        (_root_.CurrentAFT.CurrentSourceLayout.hiddenProtectedWord security word) *
      (_root_.AFT.GaussianSource.windowGaussian (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security)).weight
        (_root_.CurrentAFT.CurrentSourceLayout.protectedClosure security word) := by
  change (_root_.CurrentAFT.GaussianProductProtection.protectedLaw (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)).weight word = _
  rw [← _p2mH361 (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) (_root_.CurrentAFT.CurrentSourceProtection.cutoff security),
    _p2mH318]
  apply congrArg₂ (· * ·)
  · exact _p2mH361 (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenProtectedWord security word)
  · have h := _p2mH370 (_root_.CurrentAFT.CurrentSourceProtection.width security)
      (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) (_root_.CurrentAFT.CurrentSourceLayout.protectedClosure security word).val
    rw [dif_pos (_root_.CurrentAFT.CurrentSourceLayout.protectedClosure security word).property] at h
    exact h
open _root_.P2Mb748e9da renaming h317 → _p2mH317
end
open _root_.P2Mb748e9da renaming h308 → _p2mH308
open _root_.P2Mb748e9da renaming h309 → _p2mH309
open _root_.P2Mb748e9da renaming h310 → _p2mH310
open _root_.P2Mb748e9da renaming h311 → _p2mH311
open _root_.P2Mb748e9da renaming h312 → _p2mH312
open _root_.P2Mb748e9da renaming h313 → _p2mH313
open _root_.P2Mb748e9da renaming h314 → _p2mH314
open _root_.P2Mb748e9da renaming h315 → _p2mH315
open _root_.P2Mb748e9da renaming h316 → _p2mH316
open _root_.P2Mb748e9da renaming h317 → _p2mH317
open _root_.P2Mb748e9da renaming h318 → _p2mH318
end CurrentAFT.CurrentSourceLayout
open _root_.P2Mb748e9da renaming h308 → _p2mH308
open _root_.P2Mb748e9da renaming h309 → _p2mH309
open _root_.P2Mb748e9da renaming h310 → _p2mH310
open _root_.P2Mb748e9da renaming h311 → _p2mH311
open _root_.P2Mb748e9da renaming h312 → _p2mH312
open _root_.P2Mb748e9da renaming h313 → _p2mH313
open _root_.P2Mb748e9da renaming h314 → _p2mH314
open _root_.P2Mb748e9da renaming h315 → _p2mH315
open _root_.P2Mb748e9da renaming h316 → _p2mH316
open _root_.P2Mb748e9da renaming h317 → _p2mH317
open _root_.P2Mb748e9da renaming h318 → _p2mH318
end
open _root_.P2Mb748e9da renaming h308 → _p2mH308
open _root_.P2Mb748e9da renaming h309 → _p2mH309
open _root_.P2Mb748e9da renaming h310 → _p2mH310
open _root_.P2Mb748e9da renaming h311 → _p2mH311
open _root_.P2Mb748e9da renaming h312 → _p2mH312
open _root_.P2Mb748e9da renaming h313 → _p2mH313
open _root_.P2Mb748e9da renaming h314 → _p2mH314
open _root_.P2Mb748e9da renaming h315 → _p2mH315
open _root_.P2Mb748e9da renaming h316 → _p2mH316
open _root_.P2Mb748e9da renaming h317 → _p2mH317
open _root_.P2Mb748e9da renaming h318 → _p2mH318
section
namespace CurrentAFT.CurrentAffineLoad
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h253 (security : ℕ) (input : (Fin (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) → ℤ) × ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentAffineLoad.packSource security input) = input := by
  simp [_root_.CurrentAFT.CurrentAffineLoad.splitSource, _root_.CurrentAFT.CurrentAffineLoad.packSource]
open _root_.P2Mb748e9da renaming h253 → _p2mH253
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h252 (security : ℕ) (first second : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (first + second) = _root_.CurrentAFT.CurrentAffineLoad.splitSource security first + _root_.CurrentAFT.CurrentAffineLoad.splitSource security second := rfl
open _root_.P2Mb748e9da renaming h252 → _p2mH252
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h249 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    (_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input =
      _root_.CurrentAFT.CurrentAffineLoad.packSource security
        (_root_.CurrentAFT.AffineRealization.linearPart (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security)
          (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
          (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input)) := by
  change (Matrix.reindex _ _ _).mulVecLin input = _
  rw [Matrix.mulVecLin_reindex]
  change (fun index => (_root_.CurrentAFT.AffineRealization.matrix (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
    (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
      (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear).mulVec (input ∘ _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security)
        ((_root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security).symm index)) = _
  have hinput : input ∘ _root_.CurrentAFT.CurrentAffineGeometry.coordinateNumbering security =
      Sum.elim (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).1 (fun _ : Unit => (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input).2) := by
    funext index
    rcases index with edge | point
    · rfl
    · cases point; rfl
  rw [hinput, _p2mH210]
  rfl
open _root_.P2Mb748e9da renaming h249 → _p2mH249
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h250 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (scale shear : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      _root_.CurrentAFT.AffineRealization.linearPart (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security) (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
        (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core) scale shear (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input) := by
  rw [_p2mH249, _p2mH253]
open _root_.P2Mb748e9da renaming h250 → _p2mH250
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h251 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core) :
    _root_.CurrentAFT.CurrentAffineLoad.splitSource security (_root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
      _root_.CurrentAFT.AffineRealization.offsetCoordinates (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
        (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout) (_root_.CurrentAFT.CurrentAffineGeometry.centers security layout core)
        (_root_.CurrentAFT.ActualPublicCharge.legShift security core) intercept (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) closureScalar (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core)
        (_root_.CurrentAFT.CurrentAffineGeometry.centers_charge security layout core hcharge) := by
  exact _p2mH253 security _
open _root_.P2Mb748e9da renaming h251 → _p2mH251
end
open _root_.P2Mb748e9da renaming h249 → _p2mH249
open _root_.P2Mb748e9da renaming h250 → _p2mH250
open _root_.P2Mb748e9da renaming h251 → _p2mH251
open _root_.P2Mb748e9da renaming h252 → _p2mH252
open _root_.P2Mb748e9da renaming h253 → _p2mH253
end CurrentAFT.CurrentAffineLoad
open _root_.P2Mb748e9da renaming h249 → _p2mH249
open _root_.P2Mb748e9da renaming h250 → _p2mH250
open _root_.P2Mb748e9da renaming h251 → _p2mH251
open _root_.P2Mb748e9da renaming h252 → _p2mH252
open _root_.P2Mb748e9da renaming h253 → _p2mH253
end
open _root_.P2Mb748e9da renaming h249 → _p2mH249
open _root_.P2Mb748e9da renaming h250 → _p2mH250
open _root_.P2Mb748e9da renaming h251 → _p2mH251
open _root_.P2Mb748e9da renaming h252 → _p2mH252
open _root_.P2Mb748e9da renaming h253 → _p2mH253
section
namespace CurrentAFT.LobsterAffineLoad
open AFT PublicCharge LobsterCoordinates LobsterMixerMatrix AffineBaseline AffineRealization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h383 (bodyEdges legs : ℕ) (scale shear : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) :
    _root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs ((_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input) =
      ((_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).1,
        (fun leg => scale leg * (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
          shear leg * (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.2 leg,
         (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input).2.2)) := by
  apply Prod.ext
  · funext vertex
    change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inl vertex)) = _
    rw [_p2mH388, _p2mH387]
    rfl
  · apply Prod.ext
    · funext leg
      change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inr (.inl leg))) = _
      rw [_p2mH388, _p2mH387]
      rfl
    · funext leg
      change (_root_.CurrentAFT.LobsterMixerMatrix.numberedMatrix bodyEdges legs scale shear).mulVec input (_root_.CurrentAFT.LobsterCoordinates.edgeIndex bodyEdges legs (.inr (.inr leg))) = _
      rw [_p2mH388, _p2mH387]
      rfl
open _root_.P2Mb748e9da renaming h383 → _p2mH383
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h384 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin (bodyEdges + 1)) :
    _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex))) =
      if vertex ∈ Finset.univ.map queues then 1 else 0 := by
  have hequal : relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex)) ∈
      Finset.univ.map (_root_.CurrentAFT.AffineRealization.queueEmbedding bodyEdges legs modulus queues relabeling) ↔
      vertex ∈ Finset.univ.map queues := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨point, heq⟩
      exact ⟨point, Sum.inl.inj ((_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).injective (relabeling.injective heq))⟩
    · rintro ⟨point, heq⟩
      exact ⟨point, congrArg (fun vertex => relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inl vertex))) heq⟩
  simp only [_root_.CurrentAFT.AffineRealization.queueColumn, hequal]
open _root_.P2Mb748e9da renaming h384 → _p2mH384
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h385 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin legs ⊕ Fin legs) :
    _root_.CurrentAFT.AffineRealization.queueColumn bodyEdges legs modulus queues relabeling (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inr vertex))) = 0 := by
  have hnot : relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs (.inr vertex)) ∉
      Finset.univ.map (_root_.CurrentAFT.AffineRealization.queueEmbedding bodyEdges legs modulus queues relabeling) := by
    intro hmem
    obtain ⟨point, _, heq⟩ := Finset.mem_map.mp hmem
    have h := (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs).injective (relabeling.injective heq)
    cases h
  exact if_neg hnot
open _root_.P2Mb748e9da renaming h385 → _p2mH385
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h382 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear intercept : Fin legs → ℤ) (centers : Fin (bodyEdges + 1) → ℤ) (shift : Fin legs → ℤ)
    (closureScalar : ℤ) (hcharge : _root_.CurrentAFT.PublicCharge.PublicChargeTest modulus centers shift)
    (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ)
    (vertex : _root_.CurrentAFT.PublicCharge.EndpointIndex (bodyEdges + 1) (Fin legs)) :
    _root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ modulus)
      (_root_.CurrentAFT.AffineRealization.linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input +
        _root_.CurrentAFT.AffineRealization.offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge)
      (relabeling (_root_.CurrentAFT.LobsterCoordinates.vertexIndex bodyEdges legs vertex)) =
      _root_.CurrentAFT.PublicCharge.assembledEndpoint centers shift ((modulus : ℤ) - 1)
        (Fin.snoc (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input.1).1 closureScalar) placement attachment
        (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ bodyEdges legs input.1).2.2
        (_root_.CurrentAFT.LobsterAffineLoad.primary bodyEdges legs scale shear intercept input.1) (Finset.univ.map queues) input.2 vertex := by
  rw [_p2mH206]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, _p2mH386,
    Equiv.symm_apply_apply, _root_.CurrentAFT.AffineBaseline.numberedOffset, _root_.CurrentAFT.AffineBaseline.offset]
  rw [_p2mH383]
  rcases vertex with vertex | (leg | leg)
  · rw [_p2mH384]
    simp only [_root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.AffineBaseline.baseline, Sum.elim_inl, Pi.add_apply, _root_.CurrentAFT.PublicCharge.assembledEndpoint,
      _p2mH341, Pi.add_apply, _root_.CurrentAFT.PublicCharge.queueIncrement]
    split_ifs <;> ring
  · rw [_p2mH385]
    simp [_root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.AffineBaseline.baseline, _root_.CurrentAFT.PublicCharge.assembledEndpoint, _root_.CurrentAFT.LobsterAffineLoad.primary]
    ring
  · rw [_p2mH385]
    simp [_root_.CurrentAFT.LobsterIncidence.load, _root_.CurrentAFT.AffineBaseline.baseline, _root_.CurrentAFT.PublicCharge.assembledEndpoint, _root_.CurrentAFT.LobsterAffineLoad.primary, _root_.CurrentAFT.PublicCharge.legCompanion]
    ring
open _root_.P2Mb748e9da renaming h382 → _p2mH382
end
open _root_.P2Mb748e9da renaming h382 → _p2mH382
open _root_.P2Mb748e9da renaming h383 → _p2mH383
open _root_.P2Mb748e9da renaming h384 → _p2mH384
open _root_.P2Mb748e9da renaming h385 → _p2mH385
end CurrentAFT.LobsterAffineLoad
open _root_.P2Mb748e9da renaming h382 → _p2mH382
open _root_.P2Mb748e9da renaming h383 → _p2mH383
open _root_.P2Mb748e9da renaming h384 → _p2mH384
open _root_.P2Mb748e9da renaming h385 → _p2mH385
end
open _root_.P2Mb748e9da renaming h382 → _p2mH382
open _root_.P2Mb748e9da renaming h383 → _p2mH383
open _root_.P2Mb748e9da renaming h384 → _p2mH384
open _root_.P2Mb748e9da renaming h385 → _p2mH385
namespace CurrentAFT.AffineBaseline.numberedOffset
end CurrentAFT.AffineBaseline.numberedOffset
namespace CurrentAFT.CurrentAffineGeometry.unitToFinOne
end CurrentAFT.CurrentAffineGeometry.unitToFinOne
namespace CurrentAFT.CurrentAffineLoad
end CurrentAFT.CurrentAffineLoad
namespace CurrentAFT.CurrentAffineLoad.packSource
end CurrentAFT.CurrentAffineLoad.packSource
namespace CurrentAFT.CurrentAffineLoad.splitSource
end CurrentAFT.CurrentAffineLoad.splitSource
namespace CurrentAFT.CurrentSourceLayout
end CurrentAFT.CurrentSourceLayout
namespace CurrentAFT.CurrentSourceLayout.auxNumbering
end CurrentAFT.CurrentSourceLayout.auxNumbering
namespace CurrentAFT.CurrentSourceLayout.bodyNumbering
end CurrentAFT.CurrentSourceLayout.bodyNumbering
namespace CurrentAFT.CurrentSourceLayout.closureScalar
end CurrentAFT.CurrentSourceLayout.closureScalar
namespace CurrentAFT.CurrentSourceLayout.hiddenCutoff
end CurrentAFT.CurrentSourceLayout.hiddenCutoff
namespace CurrentAFT.CurrentSourceLayout.hiddenWord
end CurrentAFT.CurrentSourceLayout.hiddenWord
namespace CurrentAFT.CurrentSourceLayout.moveClosure
end CurrentAFT.CurrentSourceLayout.moveClosure
namespace CurrentAFT.CurrentSourceLayout.moveClosure.match_1
end CurrentAFT.CurrentSourceLayout.moveClosure.match_1
namespace CurrentAFT.CurrentSourceLayout.moveClosure.match_3
end CurrentAFT.CurrentSourceLayout.moveClosure.match_3
namespace CurrentAFT.CurrentSourceLayout.sourceNumbering
end CurrentAFT.CurrentSourceLayout.sourceNumbering
namespace CurrentAFT.CurrentSourceProtection.auxPosition
end CurrentAFT.CurrentSourceProtection.auxPosition
namespace CurrentAFT.CurrentSourceProtection.bodyPosition
end CurrentAFT.CurrentSourceProtection.bodyPosition
namespace CurrentAFT.LobsterAffineLoad
end CurrentAFT.LobsterAffineLoad
namespace CurrentAFT.LobsterAffineLoad.primary
end CurrentAFT.LobsterAffineLoad.primary
section
namespace CurrentAFT.CurrentAffineEndpoint
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentSourceProtection CurrentSourceLayout
  PublicEndpointPlacement PublicCharge LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
private theorem _root_.P2Mb748e9da.h463 {body other : ℕ} (heq : body = other)
    (centers latent : Fin body → ℤ) {Leg : Type*} [Fintype Leg]
    (shift second primary : Leg → ℤ) (legConstant : ℤ) (permutation : Equiv.Perm (Fin body))
    (attachment : Leg → Fin body) {count : ℕ} (queue : Fin count ↪ Fin body) (scalar : ℤ)
    (vertex : _root_.CurrentAFT.PublicCharge.EndpointIndex body Leg) :
    _root_.CurrentAFT.PublicCharge.assembledEndpoint (fun index => centers ((finCongr heq).symm index)) shift legConstant
      (fun index => latent ((finCongr heq).symm index))
      ((finCongr heq).symm.trans (permutation.trans (finCongr heq)))
      (fun leg => finCongr heq (attachment leg)) second primary
      (Finset.univ.map (queue.trans (finCongr heq).toEmbedding)) scalar
      (Sum.map (finCongr heq) id vertex) =
        _root_.CurrentAFT.PublicCharge.assembledEndpoint centers shift legConstant latent permutation attachment second primary
          (Finset.univ.map queue) scalar vertex := by
  subst other
  simp
open _root_.P2Mb748e9da renaming h463 → _p2mH463
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h240 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (scale shear intercept : Fin (_root_.CurrentAFT.Parameters.legCount security) → ℤ)
    (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core) (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ)
    (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffineLoad.rounding security
      ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core scale shear).mulVec (_root_.CurrentAFT.CurrentSourceLayout.hiddenWord security word) +
        _root_.CurrentAFT.CurrentAffineGeometry.offset security layout core intercept (_root_.CurrentAFT.CurrentSourceLayout.closureScalar security word) hcharge)
      (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
        _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core scale shear intercept word vertex := by
  letI : NeZero (_root_.CurrentAFT.Parameters.modulus security) := ⟨(_root_.CurrentAFT.Parameters.modulus_spec security).2.ne_zero⟩
  have hindex : (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm
      (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
        _root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.LobsterCoordinates.vertexIndex (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
          (Sum.map (_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security) id vertex)) := by
    apply (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply]
    change core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex) =
      _root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security (_root_.CurrentAFT.CurrentAffineGeometry.relabeling security layout core (_root_.CurrentAFT.CurrentAffineGeometry.naturalNumbering security vertex))
    exact (_p2mH241 security layout core vertex).symm
  unfold _root_.CurrentAFT.CurrentAffineLoad.rounding
  rw [_p2mH252, _p2mH250, _p2mH251, hindex]
  rw [_p2mH382]
  change _root_.CurrentAFT.PublicCharge.assembledEndpoint (_root_.CurrentAFT.CurrentAffineGeometry.centers security layout core) (_root_.CurrentAFT.ActualPublicCharge.legShift security core)
    ((_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1)
    (Fin.snoc (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1).1 (_root_.CurrentAFT.CurrentSourceLayout.closureScalar security word))
    (_root_.CurrentAFT.CurrentAffineGeometry.placement security core) (_root_.CurrentAFT.CurrentAffineGeometry.attachments security layout)
    (_root_.CurrentAFT.LobsterCoordinates.edgeCoordinates ℤ (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1).2.2
    (_root_.CurrentAFT.LobsterAffineLoad.primary (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      scale shear intercept (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1)
    (Finset.univ.map (_root_.CurrentAFT.CurrentAffineGeometry.queues security layout)) (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).2
    (Sum.map (_root_.CurrentAFT.CurrentAffineGeometry.bodyEquiv security) id vertex) = _
  rw [_p2mH308, _p2mH312, _p2mH311]
  have hprimary : _root_.CurrentAFT.LobsterAffineLoad.primary (_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges security) (_root_.CurrentAFT.Parameters.legCount security)
      scale shear intercept (_root_.CurrentAFT.CurrentSourceLayout.hiddenCoordinates security word).1 =
        _root_.CurrentAFT.CurrentAffineEndpoint.primaryOutput security scale shear intercept word := by
    unfold _root_.CurrentAFT.LobsterAffineLoad.primary _root_.CurrentAFT.CurrentAffineEndpoint.primaryOutput
    rw [_p2mH310, _p2mH312]
  rw [hprimary]
  exact _p2mH463 (by have := _root_.CurrentAFT.LobsterCoordinates.current_body_positive security; dsimp only [_root_.CurrentAFT.CurrentAffineGeometry.bodyEdges]; omega)
    (_root_.CurrentAFT.ActualPublicCharge.centerAt security layout core) (_root_.CurrentAFT.CurrentSourceLayout.bodyLatent security word) (_root_.CurrentAFT.ActualPublicCharge.legShift security core)
    (_root_.CurrentAFT.CurrentSourceLayout.secondInput security word) (_root_.CurrentAFT.CurrentAffineEndpoint.primaryOutput security scale shear intercept word)
    ((_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1) core.bodyPermutation
    (_root_.CurrentAFT.ActualPublicCharge.attachmentPosition security layout) (_root_.CurrentAFT.ActualPublicCharge.queuePosition security layout) (_root_.CurrentAFT.CurrentSourceLayout.queueInput security word) vertex
open _root_.P2Mb748e9da renaming h240 → _p2mH240
end
open _root_.P2Mb748e9da renaming h240 → _p2mH240
open _root_.P2Mb748e9da renaming h463 → _p2mH463
end CurrentAFT.CurrentAffineEndpoint
open _root_.P2Mb748e9da renaming h240 → _p2mH240
open _root_.P2Mb748e9da renaming h463 → _p2mH463
end
open _root_.P2Mb748e9da renaming h240 → _p2mH240
section
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration
open scoped Classical
noncomputable section
variable {F I : Type*} [Field F] [Fintype F] [Fintype I]
variable {inputs : I → F × F} {allowed : I → Finset F} {mark : F} {atom : ℝ}
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h185 (model : _root_.CurrentAFT.AffineFlagCalibration.SimultaneousLaw inputs allowed mark atom)
    (chart : _root_.AFT.BoundaryCalibration.Chart F) (hweight : model.joint.weight (false, chart) ≠ 0) :
    chart.2.1 ≠ 0 ∧ ∀ i, _root_.AFT.BoundaryCalibration.feature (inputs i).1 (inputs i).2 chart ∈ allowed i := by
  by_contra hn
  apply hweight
  rw [model.decomposition, model.regular_support chart hn]
  simp
open _root_.P2Mb748e9da renaming h185 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.regular_of_supported
open _root_.P2Mb748e9da renaming h185 → _p2mH185
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h183 (model : _root_.CurrentAFT.AffineFlagCalibration.SimultaneousLaw inputs allowed mark atom)
    (chart : _root_.AFT.BoundaryCalibration.Chart F) (hweight : model.joint.weight (true, chart) ≠ 0) :
    chart.1 = mark ∧ chart.2.2 = 0 ∧ chart.2.1 ≠ 0 ∧
      ∀ i, (inputs i).1 ≠ 0 → _root_.AFT.BoundaryCalibration.feature (inputs i).1 (inputs i).2 chart ∈ allowed i := by
  by_contra hn
  apply hweight
  rw [model.decomposition, model.marked_support chart hn]
  simp
open _root_.P2Mb748e9da renaming h183 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_of_supported
open _root_.P2Mb748e9da renaming h183 → _p2mH183
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h186 (model : _root_.CurrentAFT.AffineFlagCalibration.SimultaneousLaw inputs allowed mark atom)
    (point : Bool × _root_.AFT.BoundaryCalibration.Chart F) (hweight : model.joint.weight point ≠ 0)
    (i : I) (hi : (inputs i).1 ≠ 0) : _root_.AFT.BoundaryCalibration.feature (inputs i).1 (inputs i).2 point.2 ∈ allowed i := by
  rcases point with ⟨flag, chart⟩
  cases flag
  · exact (model.regular_of_supported chart hweight).2 i
  · exact (model.marked_of_supported chart hweight).2.2.2 i hi
open _root_.P2Mb748e9da renaming h186 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.supported_off_line
open _root_.P2Mb748e9da renaming h186 → _p2mH186
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h184 (model : _root_.CurrentAFT.AffineFlagCalibration.SimultaneousLaw inputs allowed mark atom)
    (chart : _root_.AFT.BoundaryCalibration.Chart F) (hweight : model.joint.weight (true, chart) ≠ 0)
    (i : I) (hi : (inputs i).1 = 0) : _root_.AFT.BoundaryCalibration.feature (inputs i).1 (inputs i).2 chart = mark := by
  obtain ⟨hbase, hshear, _, _⟩ := model.marked_of_supported chart hweight
  simp only [_root_.AFT.BoundaryCalibration.feature, hi, hshear, mul_zero, zero_mul, add_zero, hbase]
open _root_.P2Mb748e9da renaming h184 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_on_line
open _root_.P2Mb748e9da renaming h184 → _p2mH184
end
open _root_.P2Mb748e9da renaming h183 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_of_supported
open _root_.P2Mb748e9da renaming h183 → _p2mH183
open _root_.P2Mb748e9da renaming h184 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_on_line
open _root_.P2Mb748e9da renaming h184 → _p2mH184
open _root_.P2Mb748e9da renaming h185 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.regular_of_supported
open _root_.P2Mb748e9da renaming h185 → _p2mH185
open _root_.P2Mb748e9da renaming h186 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.supported_off_line
open _root_.P2Mb748e9da renaming h186 → _p2mH186
end CurrentAFT.AffineFlagCalibration
open _root_.P2Mb748e9da renaming h183 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_of_supported
open _root_.P2Mb748e9da renaming h183 → _p2mH183
open _root_.P2Mb748e9da renaming h184 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_on_line
open _root_.P2Mb748e9da renaming h184 → _p2mH184
open _root_.P2Mb748e9da renaming h185 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.regular_of_supported
open _root_.P2Mb748e9da renaming h185 → _p2mH185
open _root_.P2Mb748e9da renaming h186 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.supported_off_line
open _root_.P2Mb748e9da renaming h186 → _p2mH186
end
open _root_.P2Mb748e9da renaming h183 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_of_supported
open _root_.P2Mb748e9da renaming h183 → _p2mH183
open _root_.P2Mb748e9da renaming h184 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.marked_on_line
open _root_.P2Mb748e9da renaming h184 → _p2mH184
open _root_.P2Mb748e9da renaming h185 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.regular_of_supported
open _root_.P2Mb748e9da renaming h185 → _p2mH185
open _root_.P2Mb748e9da renaming h186 → CurrentAFT.AffineFlagCalibration.SimultaneousLaw.supported_off_line
open _root_.P2Mb748e9da renaming h186 → _p2mH186
section
namespace CurrentAFT.CurrentAffineLegCarry
open AFT AFT.BoundaryCalibration AffineFlagCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.CurrentAffineLegCarry.modulusPrime
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h244 (modulus : ℕ) [NeZero modulus] (value : ZMod modulus) :
    ((ZMod.finEquiv modulus).symm value).val = value.val := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => rfl
open _root_.P2Mb748e9da renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h245 (security : ℕ) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security) (first second : ℤ) :
    (_root_.CurrentAFT.CurrentAffineLegCarry.integerPrimary security chart first second : ZMod (_root_.CurrentAFT.Parameters.modulus security)) =
      _root_.AFT.BoundaryCalibration.feature (first : ZMod (_root_.CurrentAFT.Parameters.modulus security)) (second : ZMod (_root_.CurrentAFT.Parameters.modulus security)) chart.2 := by
  simp [_root_.CurrentAFT.CurrentAffineLegCarry.integerPrimary, _root_.AFT.BoundaryCalibration.feature]
open _root_.P2Mb748e9da renaming h245 → _p2mH245
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h243 (security : ℕ) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    ((_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second).val : ℤ) =
      _root_.CurrentAFT.CurrentAffineLegCarry.integerPrimary security chart first.val second.val % _root_.CurrentAFT.Parameters.modulus security := by
  rw [← ZMod.val_intCast, _p2mH245]
  exact congrArg (fun value : ℕ => (value : ℤ)) (_p2mH244 _ _)
open _root_.P2Mb748e9da renaming h243 → _p2mH243
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h242 (security : ℕ) (shift : ℤ) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    ((_root_.CurrentAFT.AffineFlagCalibration.companion security (shift - second.val) (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second)).val : ℤ) =
      _root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion security shift chart first.val second.val % _root_.CurrentAFT.Parameters.modulus security := by
  rw [← ZMod.val_intCast]
  unfold _root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion
  push_cast
  rw [ZMod.natCast_self, zero_sub, _p2mH245]
  change (((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).symm
    (-1 + ((shift - second.val : ℤ) : ZMod (_root_.CurrentAFT.Parameters.modulus security)) -
      (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security))
        ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).symm
          (_root_.AFT.BoundaryCalibration.feature ((first.val : ℤ) : ZMod (_root_.CurrentAFT.Parameters.modulus security))
            ((second.val : ℤ) : ZMod (_root_.CurrentAFT.Parameters.modulus security)) chart.2)))).val : ℤ) = _
  rw [RingEquiv.apply_symm_apply, _p2mH244]
  push_cast
  congr 2
  ring
open _root_.P2Mb748e9da renaming h242 → _p2mH242
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h248 (security : ℕ) (shift : ℤ) (color : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (hcolor : (color.val : ℤ) ∈ _root_.AFT.TrimmedSlice.slice (_root_.CurrentAFT.Parameters.modulus security) 1 shift) :
    (color.val : ℤ) + (_root_.CurrentAFT.AffineFlagCalibration.companion security shift color).val =
      (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 + shift := by
  have h := (_p2mH190 security shift color (_root_.CurrentAFT.AffineFlagCalibration.companion security shift color) hcolor).mp rfl
  omega
open _root_.P2Mb748e9da renaming h248 → _p2mH248
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h247 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (hchart : (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security primary seed).weight chart ≠ 0)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    ((_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second).val : ℤ) +
      (_root_.CurrentAFT.AffineFlagCalibration.companion security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val)
        (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second)).val =
      (_root_.CurrentAFT.Parameters.modulus security : ℤ) - 1 + _root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val := by
  let input : _root_.CurrentAFT.AffineFlagCalibration.ProtectedInput security := (first, second)
  let model := _root_.CurrentAFT.AffineFlagCalibration.currentLaw security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed)
    (by simpa only [_root_.CurrentAFT.AffineFlagCalibration.legOffsetBound, add_sub_assoc] using _root_.CurrentAFT.ActualPublicLegCharge.publicShift_bound security primary seed)
    ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) primary) (1 / 2) (by norm_num) (by norm_num)
  have hsupport : model.joint.weight chart ≠ 0 := hchart
  have htrimmed (hallowed : _root_.AFT.BoundaryCalibration.feature
      (_root_.AFT.BoundaryCalibration.protectedInputs (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) input).1
      (_root_.AFT.BoundaryCalibration.protectedInputs (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) input).2 chart.2 ∈
        _root_.AFT.BoundaryCalibration.protectedPalettes (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) 1
          (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed) input) :
      ((_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second).val : ℤ) ∈
        _root_.AFT.TrimmedSlice.slice (_root_.CurrentAFT.Parameters.modulus security) 1 (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val) := by
    simpa only [_root_.AFT.BoundaryCalibration.protectedPalettes, _root_.AFT.BoundaryCalibration.fieldPalette, Finset.mem_map_equiv, _root_.AFT.BoundaryCalibration.protectedInputs, input,
      _root_.AFT.TrimmedSlice.paletteSlice, Finset.mem_filter, Finset.mem_univ, true_and, _root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary] using hallowed
  have hfinish (hallowed : _root_.AFT.BoundaryCalibration.feature
      (_root_.AFT.BoundaryCalibration.protectedInputs (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) input).1
      (_root_.AFT.BoundaryCalibration.protectedInputs (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) input).2 chart.2 ∈
        _root_.AFT.BoundaryCalibration.protectedPalettes (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) (_root_.CurrentAFT.Parameters.modulus security) 1
          (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed) input) := _p2mH248 security
            (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val) _ (htrimmed hallowed)
  rcases chart with ⟨flag, chart⟩
  cases flag
  · have h := hfinish ((model.regular_of_supported chart hsupport).2 input)
    omega
  · by_cases hfirst : first.val = 0
    · have hon := model.marked_on_line chart hsupport input
        ((_p2mH202 security input).mpr hfirst)
      have heval : _root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security (true, chart) first second = primary := by
        unfold _root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary
        change (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).symm
          (_root_.AFT.BoundaryCalibration.feature (_root_.AFT.BoundaryCalibration.protectedInputs _ _ input).1 (_root_.AFT.BoundaryCalibration.protectedInputs _ _ input).2 chart) = primary
        rw [hon, RingEquiv.symm_apply_apply]
      rw [heval]
      have hp := _p2mH200 security primary second seed
      have hc := _p2mH165 security primary second seed
        (primary, _root_.CurrentAFT.ActualPublicLegCharge.markedPoint security primary second seed) (by rw [_p2mH166]; simp)
      have he := congrArg Prod.snd hp
      change _root_.CurrentAFT.AffineFlagCalibration.companion security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed - second.val) primary = _ at he
      rw [he]
      exact hc
    · have h := hfinish (model.supported_off_line (true, chart) hsupport input
        (fun hz => hfirst ((_p2mH202 security input).mp hz)))
      omega
open _root_.P2Mb748e9da renaming h247 → _p2mH247
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h246 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (hchart : (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security primary seed).weight chart ≠ 0)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    _root_.CurrentAFT.CurrentAffineLegCarry.integerPrimary security chart first.val second.val / _root_.CurrentAFT.Parameters.modulus security +
      _root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed) chart first.val second.val /
        _root_.CurrentAFT.Parameters.modulus security = 0 := by
  have hsum := _p2mH247 security primary seed chart hchart first second
  rw [_p2mH243, _p2mH242] at hsum
  have hfirst := Int.emod_add_mul_ediv (_root_.CurrentAFT.CurrentAffineLegCarry.integerPrimary security chart first.val second.val)
    (_root_.CurrentAFT.Parameters.modulus security : ℤ)
  have hsecond := Int.emod_add_mul_ediv
    (_root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed) chart first.val second.val)
    (_root_.CurrentAFT.Parameters.modulus security : ℤ)
  have hq : (0 : ℤ) < _root_.CurrentAFT.Parameters.modulus security := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.pos
  unfold _root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion at *
  nlinarith
open _root_.P2Mb748e9da renaming h246 → _p2mH246
end
open _root_.P2Mb748e9da renaming h242 → _p2mH242
open _root_.P2Mb748e9da renaming h243 → _p2mH243
open _root_.P2Mb748e9da renaming h244 → _p2mH244
open _root_.P2Mb748e9da renaming h245 → _p2mH245
open _root_.P2Mb748e9da renaming h246 → _p2mH246
open _root_.P2Mb748e9da renaming h247 → _p2mH247
open _root_.P2Mb748e9da renaming h248 → _p2mH248
end CurrentAFT.CurrentAffineLegCarry
open _root_.P2Mb748e9da renaming h242 → _p2mH242
open _root_.P2Mb748e9da renaming h243 → _p2mH243
open _root_.P2Mb748e9da renaming h244 → _p2mH244
open _root_.P2Mb748e9da renaming h245 → _p2mH245
open _root_.P2Mb748e9da renaming h246 → _p2mH246
open _root_.P2Mb748e9da renaming h247 → _p2mH247
open _root_.P2Mb748e9da renaming h248 → _p2mH248
end
open _root_.P2Mb748e9da renaming h242 → _p2mH242
open _root_.P2Mb748e9da renaming h243 → _p2mH243
open _root_.P2Mb748e9da renaming h244 → _p2mH244
open _root_.P2Mb748e9da renaming h245 → _p2mH245
open _root_.P2Mb748e9da renaming h246 → _p2mH246
open _root_.P2Mb748e9da renaming h247 → _p2mH247
open _root_.P2Mb748e9da renaming h248 → _p2mH248
namespace CurrentAFT.AffineFlagCalibration.evaluatePrimary
end CurrentAFT.AffineFlagCalibration.evaluatePrimary
namespace CurrentAFT.CurrentAffineLegCarry
end CurrentAFT.CurrentAffineLegCarry
namespace CurrentAFT.CurrentAffineLegCarry.integerPrimary
end CurrentAFT.CurrentAffineLegCarry.integerPrimary
section
namespace CurrentAFT.CurrentAffineData
open AFT CurrentAffineGeometry CurrentAffineLegCarry ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean AffineFlagCalibration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.CurrentAffineData.modulusPrime
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h238 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (charts : _root_.CurrentAFT.CurrentAffineData.Charts security) (closure : ℤ) (hvalid : _root_.CurrentAFT.CurrentAffineData.Valid security core charts) :
    _root_.CurrentAFT.CurrentAffineData.assemble security layout core charts closure = _root_.CurrentAFT.CurrentAffineData.assembled security layout core charts closure hvalid := by
  simp only [_root_.CurrentAFT.CurrentAffineData.assemble, dif_pos hvalid]
open _root_.P2Mb748e9da renaming h238 → _p2mH238
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h239 (security : ℕ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicLegCharge.PublicSeed security) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (hchart : (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security primary seed).weight chart ≠ 0) : chart.2.2.1 ≠ 0 :=
  _p2mH193 security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed)
    (by simpa only [_root_.CurrentAFT.AffineFlagCalibration.legOffsetBound, add_sub_assoc] using _root_.CurrentAFT.ActualPublicLegCharge.publicShift_bound security primary seed)
    ((ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) primary) (1 / 2) (by norm_num) (by norm_num) chart hchart
open _root_.P2Mb748e9da renaming h239 → _p2mH239
end
open _root_.P2Mb748e9da renaming h238 → _p2mH238
open _root_.P2Mb748e9da renaming h239 → _p2mH239
end CurrentAFT.CurrentAffineData
open _root_.P2Mb748e9da renaming h238 → _p2mH238
open _root_.P2Mb748e9da renaming h239 → _p2mH239
end
open _root_.P2Mb748e9da renaming h238 → _p2mH238
open _root_.P2Mb748e9da renaming h239 → _p2mH239
section
namespace CurrentAFT.CurrentPublicSupport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean ProposalPrimary
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h303 {Source Target : Type*} [Fintype Source] [Fintype Target]
    (law : _root_.AFT.FiniteDist Source) (record : Source → Target) (property : Target → Prop)
    (hproperty : ∀ source, law.weight source ≠ 0 → property (record source)) :
    ∀ target, (law.map record).weight target ≠ 0 → property target := by
  intro target hweight
  by_contra hbad
  apply hweight
  rw [_root_.AFT.FiniteDist.map_weight]
  apply Finset.sum_eq_zero
  intro source _
  split_ifs with hequal
  · by_contra hsource
    exact hbad (hequal ▸ hproperty source hsource)
  · rfl
open _root_.P2Mb748e9da renaming h303 → _p2mH303
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h307 (security : ℕ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security))
    (hweight : (_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight color ≠ 0) : _root_.CurrentAFT.InwardAnchor.SafeColor security color := by
  by_contra hbad
  exact hweight (by rw [_root_.CurrentAFT.ProposalPrimary.safeLaw_weight, if_neg hbad])
open _root_.P2Mb748e9da renaming h307 → _p2mH307
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h306 (security : ℕ) (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (hweight : (_root_.CurrentAFT.ActualPublicCharge.proposal security).weight core ≠ 0) : _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core := by
  unfold _root_.CurrentAFT.ActualPublicCharge.proposal at hweight
  apply _p2mH303 _ _ (_root_.CurrentAFT.CurrentPublicSupport.SafeCore security) _ core hweight
  intro draw hdraw
  constructor
  · intro leg
    apply _p2mH307
    intro hzero
    have hleg : (_root_.CurrentAFT.ActualPublicCharge.legCoreLaw security).weight (draw.1.1.1.2 leg) = 0 := by
      change (_root_.CurrentAFT.ActualPublicLegCharge.seedLaw security).weight (draw.1.1.1.2 leg).1 *
        (_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight (draw.1.1.1.2 leg).2 = 0
      rw [hzero, mul_zero]
    have hproduct : (∏ index, (_root_.CurrentAFT.ActualPublicCharge.legCoreLaw security).weight (draw.1.1.1.2 index)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ leg) hleg
    apply hdraw
    simp only [_root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.independent, hproduct, mul_zero, zero_mul]
  · intro point
    apply _p2mH307
    intro hzero
    have hproduct : (∏ index, (_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight (draw.1.1.2 index)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ point) hzero
    apply hdraw
    simp only [_root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.independent, hproduct, mul_zero, zero_mul]
open _root_.P2Mb748e9da renaming h306 → _p2mH306
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h304 {State : Type*} [Fintype State]
    (reference : _root_.AFT.FiniteDist State) (weight : State → ℝ) (charge : State → Prop)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass reference weight charge) (state : State)
    (hweight : (_root_.CurrentAFT.positivePublicCoreLaw reference weight charge hpositive).weight state ≠ 0) :
    charge state ∧ reference.weight state ≠ 0 := by
  change _root_.CurrentAFT.clippedPublicCoreWeight reference weight charge state /
    (∑ value, _root_.CurrentAFT.clippedPublicCoreWeight reference weight charge value) ≠ 0 at hweight
  have hnumerator := (div_ne_zero_iff.mp hweight).1
  unfold _root_.CurrentAFT.clippedPublicCoreWeight at hnumerator
  by_cases hcharge : charge state
  · rw [if_pos hcharge] at hnumerator
    exact ⟨hcharge, (mul_ne_zero_iff.mp hnumerator).1⟩
  · simp only [if_neg hcharge, ne_eq, not_true_eq_false] at hnumerator
open _root_.P2Mb748e9da renaming h304 → _p2mH304
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h305 (security : ℕ) (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security)
    (hweight : (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).weight core ≠ 0) :
    _root_.CurrentAFT.ActualPublicCharge.publicCharge security core ∧ _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core := by
  have hsupport := _p2mH304 (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive core hweight
  exact ⟨hsupport.1, _p2mH306 security core hsupport.2⟩
open _root_.P2Mb748e9da renaming h305 → _p2mH305
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h302 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (hsafe : _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core) (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    (_root_.CurrentAFT.Parameters.safeMargin security : ℤ) ≤ _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex ∧
      _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex < (_root_.CurrentAFT.Parameters.modulus security : ℤ) - _root_.CurrentAFT.Parameters.safeMargin security := by
  unfold _root_.CurrentAFT.ActualPublicCharge.centerAt
  generalize layout.symm vertex = role
  rcases role with center | (point | leg)
  · exact (core.controls ((_root_.CurrentAFT.UniformTaggedOutput.centerSplit security).symm center)).2.property
  · exact hsafe.2 point
  · exact hsafe.1 leg
open _root_.P2Mb748e9da renaming h302 → _p2mH302
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h301 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (hsafe : _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core) (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (increment : ℤ) (hbound : |increment| ≤ _root_.CurrentAFT.Parameters.safeMargin security) :
    (_root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex + increment) / _root_.CurrentAFT.Parameters.modulus security = 0 ∧
      (_root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex + increment) % _root_.CurrentAFT.Parameters.modulus security =
        _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex + increment := by
  have hcenter := _p2mH302 security layout core hsafe vertex
  have hincrement := abs_le.mp hbound
  have hlo : 0 ≤ _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex + increment := by omega
  have hhi : _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex + increment < _root_.CurrentAFT.Parameters.modulus security := by omega
  exact ⟨Int.ediv_eq_zero_of_lt hlo hhi, Int.emod_eq_of_lt hlo hhi⟩
open _root_.P2Mb748e9da renaming h301 → _p2mH301
end
open _root_.P2Mb748e9da renaming h301 → _p2mH301
open _root_.P2Mb748e9da renaming h302 → _p2mH302
open _root_.P2Mb748e9da renaming h303 → _p2mH303
open _root_.P2Mb748e9da renaming h304 → _p2mH304
open _root_.P2Mb748e9da renaming h305 → _p2mH305
open _root_.P2Mb748e9da renaming h306 → _p2mH306
open _root_.P2Mb748e9da renaming h307 → _p2mH307
end CurrentAFT.CurrentPublicSupport
open _root_.P2Mb748e9da renaming h301 → _p2mH301
open _root_.P2Mb748e9da renaming h302 → _p2mH302
open _root_.P2Mb748e9da renaming h303 → _p2mH303
open _root_.P2Mb748e9da renaming h304 → _p2mH304
open _root_.P2Mb748e9da renaming h305 → _p2mH305
open _root_.P2Mb748e9da renaming h306 → _p2mH306
open _root_.P2Mb748e9da renaming h307 → _p2mH307
end
open _root_.P2Mb748e9da renaming h301 → _p2mH301
open _root_.P2Mb748e9da renaming h302 → _p2mH302
open _root_.P2Mb748e9da renaming h303 → _p2mH303
open _root_.P2Mb748e9da renaming h304 → _p2mH304
open _root_.P2Mb748e9da renaming h305 → _p2mH305
open _root_.P2Mb748e9da renaming h306 → _p2mH306
open _root_.P2Mb748e9da renaming h307 → _p2mH307
namespace CurrentAFT.CurrentAffineData
end CurrentAFT.CurrentAffineData
namespace CurrentAFT.CurrentAffineData.Data
end CurrentAFT.CurrentAffineData.Data
namespace CurrentAFT.CurrentAffineData.Data.eval
end CurrentAFT.CurrentAffineData.Data.eval
namespace CurrentAFT.CurrentAffineData.Data.mk
end CurrentAFT.CurrentAffineData.Data.mk
namespace CurrentAFT.CurrentAffineData.assemble
end CurrentAFT.CurrentAffineData.assemble
namespace CurrentAFT.CurrentAffineData.assembled
end CurrentAFT.CurrentAffineData.assembled
namespace CurrentAFT.CurrentAffineData.fallback
end CurrentAFT.CurrentAffineData.fallback
namespace CurrentAFT.CurrentAffineData.scales
end CurrentAFT.CurrentAffineData.scales
namespace CurrentAFT.CurrentAffineEndpoint
end CurrentAFT.CurrentAffineEndpoint
namespace CurrentAFT.CurrentPublicSupport
end CurrentAFT.CurrentPublicSupport
section
namespace CurrentAFT.CurrentAffineProtectedCarry
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge PublicCharge
  CurrentSourceProtection CurrentSourceLayout CurrentAffineEndpoint CurrentAffineGeometry
  CurrentAffineData CurrentAffineLegCarry CurrentPublicSupport GaussianProductProtection
  PublicEndpointPlacement
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h262 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) (center : Fin (_root_.CurrentAFT.ActualBlockFock.centerCount security)) :
    _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra security layout word (layout (.inl center)) = 0 := by
  simp [_root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition, _root_.CurrentAFT.PublicCharge.queueIncrement, _root_.CurrentAFT.ActualPublicCharge.queueSet, _root_.CurrentAFT.ActualPublicCharge.queuePosition]
open _root_.P2Mb748e9da renaming h262 → _p2mH262
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h263 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) (point : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra security layout word (layout (.inr (.inl point))) = _root_.CurrentAFT.CurrentSourceLayout.queueInput security word := by
  simp [_root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition, _root_.CurrentAFT.PublicCharge.queueIncrement, _root_.CurrentAFT.ActualPublicCharge.queueSet, _root_.CurrentAFT.ActualPublicCharge.queuePosition]
open _root_.P2Mb748e9da renaming h263 → _p2mH263
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h261 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (word : Fin (_root_.CurrentAFT.CurrentSourceProtection.sourceCount security) → ℤ) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra security layout word (layout (.inr (.inr leg))) = _root_.CurrentAFT.CurrentSourceLayout.secondInput security word leg := by
  simp [_root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra, _root_.CurrentAFT.PublicCharge.attachmentIncrement, _root_.CurrentAFT.ActualPublicCharge.attachmentPosition, _root_.CurrentAFT.PublicCharge.queueIncrement, _root_.CurrentAFT.ActualPublicCharge.queueSet, _root_.CurrentAFT.ActualPublicCharge.queuePosition]
open _root_.P2Mb748e9da renaming h261 → _p2mH261
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h269 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    |_root_.CurrentAFT.PublicCharge.cycleDifference (_root_.CurrentAFT.CurrentSourceLayout.bodyLatent security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word))
      (permutation.symm vertex)| < _root_.CurrentAFT.Parameters.sourceCutoff security := by
  unfold _root_.CurrentAFT.CurrentSourceLayout.bodyLatent
  simpa only [Equiv.refl_symm, Equiv.refl_apply, _root_.CurrentAFT.CurrentSourceProtection.protectedBody, _root_.CurrentAFT.GaussianProductProtection.sourceEmbedding, Function.Embedding.coeFn_mk] using
    _p2mH322 security word (Equiv.refl _) (permutation.symm vertex)
open _root_.P2Mb748e9da renaming h269 → _p2mH269
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h268 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (index : Fin (_root_.CurrentAFT.Parameters.legCount security * 2 + 1)) :
    |_root_.CurrentAFT.PublicCharge.cycleDifference (_root_.CurrentAFT.CurrentSourceLayout.bodyLatent security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word))
      (permutation.symm vertex) + (_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word index).val| <
        _root_.CurrentAFT.Parameters.safeMargin security := by
  unfold _root_.CurrentAFT.CurrentSourceLayout.bodyLatent
  simpa only [Equiv.refl_symm, Equiv.refl_apply, _root_.CurrentAFT.CurrentSourceProtection.protectedBody, _root_.CurrentAFT.GaussianProductProtection.sourceEmbedding, Function.Embedding.coeFn_mk] using
    _p2mH323 security word (Equiv.refl _) (permutation.symm vertex) index
open _root_.P2Mb748e9da renaming h268 → _p2mH268
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h264 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    |_root_.CurrentAFT.PublicCharge.cycleDifference (_root_.CurrentAFT.CurrentSourceLayout.bodyLatent security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word))
      (core.bodyPermutation.symm vertex) +
      _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra security layout (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) vertex| ≤
        _root_.CurrentAFT.Parameters.safeMargin security := by
  obtain ⟨center | (point | leg), rfl⟩ := layout.surjective vertex
  · rw [_p2mH262, add_zero]
    have hroot := _p2mH269 security word core.bodyPermutation (layout (.inl center))
    have hp := _p2mH324 security
    unfold _root_.CurrentAFT.Parameters.safeMargin
    push_cast
    omega
  · rw [_p2mH263]
    exact (_p2mH268 security word core.bodyPermutation
      (layout (.inr (.inl point))) (Fin.last (_root_.CurrentAFT.Parameters.legCount security * 2))).le
  · rw [_p2mH261]
    exact (_p2mH268 security word core.bodyPermutation
      (layout (.inr (.inr leg))) (_root_.CurrentAFT.CurrentSourceLayout.auxNumbering security (.inl (.inr leg)))).le
open _root_.P2Mb748e9da renaming h264 → _p2mH264
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h265 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (hsafe : _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security)
    (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
      (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) (.inl vertex) /
        _root_.CurrentAFT.Parameters.modulus security = 0 := by
  have h := (_p2mH301 security layout core hsafe vertex _
    (_p2mH264 security layout core word vertex)).1
  convert h using 1
  unfold _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly _root_.CurrentAFT.PublicCharge.assembledEndpoint _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra
  congr 1
  ring
open _root_.P2Mb748e9da renaming h265 → _p2mH265
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h266 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security)
    (hcharts : ∀ leg, (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1
      (core.legs leg).1).weight (charts leg) ≠ 0)
    (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
      (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) (.inr (.inl leg)) /
        _root_.CurrentAFT.Parameters.modulus security +
    _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
      (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) (.inr (.inr leg)) /
        _root_.CurrentAFT.Parameters.modulus security = 0 := by
  exact _p2mH246 security (core.controls (.inl leg)).1 (core.legs leg).1
    (charts leg) (hcharts leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg)
open _root_.P2Mb748e9da renaming h266 → _p2mH266
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h267 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (hsafe : _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security)
    (hcharts : ∀ leg, (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1
      (core.legs leg).1).weight (charts leg) ≠ 0)
    (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) :
    (∑ vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security,
      _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
        (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) vertex /
          _root_.CurrentAFT.Parameters.modulus security) = 0 := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp only [_p2mH265 security layout core hsafe charts word, Finset.sum_const_zero, zero_add]
  exact Finset.sum_eq_zero (fun leg _ => _p2mH266 security layout core charts hcharts word leg)
open _root_.P2Mb748e9da renaming h267 → _p2mH267
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h260 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core) (hsafe : _root_.CurrentAFT.CurrentPublicSupport.SafeCore security core)
    (charts : _root_.CurrentAFT.CurrentAffineData.Charts security)
    (hcharts : ∀ leg, (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1
      (core.legs leg).1).weight (charts leg) ≠ 0)
    (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) :
    (∑ vertex : Fin (_root_.CurrentAFT.Parameters.dimension security), _root_.CurrentAFT.CurrentAffineLoad.rounding security
      ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)).mulVec
        (_root_.CurrentAFT.CurrentSourceLayout.hiddenWord security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word)) +
      _root_.CurrentAFT.CurrentAffineGeometry.offset security layout core (_root_.CurrentAFT.CurrentAffineData.intercepts security charts)
        (_root_.CurrentAFT.CurrentSourceLayout.closureScalar security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word)) hcharge) vertex /
        _root_.CurrentAFT.Parameters.modulus security) = 0 := by
  rw [← Equiv.sum_comp ((_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout).trans core.endpointPermutation.symm)]
  simp only [Equiv.trans_apply, _p2mH240]
  exact _p2mH267 security layout core hsafe charts hcharts word
open _root_.P2Mb748e9da renaming h260 → _p2mH260
end
open _root_.P2Mb748e9da renaming h260 → _p2mH260
open _root_.P2Mb748e9da renaming h261 → _p2mH261
open _root_.P2Mb748e9da renaming h262 → _p2mH262
open _root_.P2Mb748e9da renaming h263 → _p2mH263
open _root_.P2Mb748e9da renaming h264 → _p2mH264
open _root_.P2Mb748e9da renaming h265 → _p2mH265
open _root_.P2Mb748e9da renaming h266 → _p2mH266
open _root_.P2Mb748e9da renaming h267 → _p2mH267
open _root_.P2Mb748e9da renaming h268 → _p2mH268
open _root_.P2Mb748e9da renaming h269 → _p2mH269
end CurrentAFT.CurrentAffineProtectedCarry
open _root_.P2Mb748e9da renaming h260 → _p2mH260
open _root_.P2Mb748e9da renaming h261 → _p2mH261
open _root_.P2Mb748e9da renaming h262 → _p2mH262
open _root_.P2Mb748e9da renaming h263 → _p2mH263
open _root_.P2Mb748e9da renaming h264 → _p2mH264
open _root_.P2Mb748e9da renaming h265 → _p2mH265
open _root_.P2Mb748e9da renaming h266 → _p2mH266
open _root_.P2Mb748e9da renaming h267 → _p2mH267
open _root_.P2Mb748e9da renaming h268 → _p2mH268
open _root_.P2Mb748e9da renaming h269 → _p2mH269
end
open _root_.P2Mb748e9da renaming h260 → _p2mH260
open _root_.P2Mb748e9da renaming h261 → _p2mH261
open _root_.P2Mb748e9da renaming h262 → _p2mH262
open _root_.P2Mb748e9da renaming h263 → _p2mH263
open _root_.P2Mb748e9da renaming h264 → _p2mH264
open _root_.P2Mb748e9da renaming h265 → _p2mH265
open _root_.P2Mb748e9da renaming h266 → _p2mH266
open _root_.P2Mb748e9da renaming h267 → _p2mH267
open _root_.P2Mb748e9da renaming h268 → _p2mH268
open _root_.P2Mb748e9da renaming h269 → _p2mH269
namespace CurrentAFT.ActualAffineCompletedOutput
end CurrentAFT.ActualAffineCompletedOutput
namespace CurrentAFT.ActualAffineCompletedOutput.blocks
end CurrentAFT.ActualAffineCompletedOutput.blocks
namespace CurrentAFT.ActualAffineCompletedOutput.blocks.match_1
end CurrentAFT.ActualAffineCompletedOutput.blocks.match_1
namespace CurrentAFT.ActualAffineCompletedOutput.conditionalLaw
end CurrentAFT.ActualAffineCompletedOutput.conditionalLaw
namespace CurrentAFT.ActualPublicCharge.attachmentPosition
end CurrentAFT.ActualPublicCharge.attachmentPosition
namespace CurrentAFT.ActualPublicCharge.queuePosition
end CurrentAFT.ActualPublicCharge.queuePosition
namespace CurrentAFT.CurrentAffineGeometry.offset
end CurrentAFT.CurrentAffineGeometry.offset
namespace CurrentAFT.CurrentAffineProtectedCarry
end CurrentAFT.CurrentAffineProtectedCarry
namespace CurrentAFT.CurrentAffineProtectedCarry.bodyExtra
end CurrentAFT.CurrentAffineProtectedCarry.bodyExtra
namespace CurrentAFT.CurrentSourceProtection.protectedBody
end CurrentAFT.CurrentSourceProtection.protectedBody
namespace CurrentAFT.GaussianProductProtection.sourceEmbedding
end CurrentAFT.GaussianProductProtection.sourceEmbedding
section
namespace CurrentAFT.CurrentAffinePhysicalEndpoint
open AFT ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge ActualBlockFock
  ActualBlockMean CurrentSourceProtection CurrentSourceLayout CurrentAffineEndpoint
  CurrentAffineGeometry CurrentAffineData CurrentAffineLegCarry CurrentAffineProtectedCarry
  GaussianProductProtection PublicEndpointPlacement AffineFlagCalibration ProposalPrimary
  PublicCoefficientOutput
open HistogramNormalization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h257 (security : ℕ) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    (_root_.CurrentAFT.CurrentAffineLegCarry.integerPrimary security chart first.val second.val : _root_.CurrentAFT.RefinedPublicOutput.Residue security) =
      _root_.CurrentAFT.RefinedPublicOutput.embed security (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second) := by
  exact (_p2mH245 security chart first.val second.val).trans
    (RingEquiv.apply_symm_apply (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) _).symm
open _root_.P2Mb748e9da renaming h257 → _p2mH257
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h256 (security : ℕ) (shift : ℤ) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security)
    (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    (_root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion security shift chart first.val second.val : _root_.CurrentAFT.RefinedPublicOutput.Residue security) =
      _root_.CurrentAFT.RefinedPublicOutput.embed security
        (_root_.CurrentAFT.AffineFlagCalibration.companion security (shift - second.val) (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second)) := by
  have hcomp : _root_.CurrentAFT.RefinedPublicOutput.embed security
      (_root_.CurrentAFT.AffineFlagCalibration.companion security (shift - second.val) (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second)) =
        -1 + ((shift - second.val : ℤ) : _root_.CurrentAFT.RefinedPublicOutput.Residue security) -
          _root_.CurrentAFT.RefinedPublicOutput.embed security (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second) :=
    RingEquiv.apply_symm_apply (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)) _
  rw [hcomp]
  rw [← _p2mH257]
  unfold _root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion
  push_cast
  rw [ZMod.natCast_self]
  ring
open _root_.P2Mb748e9da renaming h256 → _p2mH256
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h255 (security : ℕ) (root : ℤ) (primary : _root_.CurrentAFT.RefinedPublicOutput.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicCharge.LegCore security) (chart : _root_.CurrentAFT.CurrentAffineLegCarry.PublicChart security) (first second : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
    _root_.CurrentAFT.AffineFlagCalibration.evaluateTriple security root primary seed chart first second 2 =
      _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root + second.val) seed.2 := by
  exact congrArg Prod.snd (_root_.AFT.PhysicalBlockTensors.tripleEquiv.apply_symm_apply
    (_root_.CurrentAFT.AffineFlagCalibration.pairProjection security (_root_.CurrentAFT.ActualPublicLegCharge.publicShift security primary seed.1 - second.val)
      (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security chart first second), _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root + second.val) seed.2))
open _root_.P2Mb748e9da renaming h255 → _p2mH255
set_option maxRecDepth 8192
private theorem _root_.P2Mb748e9da.h464 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (vertex : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) :
    _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
      (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) (.inl vertex) =
    _root_.CurrentAFT.ActualPublicCharge.centerAt security layout core vertex +
      _root_.CurrentAFT.ActualBlockMean.rootAt security core.bodyPermutation (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word) vertex +
        _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra security layout (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) vertex := by
  have hroot : _root_.CurrentAFT.ActualBlockMean.rootAt security core.bodyPermutation (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word) vertex =
      _root_.CurrentAFT.PublicCharge.cycleDifference (_root_.CurrentAFT.CurrentSourceLayout.bodyLatent security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word))
        (core.bodyPermutation.symm vertex) := rfl
  rw [hroot]
  unfold _root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly _root_.CurrentAFT.PublicCharge.assembledEndpoint _root_.CurrentAFT.CurrentAffineProtectedCarry.bodyExtra
  ring
open _root_.P2Mb748e9da renaming h464 → _p2mH464
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h258 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    (_root_.CurrentAFT.CurrentAffineEndpoint.naturalAssembly security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
      (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) vertex :
      _root_.CurrentAFT.RefinedPublicOutput.Residue security) =
    _root_.CurrentAFT.RefinedPublicOutput.embed security
      (_root_.CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord security layout core charts word (_root_.CurrentAFT.PublicEndpointPlacement.toPhysical security layout vertex)) := by
  rcases vertex with vertex | (leg | leg)
  · rw [_p2mH464]
    obtain ⟨center | (point | leg), rfl⟩ := layout.surjective vertex
    · rw [_p2mH262]
      simp only [_root_.CurrentAFT.ActualPublicCharge.centerAt, _root_.CurrentAFT.PublicEndpointPlacement.toPhysical, Equiv.symm_apply_apply, _root_.CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord,
        _root_.CurrentAFT.ActualBlockMean.centerRoots]
      rw [_root_.CurrentAFT.RefinedPublicOutput.embed_shift, _root_.CurrentAFT.RefinedPublicOutput.embed_value]
      push_cast
      ring
    · rw [_p2mH263]
      simp only [_root_.CurrentAFT.ActualPublicCharge.centerAt, _root_.CurrentAFT.PublicEndpointPlacement.toPhysical, Equiv.symm_apply_apply, _root_.CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord,
        _root_.CurrentAFT.ActualBlockMean.queueRoots]
      rw [_root_.CurrentAFT.RefinedPublicOutput.embed_shift, _root_.CurrentAFT.RefinedPublicOutput.embed_value]
      push_cast
      ring
    · rw [_p2mH261]
      simp only [_root_.CurrentAFT.ActualPublicCharge.centerAt, _root_.CurrentAFT.PublicEndpointPlacement.toPhysical, Equiv.symm_apply_apply, _root_.CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord]
      rw [_p2mH255]
      rw [_root_.CurrentAFT.RefinedPublicOutput.embed_shift, _root_.CurrentAFT.RefinedPublicOutput.embed_value]
      push_cast
      exact add_assoc _ _ _
  · change (_root_.CurrentAFT.CurrentAffineEndpoint.primaryOutput security (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)
      (_root_.CurrentAFT.CurrentAffineData.intercepts security charts) (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) leg :
      _root_.CurrentAFT.RefinedPublicOutput.Residue security) =
        _root_.CurrentAFT.RefinedPublicOutput.embed security
          (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security (charts leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg))
    exact _p2mH257 security (charts leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg)
  · change (_root_.CurrentAFT.CurrentAffineLegCarry.integerCompanion security (_root_.CurrentAFT.ActualPublicCharge.legShift security core leg) (charts leg)
      (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg).val (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg).val :
      _root_.CurrentAFT.RefinedPublicOutput.Residue security) =
        _root_.CurrentAFT.RefinedPublicOutput.embed security
          (_root_.CurrentAFT.AffineFlagCalibration.companion security (_root_.CurrentAFT.ActualPublicCharge.legShift security core leg - (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg).val)
            (_root_.CurrentAFT.AffineFlagCalibration.evaluatePrimary security (charts leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg)))
    exact _p2mH256 security (_root_.CurrentAFT.ActualPublicCharge.legShift security core leg) (charts leg)
      (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg) (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg)
open _root_.P2Mb748e9da renaming h258 → _p2mH258
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h259 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security))
    (vertex : _root_.CurrentAFT.PublicEndpointPlacement.AssemblyIndex security) :
    _root_.CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord security layout core charts word (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) =
      _root_.CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord security layout core charts word (_root_.CurrentAFT.PublicEndpointPlacement.toPhysical security layout vertex) := by
  simp [_root_.CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord, _root_.AFT.relabel, _root_.AFT.HistogramNormalization.renameWord, _root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten, _root_.CurrentAFT.PublicEndpointPlacement.endpointEquiv]
open _root_.P2Mb748e9da renaming h259 → _p2mH259
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h254 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security) (hcharge : _root_.CurrentAFT.ActualPublicCharge.publicCharge security core)
    (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) :
    (fun index => (_root_.CurrentAFT.CurrentAffineLoad.rounding security
      ((_root_.CurrentAFT.CurrentAffineGeometry.matrix security layout core (_root_.CurrentAFT.CurrentAffineData.scales security charts) (_root_.CurrentAFT.CurrentAffineData.shears security charts)).mulVec
        (_root_.CurrentAFT.CurrentSourceLayout.hiddenWord security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word)) +
      _root_.CurrentAFT.CurrentAffineGeometry.offset security layout core (_root_.CurrentAFT.CurrentAffineData.intercepts security charts)
        (_root_.CurrentAFT.CurrentSourceLayout.closureScalar security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word)) hcharge) index :
      _root_.CurrentAFT.RefinedPublicOutput.Residue security)) =
    fun index => _root_.CurrentAFT.RefinedPublicOutput.embed security (_root_.CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord security layout core charts word index) := by
  funext index
  obtain ⟨vertex, rfl⟩ := ((_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout).trans core.endpointPermutation.symm).surjective index
  change (_root_.CurrentAFT.CurrentAffineLoad.rounding security _
    (core.endpointPermutation.symm (_root_.CurrentAFT.PublicEndpointPlacement.endpointFlatten security layout vertex)) : _root_.CurrentAFT.RefinedPublicOutput.Residue security) = _
  simp only [Equiv.trans_apply]
  rw [_p2mH240, _p2mH259]
  exact _p2mH258 security layout core charts word vertex
open _root_.P2Mb748e9da renaming h254 → _p2mH254
end
open _root_.P2Mb748e9da renaming h254 → _p2mH254
open _root_.P2Mb748e9da renaming h255 → _p2mH255
open _root_.P2Mb748e9da renaming h256 → _p2mH256
open _root_.P2Mb748e9da renaming h257 → _p2mH257
open _root_.P2Mb748e9da renaming h258 → _p2mH258
open _root_.P2Mb748e9da renaming h259 → _p2mH259
open _root_.P2Mb748e9da renaming h464 → _p2mH464
end CurrentAFT.CurrentAffinePhysicalEndpoint
open _root_.P2Mb748e9da renaming h254 → _p2mH254
open _root_.P2Mb748e9da renaming h255 → _p2mH255
open _root_.P2Mb748e9da renaming h256 → _p2mH256
open _root_.P2Mb748e9da renaming h257 → _p2mH257
open _root_.P2Mb748e9da renaming h258 → _p2mH258
open _root_.P2Mb748e9da renaming h259 → _p2mH259
open _root_.P2Mb748e9da renaming h464 → _p2mH464
end
open _root_.P2Mb748e9da renaming h254 → _p2mH254
open _root_.P2Mb748e9da renaming h255 → _p2mH255
open _root_.P2Mb748e9da renaming h256 → _p2mH256
open _root_.P2Mb748e9da renaming h257 → _p2mH257
open _root_.P2Mb748e9da renaming h258 → _p2mH258
open _root_.P2Mb748e9da renaming h259 → _p2mH259
namespace AFT.FiniteDist.conditionalRepair
end AFT.FiniteDist.conditionalRepair
namespace AFT.FiniteDist.positiveRepairLaw
end AFT.FiniteDist.positiveRepairLaw
section
namespace CurrentAFT.CurrentPublicAffineSample
open AFT CurrentAffineData CurrentAffineLegCarry AffineFlagCalibration ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean CurrentPublicSupport
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.CurrentPublicAffineSample.modulusPrime
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h298 (security : ℕ) (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentAffineData.Charts security)
    (hweight : (_root_.CurrentAFT.CurrentPublicAffineSample.chartsLaw security core).weight charts ≠ 0) (leg : Fin (_root_.CurrentAFT.Parameters.legCount security)) :
    (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1).weight (charts leg) ≠ 0 := by
  intro hzero
  apply hweight
  exact Finset.prod_eq_zero (Finset.mem_univ leg) hzero
open _root_.P2Mb748e9da renaming h298 → _p2mH298
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h300 (security : ℕ) (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (sample : _root_.CurrentAFT.CurrentPublicAffineSample.Sample security) (hweight : (_root_.CurrentAFT.CurrentPublicAffineSample.law security weight hpositive).weight sample ≠ 0) :
    _root_.CurrentAFT.CurrentAffineData.Valid security sample.1.1 sample.1.2 ∧ _root_.CurrentAFT.CurrentPublicSupport.SafeCore security sample.1.1 ∧
      ∀ leg, (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security (sample.1.1.controls (.inl leg)).1
        (sample.1.1.legs leg).1).weight (sample.1.2 leg) ≠ 0 := by
  change ((_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).weight sample.1.1 *
    (_root_.CurrentAFT.CurrentPublicAffineSample.chartsLaw security sample.1.1).weight sample.1.2) * (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).weight sample.2 ≠ 0 at hweight
  have hcore := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hweight).1).1
  have hcharts := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hweight).1).2
  have hs := _p2mH305 security weight hpositive sample.1.1 hcore
  have hc := _p2mH298 security sample.1.1 sample.1.2 hcharts
  refine ⟨⟨hs.1, ?_⟩, hs.2, hc⟩
  intro leg
  exact _p2mH239 security _ _ _ (hc leg)
open _root_.P2Mb748e9da renaming h300 → _p2mH300
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h299 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (sample : _root_.CurrentAFT.CurrentPublicAffineSample.Sample security) (hweight : (_root_.CurrentAFT.CurrentPublicAffineSample.law security weight hpositive).weight sample ≠ 0) :
    _root_.CurrentAFT.CurrentPublicAffineSample.realize security layout sample = _root_.CurrentAFT.CurrentAffineData.assembled security layout sample.1.1 sample.1.2 sample.2.val
      (_p2mH300 security weight hpositive sample hweight).1 :=
  _p2mH238 security layout sample.1.1 sample.1.2 sample.2.val _
open _root_.P2Mb748e9da renaming h299 → _p2mH299
end
open _root_.P2Mb748e9da renaming h298 → _p2mH298
open _root_.P2Mb748e9da renaming h299 → _p2mH299
open _root_.P2Mb748e9da renaming h300 → _p2mH300
end CurrentAFT.CurrentPublicAffineSample
open _root_.P2Mb748e9da renaming h298 → _p2mH298
open _root_.P2Mb748e9da renaming h299 → _p2mH299
open _root_.P2Mb748e9da renaming h300 → _p2mH300
end
open _root_.P2Mb748e9da renaming h298 → _p2mH298
open _root_.P2Mb748e9da renaming h299 → _p2mH299
open _root_.P2Mb748e9da renaming h300 → _p2mH300
section
namespace CurrentAFT.CurrentHiddenSourceTransport
open AFT GaussianSource CurrentSourceProtection CurrentSourceLayout GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.bodySize Parameters.dimension Parameters.legCount
  sourceCount cutoff sourceNumbering
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h280 (security : ℕ) :
    (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security).map (_root_.CurrentAFT.CurrentHiddenSourceTransport.splitProtected security) =
      (_root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenLaw security).prod (_root_.CurrentAFT.CurrentHiddenSourceTransport.closureLaw security) := by
  apply _root_.AFT.FiniteDist.ext
  intro pair
  rw [_root_.AFT.FiniteDist.map_equiv_weight, _p2mH317]
  have hpair := (_root_.CurrentAFT.CurrentHiddenSourceTransport.splitProtected security).apply_symm_apply pair
  have hh := congrArg Prod.fst hpair
  have hc := congrArg Prod.snd hpair
  change _root_.CurrentAFT.CurrentSourceLayout.hiddenProtectedWord security ((_root_.CurrentAFT.CurrentHiddenSourceTransport.splitProtected security).symm pair) = pair.1 at hh
  change _root_.CurrentAFT.CurrentSourceLayout.protectedClosure security ((_root_.CurrentAFT.CurrentHiddenSourceTransport.splitProtected security).symm pair) = pair.2 at hc
  rw [hh, hc]
  rfl
open _root_.P2Mb748e9da renaming h280 → _p2mH280
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h279 (security : ℕ) :
    ((_root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenLaw security).prod (_root_.CurrentAFT.CurrentHiddenSourceTransport.closureLaw security)).map (_root_.CurrentAFT.CurrentHiddenSourceTransport.joinProtected security) =
      _root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security := by
  rw [← _p2mH280, _root_.AFT.FiniteDist.map_map]
  change (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security).map
    (fun word => (_root_.CurrentAFT.CurrentHiddenSourceTransport.splitProtected security).symm (_root_.CurrentAFT.CurrentHiddenSourceTransport.splitProtected security word)) = _
  simp only [Equiv.symm_apply_apply]
  apply _root_.AFT.FiniteDist.ext
  intro word
  rw [_root_.AFT.FiniteDist.map_weight, Finset.sum_eq_single word]
  · rw [if_pos rfl]
  · intro other _ hother
    exact if_neg hother
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
open _root_.P2Mb748e9da renaming h279 → _p2mH279
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h277 (security : ℕ) :
    _root_.CurrentAFT.CurrentSourceProtection.budget security = _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenBudget security +
      _root_.AFT.GaussianSource.clippingProbability (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security + 1 : ℕ) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) := by
  rw [_p2mH319, ← Equiv.sum_comp (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security)]
  simp only [Fintype.sum_sum_type, Fintype.sum_unique]
  change _ + _root_.AFT.GaussianSource.clippingProbability _ (_root_.CurrentAFT.CurrentSourceProtection.cutoff security (_root_.CurrentAFT.CurrentSourceLayout.sourceNumbering security (.inr ())) + 1 : ℕ) _ = _
  rw [_root_.CurrentAFT.CurrentSourceLayout.cutoff_closure]
  unfold _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenBudget _root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff
  rfl
open _root_.P2Mb748e9da renaming h277 → _p2mH277
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h278 (security : ℕ) : _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenBudget security ≤ _root_.CurrentAFT.CurrentSourceProtection.budget security := by
  rw [_p2mH277]
  have hnonneg : 0 ≤ _root_.AFT.GaussianSource.clippingProbability (_root_.CurrentAFT.CurrentSourceProtection.width security)
      (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security + 1 : ℕ) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) :=
    tsum_nonneg (fun point => by split_ifs; exact ENNReal.toReal_nonneg; rfl)
  linarith
open _root_.P2Mb748e9da renaming h278 → _p2mH278
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h281 {Public Output : Type*} [Fintype Public] [Fintype Output]
    (security : ℕ) (publicLaw : _root_.AFT.FiniteDist Public)
    (physical : Public → _root_.CurrentAFT.CurrentHiddenSourceTransport.Closure security → (Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) → _root_.AFT.FiniteDist Output) :
    _root_.AFT.FiniteDist.TVBound
      ((publicLaw.prod (_root_.CurrentAFT.CurrentHiddenSourceTransport.closureLaw security)).mix (fun draw =>
        _root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenGaussianOutput security (physical draw.1 draw.2)))
      ((publicLaw.prod (_root_.CurrentAFT.CurrentHiddenSourceTransport.closureLaw security)).mix (fun draw => (_root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenLaw security).mix
        (fun word => physical draw.1 draw.2 (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) word))))
      (_root_.CurrentAFT.CurrentSourceProtection.budget security) := by
  apply _p2mH68
  intro draw
  exact (_p2mH358 (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security)
    (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) (physical draw.1 draw.2)).mono (_p2mH278 security)
open _root_.P2Mb748e9da renaming h281 → _p2mH281
end
open _root_.P2Mb748e9da renaming h277 → _p2mH277
open _root_.P2Mb748e9da renaming h278 → _p2mH278
open _root_.P2Mb748e9da renaming h279 → _p2mH279
open _root_.P2Mb748e9da renaming h280 → _p2mH280
open _root_.P2Mb748e9da renaming h281 → _p2mH281
end CurrentAFT.CurrentHiddenSourceTransport
open _root_.P2Mb748e9da renaming h277 → _p2mH277
open _root_.P2Mb748e9da renaming h278 → _p2mH278
open _root_.P2Mb748e9da renaming h279 → _p2mH279
open _root_.P2Mb748e9da renaming h280 → _p2mH280
open _root_.P2Mb748e9da renaming h281 → _p2mH281
end
open _root_.P2Mb748e9da renaming h277 → _p2mH277
open _root_.P2Mb748e9da renaming h278 → _p2mH278
open _root_.P2Mb748e9da renaming h279 → _p2mH279
open _root_.P2Mb748e9da renaming h280 → _p2mH280
open _root_.P2Mb748e9da renaming h281 → _p2mH281
namespace AFT.canonicalCarry
end AFT.canonicalCarry
namespace AFT.fiberLabel
end AFT.fiberLabel
namespace CurrentAFT.FiniteZeroSum
end CurrentAFT.FiniteZeroSum
namespace CurrentAFT.FiniteZeroSum.uniformLaw
end CurrentAFT.FiniteZeroSum.uniformLaw
section
namespace CurrentAFT.CurrentZeroFiber
open AFT CurrentAffineGeometry
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.CurrentZeroFiber.modulusNeZero
attribute [local instance] _root_.CurrentAFT.CurrentZeroFiber.dimensionNonempty
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h338 (security : ℕ) :
    (_root_.AFT.uniformZeroFiber (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)
      (_root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security))).map (_root_.CurrentAFT.CurrentZeroFiber.coordinates security).symm =
        _root_.CurrentAFT.CurrentZeroFiber.uniformFiber security := by
  rw [_root_.AFT.uniformZeroFiber, _root_.CurrentAFT.CurrentZeroFiber.uniformFiber, _root_.AFT.FiniteDist.map_map]
  rw [← _root_.AFT.FiniteDist.uniform_map_equiv (_root_.CurrentAFT.CurrentZeroFiber.fiberEquiv security).symm, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2Mb748e9da renaming h338 → _p2mH338
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h337 (security : ℕ) :
    (_root_.CurrentAFT.FiniteZeroSum.uniformLaw (Index := Fin (_root_.CurrentAFT.Parameters.dimension security)) (_root_.CurrentAFT.Parameters.modulus security)).map
      (_root_.CurrentAFT.CurrentZeroFiber.endpointCoordinates security) = _root_.CurrentAFT.uniformZeroSum (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) := by
  ext word
  rw [_root_.AFT.FiniteDist.map_equiv_weight, _p2mH357, _p2mH461]
  have hsum : (∑ index, (_root_.CurrentAFT.CurrentZeroFiber.endpointCoordinates security).symm word index) = ∑ index, word index :=
    Equiv.sum_comp (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm word
  rw [hsum]
  split_ifs
  · simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
    rw [← _root_.CurrentAFT.LobsterCoordinates.current_vertex_count security]
    change (_root_.CurrentAFT.Parameters.modulus security : ℝ) / (_root_.CurrentAFT.Parameters.modulus security : ℝ) ^ (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security + 1) = _
    have hq : (_root_.CurrentAFT.Parameters.modulus security : ℝ) ≠ 0 := by exact_mod_cast (_root_.CurrentAFT.Parameters.modulus_spec security).2.ne_zero
    rw [pow_succ]
    field_simp
  · rfl
open _root_.P2Mb748e9da renaming h337 → _p2mH337
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h336 (n q : ℕ) [NeZero q] (column : Fin (n + 1) → ℤ)
    (hcolumn : _root_.AFT.totalCharge column = (q : ℤ)) :
    (_root_.CurrentAFT.uniformZeroSum n q).map (_root_.CurrentAFT.CurrentZeroFiber.rawPullback n q column hcolumn) = _root_.AFT.uniformZeroFiber n q column := by
  rw [_root_.CurrentAFT.uniformZeroSum, _root_.AFT.FiniteDist.map_map]
  change (_root_.AFT.FiniteDist.uniform (_root_.AFT.EndpointHyperplane n q)).map _ = _
  calc
    _ = (_root_.AFT.FiniteDist.uniform (_root_.AFT.EndpointHyperplane n q)).map
        (fun endpoint => (_root_.AFT.canonicalEndpointEquiv n q column hcolumn endpoint).val) := by
      congr 1
      funext endpoint
      simp only [_root_.CurrentAFT.CurrentZeroFiber.rawPullback, dif_pos endpoint.property]
    _ = _ := _p2mH113 n q column hcolumn
open _root_.P2Mb748e9da renaming h336 → _p2mH336
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h339 (security : ℕ) :
    (_root_.CurrentAFT.FiniteZeroSum.uniformLaw (Index := Fin (_root_.CurrentAFT.Parameters.dimension security)) (_root_.CurrentAFT.Parameters.modulus security)).map
      (_root_.CurrentAFT.CurrentZeroFiber.pullback security) = _root_.CurrentAFT.CurrentZeroFiber.uniformFiber security := by
  unfold _root_.CurrentAFT.CurrentZeroFiber.pullback
  calc
    _ = (((_root_.CurrentAFT.FiniteZeroSum.uniformLaw (Index := Fin (_root_.CurrentAFT.Parameters.dimension security))
        (_root_.CurrentAFT.Parameters.modulus security)).map (_root_.CurrentAFT.CurrentZeroFiber.endpointCoordinates security)).map
          (_root_.CurrentAFT.CurrentZeroFiber.rawPullback (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)
            (_root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security)) (_root_.CurrentAFT.CurrentZeroFiber.column_charge security))).map
              (_root_.CurrentAFT.CurrentZeroFiber.coordinates security).symm := by rw [_root_.AFT.FiniteDist.map_map, _root_.AFT.FiniteDist.map_map]
    _ = _ := by rw [_p2mH337, _p2mH336, _p2mH338]
open _root_.P2Mb748e9da renaming h339 → _p2mH339
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h334 (security : ℕ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ) :
    _root_.CurrentAFT.CurrentZeroFiber.coordinates security (fun index => (input index : ZMod (_root_.CurrentAFT.Parameters.modulus security))) =
      _root_.AFT.reduceCoordinates (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.CurrentAffineLoad.splitSource security input) := rfl
open _root_.P2Mb748e9da renaming h334 → _p2mH334
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h335 (security : ℕ) (input : Fin (_root_.CurrentAFT.Parameters.dimension security) → ℤ)
    (hcarry : (∑ vertex, _root_.CurrentAFT.CurrentAffineLoad.rounding security input vertex / _root_.CurrentAFT.Parameters.modulus security : ℤ) = 0) :
    _root_.CurrentAFT.CurrentZeroFiber.pullback security (fun vertex => (_root_.CurrentAFT.CurrentAffineLoad.rounding security input vertex :
      ZMod (_root_.CurrentAFT.Parameters.modulus security))) =
        fun index => (input index : ZMod (_root_.CurrentAFT.Parameters.modulus security)) := by
  apply (_root_.CurrentAFT.CurrentZeroFiber.coordinates security).injective
  rw [_root_.CurrentAFT.CurrentZeroFiber.pullback, Equiv.apply_symm_apply, _p2mH334]
  let coordinateInput := _root_.CurrentAFT.CurrentAffineLoad.splitSource security input
  let endpoint := _root_.AFT.endpointProjection (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)
    (_root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security)) (_root_.CurrentAFT.CurrentZeroFiber.column_charge security)
      (_root_.AFT.reduceCoordinates _ _ coordinateInput)
  have hep : _root_.CurrentAFT.CurrentZeroFiber.endpointCoordinates security (fun vertex => (_root_.CurrentAFT.CurrentAffineLoad.rounding security input vertex :
      ZMod (_root_.CurrentAFT.Parameters.modulus security))) = endpoint.val := by
    funext vertex
    rw [_root_.AFT.endpointProjection_reduceCoordinates]
    change (_root_.AFT.roundingLoad _ _ _ ((_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security vertex)) :
      ZMod (_root_.CurrentAFT.Parameters.modulus security)) = _
    rw [Equiv.symm_apply_apply]
  rw [hep, _root_.CurrentAFT.CurrentZeroFiber.rawPullback, dif_pos endpoint.property]
  have hgeneric : _root_.AFT.totalCharge (_root_.AFT.canonicalCarry (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)
      (_root_.AFT.roundingLoad _ (_root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security)) coordinateInput)) = 0 := by
    have hs := Equiv.sum_comp (_root_.CurrentAFT.CurrentAffineGeometry.dimensionEquiv security).symm (fun vertex =>
      _root_.AFT.roundingLoad (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security))
        coordinateInput vertex / _root_.CurrentAFT.Parameters.modulus security)
    exact hs.symm.trans hcarry
  exact ((_p2mH112 (_root_.CurrentAFT.CurrentAffineGeometry.edgeCount security) (_root_.CurrentAFT.Parameters.modulus security)
    (_root_.AFT.injectionColumn _ (_root_.CurrentAFT.Parameters.modulus security)) (_root_.CurrentAFT.CurrentZeroFiber.column_charge security) coordinateInput).mpr
      (by rw [hgeneric]; exact dvd_zero _)).symm
open _root_.P2Mb748e9da renaming h335 → _p2mH335
end
open _root_.P2Mb748e9da renaming h334 → _p2mH334
open _root_.P2Mb748e9da renaming h335 → _p2mH335
open _root_.P2Mb748e9da renaming h336 → _p2mH336
open _root_.P2Mb748e9da renaming h337 → _p2mH337
open _root_.P2Mb748e9da renaming h338 → _p2mH338
open _root_.P2Mb748e9da renaming h339 → _p2mH339
end CurrentAFT.CurrentZeroFiber
open _root_.P2Mb748e9da renaming h334 → _p2mH334
open _root_.P2Mb748e9da renaming h335 → _p2mH335
open _root_.P2Mb748e9da renaming h336 → _p2mH336
open _root_.P2Mb748e9da renaming h337 → _p2mH337
open _root_.P2Mb748e9da renaming h338 → _p2mH338
open _root_.P2Mb748e9da renaming h339 → _p2mH339
end
open _root_.P2Mb748e9da renaming h334 → _p2mH334
open _root_.P2Mb748e9da renaming h335 → _p2mH335
open _root_.P2Mb748e9da renaming h336 → _p2mH336
open _root_.P2Mb748e9da renaming h337 → _p2mH337
open _root_.P2Mb748e9da renaming h338 → _p2mH338
open _root_.P2Mb748e9da renaming h339 → _p2mH339
namespace AFT.canonicalEndpointEquiv
end AFT.canonicalEndpointEquiv
namespace AFT.uniformZeroFiber
end AFT.uniformZeroFiber
namespace CurrentAFT.CurrentHiddenSourceTransport
end CurrentAFT.CurrentHiddenSourceTransport
namespace CurrentAFT.CurrentPublicAffineSample
end CurrentAFT.CurrentPublicAffineSample
namespace CurrentAFT.CurrentSourceLayout.splitWord
end CurrentAFT.CurrentSourceLayout.splitWord
namespace CurrentAFT.CurrentZeroFiber
end CurrentAFT.CurrentZeroFiber
namespace CurrentAFT.CurrentZeroFiber.label
end CurrentAFT.CurrentZeroFiber.label
namespace CurrentAFT.CurrentZeroFiber.pullback
end CurrentAFT.CurrentZeroFiber.pullback
namespace CurrentAFT.CurrentZeroFiber.rawPullback
end CurrentAFT.CurrentZeroFiber.rawPullback
namespace CurrentAFT.CurrentZeroFiber.uniformFiber
end CurrentAFT.CurrentZeroFiber.uniformFiber
section
namespace CurrentAFT.CurrentAffineTransport
open AFT CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport
  CurrentSourceProtection CurrentSourceLayout CurrentAffineProtectedCarry CurrentZeroFiber
  GaussianProductProtection ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.CurrentAffineTransport.modulusNeZero
attribute [local instance] _root_.CurrentAFT.CurrentAffineTransport.dimensionNonempty
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h273 {Source Output : Type*} [Fintype Source] [Fintype Output]
    (distribution : _root_.AFT.FiniteDist Source) (value : Source → Output) :
    distribution.mix (fun source => (_root_.AFT.FiniteDist.uniform Unit).map (fun _ => value source)) =
      distribution.map value := by
  ext output
  simp [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.uniform_weight]
open _root_.P2Mb748e9da renaming h273 → _p2mH273
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h272 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security)) :
    _root_.AFT.FiniteDist.TVBound (_root_.CurrentAFT.CurrentAffineTransport.gaussianLaw security layout weight hpositive)
      (_root_.CurrentAFT.CurrentAffineTransport.protectedLaw security layout weight hpositive) (_root_.CurrentAFT.CurrentSourceProtection.budget security) := by
  have h := _p2mH281 security
    (_root_.AFT.FiniteDist.joint (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive)
      (_root_.CurrentAFT.CurrentPublicAffineSample.chartsLaw security)) (fun publicDraw closure input => (_root_.AFT.FiniteDist.uniform Unit).map
        (fun _ => _root_.CurrentAFT.CurrentAffineTransport.output security layout (publicDraw, closure) input))
  simp_rw [_p2mH273] at h
  exact h
open _root_.P2Mb748e9da renaming h272 → _p2mH272
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h276 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (sample : _root_.CurrentAFT.CurrentPublicAffineSample.Sample security) (hsample : (_root_.CurrentAFT.CurrentPublicAffineSample.law security weight hpositive).weight sample ≠ 0)
    (input : _root_.CurrentAFT.CurrentHiddenSourceTransport.HiddenWord security) :
    (∑ vertex, _root_.CurrentAFT.CurrentAffineLoad.rounding security
      ((_root_.CurrentAFT.CurrentPublicAffineSample.realize security layout sample).eval (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) input)) vertex /
        _root_.CurrentAFT.Parameters.modulus security : ℤ) = 0 := by
  have hs := _p2mH300 security weight hpositive sample hsample
  rw [_p2mH299 security layout weight hpositive sample hsample]
  let word := _root_.CurrentAFT.CurrentHiddenSourceTransport.joinProtected security (input, sample.2)
  have hsplit := (_root_.CurrentAFT.CurrentSourceLayout.splitWord security).apply_symm_apply
    (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) input, sample.2.val)
  have hh : _root_.CurrentAFT.CurrentSourceLayout.hiddenWord security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) =
      _root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) input := congrArg Prod.fst hsplit
  have hc : _root_.CurrentAFT.CurrentSourceLayout.closureScalar security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) word) = sample.2.val := congrArg Prod.snd hsplit
  have h := _p2mH260 security layout sample.1.1 hs.1.1 hs.2.1 sample.1.2 hs.2.2 word
  rw [hh, hc] at h
  exact h
open _root_.P2Mb748e9da renaming h276 → _p2mH276
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h275 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security)) :
    (_root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive).map (_root_.CurrentAFT.CurrentZeroFiber.pullback security) =
      _root_.CurrentAFT.CurrentAffineTransport.protectedLaw security layout weight hpositive := by
  rw [_root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw, _root_.AFT.FiniteDist.map_mix]
  apply _p2mH79
  intro sample hsample
  rw [_root_.AFT.FiniteDist.map_map]
  congr 1
  funext input
  exact _p2mH335 security _
    (_p2mH276 security layout weight hpositive sample hsample input)
open _root_.P2Mb748e9da renaming h275 → _p2mH275
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h274 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (error : ℝ)
    (hendpoint : (_root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive).totalVariation
      (_root_.CurrentAFT.FiniteZeroSum.uniformLaw (Index := Fin (_root_.CurrentAFT.Parameters.dimension security)) (_root_.CurrentAFT.Parameters.modulus security)) ≤ error) :
    (_root_.CurrentAFT.CurrentAffineTransport.protectedLaw security layout weight hpositive).totalVariation (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security) ≤ error := by
  have h := ((_p2mH81 _ _ _).mpr hendpoint).map (_root_.CurrentAFT.CurrentZeroFiber.pullback security)
  rw [_p2mH275, _p2mH339] at h
  exact (_p2mH81 _ _ _).mp h
open _root_.P2Mb748e9da renaming h274 → _p2mH274
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h271 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (error : ℝ)
    (hendpoint : (_root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive).totalVariation
      (_root_.CurrentAFT.FiniteZeroSum.uniformLaw (Index := Fin (_root_.CurrentAFT.Parameters.dimension security)) (_root_.CurrentAFT.Parameters.modulus security)) ≤ error) :
    (_root_.CurrentAFT.CurrentAffineTransport.gaussianLaw security layout weight hpositive).totalVariation (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security) ≤ error + _root_.CurrentAFT.CurrentSourceProtection.budget security := by
  have hp := _p2mH274 security layout weight hpositive error hendpoint
  have h := (_p2mH272 security layout weight hpositive).triangle
    ((_p2mH81 _ _ _).mpr hp)
  rw [add_comm] at h
  exact (_p2mH81 _ _ _).mp h
open _root_.P2Mb748e9da renaming h271 → _p2mH271
end
open _root_.P2Mb748e9da renaming h271 → _p2mH271
open _root_.P2Mb748e9da renaming h272 → _p2mH272
open _root_.P2Mb748e9da renaming h273 → _p2mH273
open _root_.P2Mb748e9da renaming h274 → _p2mH274
open _root_.P2Mb748e9da renaming h275 → _p2mH275
open _root_.P2Mb748e9da renaming h276 → _p2mH276
end CurrentAFT.CurrentAffineTransport
open _root_.P2Mb748e9da renaming h271 → _p2mH271
open _root_.P2Mb748e9da renaming h272 → _p2mH272
open _root_.P2Mb748e9da renaming h273 → _p2mH273
open _root_.P2Mb748e9da renaming h274 → _p2mH274
open _root_.P2Mb748e9da renaming h275 → _p2mH275
open _root_.P2Mb748e9da renaming h276 → _p2mH276
end
open _root_.P2Mb748e9da renaming h271 → _p2mH271
open _root_.P2Mb748e9da renaming h272 → _p2mH272
open _root_.P2Mb748e9da renaming h273 → _p2mH273
open _root_.P2Mb748e9da renaming h274 → _p2mH274
open _root_.P2Mb748e9da renaming h275 → _p2mH275
open _root_.P2Mb748e9da renaming h276 → _p2mH276
namespace CurrentAFT.CurrentAffinePhysicalEndpoint
end CurrentAFT.CurrentAffinePhysicalEndpoint
namespace CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord
end CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord
namespace CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord.match_1
end CurrentAFT.CurrentAffinePhysicalEndpoint.blockWord.match_1
namespace CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord
end CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord
namespace CurrentAFT.CurrentAffineTransport
end CurrentAFT.CurrentAffineTransport
namespace CurrentAFT.CurrentAffineTransport.protectedEndpointLaw
end CurrentAFT.CurrentAffineTransport.protectedEndpointLaw
namespace CurrentAFT.PublicEndpointPlacement.endpointEquiv
end CurrentAFT.PublicEndpointPlacement.endpointEquiv
namespace CurrentAFT.PublicEndpointPlacement.endpointFlatten
end CurrentAFT.PublicEndpointPlacement.endpointFlatten
section
namespace CurrentAFT.CurrentAffineSampleAgreement
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentSourceProtection CurrentSourceLayout CurrentHiddenSourceTransport
  CurrentPublicAffineSample CurrentAffinePhysicalEndpoint GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h270 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security))
    (sample : _root_.CurrentAFT.CurrentPublicAffineSample.Sample security) (hsample : (_root_.CurrentAFT.CurrentPublicAffineSample.law security weight hpositive).weight sample ≠ 0)
    (input : _root_.CurrentAFT.CurrentHiddenSourceTransport.HiddenWord security) :
    _root_.CurrentAFT.CurrentAffineTransport.endpoint security layout sample (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) input) =
      _root_.CurrentAFT.CurrentAffineSampleAgreement.physicalWord security layout sample input := by
  have hs := _p2mH300 security weight hpositive sample hsample
  have hsplit := (_root_.CurrentAFT.CurrentSourceLayout.splitWord security).apply_symm_apply
    (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) input, sample.2.val)
  have hh : _root_.CurrentAFT.CurrentSourceLayout.hiddenWord security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) (_root_.CurrentAFT.CurrentAffineSampleAgreement.sourceWord security sample input)) =
      _root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceLayout.hiddenCutoff security) input := congrArg Prod.fst hsplit
  have hc : _root_.CurrentAFT.CurrentSourceLayout.closureScalar security (_root_.CurrentAFT.GaussianProductProtection.sourceEmbedding (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) (_root_.CurrentAFT.CurrentAffineSampleAgreement.sourceWord security sample input)) =
      sample.2.val := congrArg Prod.snd hsplit
  have h := _p2mH254 security layout sample.1.1 sample.1.2 hs.1.1 (_root_.CurrentAFT.CurrentAffineSampleAgreement.sourceWord security sample input)
  rw [hh, hc] at h
  unfold _root_.CurrentAFT.CurrentAffineTransport.endpoint
  rw [_p2mH299 security layout weight hpositive sample hsample]
  exact h
open _root_.P2Mb748e9da renaming h270 → _p2mH270
end
open _root_.P2Mb748e9da renaming h270 → _p2mH270
end CurrentAFT.CurrentAffineSampleAgreement
open _root_.P2Mb748e9da renaming h270 → _p2mH270
end
open _root_.P2Mb748e9da renaming h270 → _p2mH270
section
namespace CurrentAFT.FiniteProductFubini
open AFT PublicAuxiliaryFubini
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h356 {Index First Second : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype First] [Fintype Second]
    (first : Index → _root_.AFT.FiniteDist First) (second : Index → _root_.AFT.FiniteDist Second)
    (factor : Index → First → Second → ℝ) :
    (_root_.AFT.FiniteDist.independent first).expectation (fun left =>
      (_root_.AFT.FiniteDist.independent second).expectation (fun right =>
        ∏ index, factor index (left index) (right index))) =
      ∏ index, (first index).expectation (fun left => (second index).expectation (factor index left)) := by
  rw [_root_.AFT.FiniteDist.expectation_comm]
  trans (_root_.AFT.FiniteDist.independent second).expectation (fun right =>
    ∏ index, (first index).expectation (fun left => factor index left (right index)))
  · apply congrArg (_root_.AFT.FiniteDist.expectation (_root_.AFT.FiniteDist.independent second))
    funext right
    exact _p2mH427 first (fun index left => factor index left (right index))
  · trans ∏ index, (second index).expectation (fun right =>
      (first index).expectation (fun left => factor index left right))
    · exact _p2mH427 second (fun index right =>
        (first index).expectation (fun left => factor index left right))
    · apply Finset.prod_congr rfl
      intro index _
      exact _root_.AFT.FiniteDist.expectation_comm _ _ _
open _root_.P2Mb748e9da renaming h356 → _p2mH356
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h355 {Index Public First Second : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Public] [Fintype First] [Fintype Second]
    (publicLaw : Index → _root_.AFT.FiniteDist Public) (first : Index → _root_.AFT.FiniteDist First)
    (second : Index → _root_.AFT.FiniteDist Second) (factor : Index → Public → First → Second → ℝ) :
    (_root_.AFT.FiniteDist.independent publicLaw).expectation (fun charts =>
      (_root_.AFT.FiniteDist.independent first).expectation (fun left =>
        (_root_.AFT.FiniteDist.independent second).expectation (fun right =>
          ∏ index, factor index (charts index) (left index) (right index)))) =
      ∏ index, (publicLaw index).expectation (fun chart =>
        (first index).expectation (fun left => (second index).expectation (factor index chart left))) := by
  trans (_root_.AFT.FiniteDist.independent publicLaw).expectation (fun charts =>
    ∏ index, (first index).expectation (fun left =>
      (second index).expectation (factor index (charts index) left)))
  · apply congrArg (_root_.AFT.FiniteDist.expectation (_root_.AFT.FiniteDist.independent publicLaw))
    funext charts
    exact _p2mH356 first second (fun index => factor index (charts index))
  · exact _p2mH427 publicLaw (fun index chart =>
      (first index).expectation (fun left => (second index).expectation (factor index chart left)))
open _root_.P2Mb748e9da renaming h355 → _p2mH355
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h354 {Index Color : Type*} [Fintype Index]
    (Slots : Index → Type*) (first second : Sigma Slots → Color) :
    (if first = second then (1 : ℝ) else 0) =
      ∏ index, if (fun slot => first ⟨index, slot⟩) = (fun slot => second ⟨index, slot⟩) then 1 else 0 := by
  rw [Finset.prod_ite_zero]
  have heq : (∀ index ∈ (Finset.univ : Finset Index),
      (fun slot => first ⟨index, slot⟩) = (fun slot => second ⟨index, slot⟩)) ↔ first = second := by
    simp only [Finset.mem_univ, forall_true_left]
    constructor
    · intro h
      funext point
      exact congrFun (h point.1) point.2
    · rintro rfl
      exact fun _ => rfl
  simp only [heq, Finset.prod_const_one]
open _root_.P2Mb748e9da renaming h354 → _p2mH354
end
open _root_.P2Mb748e9da renaming h354 → _p2mH354
open _root_.P2Mb748e9da renaming h355 → _p2mH355
open _root_.P2Mb748e9da renaming h356 → _p2mH356
end CurrentAFT.FiniteProductFubini
open _root_.P2Mb748e9da renaming h354 → _p2mH354
open _root_.P2Mb748e9da renaming h355 → _p2mH355
open _root_.P2Mb748e9da renaming h356 → _p2mH356
end
open _root_.P2Mb748e9da renaming h354 → _p2mH354
open _root_.P2Mb748e9da renaming h355 → _p2mH355
open _root_.P2Mb748e9da renaming h356 → _p2mH356
section
namespace CurrentAFT.CurrentProtectedSourceParts
open AFT GaussianSource CurrentSourceProtection CurrentSourceLayout
  CurrentAffineProtectedCarry GaussianProductProtection ActualCycleMeanMGF
  AffineFlagCalibration DiffuseProfiles
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h297 (security : ℕ) (word : _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)) :
    (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security).weight word = (_root_.CurrentAFT.CurrentProtectedSourceParts.partsLaw security).weight (_root_.CurrentAFT.CurrentProtectedSourceParts.splitParts security word) := by
  change (_root_.CurrentAFT.GaussianProductProtection.protectedLaw (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)).weight word = _
  rw [← _p2mH361 (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.CurrentSourceProtection.width_pos security) (_root_.CurrentAFT.CurrentSourceProtection.cutoff security)]
  unfold _root_.CurrentAFT.GaussianProductProtection.protectedMass
  rw [← Equiv.prod_comp (_root_.CurrentAFT.CurrentProtectedSourceParts.partsNumbering security)]
  simp only [Fintype.prod_sum_type, Fintype.prod_unique]
  simp_rw [_root_.CurrentAFT.CurrentProtectedSourceParts.partsNumbering_body, _root_.CurrentAFT.CurrentProtectedSourceParts.partsNumbering_aux, _root_.CurrentAFT.CurrentSourceProtection.cutoff_body, _root_.CurrentAFT.CurrentSourceProtection.cutoff_aux]
  rw [_root_.CurrentAFT.CurrentProtectedSourceParts.auxNumbering_queue]
  change (∏ body, _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security)
    (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word body).val) *
      (((∏ leg, _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)
        (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg).val) *
        ∏ leg, _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)
          (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg).val) *
        _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1)
          (_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word (Fin.last (_root_.CurrentAFT.Parameters.legCount security * 2))).val) = _
  have hedge (value : _root_.CurrentAFT.ActualCycleMeanMGF.Edge security) :
      _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.DiffuseProfiles.edgeCutoff security) value.val =
        (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).weight value := by
    rw [_p2mH370 _ _ (_root_.CurrentAFT.CurrentSourceProtection.width_pos security), dif_pos value.property]
    rfl
  have hscalar (value : _root_.CurrentAFT.AffineFlagCalibration.Scalar security) :
      _root_.CurrentAFT.GaussianWindowProtection.protectedMass (_root_.CurrentAFT.CurrentSourceProtection.width security) (_root_.CurrentAFT.Parameters.sourceCutoff security - 1) value.val =
        (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight value := by
    rw [_p2mH370 _ _ (_root_.CurrentAFT.CurrentSourceProtection.width_pos security), dif_pos value.property]
    rfl
  simp_rw [hedge, hscalar]
  change _ = (∏ body, (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).weight (_root_.CurrentAFT.CurrentSourceProtection.protectedBody security word body)) *
    ((∏ leg, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedFirst security word leg)) *
      ((∏ leg, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight (_root_.CurrentAFT.CurrentAffineProtectedCarry.protectedSecond security word leg)) *
        (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight (_root_.CurrentAFT.CurrentSourceProtection.protectedAux security word (Fin.last (_root_.CurrentAFT.Parameters.legCount security * 2)))))
  ring
open _root_.P2Mb748e9da renaming h297 → _p2mH297
end
open _root_.P2Mb748e9da renaming h297 → _p2mH297
end CurrentAFT.CurrentProtectedSourceParts
open _root_.P2Mb748e9da renaming h297 → _p2mH297
end
open _root_.P2Mb748e9da renaming h297 → _p2mH297
namespace CurrentAFT.CurrentProtectedSourceParts
end CurrentAFT.CurrentProtectedSourceParts
namespace CurrentAFT.CurrentProtectedSourceParts.joinParts
end CurrentAFT.CurrentProtectedSourceParts.joinParts
namespace CurrentAFT.CurrentProtectedSourceParts.partValue
end CurrentAFT.CurrentProtectedSourceParts.partValue
namespace CurrentAFT.CurrentProtectedSourceParts.partValue.match_1
end CurrentAFT.CurrentProtectedSourceParts.partValue.match_1
namespace CurrentAFT.FiniteProductFubini
end CurrentAFT.FiniteProductFubini
section
namespace CurrentAFT.CurrentProtectedAffineLaw
open AFT AffineFlagCalibration ActualAffineCompletedOutput ActualPublicCharge
  ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock ActualBlockMean
  ProposalPrimary DiffuseProfiles PublicAuxiliaryFubini FiniteProductFubini PublicCoefficientOutput
open HistogramNormalization PhysicalSynthesis
open CurrentSourceProtection CurrentProtectedSourceParts GaussianProductProtection
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedLawFinDecidableEq
attribute [local instance] _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedLawPrime
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h285 {Index Color : Type*} [Fintype Index]
    (slots : Index → Type*) (first second : Sigma slots → Color) :
    _root_.CurrentAFT.CurrentProtectedAffineLaw.delta first second = ∏ index, _root_.CurrentAFT.CurrentProtectedAffineLaw.delta (fun slot => first ⟨index, slot⟩) (fun slot => second ⟨index, slot⟩) := by
  exact _p2mH354 slots first second
open _root_.P2Mb748e9da renaming h285 → _p2mH285
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h286 {Input Output : Type*} [Fintype Input] [Fintype Output]
    (law : _root_.AFT.FiniteDist Input) (value : Input → Output) (target : Output) :
    (law.map value).weight target = law.expectation (fun input => _root_.CurrentAFT.CurrentProtectedAffineLaw.delta (value input) target) := by
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.expectation, _root_.CurrentAFT.CurrentProtectedAffineLaw.delta, mul_ite, mul_one, mul_zero]
open _root_.P2Mb748e9da renaming h286 → _p2mH286
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h292 (security : ℕ) (root : ℤ) (center : _root_.CurrentAFT.RefinedPublicOutput.Palette security)
    (word : Fin 1 → _root_.CurrentAFT.RefinedPublicOutput.Palette security) :
    (_root_.CurrentAFT.RefinedPublicOutput.singleton security root center).weight word =
      _root_.CurrentAFT.CurrentProtectedAffineLaw.delta (fun _ : Fin 1 => _root_.CurrentAFT.ProposalPrimary.shiftEquiv security root center) word := by
  rw [_root_.CurrentAFT.RefinedPublicOutput.singleton, _root_.CurrentAFT.FixedPairedFirst.pointLaw, _root_.AFT.FiniteDist.map_map]
  simp only [_root_.AFT.FiniteDist.map_weight, Fintype.sum_unique, _root_.AFT.FiniteDist.uniform_weight,
    Fintype.card_unique, Nat.cast_one, inv_one, _root_.CurrentAFT.CurrentProtectedAffineLaw.delta]
  split_ifs <;> rfl
open _root_.P2Mb748e9da renaming h292 → _p2mH292
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h282 (security : ℕ) (root : ℤ) (primary : _root_.CurrentAFT.AffineFlagCalibration.Palette security)
    (seed : _root_.CurrentAFT.ActualPublicCharge.LegCore security) (word : Fin 3 → _root_.CurrentAFT.RefinedPublicOutput.Palette security) :
    (_root_.CurrentAFT.AffineFlagCalibration.completedTriple security root primary seed).weight word =
      (_root_.CurrentAFT.AffineFlagCalibration.completionLaw security primary seed.1).expectation (fun chart =>
        (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).expectation (fun first => (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).expectation (fun second =>
          _root_.CurrentAFT.CurrentProtectedAffineLaw.delta (_root_.CurrentAFT.AffineFlagCalibration.evaluateTriple security root primary seed chart first second) word))) := by
  simp only [_root_.CurrentAFT.AffineFlagCalibration.completedTriple, _root_.AFT.FiniteDist.mix_weight, _p2mH286, _root_.AFT.FiniteDist.expectation]
open _root_.P2Mb748e9da renaming h282 → _p2mH282
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h283 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (queue : _root_.CurrentAFT.AffineFlagCalibration.Scalar security)
    (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security) :
    _root_.CurrentAFT.CurrentProtectedAffineLaw.conditionalChartOutput security layout core queue latent =
      _root_.CurrentAFT.ActualAffineCompletedOutput.conditionalLaw security layout core queue.val latent := by
  ext word
  simp only [_root_.CurrentAFT.CurrentProtectedAffineLaw.conditionalChartOutput, _root_.AFT.FiniteDist.mix_weight, _p2mH286]
  change (_root_.CurrentAFT.CurrentProtectedAffineLaw.chartProduct security core).expectation (fun charts => (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security).expectation
    (fun first => (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security).expectation (fun second =>
      _root_.CurrentAFT.CurrentProtectedAffineLaw.delta (_root_.CurrentAFT.CurrentProtectedAffineLaw.rawBlockWord security layout core queue latent charts first second) word))) = _
  simp_rw [_p2mH285 (_root_.CurrentAFT.ActualBlockFock.Slots security)]
  simp only [Fintype.prod_sum_type, _root_.CurrentAFT.CurrentProtectedAffineLaw.rawBlockWord]
  simp_rw [_root_.AFT.FiniteDist.expectation_mul_const]
  have hprod := _p2mH355
    (fun leg : Fin (_root_.CurrentAFT.Parameters.legCount security) =>
      _root_.CurrentAFT.AffineFlagCalibration.completionLaw security (core.controls (.inl leg)).1 (core.legs leg).1)
    (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.DiffuseProfiles.scalarLaw security)
    (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.DiffuseProfiles.scalarLaw security)
    (fun leg chart first second =>
      _root_.CurrentAFT.CurrentProtectedAffineLaw.delta (_root_.CurrentAFT.AffineFlagCalibration.evaluateTriple security (_root_.CurrentAFT.ActualBlockMean.attachmentRoots security layout core.bodyPermutation latent leg)
        (core.controls (.inl leg)).1 (core.legs leg) chart first second)
          (fun slot => word ⟨.inl leg, slot⟩))
  unfold _root_.CurrentAFT.ActualAffineCompletedOutput.conditionalLaw
  simp only [_root_.AFT.FiniteDist.retype_weight, _root_.AFT.BlockProducts.blockLaw, _root_.AFT.BlockProducts.blockMass,
    Fintype.prod_sum_type, _root_.CurrentAFT.ActualAffineCompletedOutput.blocks]
  apply congrArg₂ (fun a b : ℝ => a * b)
  · simp only [_p2mH282]
    exact hprod
  · simp only [_p2mH292]
    rfl
open _root_.P2Mb748e9da renaming h283 → _p2mH283
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h291 (security : ℕ) :
    (_root_.AFT.FiniteDist.retype (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security)).map (_root_.CurrentAFT.CurrentProtectedSourceParts.splitParts security) = _root_.CurrentAFT.CurrentProtectedAffineLaw.completedPartsLaw security := by
  ext parts
  rw [_root_.AFT.FiniteDist.map_equiv_weight, _root_.AFT.FiniteDist.retype_weight, _p2mH297,
    Equiv.apply_symm_apply]
  rfl
open _root_.P2Mb748e9da renaming h291 → _p2mH291
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h290 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (charts : _root_.CurrentAFT.CurrentProtectedAffineLaw.ChartWord security) :
    (_root_.AFT.FiniteDist.retype (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security)).map
      (_root_.CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord security layout core charts) =
        (_root_.CurrentAFT.CurrentProtectedAffineLaw.completedPartsLaw security).map (_root_.CurrentAFT.CurrentProtectedAffineLaw.rawOutputWord security layout core charts) := by
  rw [← _p2mH291, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2Mb748e9da renaming h290 → _p2mH290
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h287 {A B O : Type*} [Fintype A] [Fintype B] [Fintype O]
    (first : _root_.AFT.FiniteDist A) (second : _root_.AFT.FiniteDist B) (kernel : A × B → _root_.AFT.FiniteDist O) :
    (first.prod second).mix kernel = first.mix (fun a => second.mix (fun b => kernel (a, b))) := by
  ext output
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.prod_weight, Fintype.sum_prod_type,
    Finset.mul_sum, mul_assoc]
open _root_.P2Mb748e9da renaming h287 → _p2mH287
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h284 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (queue : _root_.CurrentAFT.AffineFlagCalibration.Scalar security)
    (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security) :
    (_root_.CurrentAFT.CurrentProtectedAffineLaw.chartProduct security core).mix (fun charts => (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security).mix (fun first =>
      (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security).map (fun second => _root_.CurrentAFT.CurrentProtectedAffineLaw.rawOutputWord security layout core charts
        (latent, (first, (second, queue)))))) =
      (_root_.CurrentAFT.CurrentProtectedAffineLaw.conditionalChartOutput security layout core queue latent).map
        (fun word => _root_.AFT.relabel (_root_.AFT.HistogramNormalization.renameWord (_root_.CurrentAFT.PublicCoefficientOutput.flatten security) word) core.endpointPermutation) := by
  unfold _root_.CurrentAFT.CurrentProtectedAffineLaw.conditionalChartOutput
  simp only [_root_.AFT.FiniteDist.map_mix, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2Mb748e9da renaming h284 → _p2mH284
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h289 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedChartPalette security layout core = _root_.CurrentAFT.ActualAffineCompletedOutput.lawGiven security layout core := by
  unfold _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedChartPalette
  simp_rw [_p2mH290]
  rw [_p2mH199]
  unfold _root_.CurrentAFT.CurrentProtectedAffineLaw.completedPartsLaw
  rw [_p2mH287]
  simp_rw [_p2mH287]
  simp_rw [_p2mH78 (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security) (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security)]
  rw [_p2mH78]
  simp_rw [_p2mH199 (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security) (_root_.CurrentAFT.CurrentProtectedAffineLaw.chartProduct security core)]
  simp_rw [_p2mH78 (_root_.CurrentAFT.CurrentProtectedAffineLaw.scalarProduct security) (_root_.CurrentAFT.CurrentProtectedAffineLaw.chartProduct security core)]
  simp_rw [_p2mH284, _p2mH283]
  rfl
open _root_.P2Mb748e9da renaming h289 → _p2mH289
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h288 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedChartMapped security layout core = _root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel security layout core := by
  rw [_root_.CurrentAFT.CurrentProtectedAffineLaw.protectedChartMapped, _p2mH289]
  rfl
open _root_.P2Mb748e9da renaming h288 → _p2mH288
end
open _root_.P2Mb748e9da renaming h282 → _p2mH282
open _root_.P2Mb748e9da renaming h283 → _p2mH283
open _root_.P2Mb748e9da renaming h284 → _p2mH284
open _root_.P2Mb748e9da renaming h285 → _p2mH285
open _root_.P2Mb748e9da renaming h286 → _p2mH286
open _root_.P2Mb748e9da renaming h287 → _p2mH287
open _root_.P2Mb748e9da renaming h288 → _p2mH288
open _root_.P2Mb748e9da renaming h289 → _p2mH289
open _root_.P2Mb748e9da renaming h290 → _p2mH290
open _root_.P2Mb748e9da renaming h291 → _p2mH291
open _root_.P2Mb748e9da renaming h292 → _p2mH292
end CurrentAFT.CurrentProtectedAffineLaw
open _root_.P2Mb748e9da renaming h282 → _p2mH282
open _root_.P2Mb748e9da renaming h283 → _p2mH283
open _root_.P2Mb748e9da renaming h284 → _p2mH284
open _root_.P2Mb748e9da renaming h285 → _p2mH285
open _root_.P2Mb748e9da renaming h286 → _p2mH286
open _root_.P2Mb748e9da renaming h287 → _p2mH287
open _root_.P2Mb748e9da renaming h288 → _p2mH288
open _root_.P2Mb748e9da renaming h289 → _p2mH289
open _root_.P2Mb748e9da renaming h290 → _p2mH290
open _root_.P2Mb748e9da renaming h291 → _p2mH291
open _root_.P2Mb748e9da renaming h292 → _p2mH292
end
open _root_.P2Mb748e9da renaming h282 → _p2mH282
open _root_.P2Mb748e9da renaming h283 → _p2mH283
open _root_.P2Mb748e9da renaming h284 → _p2mH284
open _root_.P2Mb748e9da renaming h285 → _p2mH285
open _root_.P2Mb748e9da renaming h286 → _p2mH286
open _root_.P2Mb748e9da renaming h287 → _p2mH287
open _root_.P2Mb748e9da renaming h288 → _p2mH288
open _root_.P2Mb748e9da renaming h289 → _p2mH289
open _root_.P2Mb748e9da renaming h290 → _p2mH290
open _root_.P2Mb748e9da renaming h291 → _p2mH291
open _root_.P2Mb748e9da renaming h292 → _p2mH292
namespace CurrentAFT.AffineFlagCalibration.completedTriple
end CurrentAFT.AffineFlagCalibration.completedTriple
namespace CurrentAFT.CurrentAffineSampleAgreement
end CurrentAFT.CurrentAffineSampleAgreement
namespace CurrentAFT.CurrentProtectedAffineLaw
end CurrentAFT.CurrentProtectedAffineLaw
namespace CurrentAFT.CurrentProtectedAffineLaw.conditionalChartOutput
end CurrentAFT.CurrentProtectedAffineLaw.conditionalChartOutput
namespace CurrentAFT.CurrentProtectedAffineLaw.delta
end CurrentAFT.CurrentProtectedAffineLaw.delta
namespace CurrentAFT.CurrentProtectedAffineLaw.protectedChartMapped
end CurrentAFT.CurrentProtectedAffineLaw.protectedChartMapped
namespace CurrentAFT.CurrentProtectedAffineLaw.rawBlockWord
end CurrentAFT.CurrentProtectedAffineLaw.rawBlockWord
namespace CurrentAFT.CurrentProtectedAffineLaw.rawBlockWord.match_1
end CurrentAFT.CurrentProtectedAffineLaw.rawBlockWord.match_1
namespace CurrentAFT.RefinedPublicOutput.singleton
end CurrentAFT.RefinedPublicOutput.singleton
section
namespace CurrentAFT.CurrentProtectedSampleFubini
open AFT CurrentSourceProtection CurrentSourceLayout CurrentHiddenSourceTransport
  CurrentPublicAffineSample CurrentAffinePhysicalEndpoint CurrentAffineSampleAgreement
  GaussianProductProtection ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h296 {Public Charts Output : Type*}
    [Fintype Public] [Fintype Charts] [Fintype Output]
    (security : ℕ) (publicLaw : _root_.AFT.FiniteDist Public) (chartLaw : Public → _root_.AFT.FiniteDist Charts)
    (value : Public → Charts → _root_.CurrentAFT.GaussianProductProtection.ProtectedWord (_root_.CurrentAFT.CurrentSourceProtection.cutoff security) → Output) :
    ((_root_.AFT.FiniteDist.joint publicLaw chartLaw).prod (_root_.CurrentAFT.CurrentHiddenSourceTransport.closureLaw security)).mix
      (fun sample => (_root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenLaw security).map (fun input =>
        value sample.1.1 sample.1.2 (_root_.CurrentAFT.CurrentHiddenSourceTransport.joinProtected security (input, sample.2)))) =
      publicLaw.mix (fun publicDraw => (chartLaw publicDraw).mix (fun charts =>
        (_root_.CurrentAFT.CurrentSourceProtection.protectedSourceLaw security).map (value publicDraw charts))) := by
  rw [← _p2mH279 security]
  simp_rw [_root_.AFT.FiniteDist.map_map]
  ext output
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.prod_weight,
    _root_.AFT.FiniteDist.joint, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro publicDraw _
  apply Finset.sum_congr rfl
  intro charts _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  apply Finset.sum_congr rfl
  intro closure _
  split_ifs <;> ring
open _root_.P2Mb748e9da renaming h296 → _p2mH296
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h295 (security : ℕ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security)) :
    _root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive =
      (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).mix
        (_root_.CurrentAFT.CurrentProtectedSampleFubini.corePhysicalLaw security layout) := by
  calc
    _ = (_root_.CurrentAFT.CurrentPublicAffineSample.law security weight hpositive).mix (fun sample => (_root_.CurrentAFT.CurrentHiddenSourceTransport.hiddenLaw security).map
        (_root_.CurrentAFT.CurrentAffineSampleAgreement.physicalWord security layout sample)) := by
      apply _p2mH79
      intro sample hsample
      congr 1
      funext input
      exact _p2mH270 security layout weight hpositive sample hsample input
    _ = _ := _p2mH296 security
      (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive)
      (_root_.CurrentAFT.CurrentPublicAffineSample.chartsLaw security) (fun core charts word index =>
        _root_.CurrentAFT.RefinedPublicOutput.embed security (_root_.CurrentAFT.CurrentAffinePhysicalEndpoint.outputWord security layout core charts word index))
open _root_.P2Mb748e9da renaming h295 → _p2mH295
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h293 (security : ℕ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
    _root_.CurrentAFT.CurrentProtectedSampleFubini.corePhysicalLaw security layout core =
      _root_.AFT.FiniteDist.retype (_root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel security layout core) := by
  rw [← _p2mH288]
  unfold _root_.CurrentAFT.CurrentProtectedSampleFubini.corePhysicalLaw _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedChartMapped
    _root_.CurrentAFT.CurrentProtectedAffineLaw.protectedChartPalette
  simp only [_root_.AFT.FiniteDist.map_mix, _root_.AFT.FiniteDist.map_map]
  ext word
  simp only [_root_.AFT.FiniteDist.retype_weight, _root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_weight]
  apply Finset.sum_congr (by ext charts; simp)
  intro charts _
  apply congrArg₂ (fun first second : ℝ => first * second) rfl
  apply Finset.sum_congr (by ext source; simp)
  intro source _
  split_ifs <;> rfl
open _root_.P2Mb748e9da renaming h293 → _p2mH293
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h294 (security : ℕ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (weight : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security)) :
    _root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw security layout weight hpositive =
      (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) weight (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).mix
        (fun core => _root_.AFT.FiniteDist.retype (_root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel security layout core)) := by
  rw [_p2mH295]
  congr 1
  funext core
  exact _p2mH293 security layout core
open _root_.P2Mb748e9da renaming h294 → _p2mH294
end
open _root_.P2Mb748e9da renaming h293 → _p2mH293
open _root_.P2Mb748e9da renaming h294 → _p2mH294
open _root_.P2Mb748e9da renaming h295 → _p2mH295
open _root_.P2Mb748e9da renaming h296 → _p2mH296
end CurrentAFT.CurrentProtectedSampleFubini
open _root_.P2Mb748e9da renaming h293 → _p2mH293
open _root_.P2Mb748e9da renaming h294 → _p2mH294
open _root_.P2Mb748e9da renaming h295 → _p2mH295
open _root_.P2Mb748e9da renaming h296 → _p2mH296
end
open _root_.P2Mb748e9da renaming h293 → _p2mH293
open _root_.P2Mb748e9da renaming h294 → _p2mH294
open _root_.P2Mb748e9da renaming h295 → _p2mH295
open _root_.P2Mb748e9da renaming h296 → _p2mH296
section
namespace CurrentAFT.AffineActivationFubini
open AFT AffineFlagCalibration ActualPublicCharge ActualPublicLegCharge
  ActualAffineCompletedOutput DiffuseProfiles ProposalPrimary LocalReferenceEnergy
  PublicOutputExperiment PublicAuxiliaryFubini ActualCycleMeanMGF ConditionalHistogramMean
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationFubiniFinDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationFubiniProdDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationPublicIndexDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationBodyIndexDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationEndpointIndexDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationQueueIndexDecidableEq
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationAnchorNonempty
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h172 {Index Input Output : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Input] [Fintype Output]
    (reference : Index → _root_.AFT.FiniteDist Input) (value : Index → Input → Output) :
    (_root_.AFT.FiniteDist.independent reference).map (fun word index => value index (word index)) =
      _root_.AFT.FiniteDist.independent (fun index => (reference index).map (value index)) := by
  ext target
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_ite_zero]
  have heq : (∀ index ∈ (Finset.univ : Finset Index), value index (word index) = target index) ↔
      (fun index => value index (word index)) = target := by
    simp only [Finset.mem_univ, forall_true_left, funext_iff]
  simp only [heq]
open _root_.P2Mb748e9da renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h173 (security : ℕ) (test : _root_.CurrentAFT.ActualPublicCharge.LegCore security → ℝ) :
    (_root_.CurrentAFT.ActualPublicCharge.legCoreLaw security).expectation test =
      (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).expectation (fun flag =>
        (_root_.CurrentAFT.AffineActivationFubini.legAuxLaw security).expectation (fun aux => test (_root_.CurrentAFT.AffineActivationFubini.joinLeg security flag aux))) := by
  unfold _root_.CurrentAFT.ActualPublicCharge.legCoreLaw _root_.CurrentAFT.ActualPublicLegCharge.seedLaw _root_.CurrentAFT.AffineActivationFubini.legAuxLaw
  simp only [_root_.AFT.FiniteDist.expectation_prod, _root_.AFT.FiniteDist.expectation_map, Function.comp_def]
  rfl
open _root_.P2Mb748e9da renaming h173 → _p2mH173
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h175 (security : ℕ) (test : _root_.CurrentAFT.ActualPublicCharge.LegCore security → ℝ) :
    (_root_.CurrentAFT.ActualPublicCharge.legCoreLaw security).expectation (fun seed => (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).expectation
      (fun flag => test (_root_.CurrentAFT.AffineFlagCalibration.setMarked security seed.1 flag, seed.2))) =
        (_root_.CurrentAFT.ActualPublicCharge.legCoreLaw security).expectation test := by
  rw [_p2mH173, _p2mH173]
  change (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).expectation (fun _ =>
    (_root_.CurrentAFT.AffineActivationFubini.legAuxLaw security).expectation (fun aux => (_root_.CurrentAFT.ActualPublicLegCharge.activationLaw security).expectation
      (fun flag => test (_root_.CurrentAFT.AffineActivationFubini.joinLeg security flag aux)))) = _
  rw [_root_.AFT.FiniteDist.expectation_const, _root_.AFT.FiniteDist.expectation_comm]
open _root_.P2Mb748e9da renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h174 (security : ℕ) :
    (_root_.CurrentAFT.ActualPublicCharge.legCoreLaw security).mix (_root_.CurrentAFT.AffineActivationFubini.legRefresh security) = _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security := by
  ext target
  have h := _p2mH175 security
    (fun seed => if seed = target then (1 : ℝ) else 0)
  simp only [_root_.AFT.FiniteDist.expectation, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  simpa only [_root_.AFT.FiniteDist.mix_weight, _root_.CurrentAFT.AffineActivationFubini.legRefresh, _root_.AFT.FiniteDist.map_weight] using h
open _root_.P2Mb748e9da renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h176 (security : ℕ) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security)).mix
      (fun legs => (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).map (_root_.CurrentAFT.AffineActivationFubini.updateLegs security legs)) =
        _root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security) := by
  have hk (legs : Fin (_root_.CurrentAFT.Parameters.legCount security) → _root_.CurrentAFT.ActualPublicCharge.LegCore security) :
      (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).map (_root_.CurrentAFT.AffineActivationFubini.updateLegs security legs) =
        _root_.AFT.FiniteDist.independent (fun leg => _root_.CurrentAFT.AffineActivationFubini.legRefresh security (legs leg)) :=
    _p2mH172 (fun _ => _root_.CurrentAFT.ActualPublicLegCharge.activationLaw security)
      (fun leg flag => (_root_.CurrentAFT.AffineFlagCalibration.setMarked security (legs leg).1 flag, (legs leg).2))
  simp_rw [hk]
  rw [_p2mH23]
  simp only [_p2mH174]
open _root_.P2Mb748e9da renaming h176 → _p2mH176
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h177 (security : ℕ)
    (test : (Fin (_root_.CurrentAFT.Parameters.legCount security) → _root_.CurrentAFT.ActualPublicCharge.LegCore security) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security)).expectation
      (fun legs => (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).expectation (fun bits => test (_root_.CurrentAFT.AffineActivationFubini.updateLegs security legs bits))) =
      (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security)).expectation test := by
  have h := congrArg (fun law => law.expectation test) (_p2mH176 security)
  simp only [_p2mH426, _root_.AFT.FiniteDist.expectation_map, Function.comp_def] at h
  exact h
open _root_.P2Mb748e9da renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h178 (security : ℕ)
    [decision : DecidableEq (Fin (_root_.CurrentAFT.Parameters.legCount security))]
    (test : (Fin (_root_.CurrentAFT.Parameters.legCount security) → _root_.CurrentAFT.ActualPublicCharge.LegCore security) → ℝ) :
    (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security)).expectation
      (fun legs => (_root_.AFT.FiniteDist.retype (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security)).expectation
        (fun bits => test (_root_.CurrentAFT.AffineActivationFubini.updateLegs security legs bits))) =
      (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.legCount security) => _root_.CurrentAFT.ActualPublicCharge.legCoreLaw security)).expectation test := by
  have hd : decision = _root_.CurrentAFT.AffineActivationFubini.activationFubiniFinDecidableEq (_root_.CurrentAFT.Parameters.legCount security) := Subsingleton.elim _ _
  cases hd
  simpa only [_p2mH76] using _p2mH177 security test
open _root_.P2Mb748e9da renaming h178 → _p2mH178
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h181 (security : ℕ) (test : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ) :
    (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation (fun core => (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).expectation
      (fun bits => test (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits))) =
        (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation test := by
  rw [_p2mH162, _p2mH162]
  apply congrArg (_root_.AFT.FiniteDist.expectation (_root_.CurrentAFT.PublicOutputExperiment.reference security))
  funext controls
  unfold _root_.CurrentAFT.ActualPublicCharge.auxiliaryLaw _root_.CurrentAFT.ActualPublicCharge.localSeedsLaw _root_.CurrentAFT.ActualPublicCharge.bodyPermutationLaw _root_.CurrentAFT.ActualPublicCharge.endpointPermutationLaw
  simp only [_root_.AFT.FiniteDist.expectation_map, Function.comp_def, _root_.AFT.FiniteDist.expectation_prod]
  simp_rw [_root_.AFT.FiniteDist.expectation_comm
    (_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin (_root_.CurrentAFT.Parameters.dimension security)))) (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security)]
  simp_rw [_root_.AFT.FiniteDist.expectation_comm
    (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))) (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security)]
  simp_rw [_root_.AFT.FiniteDist.expectation_comm
    (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.modulus security) => _root_.CurrentAFT.ProposalPrimary.safeLaw security))
      (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security)]
  have href := (@_p2mH178 security (instDecidableEqFin _) (fun legs =>
    (_root_.AFT.FiniteDist.independent (fun _ : Fin (_root_.CurrentAFT.Parameters.modulus security) => _root_.CurrentAFT.ProposalPrimary.safeLaw security)).expectation (fun baselines =>
      (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))).expectation (fun body =>
        (_root_.AFT.FiniteDist.uniform (Equiv.Perm (Fin (_root_.CurrentAFT.Parameters.dimension security)))).expectation
          (fun endpoints => test ⟨controls, legs, baselines, body, endpoints⟩)))))
  simp only [_p2mH76] at href
  convert href using 1 <;> rfl
open _root_.P2Mb748e9da renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h182 (security : ℕ) (multiplier test : _root_.CurrentAFT.ActualPublicCharge.Core security → ℝ)
    (hinvariant : ∀ core bits, multiplier (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits) = multiplier core) :
    (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation (fun core => multiplier core *
      (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).expectation (fun bits => test (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits))) =
        (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation (fun core => multiplier core * test core) := by
  calc
    _ = (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation (fun core => (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security).expectation
        (fun bits => multiplier (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits) *
          test (_root_.CurrentAFT.AffineFlagCalibration.setActivationBits security core bits))) := by
      apply congrArg (_root_.AFT.FiniteDist.expectation (_root_.CurrentAFT.ActualPublicCharge.proposal security))
      funext core
      rw [← _root_.AFT.FiniteDist.expectation_const_mul]
      apply congrArg (_root_.AFT.FiniteDist.expectation (_root_.CurrentAFT.ActualAffineCompletedOutput.activationBitsLaw security))
      funext bits
      rw [hinvariant]
    _ = _ := _p2mH181 security (fun core => multiplier core * test core)
open _root_.P2Mb748e9da renaming h182 → _p2mH182
attribute [local instance] _root_.CurrentAFT.AffineActivationFubini.activationOutputEndpointDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h179 (security order : ℕ)
    (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (word : Fin (_root_.CurrentAFT.Parameters.dimension security) → _root_.CurrentAFT.RefinedPublicOutput.Residue security) :
    (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation (fun core => _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient core *
      (_root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel security layout core).weight word) =
    (_root_.CurrentAFT.ActualPublicCharge.proposal security).expectation (fun core => _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient core *
      (_root_.CurrentAFT.RefinedPublicOutput.mappedChannel security layout core).weight word) := by
  have h := _p2mH182 security (_root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient)
    (fun core => (_root_.CurrentAFT.RefinedPublicOutput.mappedChannel security layout core).weight word)
    (_p2mH201 security order coefficient)
  apply Eq.trans _ h
  apply congrArg (_root_.AFT.FiniteDist.expectation (_root_.CurrentAFT.ActualPublicCharge.proposal security))
  funext core
  apply congrArg (fun x : ℝ => _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient core * x)
  exact congrArg (fun law => law.weight word) (_p2mH123 security layout core).symm
open _root_.P2Mb748e9da renaming h179 → _p2mH179
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h180 (security order : ℕ)
    (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
      (_root_.CurrentAFT.ActualPublicCharge.publicCharge security)) :
    (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
      (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).mix (_root_.CurrentAFT.ActualAffineCompletedOutput.mappedChannel security layout) =
    (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
      (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).mix (_root_.CurrentAFT.RefinedPublicOutput.mappedChannel security layout) := by
  ext word
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.CurrentAFT.positivePublicCoreLaw, _root_.AFT.FiniteDist.normalize,
    div_mul_eq_mul_div, ← Finset.sum_div]
  apply congrArg (fun numerator : ℝ => numerator /
    ∑ core, _root_.CurrentAFT.clippedPublicCoreWeight (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
      (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) core)
  have hw (core : _root_.CurrentAFT.ActualPublicCharge.Core security) :
      _root_.CurrentAFT.clippedPublicCoreWeight (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
        (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) core =
      (_root_.CurrentAFT.ActualPublicCharge.proposal security).weight core * _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier security order coefficient core := by
    unfold _root_.CurrentAFT.clippedPublicCoreWeight _root_.CurrentAFT.AffineFlagCalibration.positiveMultiplier
    split_ifs <;> ring
  simp_rw [hw]
  simpa only [_root_.AFT.FiniteDist.expectation, mul_assoc] using
    _p2mH179 security order coefficient layout word
open _root_.P2Mb748e9da renaming h180 → _p2mH180
end
open _root_.P2Mb748e9da renaming h172 → _p2mH172
open _root_.P2Mb748e9da renaming h173 → _p2mH173
open _root_.P2Mb748e9da renaming h174 → _p2mH174
open _root_.P2Mb748e9da renaming h175 → _p2mH175
open _root_.P2Mb748e9da renaming h176 → _p2mH176
open _root_.P2Mb748e9da renaming h177 → _p2mH177
open _root_.P2Mb748e9da renaming h178 → _p2mH178
open _root_.P2Mb748e9da renaming h179 → _p2mH179
open _root_.P2Mb748e9da renaming h180 → _p2mH180
open _root_.P2Mb748e9da renaming h181 → _p2mH181
open _root_.P2Mb748e9da renaming h182 → _p2mH182
end CurrentAFT.AffineActivationFubini
open _root_.P2Mb748e9da renaming h172 → _p2mH172
open _root_.P2Mb748e9da renaming h173 → _p2mH173
open _root_.P2Mb748e9da renaming h174 → _p2mH174
open _root_.P2Mb748e9da renaming h175 → _p2mH175
open _root_.P2Mb748e9da renaming h176 → _p2mH176
open _root_.P2Mb748e9da renaming h177 → _p2mH177
open _root_.P2Mb748e9da renaming h178 → _p2mH178
open _root_.P2Mb748e9da renaming h179 → _p2mH179
open _root_.P2Mb748e9da renaming h180 → _p2mH180
open _root_.P2Mb748e9da renaming h181 → _p2mH181
open _root_.P2Mb748e9da renaming h182 → _p2mH182
end
open _root_.P2Mb748e9da renaming h172 → _p2mH172
open _root_.P2Mb748e9da renaming h173 → _p2mH173
open _root_.P2Mb748e9da renaming h174 → _p2mH174
open _root_.P2Mb748e9da renaming h175 → _p2mH175
open _root_.P2Mb748e9da renaming h176 → _p2mH176
open _root_.P2Mb748e9da renaming h177 → _p2mH177
open _root_.P2Mb748e9da renaming h178 → _p2mH178
open _root_.P2Mb748e9da renaming h179 → _p2mH179
open _root_.P2Mb748e9da renaming h180 → _p2mH180
open _root_.P2Mb748e9da renaming h181 → _p2mH181
open _root_.P2Mb748e9da renaming h182 → _p2mH182
namespace CurrentAFT.ActualCalibrationExact
end CurrentAFT.ActualCalibrationExact
namespace CurrentAFT.AffineActivationFubini
end CurrentAFT.AffineActivationFubini
namespace CurrentAFT.AffineActivationFubini.legRefresh
end CurrentAFT.AffineActivationFubini.legRefresh
namespace CurrentAFT.CurrentProtectedSampleFubini
end CurrentAFT.CurrentProtectedSampleFubini
namespace CurrentAFT.CurrentSourceTail
end CurrentAFT.CurrentSourceTail
namespace CurrentAFT.FiniteEnumeration
end CurrentAFT.FiniteEnumeration
section
namespace CurrentAFT.ActualGaussianAffine
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber CurrentProtectedSampleFubini
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.ActualGaussianAffine.modulusNeZero
attribute [local instance] _root_.CurrentAFT.ActualGaussianAffine.dimensionNonempty
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h161 (security : ℕ) (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (core : _root_.CurrentAFT.ActualPublicCharge.Core security) (word : _root_.CurrentAFT.CurrentZeroFiber.Word security) :
    (_root_.AFT.FiniteDist.retype (_root_.CurrentAFT.RefinedPublicOutput.mappedChannel security layout core) :
      _root_.AFT.FiniteDist (_root_.CurrentAFT.CurrentZeroFiber.Word security)).weight word =
      (_root_.CurrentAFT.ActualPublicExperiment.channel security layout core).weight word := by
  unfold _root_.CurrentAFT.RefinedPublicOutput.mappedChannel _root_.CurrentAFT.ActualPublicExperiment.channel _root_.CurrentAFT.ActualPublicExperiment.paletteChannel
  simp only [_root_.AFT.FiniteDist.map_weight, _root_.AFT.FiniteDist.retype_weight]
  apply Finset.sum_congr (by ext source; simp)
  intro source _
  have he : _root_.CurrentAFT.PublicEndpointFourier.wordEquiv (ZMod.finEquiv (_root_.CurrentAFT.Parameters.modulus security)).toEquiv source =
      (fun index => _root_.CurrentAFT.RefinedPublicOutput.embed security (source index)) := by
    funext index
    rfl
  rw [he]
  split_ifs <;> rfl
open _root_.P2Mb748e9da renaming h161 → _p2mH161
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h160 (security order : ℕ)
    (coefficient : _root_.CurrentAFT.ActualControls.Coefficients security order)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient) (_root_.CurrentAFT.ActualPublicCharge.publicCharge security)) :
    _root_.CurrentAFT.CurrentAffineTransport.protectedEndpointLaw security layout (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient) hpositive =
      (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
        (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).mix (_root_.CurrentAFT.ActualPublicExperiment.channel security layout) := by
  rw [_p2mH294]
  ext word
  have h := congrArg (fun distribution =>
      (_root_.AFT.FiniteDist.retype distribution : _root_.AFT.FiniteDist (_root_.CurrentAFT.CurrentZeroFiber.Word security)).weight word)
    (_p2mH180 security order coefficient layout hpositive)
  simp only [_root_.AFT.FiniteDist.retype_weight, _root_.AFT.FiniteDist.mix_weight] at h
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.retype_weight]
  calc
    _ = ∑ core, (_root_.CurrentAFT.positivePublicCoreLaw (_root_.CurrentAFT.ActualPublicCharge.proposal security) (_root_.CurrentAFT.ActualPublicCharge.pulledWeight security order coefficient)
          (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) hpositive).weight core *
        (_root_.AFT.FiniteDist.retype (_root_.CurrentAFT.RefinedPublicOutput.mappedChannel security layout core) :
          _root_.AFT.FiniteDist (_root_.CurrentAFT.CurrentZeroFiber.Word security)).weight word := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro core _
      rw [_p2mH161]
open _root_.P2Mb748e9da renaming h160 → _p2mH160
end
open _root_.P2Mb748e9da renaming h160 → _p2mH160
open _root_.P2Mb748e9da renaming h161 → _p2mH161
end CurrentAFT.ActualGaussianAffine
open _root_.P2Mb748e9da renaming h160 → _p2mH160
open _root_.P2Mb748e9da renaming h161 → _p2mH161
end
open _root_.P2Mb748e9da renaming h160 → _p2mH160
open _root_.P2Mb748e9da renaming h161 → _p2mH161
namespace CurrentAFT.ActualGaussianAffine
end CurrentAFT.ActualGaussianAffine
section
namespace CurrentAFT.ActualGaussianAccuracy
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCalibrationClipping ActualGaussianAffine
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.ActualGaussianAccuracy.modulusNeZero
attribute [local instance] _root_.CurrentAFT.ActualGaussianAccuracy.dimensionNonempty
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h159 (accuracyOrder : ℕ) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∀ hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
          (_p2mH134 accuracyOrder) ≤ security,
      ∀ layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security,
      ∃ hpositive : 0 < _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security)
          (_root_.CurrentAFT.ActualCalibratedPublic.weight security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
            (_p2mH134 accuracyOrder) hsecurity layout) (_root_.CurrentAFT.ActualPublicCharge.publicCharge security),
        1 / (2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security)
          (_root_.CurrentAFT.ActualCalibratedPublic.weight security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
            (_p2mH134 accuracyOrder) hsecurity layout) (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) ∧
        (_root_.CurrentAFT.CurrentAffineTransport.gaussianLaw security layout
          (_root_.CurrentAFT.ActualCalibratedPublic.weight security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
            (_p2mH134 accuracyOrder) hsecurity layout) hpositive).totalVariation
          (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security) ≤
            2 * (_root_.CurrentAFT.Parameters.modulus security : ℝ) *
              (_root_.CurrentAFT.ActualCalibrationRates.fourierError security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) +
                _root_.CurrentAFT.ActualCalibrationClipping.loss security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
                  (_p2mH134 accuracyOrder) hsecurity (_root_.CurrentAFT.ActualLayouts.blockLayout layout)) +
              _root_.CurrentAFT.CurrentSourceProtection.budget security := by
  obtain ⟨cutoff, hcutoff⟩ := ActualCalibratedPublic.positive_eventually accuracyOrder
  refine ⟨cutoff, ?_⟩
  intro security hlarge hsecurity layout
  obtain ⟨hpositive, hlower, herror⟩ := hcutoff security hlarge hsecurity layout
    (_p2mH128 security _ _ hsecurity layout)
  refine ⟨hpositive, hlower, ?_⟩
  apply _p2mH271
  unfold _root_.CurrentAFT.ActualCalibratedPublic.weight
  rw [_p2mH160]
  exact herror
open _root_.P2Mb748e9da renaming h159 → _p2mH159
end
open _root_.P2Mb748e9da renaming h159 → _p2mH159
end CurrentAFT.ActualGaussianAccuracy
open _root_.P2Mb748e9da renaming h159 → _p2mH159
end
open _root_.P2Mb748e9da renaming h159 → _p2mH159
namespace CurrentAFT.ActualGaussianAccuracy
end CurrentAFT.ActualGaussianAccuracy
namespace CurrentAFT.ActualGaussianAccuracy.five_inversePower
end CurrentAFT.ActualGaussianAccuracy.five_inversePower
namespace CurrentAFT.CurrentChartsDraw
end CurrentAFT.CurrentChartsDraw
namespace CurrentAFT.CurrentChartsDraw.tapeLaw
end CurrentAFT.CurrentChartsDraw.tapeLaw
namespace CurrentAFT.CurrentMaterializedCompletion
end CurrentAFT.CurrentMaterializedCompletion
namespace CurrentAFT.CurrentMaterializedCompletion.publicLaw
end CurrentAFT.CurrentMaterializedCompletion.publicLaw
section
namespace CurrentAFT.NumericalGaussianAccuracy
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineTransport CurrentPublicAffineSample CurrentZeroFiber
  ActualCompleteStability ActualCalibrationFourier ActualCalibrationRates
  ActualCalibrationClipping ActualGaussianAccuracy
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2Mb748e9da.h396 (security order : ℕ) (hsecurity : 3  ≤  security) :
    4*_root_.CurrentAFT.inversePower security (order+2)+2/(security : ℝ)^(order+2)  ≤  1/(security : ℝ)^order := by
  have hs : (3 : ℝ) ≤ security := by exact_mod_cast hsecurity
  have hspos : (0 : ℝ)<security := by linarith
  have hb : (security : ℝ) ≤ _root_.CurrentAFT.Parameters.base security := by
    exact_mod_cast (show security ≤ _root_.CurrentAFT.Parameters.base security by unfold _root_.CurrentAFT.Parameters.base; omega)
  have hi : _root_.CurrentAFT.inversePower security (order+2) ≤ 1/(security : ℝ)^(order+2) :=
    one_div_le_one_div_of_le (pow_pos hspos _) (pow_le_pow_left₀ hspos.le hb _)
  calc
    _ ≤ 4*(1/(security : ℝ)^(order+2))+2/(security : ℝ)^(order+2) := by linarith only [hi]
    _ = 6/(security : ℝ)^(order+2) := by ring
    _  ≤  _ := by
      rw [pow_add]
      apply (div_le_div_iff₀ (mul_pos (pow_pos hspos _) (pow_pos hspos _)) (pow_pos hspos _)).mpr
      have hsq : (6 : ℝ) ≤ (security : ℝ)^2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hsq (pow_nonneg hspos.le order)]
open _root_.P2Mb748e9da renaming h396 → _p2mH396
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.NumericalGaussianAccuracy.__p2m_proof_b748e9dae4cdac970986 (accuracyOrder : ℕ) (extra : ℕ → ℝ) (hextra : _root_.AFT.Negligible extra) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      ∃ hsecurity : _root_.CurrentAFT.ActualCompleteStability.threshold (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
        (_p2mH134 accuracyOrder) ≤ security,
      ∀ layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security,
      ∃ hpositive : 0<_root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security)
        (_root_.CurrentAFT.ActualCalibratedPublic.weight security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
          (_p2mH134 accuracyOrder) hsecurity layout) (_root_.CurrentAFT.ActualPublicCharge.publicCharge security),
        1/(2*(_root_.CurrentAFT.Parameters.modulus security : ℝ)) ≤ _root_.CurrentAFT.publicCoreMass (_root_.CurrentAFT.ActualPublicCharge.proposal security)
          (_root_.CurrentAFT.ActualCalibratedPublic.weight security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
            (_p2mH134 accuracyOrder) hsecurity layout) (_root_.CurrentAFT.ActualPublicCharge.publicCharge security) ∧
        (_root_.CurrentAFT.CurrentAffineTransport.gaussianLaw security layout
          (_root_.CurrentAFT.ActualCalibratedPublic.weight security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
            (_p2mH134 accuracyOrder) hsecurity layout) hpositive).totalVariation
          (_root_.CurrentAFT.CurrentZeroFiber.uniformFiber security)+extra security  ≤  (security : ℝ)^(-(accuracyOrder : ℝ)) := by
  obtain ⟨positiveCutoff, hpositive⟩ := _p2mH159 accuracyOrder
  obtain ⟨clipCutoff, hclip⟩ := _p2mH126 (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
    (_p2mH134 accuracyOrder) (accuracyOrder+2)
  have hall : ∀ᶠ security : ℕ in atTop,
      positiveCutoff ≤ security ∧ clipCutoff ≤ security ∧
      _root_.CurrentAFT.ActualCompleteStability.threshold (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) (_p2mH134 accuracyOrder) ≤ security ∧
      3 ≤ security ∧ (_root_.CurrentAFT.Parameters.modulus security : ℝ)*
        _root_.CurrentAFT.ActualCalibrationRates.fourierError security (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder) ≤ _root_.CurrentAFT.inversePower security (accuracyOrder+2) ∧
      |_root_.CurrentAFT.CurrentSourceProtection.budget security| ≤ 1/(security : ℝ)^(accuracyOrder+2) ∧
      |extra security| ≤ 1/(security : ℝ)^(accuracyOrder+2) := by
    filter_upwards [eventually_ge_atTop positiveCutoff, eventually_ge_atTop clipCutoff,
      eventually_ge_atTop (_root_.CurrentAFT.ActualCompleteStability.threshold (_root_.CurrentAFT.Parameters.calibrationOrder accuracyOrder)
        (_p2mH134 accuracyOrder)), eventually_ge_atTop 3,
      _p2mH135 accuracyOrder, _p2mH328 (accuracyOrder+2),
      hextra (accuracyOrder+2)] with security hp hc ht hs hf hb he
    exact ⟨hp, hc, ht, hs, hf, hb, he⟩
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  refine ⟨cutoff, ?_⟩
  intro security hlarge
  obtain ⟨hp, hc, ht, hs, hf, hb, he⟩ := hcutoff security hlarge
  refine ⟨ht, ?_⟩
  intro layout
  obtain ⟨hcore, hlower, hbound⟩ := hpositive security hp ht layout
  have hloss := hclip security hc ht (_root_.CurrentAFT.ActualLayouts.blockLayout layout)
  have hbudget := (le_abs_self (_root_.CurrentAFT.CurrentSourceProtection.budget security)).trans hb
  have hnum := (le_abs_self (extra security)).trans he
  refine ⟨hcore, hlower, ?_⟩
  calc
    _  ≤  4*_root_.CurrentAFT.inversePower security (accuracyOrder+2)+2/(security : ℝ)^(accuracyOrder+2) := by
      rw [show 2/(security : ℝ)^(accuracyOrder+2) = 2*(1/(security : ℝ)^(accuracyOrder+2)) by ring]
      nlinarith only [hf, hloss, hbudget, hbound, hnum]
    _  ≤  1/(security : ℝ)^accuracyOrder := _p2mH396 security accuracyOrder hs
    _ = _ := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      simp only [one_div]
end
open _root_.P2Mb748e9da renaming h396 → _p2mH396
end CurrentAFT.NumericalGaussianAccuracy
open _root_.P2Mb748e9da renaming h396 → _p2mH396
end
open _root_.P2Mb748e9da renaming h396 → _p2mH396
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.NumericalGaussianAccuracy.__p2m_proof_b748e9dae4cdac970986) := @_root_.CurrentAFT.NumericalGaussianAccuracy.__p2m_proof_b748e9dae4cdac970986
