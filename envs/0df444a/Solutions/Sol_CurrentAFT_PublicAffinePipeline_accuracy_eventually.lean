-- Prove2me | solution 1 for CurrentAFT.PublicAffinePipeline.accuracy_eventually
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T22:06:51.471783+00:00
-- url     : https://prove2.me/submissions/b90da8a8-61b3-4a2d-b133-cf58b6e702e3

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Theorems.Thm_AFT_FiniteDist_l1_independent_fin_le
import Theorems.Thm_AFT_FiniteDist_l1_independent_le
import Theorems.Thm_AFT_FiniteDist_l1_map_le
import Theorems.Thm_AFT_FiniteDist_l1_prod_le
import Theorems.Thm_AFT_FiniteDist_totalVariation_eq_half_l1
import Theorems.Thm_CurrentAFT_NumericalGaussianAccuracy_gaussian_with_numerics
namespace P2M661a572e
end P2M661a572e
section
namespace AFT
namespace FiniteDist
open scoped BigOperators
open scoped Classical
variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h79 (p : FiniteDist α) (s : Finset α) : 0 ≤ p.event s :=
  Finset.sum_nonneg (fun a _ => p.nonneg a)
open _root_.P2M661a572e renaming h79 → AFT.FiniteDist.event_nonneg
open _root_.P2M661a572e renaming h79 → _p2mH79
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h94 (p : FiniteDist α) : TVBound p p 0 := by
  intro s
  simp
open _root_.P2M661a572e renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h69 {p q : FiniteDist α} {error largerError : ℝ}
    (h : TVBound p q error) (hle : error ≤ largerError) :
    TVBound p q largerError := fun s => (h s).trans hle
open _root_.P2M661a572e renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2M661a572e renaming h69 → _p2mH69
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h70 {p q r : FiniteDist α} {firstError secondError : ℝ}
    (hfirst : TVBound p q firstError) (hsecond : TVBound q r secondError) :
    TVBound p r (firstError + secondError) := by
  intro s
  calc
    |p.event s - r.event s| ≤ |p.event s - q.event s| + |q.event s - r.event s| :=
      abs_sub_le _ _ _
    _ ≤ firstError + secondError := add_le_add (hfirst s) (hsecond s)
open _root_.P2M661a572e renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2M661a572e renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h77 (p : FiniteDist α) (f : α → β) (s : Finset β) :
    (p.map f).event s = ∑ a, if f a ∈ s then p.weight a else 0 := by
  classical
  simp only [event, map_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [eq_comm]
open _root_.P2M661a572e renaming h77 → _p2mH77
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h66 {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) (f : α → β) : TVBound (p.map f) (q.map f) error := by
  classical
  intro s
  rw [_p2mH77, _p2mH77]
  simpa only [event, Finset.sum_filter] using
    h (Finset.univ.filter (fun a => f a ∈ s))
open _root_.P2M661a572e renaming h66 → AFT.FiniteDist.TVBound.map
open _root_.P2M661a572e renaming h66 → _p2mH66
end FiniteDist
open _root_.P2M661a572e renaming h66 → AFT.FiniteDist.TVBound.map
open _root_.P2M661a572e renaming h66 → _p2mH66
open _root_.P2M661a572e renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2M661a572e renaming h69 → _p2mH69
open _root_.P2M661a572e renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2M661a572e renaming h70 → _p2mH70
open _root_.P2M661a572e renaming h77 → _p2mH77
open _root_.P2M661a572e renaming h79 → AFT.FiniteDist.event_nonneg
open _root_.P2M661a572e renaming h79 → _p2mH79
open _root_.P2M661a572e renaming h94 → _p2mH94
end AFT
open _root_.P2M661a572e renaming h66 → AFT.FiniteDist.TVBound.map
open _root_.P2M661a572e renaming h66 → _p2mH66
open _root_.P2M661a572e renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2M661a572e renaming h69 → _p2mH69
open _root_.P2M661a572e renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2M661a572e renaming h70 → _p2mH70
open _root_.P2M661a572e renaming h77 → _p2mH77
open _root_.P2M661a572e renaming h79 → AFT.FiniteDist.event_nonneg
open _root_.P2M661a572e renaming h79 → _p2mH79
open _root_.P2M661a572e renaming h94 → _p2mH94
end
open _root_.P2M661a572e renaming h79 → AFT.FiniteDist.event_nonneg
open _root_.P2M661a572e renaming h79 → _p2mH79
open _root_.P2M661a572e renaming h69 → AFT.FiniteDist.TVBound.mono
open _root_.P2M661a572e renaming h69 → _p2mH69
open _root_.P2M661a572e renaming h77 → _p2mH77
open _root_.P2M661a572e renaming h70 → AFT.FiniteDist.TVBound.triangle
open _root_.P2M661a572e renaming h70 → _p2mH70
open _root_.P2M661a572e renaming h94 → _p2mH94
open _root_.P2M661a572e renaming h66 → AFT.FiniteDist.TVBound.map
open _root_.P2M661a572e renaming h66 → _p2mH66
section
namespace AFT
open scoped BigOperators Classical
variable {α β : Type*} [Fintype α] [Fintype β]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h155 (weight test : α → ℝ)
    (hzero : signedMass weight = 0) (htest : ∀ a, 0 ≤ test a ∧ test a ≤ 1) :
    |∑ a, weight a * test a| ≤ positiveMass weight := by
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
  have hmass : positiveMass weight = negativeMass weight := by
    simpa [hzero] using positiveMass_eq weight
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => (hpoint a).1)
    rw [hmass]
    simpa only [Finset.sum_neg_distrib, negativeMass] using h
  · exact Finset.sum_le_sum (fun a _ => (hpoint a).2)
open _root_.P2M661a572e renaming h155 → _p2mH155
namespace FiniteDist
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h92 (p q : FiniteDist α) :
    signedMass (fun a => p.weight a - q.weight a) = 0 := by
  simp [signedMass, Finset.sum_sub_distrib, p.sum_one, q.sum_one]
open _root_.P2M661a572e renaming h92 → _p2mH92
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h93 (p q : FiniteDist α) (error : ℝ) :
    TVBound p q error ↔ totalVariation p q ≤ error := by
  classical
  constructor
  · intro h
    let s := Finset.univ.filter (fun a => 0 ≤ p.weight a - q.weight a)
    have hevent : p.event s - q.event s = totalVariation p q := by
      simp only [event, s, Finset.sum_filter, ← Finset.sum_sub_distrib,
        totalVariation, positiveMass]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 0 ≤ p.weight a - q.weight a
      · simp [ha]
      · simp [ha, max_eq_right (le_of_not_ge ha)]
    have hn : 0 ≤ totalVariation p q :=
      Finset.sum_nonneg (fun _ _ => le_max_right _ _)
    have he := h s
    rwa [hevent, abs_of_nonneg hn] at he
  · intro h s
    have ht : ∀ a : α, 0 ≤ (if a ∈ s then (1 : ℝ) else 0) ∧
        (if a ∈ s then (1 : ℝ) else 0) ≤ 1 := by
      intro a
      split_ifs <;> norm_num
    have hb := _p2mH155 (fun a => p.weight a - q.weight a)
      (fun a => if a ∈ s then 1 else 0) (_p2mH92 p q) ht
    have he : (∑ a, (p.weight a - q.weight a) * (if a ∈ s then (1 : ℝ) else 0)) =
        p.event s - q.event s := by
      simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
      simp [event, Finset.sum_sub_distrib]
    rw [he] at hb
    exact hb.trans h
open _root_.P2M661a572e renaming h93 → _p2mH93
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h76 (p : FiniteDist α) (s : Finset α) : p.event s ≤ 1 := by
  rw [← p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun a _ _ => p.nonneg a)
open _root_.P2M661a572e renaming h76 → AFT.FiniteDist.event_le_one
open _root_.P2M661a572e renaming h76 → _p2mH76
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h78 (p : FiniteDist α) (kernel : α → FiniteDist β) (s : Finset β) :
    (p.mix kernel).event s = ∑ a, p.weight a * (kernel a).event s := by
  simp only [event, mix_weight, Finset.mul_sum]
  exact Finset.sum_comm
open _root_.P2M661a572e renaming h78 → _p2mH78
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h67 {p q : FiniteDist α} {error : ℝ}
    (h : TVBound p q error) (kernel : α → FiniteDist β) :
    TVBound (p.mix kernel) (q.mix kernel) error := by
  intro s
  rw [_p2mH78, _p2mH78, ← Finset.sum_sub_distrib]
  simp_rw [← sub_mul]
  have hb := _p2mH155 (fun a => p.weight a - q.weight a)
    (fun a => (kernel a).event s) (_p2mH92 p q)
    (fun a => ⟨_p2mH79 _ _, _p2mH76 _ _⟩)
  exact hb.trans ((_p2mH93 p q error).mp h)
open _root_.P2M661a572e renaming h67 → AFT.FiniteDist.TVBound.mix
open _root_.P2M661a572e renaming h67 → _p2mH67
end FiniteDist
open _root_.P2M661a572e renaming h67 → AFT.FiniteDist.TVBound.mix
open _root_.P2M661a572e renaming h67 → _p2mH67
open _root_.P2M661a572e renaming h76 → AFT.FiniteDist.event_le_one
open _root_.P2M661a572e renaming h76 → _p2mH76
open _root_.P2M661a572e renaming h78 → _p2mH78
open _root_.P2M661a572e renaming h92 → _p2mH92
open _root_.P2M661a572e renaming h93 → _p2mH93
end AFT
open _root_.P2M661a572e renaming h67 → AFT.FiniteDist.TVBound.mix
open _root_.P2M661a572e renaming h67 → _p2mH67
open _root_.P2M661a572e renaming h76 → AFT.FiniteDist.event_le_one
open _root_.P2M661a572e renaming h76 → _p2mH76
open _root_.P2M661a572e renaming h78 → _p2mH78
open _root_.P2M661a572e renaming h92 → _p2mH92
open _root_.P2M661a572e renaming h93 → _p2mH93
open _root_.P2M661a572e renaming h155 → _p2mH155
end
open _root_.P2M661a572e renaming h76 → AFT.FiniteDist.event_le_one
open _root_.P2M661a572e renaming h76 → _p2mH76
open _root_.P2M661a572e renaming h78 → _p2mH78
open _root_.P2M661a572e renaming h93 → _p2mH93
open _root_.P2M661a572e renaming h155 → _p2mH155
open _root_.P2M661a572e renaming h67 → AFT.FiniteDist.TVBound.mix
open _root_.P2M661a572e renaming h67 → _p2mH67
open _root_.P2M661a572e renaming h92 → _p2mH92
section
namespace AFT
open scoped BigOperators
open scoped Classical
variable {dimension : ℕ} {Color : Type*}
variable [Fintype Color]
namespace FiniteDist
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h85 (distribution : FiniteDist α) (value output : β) :
    (distribution.map (fun _ => value)).weight output = if value = output then 1 else 0 := by
  rw [map_weight]
  split_ifs <;> simp [distribution.sum_one]
open _root_.P2M661a572e renaming h85 → _p2mH85
end FiniteDist
open _root_.P2M661a572e renaming h85 → _p2mH85
section HistogramKernel
variable [Nonempty Color]
end HistogramKernel
section ZeroSumReference
variable [AddCommMonoid Color]
end ZeroSumReference
end AFT
open _root_.P2M661a572e renaming h85 → _p2mH85
end
open _root_.P2M661a572e renaming h85 → _p2mH85
section
namespace AFT
open Filter
open scoped Topology
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h156 (power exponent rate : ℝ)
    (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Tendsto (fun parameter : ℝ => parameter ^ power *
      Real.exp (-rate * parameter ^ exponent)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    (power / exponent) rate hrate).comp (tendsto_rpow_atTop hexponent)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with parameter hp
  simp only [Function.comp_apply]
  rw [← Real.rpow_mul hp, mul_div_cancel₀ power hexponent.ne']
open _root_.P2M661a572e renaming h156 → _p2mH156
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h152
    (constant : ℝ) (degree : ℕ) (exponent rate : ℝ)
    (hconstant : 0 ≤ constant) (hexponent : 0 < exponent) (hrate : 0 < rate) :
    Negligible (fun parameter => constant * (parameter : ℝ) ^ degree *
      Real.exp (-rate * (parameter : ℝ) ^ exponent)) := by
  intro order
  have hreal := (_p2mH156 (degree + order : ℕ) exponent rate
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
open _root_.P2M661a572e renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h108 {error bound : ℕ → ℝ} (hbound : Negligible bound)
    (h : ∀ᶠ parameter in atTop, |error parameter| ≤ |bound parameter|) :
    Negligible error := by
  intro order
  filter_upwards [h, hbound order] with parameter hp hq
  exact hp.trans hq
open _root_.P2M661a572e renaming h108 → AFT.Negligible.of_eventually_le
open _root_.P2M661a572e renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h106 {left right : ℕ → ℝ} (hl : Negligible left)
    (hr : Negligible right) : Negligible (fun parameter => left parameter + right parameter) := by
  intro order
  filter_upwards [hl (order + 1), hr (order + 1), eventually_ge_atTop 2]
    with parameter hl' hr' hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  have htwo : (2 : ℝ) ≤ parameter := by exact_mod_cast hp
  apply (abs_add_le _ _).trans ((add_le_add hl' hr').trans ?_)
  rw [pow_succ, ← add_div]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hp' order) hp') (pow_pos hp' order)).mpr
  nlinarith [pow_pos hp' order]
open _root_.P2M661a572e renaming h106 → AFT.Negligible.add
open _root_.P2M661a572e renaming h106 → _p2mH106
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h107 {error : ℕ → ℝ} (h : Negligible error) (degree : ℕ) :
    Negligible (fun parameter => (parameter : ℝ) ^ degree * error parameter) := by
  intro order
  filter_upwards [h (degree + order), eventually_ge_atTop 1] with parameter he hp
  have hp' : (0 : ℝ) < parameter := by exact_mod_cast (show 0 < parameter by omega)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (parameter : ℝ) ^ degree)]
  calc
    _ ≤ (parameter : ℝ) ^ degree * (1 / (parameter : ℝ) ^ (degree + order)) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by rw [pow_add]; field_simp
open _root_.P2M661a572e renaming h107 → AFT.Negligible.mul_polynomial
open _root_.P2M661a572e renaming h107 → _p2mH107
end AFT
open _root_.P2M661a572e renaming h106 → AFT.Negligible.add
open _root_.P2M661a572e renaming h106 → _p2mH106
open _root_.P2M661a572e renaming h107 → AFT.Negligible.mul_polynomial
open _root_.P2M661a572e renaming h107 → _p2mH107
open _root_.P2M661a572e renaming h108 → AFT.Negligible.of_eventually_le
open _root_.P2M661a572e renaming h108 → _p2mH108
open _root_.P2M661a572e renaming h152 → _p2mH152
open _root_.P2M661a572e renaming h156 → _p2mH156
end
open _root_.P2M661a572e renaming h152 → _p2mH152
open _root_.P2M661a572e renaming h108 → AFT.Negligible.of_eventually_le
open _root_.P2M661a572e renaming h108 → _p2mH108
open _root_.P2M661a572e renaming h107 → AFT.Negligible.mul_polynomial
open _root_.P2M661a572e renaming h107 → _p2mH107
open _root_.P2M661a572e renaming h106 → AFT.Negligible.add
open _root_.P2M661a572e renaming h106 → _p2mH106
open _root_.P2M661a572e renaming h156 → _p2mH156
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h123 (value : ℝ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (index : ℕ) :
    |(-1 : ℝ)^index*value^(2*index+1)/(2*index+1 : ℕ)| ≤ (1/2 : ℝ)^(index+1) := by
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (pow_nonneg hv _),abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ value^(2*index+1) := div_le_self (pow_nonneg hv _) (by exact_mod_cast (show 1≤2*index+1 by omega))
    _ ≤ (1/2 : ℝ)^(2*index+1) := pow_le_pow_left₀ hv hv' _
    _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
open _root_.P2M661a572e renaming h123 → _p2mH123
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h122 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2) (terms : ℕ) :
    |(arctanSum value terms : ℝ)-Real.arctan value| ≤ (1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  let term := fun index : ℕ => (-1 : ℝ)^index*(value : ℝ)^(2*index+1)/(2*index+1 : ℕ)
  have hseries : HasSum term (Real.arctan value) := Real.hasSum_arctan (by
    rw [Real.norm_eq_abs,abs_of_nonneg hv0]
    linarith)
  have hsplit := hseries.summable.sum_add_tsum_nat_add terms
  rw [hseries.tsum_eq] at hsplit
  have hcast : (arctanSum value terms : ℝ)=∑ i∈Finset.range terms,term i := by
    unfold arctanSum term
    push_cast
    rfl
  have hgeom : Summable (fun i : ℕ => (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i) :=
    (summable_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left _
  have hbound (i : ℕ) : ‖term (i+terms)‖ ≤ (1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i := by
    have hh := _p2mH123 (value : ℝ) hv0 hv1 (i+terms)
    rw [← pow_add]
    have hi : i+terms+1=terms+1+i := by omega
    simpa only [term,Real.norm_eq_abs,hi] using hh
  have htail := (summable_nat_add_iff terms).mpr hseries.summable
  have hnorm := htail.norm
  have hsum := (norm_tsum_le_tsum_norm hnorm).trans (Summable.tsum_le_tsum hbound hnorm hgeom)
  have hgeomval : (∑' i : ℕ,(1/2 : ℝ)^(terms+1)*(1/2 : ℝ)^i)=(1/2 : ℝ)^terms := by
    have hh := ((hasSum_geometric_of_norm_lt_one (show ‖(1/2 : ℝ)‖<1 by norm_num)).mul_left
      ((1/2 : ℝ)^(terms+1))).tsum_eq
    calc
      _ = (1/2 : ℝ)^(terms+1)*2 := by
        simpa only [show ((1 : ℝ)-1/2)⁻¹=2 by norm_num] using hh
      _ = _ := by rw [pow_succ]; ring
  rw [hgeomval,Real.norm_eq_abs] at hsum
  rw [hcast,abs_sub_comm,show Real.arctan (value : ℝ)-(∑ i∈Finset.range terms,term i)=
    ∑' i,term (i+terms) by linarith]
  exact hsum
open _root_.P2M661a572e renaming h122 → _p2mH122
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h131 (bits : ℕ) : |(piApprox bits : ℝ)-Real.pi| ≤ 1/(2 : ℝ)^bits := by
  have h1 := _p2mH122 (1/2) (by norm_num) (by norm_num) (bits+3)
  have h2 := _p2mH122 (1/3) (by norm_num) (by norm_num) (bits+3)
  have hid : Real.pi=4*(Real.arctan (1/2)+Real.arctan (1/3)) := by
    have hh := Real.arctan_inv_2_add_arctan_inv_3
    norm_num only [one_div] at ⊢
    linarith
  have he : (piApprox bits : ℝ)-Real.pi=4*((arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)+
      ((arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3))) := by
    rw [hid]
    simp only [piApprox,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_add]
    ring
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  calc
    _ ≤ 4*(|(arctanSum (1/2) (bits+3) : ℝ)-Real.arctan (1/2)|+
        |(arctanSum (1/3) (bits+3) : ℝ)-Real.arctan (1/3)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ 4*((1/2 : ℝ)^(bits+3)+(1/2 : ℝ)^(bits+3)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using add_le_add h1 h2
    _ = _ := by rw [pow_add,div_pow,one_pow]; norm_num; ring
open _root_.P2M661a572e renaming h131 → _p2mH131
end
open _root_.P2M661a572e renaming h122 → _p2mH122
open _root_.P2M661a572e renaming h123 → _p2mH123
open _root_.P2M661a572e renaming h131 → _p2mH131
end AFT.RationalNumerics
open _root_.P2M661a572e renaming h122 → _p2mH122
open _root_.P2M661a572e renaming h123 → _p2mH123
open _root_.P2M661a572e renaming h131 → _p2mH131
end
open _root_.P2M661a572e renaming h123 → _p2mH123
open _root_.P2M661a572e renaming h131 → _p2mH131
open _root_.P2M661a572e renaming h122 → _p2mH122
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h126 (value : ℚ) (hv : 0 ≤ value) (hv' : value ≤ 1/2)
    (terms : ℕ) (ht : 0 < terms) :
    |(expSum value terms : ℝ)-Real.exp value| ≤ 2*(1/2 : ℝ)^terms := by
  have hv0 : (0 : ℝ) ≤ value := by exact_mod_cast hv
  have hv1 : (value : ℝ) ≤ 1/2 := by
    have hh : value*2 ≤ 1 := (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).mp hv'
    have hh' : (value : ℝ)*2 ≤ 1 := by exact_mod_cast hh
    linarith
  have hterm : (1 : ℝ) ≤ terms := by exact_mod_cast ht
  have hfactorial : (1 : ℝ) ≤ terms.factorial := by exact_mod_cast Nat.factorial_pos terms
  have hden : (0 : ℝ) < (terms.factorial : ℝ)*terms := by positivity
  have hquot : ((terms+1 : ℕ) : ℝ)/((terms.factorial : ℝ)*terms) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    push_cast
    nlinarith
  have hh := Real.exp_bound (x := (value : ℝ)) (by rw [abs_of_nonneg hv0]; linarith) ht
  have he : (expSum value terms : ℝ)=∑ i∈Finset.range terms,(value : ℝ)^i/(i.factorial : ℕ) := by
    unfold expSum
    push_cast
    rfl
  rw [he,abs_sub_comm]
  apply hh.trans
  rw [abs_of_nonneg hv0]
  exact (mul_le_mul (pow_le_pow_left₀ hv0 hv1 terms) hquot (by positivity) (by positivity)).trans_eq (mul_comm _ _)
open _root_.P2M661a572e renaming h126 → _p2mH126
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h130 (first second : ℝ) (hf : 1 ≤ first) (hs : 1 ≤ second) :
    |first⁻¹-second⁻¹| ≤ |first-second| := by
  have hfirst : first ≠ 0 := by linarith
  have hsecond : second ≠ 0 := by linarith
  have he : first⁻¹-second⁻¹=(second-first)/(first*second) := by field_simp
  rw [he,abs_div,abs_sub_comm,abs_of_nonneg (by positivity : 0 ≤ first*second)]
  exact div_le_self (abs_nonneg _) (by nlinarith)
open _root_.P2M661a572e renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h135 (first second : ℝ)
    (hf : 0 ≤ first ∧ first ≤ 1) (hs : 0 ≤ second ∧ second ≤ 1) (count : ℕ) :
    |first^count-second^count| ≤ (count : ℝ)*|first-second| := by
  have hh := abs_pow_sub_pow_le first second count
  rw [abs_of_nonneg hf.1,abs_of_nonneg hs.1] at hh
  have hp : max first second^(count-1) ≤ 1 := pow_le_one₀ (le_max_of_le_left hf.1) (max_le hf.2 hs.2)
  calc
    _ ≤ |first-second| *count*max first second^(count-1) := hh
    _ ≤ |first-second| *count*1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring
open _root_.P2M661a572e renaming h135 → _p2mH135
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h125 (argument : ℚ) (scale bits : ℕ)
    (ha : 0 ≤ argument) (hscale : 0 < scale) (hbound : 2*argument ≤ (scale : ℚ)) :
    |(expNegScaled argument scale bits : ℝ)-Real.exp (-(argument : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let value : ℚ := argument/(scale : ℚ)
  let terms := bits+scale+1
  have hs0 : (0 : ℚ) < scale := by exact_mod_cast hscale
  have hv0 : 0 ≤ value := div_nonneg ha hs0.le
  have hv1 : value ≤ 1/2 := by
    apply (div_le_iff₀ hs0).mpr
    linarith
  have ht : 0 < terms := by dsimp [terms]; omega
  have hfirst := expSum_ge_one value hv0 terms ht
  have hsecond : (1 : ℝ) ≤ Real.exp (value : ℝ) := Real.one_le_exp_iff.mpr (by exact_mod_cast hv0)
  have hpi := _p2mH135 ((expSum value terms : ℝ)⁻¹) ((Real.exp (value : ℝ))⁻¹)
    ⟨by positivity,inv_le_one_of_one_le₀ hfirst⟩ ⟨by positivity,inv_le_one_of_one_le₀ hsecond⟩ scale
  have hi := _p2mH130 (expSum value terms) (Real.exp (value : ℝ)) hfirst hsecond
  have happrox := (hpi.trans (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg scale))).trans
    (mul_le_mul_of_nonneg_left (_p2mH126 value hv0 hv1 terms ht) (Nat.cast_nonneg scale))
  have hexp : (Real.exp (value : ℝ))⁻¹^scale=Real.exp (-(argument : ℝ)) := by
    rw [← Real.exp_neg,← Real.exp_nat_mul]
    congr 1
    dsimp [value]
    push_cast
    field_simp
  have hprogram : (expNegScaled argument scale bits : ℝ)=(expSum value terms : ℝ)⁻¹^scale := by
    simp only [expNegScaled,value,terms,Rat.cast_pow,Rat.cast_inv]
  rw [hprogram,← hexp]
  apply happrox.trans
  have hsbound : (scale : ℝ) ≤ (2 : ℝ)^scale := by exact_mod_cast (Nat.lt_two_pow_self (n:=scale)).le
  calc
    _ ≤ (2 : ℝ)^scale*(2*(1/2 : ℝ)^terms) := mul_le_mul_of_nonneg_right hsbound (by positivity)
    _ = _ := by
      dsimp [terms]
      rw [pow_add,pow_add,div_pow,one_pow,div_pow,one_pow]
      field_simp
open _root_.P2M661a572e renaming h125 → _p2mH125
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h124 (argument : ℚ) (bits : ℕ) :
    |(expNegApprox argument bits : ℝ)-Real.exp (-max (argument : ℝ) 0)| ≤ 1/(2 : ℝ)^bits := by
  have hb : 2*max argument 0 ≤ (expScale argument : ℚ) := by
    have hh := Nat.le_ceil (max argument 0)
    simp only [expScale,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith
  have hh := _p2mH125 (max argument 0) (expScale argument) bits
    (le_max_right _ _) (expScale_positive argument) hb
  simpa only [expNegApprox,Rat.cast_max,Rat.cast_zero] using hh
open _root_.P2M661a572e renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h127 (first second : ℝ) (hf : 0 ≤ first) (hs : 0 ≤ second) :
    |Real.exp (-first)-Real.exp (-second)| ≤ |first-second| := by
  have ordered (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      Real.exp (-a)-Real.exp (-b) ≤ b-a := by
    have he := Real.add_one_le_exp (a-b)
    have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-a)).le
    have heq : Real.exp (-a)*Real.exp (a-b)=Real.exp (-b) := by rw [← Real.exp_add]; congr 1; ring
    rw [heq] at hm
    have hl : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hab)
    nlinarith
  rcases le_total first second with h|h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonpos (sub_nonpos.mpr h)]
    have hh := ordered first second hf h
    linarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr (by linarith))),
      abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := ordered second first hs h
    linarith
open _root_.P2M661a572e renaming h127 → _p2mH127
end
open _root_.P2M661a572e renaming h124 → _p2mH124
open _root_.P2M661a572e renaming h125 → _p2mH125
open _root_.P2M661a572e renaming h126 → _p2mH126
open _root_.P2M661a572e renaming h127 → _p2mH127
open _root_.P2M661a572e renaming h130 → _p2mH130
open _root_.P2M661a572e renaming h135 → _p2mH135
end AFT.RationalNumerics
open _root_.P2M661a572e renaming h124 → _p2mH124
open _root_.P2M661a572e renaming h125 → _p2mH125
open _root_.P2M661a572e renaming h126 → _p2mH126
open _root_.P2M661a572e renaming h127 → _p2mH127
open _root_.P2M661a572e renaming h130 → _p2mH130
open _root_.P2M661a572e renaming h135 → _p2mH135
end
open _root_.P2M661a572e renaming h127 → _p2mH127
open _root_.P2M661a572e renaming h124 → _p2mH124
open _root_.P2M661a572e renaming h126 → _p2mH126
open _root_.P2M661a572e renaming h130 → _p2mH130
open _root_.P2M661a572e renaming h125 → _p2mH125
open _root_.P2M661a572e renaming h135 → _p2mH135
section
namespace AFT.RationalNumerics
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h128 (squaredWidth : ℚ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) :
    |(gaussianApprox squaredWidth point bits : ℝ)-
      Real.exp (-Real.pi*(point : ℝ)^2/(squaredWidth : ℝ))| ≤ 1/(2 : ℝ)^bits := by
  let ratio := gaussianRatio squaredWidth point
  let guard := gaussianGuard squaredWidth point
  let argument := piApprox (bits+guard+1)*ratio
  have hr0 : (0 : ℚ) ≤ ratio := div_nonneg (sq_nonneg _) hwidth.le
  have hr : (0 : ℝ) ≤ ratio := by exact_mod_cast hr0
  have hguard : (ratio : ℝ) ≤ (guard : ℝ) := by exact_mod_cast Nat.le_ceil ratio
  have hguardpow : (guard : ℝ) ≤ (2 : ℝ)^guard := by exact_mod_cast (Nat.lt_two_pow_self (n:=guard)).le
  have hpi := _p2mH131 (bits+guard+1)
  have harg : |(argument : ℝ)-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have he : (argument : ℝ)-Real.pi*(ratio : ℝ)=((piApprox (bits+guard+1) : ℝ)-Real.pi)*(ratio : ℝ) := by
      dsimp [argument]
      push_cast
      ring
    rw [he,abs_mul,abs_of_nonneg hr]
    calc
      _ ≤ (1/(2 : ℝ)^(bits+guard+1))*(2 : ℝ)^guard :=
        mul_le_mul hpi (hguard.trans hguardpow) hr (by positivity)
      _ = _ := by rw [pow_add,pow_add,pow_add]; field_simp
  have ht : 0 ≤ Real.pi*(ratio : ℝ) := mul_nonneg Real.pi_pos.le hr
  have hclip : |max (argument : ℝ) 0-Real.pi*(ratio : ℝ)| ≤ 1/(2 : ℝ)^(bits+1) := by
    have hh := abs_max_sub_max_le_abs (argument : ℝ) (Real.pi*(ratio : ℝ)) 0
    rw [max_eq_left ht] at hh
    exact hh.trans harg
  have he := _p2mH124 argument (bits+1)
  have hl := _p2mH127 (max (argument : ℝ) 0) (Real.pi*(ratio : ℝ)) (le_max_right _ _) ht
  have htarget : -Real.pi*(point : ℝ)^2/(squaredWidth : ℝ) = -(Real.pi*(ratio : ℝ)) := by
    dsimp [ratio,gaussianRatio]
    push_cast
    ring
  rw [htarget]
  calc
    _ ≤ |(expNegApprox argument (bits+1) : ℝ)-Real.exp (-max (argument : ℝ) 0)|+
        |Real.exp (-max (argument : ℝ) 0)-Real.exp (-(Real.pi*(ratio : ℝ)))| := abs_sub_le _ _ _
    _ ≤ 1/(2 : ℝ)^(bits+1)+1/(2 : ℝ)^(bits+1) := add_le_add he (hl.trans hclip)
    _ = _ := by rw [pow_succ]; field_simp; norm_num
open _root_.P2M661a572e renaming h128 → _p2mH128
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h129 (squaredWidth : ℚ) (width : ℝ) (point : ℤ) (bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    |(gaussianApprox squaredWidth point bits : ℝ)-GaussianSource.weight width point| ≤ 1/(2 : ℝ)^bits := by
  convert _p2mH128 squaredWidth point bits hwidth using 1
  unfold GaussianSource.weight
  rw [hsquare]
  have h : -(Real.pi / (squaredWidth : ℝ)) * (point : ℝ)^2 =
      -Real.pi * (point : ℝ)^2 / (squaredWidth : ℝ) := by ring
  rw [h]
open _root_.P2M661a572e renaming h129 → _p2mH129
end
open _root_.P2M661a572e renaming h128 → _p2mH128
open _root_.P2M661a572e renaming h129 → _p2mH129
end AFT.RationalNumerics
open _root_.P2M661a572e renaming h128 → _p2mH128
open _root_.P2M661a572e renaming h129 → _p2mH129
end
open _root_.P2M661a572e renaming h128 → _p2mH128
open _root_.P2M661a572e renaming h129 → _p2mH129
section
namespace AFT.SignedConditioning
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h148 (first second : Color → ℝ) :
    |(∑ color, first color) - ∑ color, second color| ≤ ∑ color, |first color - second color| := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _
open _root_.P2M661a572e renaming h148 → _p2mH148
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h149 (signed reference : Color → ℝ)
    (href : ∀ color, 0 ≤ reference color)
    (hsigned : 0 < ∑ color, signed color) (hreference : 0 < ∑ color, reference color) :
    (∑ color, |signed color / (∑ x, signed x) - reference color / (∑ x, reference x)|) ≤
      2 * (∑ color, |signed color - reference color|) / (∑ color, signed color) := by
  let total := ∑ color, signed color
  let referenceTotal := ∑ color, reference color
  let error := ∑ color, |signed color - reference color|
  have hmass : |referenceTotal - total| ≤ error := by
    simpa only [abs_sub_comm] using _p2mH148 signed reference
  have hpoint (color) : |signed color / total - reference color / referenceTotal| ≤
      |signed color - reference color| / total +
        reference color * |referenceTotal - total| / (total * referenceTotal) := by
    have heq : signed color / total - reference color / referenceTotal =
        (signed color - reference color) / total +
          reference color * (referenceTotal - total) / (total * referenceTotal) := by
      dsimp only [total, referenceTotal]
      field_simp
      ring
    rw [heq]
    exact (abs_add_le _ _).trans_eq (by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hsigned,
        abs_of_pos (mul_pos hsigned hreference), abs_of_nonneg (href color)])
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hpoint color)
  simp only [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul] at hh
  have heq : (∑ color, |signed color - reference color|) / total +
      (∑ color, reference color) * |referenceTotal - total| / (total * referenceTotal) =
        (error + |referenceTotal - total|) / total := by
    dsimp only [error, total, referenceTotal]
    field_simp
  rw [heq] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ hsigned.le
  linarith
open _root_.P2M661a572e renaming h149 → _p2mH149
end
open _root_.P2M661a572e renaming h148 → _p2mH148
open _root_.P2M661a572e renaming h149 → _p2mH149
end AFT.SignedConditioning
open _root_.P2M661a572e renaming h148 → _p2mH148
open _root_.P2M661a572e renaming h149 → _p2mH149
end
open _root_.P2M661a572e renaming h148 → _p2mH148
open _root_.P2M661a572e renaming h149 → _p2mH149
section
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h136 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hwidth : 0 < squaredWidth) (hsquare : width^2=(squaredWidth : ℝ)) :
    (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|) ≤ 1/(2 : ℝ)^bits := by
  let raw : Window cutoff → ℝ := fun point => (windowApproxRaw squaredWidth cutoff bits point : ℝ)
  have hraw : 1 ≤ ∑ point,raw point := by
    have hh := windowApproxNormalizer_ge_one squaredWidth cutoff bits
    rw [windowApproxNormalizer_eq_sum] at hh
    dsimp only [raw]
    exact_mod_cast hh
  have hnormal := _p2mH149 raw (fun point => GaussianSource.weight width point)
    (fun point => (weight_pos _ _).le) (zero_lt_one.trans_le hraw)
    (zero_lt_one.trans_le (windowNormalizer_ge_one width cutoff))
  have herr : (∑ point,|raw point-GaussianSource.weight width point|) ≤
      (2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits) := by
    have hh := Finset.sum_le_sum (fun point (_ : point ∈ (Finset.univ : Finset (Window cutoff))) =>
      _p2mH129 squaredWidth width point (windowApproxPrecision cutoff bits) hwidth hsquare)
    have hc : Fintype.card (Window cutoff)=2*cutoff+1 := by
      rw [← Fintype.card_congr (windowIndexEquiv cutoff),Fintype.card_fin]
    simpa only [raw,windowApproxRaw,Finset.sum_const,Finset.card_univ,hc,nsmul_eq_mul,mul_one_div] using hh
  have hden : 0 ≤ ∑ point,|raw point-GaussianSource.weight width point| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have heq : (∑ point,|(windowApproxLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|)=
      ∑ point,|raw point/(∑ x,raw x)-GaussianSource.weight width point/(∑ x:Window cutoff,GaussianSource.weight width x)| := by
    apply Finset.sum_congr rfl
    intro point _
    simp only [windowApproxLaw,windowApproxWeight,windowApproxNormalizer_eq_sum,windowGaussian,FiniteDist.normalize,raw,Rat.cast_div,Rat.cast_sum]
  rw [heq]
  calc
    _ ≤ 2*(∑ point,|raw point-GaussianSource.weight width point|)/(∑ x,raw x) := hnormal
    _ ≤ 2*(∑ point,|raw point-GaussianSource.weight width point|)/1 :=
      div_le_div_of_nonneg_left (by positivity) zero_lt_one hraw
    _ ≤ 2*((2*cutoff+1 : ℕ)/(2 : ℝ)^(windowApproxPrecision cutoff bits)) := by rw [div_one]; gcongr
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1)/(2 : ℝ)^(windowApproxPrecision cutoff bits)) := by
      gcongr
      exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
    _ = _ := by
      unfold windowApproxPrecision
      rw [pow_add,pow_add]
      field_simp
      ring
open _root_.P2M661a572e renaming h136 → _p2mH136
end
open _root_.P2M661a572e renaming h136 → _p2mH136
end AFT.RationalNumerics
open _root_.P2M661a572e renaming h136 → _p2mH136
end
open _root_.P2M661a572e renaming h136 → _p2mH136
section
namespace AFT.FiniteTicketSampler
open scoped BigOperators Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h102 (counts : List ℕ) (index : ℕ) :
    (∑ ticket ∈ Finset.range counts.sum, if bucket counts ticket = index then 1 else 0) =
      counts[index]?.getD 0 := by
  induction counts generalizing index with
  | nil => simp
  | cons count rest ih =>
    rw [List.sum_cons, Finset.sum_range_add]
    have hfirst (ticket : ℕ) (ht : ticket ∈ Finset.range count) :
        bucket (count :: rest) ticket = 0 := by
      simp only [bucket, if_pos (Finset.mem_range.mp ht)]
    have hsecond (ticket : ℕ) : bucket (count :: rest) (count + ticket) = 1 + bucket rest ticket := by
      simp only [bucket, show ¬count + ticket < count by omega, if_false, Nat.add_sub_cancel_left]
    simp_rw [hsecond]
    cases index with
    | zero =>
      have hf : (∑ ticket ∈ Finset.range count, if bucket (count :: rest) ticket = 0 then 1 else 0) = count := by
        calc
          _ = ∑ _ticket ∈ Finset.range count, (1 : ℕ) := by
            apply Finset.sum_congr rfl
            intro ticket ht
            rw [hfirst ticket ht]
            simp
          _ = _ := by simp
      simp [hf]
    | succ index =>
      have hf : (∑ ticket ∈ Finset.range count,
          if bucket (count :: rest) ticket = index + 1 then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro ticket ht
        rw [hfirst ticket ht]
        simp
      simp only [hf, zero_add, Nat.add_comm 1, Nat.add_right_cancel_iff,
        List.getElem?_cons_succ, ih]
open _root_.P2M661a572e renaming h102 → _p2mH102
end AFT.FiniteTicketSampler
open _root_.P2M661a572e renaming h102 → _p2mH102
end
open _root_.P2M661a572e renaming h102 → _p2mH102
section
namespace AFT.FiniteQuantization
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h96 (law : FiniteDist Color) (tickets : ℕ) : deficit law tickets ≤ Fintype.card Color := by
  have hh := Finset.sum_le_sum fun color (_ : color ∈ Finset.univ) =>
    (Nat.lt_floor_add_one ((tickets : ℝ) * law.weight color)).le
  rw [← Finset.mul_sum, law.sum_one, mul_one, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  have ht : (tickets : ℝ) ≤ (floorTotal law tickets : ℝ) + Fintype.card Color := by
    simpa only [floorTotal, floorCount, Nat.cast_sum] using hh
  have ht' : tickets ≤ floorTotal law tickets + Fintype.card Color := by exact_mod_cast ht
  unfold deficit
  omega
open _root_.P2M661a572e renaming h96 → _p2mH96
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h97 (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (color : Color) :
    |(floorCount law tickets color : ℝ) / tickets - law.weight color| ≤ 1 / tickets := by
  have ht0 : (0 : ℝ) < tickets := by exact_mod_cast ht
  have hh := Nat.abs_floor_sub_le (mul_nonneg ht0.le (law.nonneg color))
  have heq : (floorCount law tickets color : ℝ) / tickets - law.weight color =
      ((floorCount law tickets color : ℝ) - (tickets : ℝ) * law.weight color) / tickets := by field_simp
  rw [heq, abs_div, abs_of_pos ht0]
  exact div_le_div_of_nonneg_right hh ht0.le
open _root_.P2M661a572e renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h99 (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) :
    (∑ color, |(roundedLaw law tickets ht fallback).weight color - law.weight color|) ≤
      2 * (Fintype.card Color : ℝ) / tickets := by
  have ht0 : (0 : ℝ) < tickets := by exact_mod_cast ht
  have hp (color) : |(roundedLaw law tickets ht fallback).weight color - law.weight color| ≤
      1 / tickets + if color = fallback then (deficit law tickets : ℝ) / tickets else 0 := by
    have heq : (roundedLaw law tickets ht fallback).weight color - law.weight color =
        ((floorCount law tickets color : ℝ) / tickets - law.weight color) +
          (if color = fallback then (deficit law tickets : ℝ) / tickets else 0) := by
      simp only [roundedLaw, count, Nat.cast_add, add_div]
      split_ifs <;> push_cast <;> ring
    rw [heq]
    apply (abs_add_le _ _).trans
    apply add_le_add (_p2mH97 law tickets ht color)
    apply le_of_eq
    apply abs_of_nonneg
    split_ifs <;> positivity
  have hh := Finset.sum_le_sum (fun color (_ : color ∈ Finset.univ) => hp color)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  have hd : (deficit law tickets : ℝ) ≤ Fintype.card Color := by exact_mod_cast _p2mH96 law tickets
  have hd' := div_le_div_of_nonneg_right hd ht0.le
  calc
    _ ≤ (Fintype.card Color : ℝ) * (1 / tickets) + (deficit law tickets : ℝ) / tickets := hh
    _ ≤ (Fintype.card Color : ℝ) * (1 / tickets) + Fintype.card Color / tickets := add_le_add le_rfl hd'
    _ = _ := by ring
open _root_.P2M661a572e renaming h99 → _p2mH99
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h100 (law : FiniteDist Color) (tickets : ℕ) (ht : 0 < tickets) (fallback : Color) :
    FiniteDist.TVBound (roundedLaw law tickets ht fallback) law ((Fintype.card Color : ℝ) / tickets) := by
  apply (_p2mH93 _ _ _).mpr
  rw [FiniteDist.totalVariation_eq_half_l1]
  have hh := _p2mH99 law tickets ht fallback
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
open _root_.P2M661a572e renaming h100 → _p2mH100
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h98 (law : FiniteDist Color) (bits : ℕ) (fallback : Color) :
    FiniteDist.TVBound (roundedLaw law (2 ^ bits) (by positivity) fallback) law
      ((Fintype.card Color : ℝ) / (2 : ℝ) ^ bits) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    _p2mH100 law (2 ^ bits) (by positivity) fallback
open _root_.P2M661a572e renaming h98 → _p2mH98
end
open _root_.P2M661a572e renaming h96 → _p2mH96
open _root_.P2M661a572e renaming h97 → _p2mH97
open _root_.P2M661a572e renaming h98 → _p2mH98
open _root_.P2M661a572e renaming h99 → _p2mH99
open _root_.P2M661a572e renaming h100 → _p2mH100
end AFT.FiniteQuantization
open _root_.P2M661a572e renaming h96 → _p2mH96
open _root_.P2M661a572e renaming h97 → _p2mH97
open _root_.P2M661a572e renaming h98 → _p2mH98
open _root_.P2M661a572e renaming h99 → _p2mH99
open _root_.P2M661a572e renaming h100 → _p2mH100
end
open _root_.P2M661a572e renaming h98 → _p2mH98
open _root_.P2M661a572e renaming h99 → _p2mH99
open _root_.P2M661a572e renaming h96 → _p2mH96
open _root_.P2M661a572e renaming h97 → _p2mH97
open _root_.P2M661a572e renaming h100 → _p2mH100
section
namespace AFT.FiniteTicketSampler
open scoped BigOperators Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h104 {n : ℕ} (counts : Fin n → ℕ) (hpositive : 0 < ∑ index, counts index)
    (index : Fin n) :
    (by
      letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
      exact ((FiniteDist.uniform (Fin (∑ index, counts index))).map (drawFin counts)).weight index) =
      (counts index : ℝ) / (∑ index, counts index) := by
  letI : NeZero (∑ index, counts index) := ⟨hpositive.ne'⟩
  have hc := _p2mH102 (List.ofFn counts) index.val
  simp only [List.sum_ofFn, List.getElem?_ofFn, dif_pos index.isLt, Option.getD_some] at hc
  have hreal : (∑ ticket ∈ Finset.range (∑ index, counts index),
      if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0) = counts index := by
    exact_mod_cast hc
  simp only [FiniteDist.map_weight, FiniteDist.uniform_weight, Fintype.card_fin,
    drawFin, Fin.ext_iff]
  simp_rw [show ∀ ticket : Fin (∑ index, counts index),
    (if bucket (List.ofFn counts) ticket.val = index.val then ((∑ index, counts index : ℕ) : ℝ)⁻¹ else 0) =
      ((∑ index, counts index : ℕ) : ℝ)⁻¹ *
        (if bucket (List.ofFn counts) ticket.val = index.val then 1 else 0) from
          fun ticket => by split_ifs <;> simp]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
    (fun ticket => if bucket (List.ofFn counts) ticket = index.val then (1 : ℝ) else 0)
      (∑ index, counts index), hreal]
  ring
open _root_.P2M661a572e renaming h104 → _p2mH104
end FiniteTicketSampler
open _root_.P2M661a572e renaming h104 → _p2mH104
namespace FiniteQuantization
open scoped BigOperators Classical
noncomputable section
end
end FiniteQuantization
end AFT
open _root_.P2M661a572e renaming h104 → _p2mH104
end
open _root_.P2M661a572e renaming h104 → _p2mH104
section
namespace AFT.FiniteTicketSampler
open scoped BigOperators Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h105 (bits : ℕ) :
    FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2)) =
      FiniteDist.uniform (Fin bits → Fin 2) := by
  apply FiniteDist.ext
  intro word
  simp only [FiniteDist.independent, FiniteDist.uniform_weight, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]
open _root_.P2M661a572e renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h101 (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map (bitTicket bits) =
      FiniteDist.uniform (Fin (2 ^ bits)) := by
  rw [_p2mH105]
  exact FiniteDist.uniform_map_equiv finFunctionFinEquiv
open _root_.P2M661a572e renaming h101 → _p2mH101
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h103 {n : ℕ} (bits : ℕ) (counts : Fin n → ℕ)
    (htotal : ∑ index, counts index = 2 ^ bits) (index : Fin n) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (drawBitTable bits counts htotal)).weight index = (counts index : ℝ) / (2 : ℝ) ^ bits := by
  have hpos : 0 < ∑ index, counts index := by rw [htotal]; positivity
  letI : NeZero (∑ index, counts index) := ⟨hpos.ne'⟩
  have hu := _p2mH101 bits
  have ht := FiniteDist.uniform_map_equiv (finCongr htotal.symm)
  have hm := congrArg (fun p : FiniteDist (Fin (2 ^ bits)) =>
    p.map (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) hu
  rw [FiniteDist.map_map] at hm
  have hc := congrArg (fun p : FiniteDist (Fin (∑ index, counts index)) => p.map (drawFin counts)) ht
  rw [FiniteDist.map_map] at hc
  change ((FiniteDist.uniform (Fin (2 ^ bits))).map
    (fun ticket => drawFin counts (Fin.cast htotal.symm ticket))) = _ at hc
  change ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
    (fun word => drawFin counts (Fin.cast htotal.symm (bitTicket bits word)))).weight index = _
  rw [hm, hc]
  exact (_p2mH104 counts hpos index).trans (by simp only [htotal, Nat.cast_pow, Nat.cast_ofNat])
open _root_.P2M661a572e renaming h103 → _p2mH103
end FiniteTicketSampler
open _root_.P2M661a572e renaming h101 → _p2mH101
open _root_.P2M661a572e renaming h103 → _p2mH103
open _root_.P2M661a572e renaming h105 → _p2mH105
end AFT
open _root_.P2M661a572e renaming h101 → _p2mH101
open _root_.P2M661a572e renaming h103 → _p2mH103
open _root_.P2M661a572e renaming h105 → _p2mH105
end
open _root_.P2M661a572e renaming h105 → _p2mH105
open _root_.P2M661a572e renaming h101 → _p2mH101
open _root_.P2M661a572e renaming h103 → _p2mH103
section
namespace AFT.RationalFiniteQuantization
open scoped BigOperators
variable {size : ℕ}
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h119 (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) :
    floorCount weight tickets index =
      FiniteQuantization.floorCount (law weight hnonneg hsum) tickets index := by
  simp only [floorCount, FiniteQuantization.floorCount, law, ← Int.floor_toNat]
  have hcast : (tickets : ℝ) * (weight index : ℝ) =
      ((tickets : ℚ) * weight index : ℚ) := by push_cast; rfl
  rw [hcast, Rat.floor_cast]
open _root_.P2M661a572e renaming h119 → _p2mH119
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h116 (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (index : Fin (size + 1)) :
    counts weight tickets index =
      FiniteQuantization.count (law weight hnonneg hsum) tickets 0 index := by
  simp only [counts, FiniteQuantization.count, deficit, FiniteQuantization.deficit,
    floorTotal, FiniteQuantization.floorTotal, _p2mH119 weight hnonneg hsum]
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h116 → _p2mH116
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h120 (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) :
    roundedLaw weight hnonneg hsum tickets ht =
      FiniteQuantization.roundedLaw (law weight hnonneg hsum) tickets ht 0 := by
  apply FiniteDist.ext
  intro index
  exact congrArg (fun count : ℕ => (count : ℝ) / tickets)
    (_p2mH116 weight hnonneg hsum tickets index)
open _root_.P2M661a572e renaming h120 → _p2mH120
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h121 (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (tickets : ℕ) (ht : 0 < tickets) :
    (∑ index, |(roundedLaw weight hnonneg hsum tickets ht).weight index -
      (weight index : ℝ)|) ≤ 2 * (size + 1 : ℝ) / tickets := by
  rw [_p2mH120]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, law] using
    _p2mH99 (law weight hnonneg hsum) tickets ht 0
open _root_.P2M661a572e renaming h121 → _p2mH121
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h117 (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw weight hnonneg hsum bits) =
      roundedLaw weight hnonneg hsum (2 ^ bits) (by positivity) := by
  apply FiniteDist.ext
  intro index
  unfold draw
  simpa only [roundedLaw, Nat.cast_pow, Nat.cast_ofNat] using
    _p2mH103 bits (counts weight (2 ^ bits))
      (counts_total weight hnonneg hsum (2 ^ bits)) index
open _root_.P2M661a572e renaming h117 → _p2mH117
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h118 (weight : Fin (size + 1) → ℚ)
    (hnonneg : ∀ index, 0 ≤ weight index) (hsum : ∑ index, weight index = 1)
    (bits : ℕ) :
    FiniteDist.TVBound
      ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
        (draw weight hnonneg hsum bits))
      (law weight hnonneg hsum) ((size + 1 : ℝ) / (2 : ℝ) ^ bits) := by
  rw [_p2mH117, _p2mH120]
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    _p2mH98 (law weight hnonneg hsum) bits 0
open _root_.P2M661a572e renaming h118 → _p2mH118
end
open _root_.P2M661a572e renaming h116 → _p2mH116
open _root_.P2M661a572e renaming h117 → _p2mH117
open _root_.P2M661a572e renaming h118 → _p2mH118
open _root_.P2M661a572e renaming h119 → _p2mH119
open _root_.P2M661a572e renaming h120 → _p2mH120
open _root_.P2M661a572e renaming h121 → _p2mH121
end AFT.RationalFiniteQuantization
open _root_.P2M661a572e renaming h116 → _p2mH116
open _root_.P2M661a572e renaming h117 → _p2mH117
open _root_.P2M661a572e renaming h118 → _p2mH118
open _root_.P2M661a572e renaming h119 → _p2mH119
open _root_.P2M661a572e renaming h120 → _p2mH120
open _root_.P2M661a572e renaming h121 → _p2mH121
end
open _root_.P2M661a572e renaming h117 → _p2mH117
open _root_.P2M661a572e renaming h119 → _p2mH119
open _root_.P2M661a572e renaming h116 → _p2mH116
open _root_.P2M661a572e renaming h121 → _p2mH121
open _root_.P2M661a572e renaming h118 → _p2mH118
open _root_.P2M661a572e renaming h120 → _p2mH120
section
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h137 (squaredWidth : ℚ) (cutoff bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) => FiniteDist.uniform (Fin 2))).map
      (windowGaussianDraw squaredWidth cutoff bits)=windowTicketLaw squaredWidth cutoff bits := by
  unfold windowGaussianDraw windowTicketLaw
  rw [← FiniteDist.map_map,_p2mH117]
open _root_.P2M661a572e renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h140 (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    (windowTicketLaw squaredWidth cutoff bits).weight point=
      (windowTicketCounts squaredWidth cutoff bits ((windowIndexEquiv cutoff).symm point) : ℝ)/
        (2 : ℝ)^(windowTicketBits cutoff bits) := by
  have hh := FiniteDist.map_equiv_weight
    (RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
      (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
      (2^(windowTicketBits cutoff bits)) (by positivity)) (windowIndexEquiv cutoff) point
  simpa only [windowTicketLaw,RationalFiniteQuantization.roundedLaw,
    windowTicketCounts,Nat.cast_pow,Nat.cast_ofNat] using hh
open _root_.P2M661a572e renaming h140 → _p2mH140
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h139 (squaredWidth : ℚ) (cutoff bits : ℕ) :
    (∑ point,|(windowTicketLaw squaredWidth cutoff bits).weight point-
      (windowApproxLaw squaredWidth cutoff (bits+1)).weight point|)≤1/(2 : ℝ)^(bits+1) := by
  have hh := _p2mH121 (windowGaussianWeights squaredWidth cutoff (bits+1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
    (2^(windowTicketBits cutoff bits)) (by positivity)
  have heq : (∑ point,|(windowTicketLaw squaredWidth cutoff bits).weight point-
      (windowApproxLaw squaredWidth cutoff (bits+1)).weight point|)=
      ∑ index,|(RationalFiniteQuantization.roundedLaw (windowGaussianWeights squaredWidth cutoff (bits+1))
        (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _)
        (2^(windowTicketBits cutoff bits)) (by positivity)).weight index-
          (windowGaussianWeights squaredWidth cutoff (bits+1) index : ℝ)| := by
    rw [← (windowIndexEquiv cutoff).sum_comp]
    apply Finset.sum_congr rfl
    intro index _
    rw [_p2mH140]
    simp only [Equiv.symm_apply_apply,windowApproxLaw,windowGaussianWeights,
      RationalFiniteQuantization.roundedLaw,windowTicketCounts,Nat.cast_pow,Nat.cast_ofNat]
  rw [heq]
  apply hh.trans
  have hpow : ((2*cutoff+1 : ℕ) : ℝ)≤(2 : ℝ)^(2*cutoff+1) := by
    exact_mod_cast (Nat.lt_two_pow_self (n:=2*cutoff+1)).le
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  calc
    _ ≤ 2*((2 : ℝ)^(2*cutoff+1))/(2 : ℝ)^(windowTicketBits cutoff bits) := by
      gcongr
      exact_mod_cast hpow
    _ = _ := by unfold windowTicketBits; rw [pow_add,pow_add,pow_add]; field_simp; ring
open _root_.P2M661a572e renaming h139 → _p2mH139
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h138 (squaredWidth : ℚ) (width : ℝ) (cutoff bits : ℕ)
    (hpositive : 0<squaredWidth) (hsquare : (squaredWidth : ℝ)=width^2) :
    (∑ point,|(windowTicketLaw squaredWidth cutoff bits).weight point-
      (windowGaussian width cutoff).weight point|)≤1/(2 : ℝ)^bits := by
  have htriangle := Finset.sum_le_sum (fun point (_ : point∈(Finset.univ : Finset (Window cutoff))) =>
    abs_sub_le ((windowTicketLaw squaredWidth cutoff bits).weight point)
      ((windowApproxLaw squaredWidth cutoff (bits+1)).weight point) ((windowGaussian width cutoff).weight point))
  rw [Finset.sum_add_distrib] at htriangle
  apply htriangle.trans
  apply (add_le_add (_p2mH139 squaredWidth cutoff bits)
    (_p2mH136 squaredWidth width cutoff (bits+1) hpositive hsquare.symm)).trans_eq
  rw [pow_succ]
  field_simp
  norm_num
open _root_.P2M661a572e renaming h138 → _p2mH138
end
open _root_.P2M661a572e renaming h137 → _p2mH137
open _root_.P2M661a572e renaming h138 → _p2mH138
open _root_.P2M661a572e renaming h139 → _p2mH139
open _root_.P2M661a572e renaming h140 → _p2mH140
end AFT.RationalNumerics
open _root_.P2M661a572e renaming h137 → _p2mH137
open _root_.P2M661a572e renaming h138 → _p2mH138
open _root_.P2M661a572e renaming h139 → _p2mH139
open _root_.P2M661a572e renaming h140 → _p2mH140
end
open _root_.P2M661a572e renaming h140 → _p2mH140
open _root_.P2M661a572e renaming h138 → _p2mH138
open _root_.P2M661a572e renaming h139 → _p2mH139
open _root_.P2M661a572e renaming h137 → _p2mH137
namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h87 (first : FiniteDist A) (second : FiniteDist B) (f : A → C) (g : B → D) :
    (first.prod second).map (fun pair => (f pair.1, g pair.2)) = (first.map f).prod (second.map g) := by
  apply FiniteDist.ext
  rintro ⟨c, d⟩
  simp only [map_weight, prod_weight, Fintype.sum_prod_type, Prod.mk.injEq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> simp_all
open _root_.P2M661a572e renaming h87 → _p2mH87
end
open _root_.P2M661a572e renaming h87 → _p2mH87
end AFT.FiniteDist
open _root_.P2M661a572e renaming h87 → _p2mH87
namespace AFT.SafeConvolution
open scoped BigOperators Classical
noncomputable section
variable {G : Type*} [Fintype G] [AddCommGroup G]
end
end AFT.SafeConvolution
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Color : Type*} [Fintype Color]
attribute [local instance] _root_.AFT.RepresentedPolynomial.jointPairFinDecEq
end
end AFT.RepresentedPolynomial
namespace AFT.GaussianSource
noncomputable section
end
end AFT.GaussianSource
namespace AFT.V7Calibration
open GaussianSource SafeConvolution RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] actualModulusNeZero
end
end AFT.V7Calibration
end
open _root_.P2M661a572e renaming h87 → _p2mH87
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
section
namespace AFT.BetaReference
open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h0 (constant base : ℝ) (hc : 0 ≤ constant)
    (hb : 0 < base) (hb1 : base < 1) (population : ℕ → ℕ)
    (hpop : ∀ᶠ n in atTop,n ≤ population n) :
    Negligible (fun n => constant*base^population n) := by
  have hh := _p2mH152 constant 0 1 (-Real.log base) hc (by norm_num)
    (neg_pos.mpr (Real.log_neg hb hb1))
  apply hh.of_eventually_le
  filter_upwards [hpop] with n hn
  rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  simp only [pow_zero,mul_one,Real.rpow_one,neg_neg]
  have he : Real.exp (Real.log base*(n : ℝ))=base^n := by rw [mul_comm,Real.exp_nat_mul,Real.exp_log hb]
  rw [he]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb.le hb1.le hn) hc
open _root_.P2M661a572e renaming h0 → _p2mH0
end
open _root_.P2M661a572e renaming h0 → _p2mH0
end AFT.BetaReference
open _root_.P2M661a572e renaming h0 → _p2mH0
namespace AFT.V7Calibration
open GaussianSource BetaReference MeasureTheory Filter
open scoped Topology
noncomputable section
end
end AFT.V7Calibration
end
open _root_.P2M661a572e renaming h0 → _p2mH0
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {A S : Type*} [Fintype A] [Fintype S]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h75 (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) (a : A) :
    (cappedRejection proposal coin hcoin fallback count).weight a =
      (1 - (1 - acceptance proposal coin) ^ count) *
        (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept).weight a +
          (1 - acceptance proposal coin) ^ count * fallback.weight a := by
  induction count with
  | zero => simp [cappedRejection]
  | succ count ih =>
    simp only [cappedRejection, rejectionStep, ih, pow_succ, acceptedLaw]
    field_simp
    ring
open _root_.P2M661a572e renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h74 (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal coin hcoin fallback count)
      (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept)
      ((1 - acceptance proposal coin) ^ count) := by
  intro event
  let accepted := acceptedLaw proposal coin (fun a => (hcoin a).1) haccept
  have hfailure : 0 ≤ (1 - acceptance proposal coin) ^ count :=
    pow_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) _
  have hid : (cappedRejection proposal coin hcoin fallback count).event event - accepted.event event =
      (1 - acceptance proposal coin) ^ count * (fallback.event event - accepted.event event) := by
    simp only [FiniteDist.event, _p2mH75 proposal coin hcoin haccept fallback count, Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [accepted]
    ring
  change |(cappedRejection proposal coin hcoin fallback count).event event - accepted.event event| ≤ _
  rw [hid, abs_mul, abs_of_nonneg hfailure]
  have hdiff : |fallback.event event - accepted.event event| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [_p2mH79 fallback event, _p2mH76 fallback event,
      _p2mH79 accepted event, _p2mH76 accepted event]
  exact (mul_le_mul_of_nonneg_left hdiff hfailure).trans_eq (mul_one _)
open _root_.P2M661a572e renaming h74 → _p2mH74
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h72 (proposal : FiniteDist A) (coin : A → ℝ)
    (hcoin : ∀ a, 0 ≤ coin a ∧ coin a ≤ 1) (haccept : 0 < acceptance proposal coin)
    (fallback : FiniteDist A) (count : ℕ) :
    TVBound (cappedRejection proposal coin hcoin fallback count)
      (acceptedLaw proposal coin (fun a => (hcoin a).1) haccept)
      (Real.exp (-(count : ℝ) * acceptance proposal coin)) := by
  apply (_p2mH74 proposal coin hcoin haccept fallback count).mono
  have hbase : 1 - acceptance proposal coin ≤ Real.exp (-acceptance proposal coin) := by
    linarith [Real.add_one_le_exp (-acceptance proposal coin)]
  have hh := pow_le_pow_left₀ (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2) hbase count
  simpa only [← Real.exp_nat_mul, mul_neg, neg_mul] using hh
open _root_.P2M661a572e renaming h72 → _p2mH72
end
open _root_.P2M661a572e renaming h72 → _p2mH72
open _root_.P2M661a572e renaming h74 → _p2mH74
open _root_.P2M661a572e renaming h75 → _p2mH75
end AFT.FiniteDist
open _root_.P2M661a572e renaming h72 → _p2mH72
open _root_.P2M661a572e renaming h74 → _p2mH74
open _root_.P2M661a572e renaming h75 → _p2mH75
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {A : Type*} [Fintype A]
end
end AFT.FiniteDist
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {A S : Type*} [Fintype A] [Fintype S]
end
end AFT.FiniteDist
end
open _root_.P2M661a572e renaming h75 → _p2mH75
open _root_.P2M661a572e renaming h74 → _p2mH74
open _root_.P2M661a572e renaming h72 → _p2mH72
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.acceptance
end AFT.FiniteDist.acceptance
namespace AFT.FiniteDist.cappedCondition
end AFT.FiniteDist.cappedCondition
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FiniteDist.eventCoin
end AFT.FiniteDist.eventCoin
section
namespace AFT.FiniteConditionProgram
open scoped BigOperators
variable {State : Type*}
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable [Fintype State]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h63 (proposal : FiniteDist State) (attempts : ℕ) :
    FiniteDist.independent (fun _ : Fin (attempts + 1) => proposal) =
      (proposal.prod (FiniteDist.independent (fun _ : Fin attempts => proposal))).map
        (Fin.consEquiv (fun _ : Fin (attempts + 1) => State)) := by
  apply FiniteDist.ext
  intro word
  rw [FiniteDist.map_equiv_weight]
  change (∏ index, proposal.weight (word index)) =
    proposal.weight (word 0) * ∏ index : Fin attempts, proposal.weight (word index.succ)
  exact Fin.prod_univ_succ _
open _root_.P2M661a572e renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h64 {Index Random : Type*} [Fintype Index] [DecidableEq Index]
    [Fintype Random] (randomness : Index → FiniteDist Random)
    (decode : Index → Random → State) :
    (FiniteDist.independent randomness).map (fun word index => decode index (word index)) =
      FiniteDist.independent (fun index => (randomness index).map (decode index)) := by
  apply FiniteDist.ext
  intro values
  simp only [FiniteDist.map_weight, FiniteDist.independent]
  change (∑ word : Index → Random,
    if (fun index => decode index (word index)) = values
    then ∏ index, (randomness index).weight (word index) else 0) =
    ∏ index, ∑ point, if decode index point = values index then (randomness index).weight point else 0
  have he := Fintype.prod_sum (fun index point =>
    if decode index point = values index then (randomness index).weight point else 0)
  apply Eq.trans ?_ he.symm
  apply Finset.sum_congr (by ext; simp)
  intro word _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]
open _root_.P2M661a572e renaming h64 → _p2mH64
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h65 {Random : Type*} [Fintype Random] [Nonempty Random]
    (attempts : ℕ) :
    FiniteDist.independent (fun _ : Fin attempts => FiniteDist.uniform Random) =
      FiniteDist.uniform (Fin attempts → Random) := by
  apply FiniteDist.ext
  intro word
  simp only [FiniteDist.independent, FiniteDist.uniform_weight, Fintype.card_fun,
    Fintype.card_fin, Finset.prod_const, Finset.card_univ, Nat.cast_pow, inv_pow]
open _root_.P2M661a572e renaming h65 → _p2mH65
end
open _root_.P2M661a572e renaming h63 → _p2mH63
open _root_.P2M661a572e renaming h64 → _p2mH64
open _root_.P2M661a572e renaming h65 → _p2mH65
end AFT.FiniteConditionProgram
open _root_.P2M661a572e renaming h63 → _p2mH63
open _root_.P2M661a572e renaming h64 → _p2mH64
open _root_.P2M661a572e renaming h65 → _p2mH65
end
open _root_.P2M661a572e renaming h64 → _p2mH64
open _root_.P2M661a572e renaming h65 → _p2mH65
open _root_.P2M661a572e renaming h63 → _p2mH63
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
section
namespace AFT.V7Calibration
open GaussianSource RationalNumerics Filter
open scoped BigOperators
noncomputable section
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] _root_.AFT.V7Calibration.sliceProgramFinDecEq
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h151 (modulus boundary shift color : ℤ) :
    |(sliceProbabilityProgram modulus boundary shift color : ℝ)|≤1 := by
  rw [sliceProbabilityProgram_eq_original]
  split_ifs with hh
  · simp only [Rat.cast_inv,Rat.cast_natCast]
    rw [abs_of_nonneg (by positivity)]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (Finset.one_le_card.mpr ⟨color,hh⟩)
  · norm_num
open _root_.P2M661a572e renaming h151 → _p2mH151
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h150 (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    |(averagedSliceProgram modulus boundary start source width color : ℝ)|≤1 := by
  by_cases hw : width=0
  · subst width
    simp [averagedSliceProgram_eq_sum,anchorInterval]
  simp only [averagedSliceProgram_eq_sum,Rat.cast_sum,Rat.cast_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ shift∈anchorInterval start width,intervalAnchorLaw start width shift := by
      apply Finset.sum_le_sum
      intro shift _
      rw [abs_mul,intervalProbabilityProgram_cast,abs_of_nonneg (intervalAnchorLaw_nonneg _ _ _)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (_p2mH151 modulus boundary (shift-source) color)
        (intervalAnchorLaw_nonneg start shift width)
    _ = 1 := intervalAnchorLaw_mass start width hw
open _root_.P2M661a572e renaming h150 → _p2mH150
end
open _root_.P2M661a572e renaming h150 → _p2mH150
open _root_.P2M661a572e renaming h151 → _p2mH151
end AFT.V7Calibration
open _root_.P2M661a572e renaming h150 → _p2mH150
open _root_.P2M661a572e renaming h151 → _p2mH151
end
open _root_.P2M661a572e renaming h151 → _p2mH151
open _root_.P2M661a572e renaming h150 → _p2mH150
section
set_option backward.isDefEq.respectTransparency false
namespace AFT
open scoped BigOperators
end AFT
namespace AFT
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h157 (n : ℕ)
    (treeBasis : (Fin n → ℤ) ≃ₗ[ℤ] zeroSumLattice n)
    (B : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℤ))
    (c w : Fin (n + 1) → ℤ) (a : Fin n → ℤ)
    (ha : pathLoad n a = w - c) (x : (Fin n → ℤ) × ℤ) :
    roundingLoad n c (blockTransport n (edgeBasisChange n treeBasis) B a x) =
      (treeBasis (B x.1) : Fin (n + 1) → ℤ) + x.2 • w := by
  simp only [roundingLoad, blockTransport, LinearMap.coe_mk, AddHom.coe_mk,
    pathLoad_add, pathLoad_smul, pathLoad_edgeBasisChange, ha, smul_sub]
  abel
open _root_.P2M661a572e renaming h157 → _p2mH157
end AFT
open _root_.P2M661a572e renaming h157 → _p2mH157
namespace AFT
end AFT
namespace AFT
end AFT
end
open _root_.P2M661a572e renaming h157 → _p2mH157
section
namespace AFT.PermutationProgram
open scoped BigOperators
noncomputable section
open FiniteDist
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h553 {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    (uniform A).prod (uniform B)=uniform (A × B) := by
  ext point
  simp only [prod_weight,uniform_weight,Fintype.card_prod,Nat.cast_mul,mul_inv_rev]
  ring
open _root_.P2M661a572e renaming h553 → _p2mH553
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h552 (count : ℕ) (A : Type*) [Fintype A] [Nonempty A] :
    independent (fun _ : Fin count => uniform A)=uniform (Fin count → A) := by
  ext word
  simp only [independent,uniform_weight,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Fintype.card_fun,Nat.cast_pow,inv_pow]
open _root_.P2M661a572e renaming h552 → _p2mH552
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h550 {A B X Y : Type*} [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
    (first : FiniteDist A) (second : FiniteDist B) (f : A → X) (g : B → Y) :
    (first.prod second).map (fun point => (f point.1,g point.2))=(first.map f).prod (second.map g) := by
  ext point
  rcases point with ⟨x,y⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hf : f a=x <;> by_cases hg : g b=y <;> simp [hf,hg]
open _root_.P2M661a572e renaming h550 → _p2mH550
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h551 {A B : Type*} [Fintype A] [Fintype B]
    {first first' : FiniteDist A} {second second' : FiniteDist B} {error error' : ℝ}
    (hfirst : TVBound first first' error) (hsecond : TVBound second second' error') :
    TVBound (first.prod second) (first'.prod second') (error+error') := by
  rw [_p2mH93,totalVariation_eq_half_l1] at hfirst hsecond ⊢
  linarith [l1_prod_le first first' second second']
open _root_.P2M661a572e renaming h551 → _p2mH551
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h109 (size bits : ℕ) : TVBound (choiceLaw size bits) (uniform (Fin (size+1)))
    ((size+1 : ℝ)/(2 : ℝ)^bits) := by
  have hh := _p2mH118 (choiceWeight size)
    (choiceWeight_nonneg size) (choiceWeight_sum size) bits
  rw [_p2mH105] at hh
  have he : RationalFiniteQuantization.law (choiceWeight size)
      (choiceWeight_nonneg size) (choiceWeight_sum size)=uniform (Fin (size+1)) := by
    ext point
    simp [RationalFiniteQuantization.law,choiceWeight,uniform_weight]
  rwa [he] at hh
open _root_.P2M661a572e renaming h109 → _p2mH109
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h111 (count bits : ℕ) :
    permutationLaw (count+1) bits=
      ((choiceLaw count bits).prod (permutationLaw count bits)).map Equiv.Perm.decomposeFin.symm := by
  unfold permutationLaw
  rw [← _p2mH552 (count+1),_p2mH63,FiniteDist.map_map]
  rw [choiceLaw,← _p2mH550,FiniteDist.map_map]
  rw [_p2mH552 count]
  rfl
open _root_.P2M661a572e renaming h111 → _p2mH111
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h110 (count bits : ℕ) :
    (uniform (Fin (count*bits) → Fin 2)).map (draw count bits)=permutationLaw count bits := by
  have hh := congrArg (fun law => law.map (rows bits count))
    (uniform_map_equiv (FiniteConditionProgram.groupBits count bits))
  unfold draw permutationLaw
  simpa only [FiniteDist.map_map, Function.comp_def] using hh
open _root_.P2M661a572e renaming h110 → _p2mH110
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h112 (count bits : ℕ) :
    TVBound (permutationLaw count bits) (uniform (Equiv.Perm (Fin count)))
      ((count : ℝ)^2/(2 : ℝ)^bits) := by
  induction count with
  | zero =>
    have he : permutationLaw 0 bits=uniform (Equiv.Perm (Fin 0)) := by
      ext permutation
      simp [permutationLaw,map_weight,uniform_weight,rows]
      exact Subsingleton.elim _ _
    rw [he]
    simpa using _p2mH94 (uniform (Equiv.Perm (Fin 0)))
  | succ count ih =>
    have hh := (_p2mH551 (_p2mH109 count bits) ih).map Equiv.Perm.decomposeFin.symm
    rw [_p2mH553,uniform_map_equiv,← _p2mH111] at hh
    apply hh.mono
    have hden : 0<(2 : ℝ)^bits := by positivity
    rw [← add_div,Nat.cast_add,Nat.cast_one]
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith [Nat.cast_nonneg (α := ℝ) count]
open _root_.P2M661a572e renaming h112 → _p2mH112
end
open _root_.P2M661a572e renaming h109 → _p2mH109
open _root_.P2M661a572e renaming h110 → _p2mH110
open _root_.P2M661a572e renaming h111 → _p2mH111
open _root_.P2M661a572e renaming h112 → _p2mH112
open _root_.P2M661a572e renaming h550 → _p2mH550
open _root_.P2M661a572e renaming h551 → _p2mH551
open _root_.P2M661a572e renaming h552 → _p2mH552
open _root_.P2M661a572e renaming h553 → _p2mH553
end AFT.PermutationProgram
open _root_.P2M661a572e renaming h109 → _p2mH109
open _root_.P2M661a572e renaming h110 → _p2mH110
open _root_.P2M661a572e renaming h111 → _p2mH111
open _root_.P2M661a572e renaming h112 → _p2mH112
open _root_.P2M661a572e renaming h550 → _p2mH550
open _root_.P2M661a572e renaming h551 → _p2mH551
open _root_.P2M661a572e renaming h552 → _p2mH552
open _root_.P2M661a572e renaming h553 → _p2mH553
end
open _root_.P2M661a572e renaming h111 → _p2mH111
open _root_.P2M661a572e renaming h110 → _p2mH110
open _root_.P2M661a572e renaming h109 → _p2mH109
open _root_.P2M661a572e renaming h112 → _p2mH112
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State : Type*} [Fintype State]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h90 (proposal : FiniteDist State) (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1) (remaining : FiniteDist State) :
    rejectionStep proposal coin hcoin remaining=proposal.mix (rejectionKernel coin hcoin remaining) := by
  ext point
  simp only [rejectionStep,mix_weight,rejectionKernel,mul_add,Finset.sum_add_distrib,
    mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [← mul_assoc]
  rw [← Finset.sum_mul]
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,proposal.sum_one,acceptance]
open _root_.P2M661a572e renaming h90 → _p2mH90
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h91 (proposal : FiniteDist State) (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1) (first second : FiniteDist State)
    (error : ℝ) (h : TVBound first second error) :
    TVBound (rejectionStep proposal coin hcoin first) (rejectionStep proposal coin hcoin second) error := by
  intro event
  have he : (rejectionStep proposal coin hcoin first).event event-
      (rejectionStep proposal coin hcoin second).event event=
      (1-acceptance proposal coin)*(first.event event-second.event event) := by
    simp only [FiniteDist.event,rejectionStep,Finset.sum_add_distrib,← Finset.mul_sum]
    ring
  rw [he,abs_mul,abs_of_nonneg (sub_nonneg.mpr (acceptance_bounds proposal coin hcoin).2)]
  calc
    _ ≤ 1*|first.event event-second.event event| :=
      mul_le_mul_of_nonneg_right (by linarith [(acceptance_bounds proposal coin hcoin).1]) (abs_nonneg _)
    _ ≤ error := by simpa only [one_mul] using h event
open _root_.P2M661a572e renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h73 (first second : FiniteDist State) (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1) (fallback : FiniteDist State)
    (error : ℝ) (h : TVBound first second error) (count : ℕ) :
    TVBound (cappedRejection first coin hcoin fallback count)
      (cappedRejection second coin hcoin fallback count) ((count : ℝ)*error) := by
  induction count with
  | zero => intro event; simp only [cappedRejection,Nat.cast_zero,zero_mul,sub_self,abs_zero,le_refl]
  | succ count ih =>
    have hproposal := h.mix (rejectionKernel coin hcoin (cappedRejection first coin hcoin fallback count))
    rw [← _p2mH90,← _p2mH90] at hproposal
    have hremaining := _p2mH91 second coin hcoin _ _ _ ih
    have hh := hproposal.triangle hremaining
    simpa only [cappedRejection,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hh
open _root_.P2M661a572e renaming h73 → _p2mH73
end
open _root_.P2M661a572e renaming h73 → _p2mH73
open _root_.P2M661a572e renaming h90 → _p2mH90
open _root_.P2M661a572e renaming h91 → _p2mH91
end AFT.FiniteDist
open _root_.P2M661a572e renaming h73 → _p2mH73
open _root_.P2M661a572e renaming h90 → _p2mH90
open _root_.P2M661a572e renaming h91 → _p2mH91
end
open _root_.P2M661a572e renaming h73 → _p2mH73
open _root_.P2M661a572e renaming h91 → _p2mH91
open _root_.P2M661a572e renaming h90 → _p2mH90
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {State : Type*} [Fintype State]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h88 (coin : State → ℝ)
    (hcoin : ∀ point,0 ≤ coin point ∧ coin point ≤ 1)
    (remaining : FiniteDist State) (point : State) (event : Finset State) :
    (rejectionKernel coin hcoin remaining point).event event=
      (if point∈event then coin point else 0)+(1-coin point)*remaining.event event := by
  simp only [FiniteDist.event,rejectionKernel,Finset.sum_add_distrib,← Finset.mul_sum]
  simp
open _root_.P2M661a572e renaming h88 → _p2mH88
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h89 (proposal : FiniteDist State) (first second : State → ℝ)
    (hfirst : ∀ point,0 ≤ first point ∧ first point ≤ 1)
    (hsecond : ∀ point,0 ≤ second point ∧ second point ≤ 1)
    (remaining : FiniteDist State) (error : ℝ)
    (herror : ∀ point,|first point-second point| ≤ error) :
    TVBound (rejectionStep proposal first hfirst remaining)
      (rejectionStep proposal second hsecond remaining) error := by
  intro event
  rw [_p2mH90,_p2mH90,_p2mH78,_p2mH78,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ point,proposal.weight point*error := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro point _
      rw [← mul_sub,abs_mul,abs_of_nonneg (proposal.nonneg point)]
      apply mul_le_mul_of_nonneg_left _ (proposal.nonneg point)
      rw [_p2mH88,_p2mH88]
      have he := remaining.event_nonneg event
      have he' := remaining.event_le_one event
      by_cases hp : point∈event
      · simp only [if_pos hp]
        have hid : first point+(1-first point)*remaining.event event-
            (second point+(1-second point)*remaining.event event)=
            (first point-second point)*(1-remaining.event event) := by ring
        rw [hid,abs_mul,abs_of_nonneg (by linarith : 0≤1-remaining.event event)]
        exact (mul_le_mul_of_nonneg_left (by linarith : 1-remaining.event event≤1) (abs_nonneg _)).trans
          (by simpa only [mul_one] using herror point)
      · simp only [if_neg hp,zero_add]
        have hid : (1-first point)*remaining.event event-(1-second point)*remaining.event event=
            -(first point-second point)*remaining.event event := by ring
        rw [hid,abs_mul,abs_neg,abs_of_nonneg he]
        exact (mul_le_mul_of_nonneg_left he' (abs_nonneg _)).trans
          (by simpa only [mul_one] using herror point)
    _ = error := by rw [← Finset.sum_mul,proposal.sum_one,one_mul]
open _root_.P2M661a572e renaming h89 → _p2mH89
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h71 (proposal : FiniteDist State) (first second : State → ℝ)
    (hfirst : ∀ point,0 ≤ first point ∧ first point ≤ 1)
    (hsecond : ∀ point,0 ≤ second point ∧ second point ≤ 1)
    (fallback : FiniteDist State) (error : ℝ)
    (herror : ∀ point,|first point-second point| ≤ error) (count : ℕ) :
    TVBound (cappedRejection proposal first hfirst fallback count)
      (cappedRejection proposal second hsecond fallback count) ((count : ℝ)*error) := by
  induction count with
  | zero => intro event; simp only [cappedRejection,Nat.cast_zero,zero_mul,sub_self,abs_zero,le_refl]
  | succ count ih =>
    have hstep := _p2mH89 proposal first second hfirst hsecond
      (cappedRejection proposal first hfirst fallback count) error herror
    have hremaining := _p2mH91 proposal second hsecond _ _ _ ih
    have hh := hstep.triangle hremaining
    simpa only [cappedRejection,Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm] using hh
open _root_.P2M661a572e renaming h71 → _p2mH71
end
open _root_.P2M661a572e renaming h71 → _p2mH71
open _root_.P2M661a572e renaming h88 → _p2mH88
open _root_.P2M661a572e renaming h89 → _p2mH89
end AFT.FiniteDist
open _root_.P2M661a572e renaming h71 → _p2mH71
open _root_.P2M661a572e renaming h88 → _p2mH88
open _root_.P2M661a572e renaming h89 → _p2mH89
end
open _root_.P2M661a572e renaming h88 → _p2mH88
open _root_.P2M661a572e renaming h71 → _p2mH71
open _root_.P2M661a572e renaming h89 → _p2mH89
section
namespace AFT.RationalAcceptanceCoin
open scoped BigOperators
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h113 (bits : ℕ) (value : ℚ) :
    ((FiniteDist.independent (fun _ : Fin bits => FiniteDist.uniform (Fin 2))).map
      (draw bits value)).weight 0=probability bits value := by
  exact _p2mH103 bits (counts bits value) (counts_total bits value) 0
open _root_.P2M661a572e renaming h113 → _p2mH113
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h114 (bits : ℕ) (value : ℚ) :
    0 ≤ probability bits value ∧ probability bits value ≤ 1 := by
  refine ⟨by unfold probability; positivity,?_⟩
  apply (div_le_one (by positivity : (0 : ℝ) < 2^bits)).mpr
  exact_mod_cast count_le bits value
open _root_.P2M661a572e renaming h114 → _p2mH114
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h115 (bits : ℕ) (value : ℚ) :
    |probability bits value-(clipped value : ℝ)| ≤ 1/(2 : ℝ)^bits := by
  have hlo := Nat.floor_le (mul_nonneg (by positivity : (0 : ℚ) ≤ 2^bits) (clipped_bounds value).1)
  have hhi := Nat.lt_floor_add_one ((2^bits : ℚ)*clipped value)
  have hlod : (count bits value : ℚ) ≤ (2 : ℚ)^bits*clipped value := by simpa only [count] using hlo
  have hlo' : (count bits value : ℝ) ≤ (2 : ℝ)^bits*(clipped value : ℝ) := by exact_mod_cast hlod
  have hhid : (2 : ℚ)^bits*clipped value ≤ (count bits value : ℚ)+1 := by simpa only [count] using hhi.le
  have hhi' : (2 : ℝ)^bits*(clipped value : ℝ) ≤ (count bits value : ℝ)+1 := by exact_mod_cast hhid
  have hp : (0 : ℝ) < 2^bits := by positivity
  have he : probability bits value-(clipped value : ℝ)=
      ((count bits value : ℝ)-(2 : ℝ)^bits*(clipped value : ℝ))/(2 : ℝ)^bits := by
    unfold probability
    field_simp
  rw [he,abs_div,abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  rw [abs_le]
  constructor <;> linarith
open _root_.P2M661a572e renaming h115 → _p2mH115
end
open _root_.P2M661a572e renaming h113 → _p2mH113
open _root_.P2M661a572e renaming h114 → _p2mH114
open _root_.P2M661a572e renaming h115 → _p2mH115
end AFT.RationalAcceptanceCoin
open _root_.P2M661a572e renaming h113 → _p2mH113
open _root_.P2M661a572e renaming h114 → _p2mH114
open _root_.P2M661a572e renaming h115 → _p2mH115
end
open _root_.P2M661a572e renaming h114 → _p2mH114
open _root_.P2M661a572e renaming h113 → _p2mH113
open _root_.P2M661a572e renaming h115 → _p2mH115
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h13 (input : RationalBits) :
    (clipUnit input).data.decode=RationalAcceptanceCoin.clipped input.decode := by
  have hd : (0 : ℚ)<value input.denominator := by exact_mod_cast input.denominator_positive
  cases hs : input.negative with
  | true =>
      have hn : input.decode≤ 0 := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_true,Int.cast_neg,Int.cast_natCast]
        exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hd.le
      simp only [clipUnit,hs,ite_true,zero_value,RationalAcceptanceCoin.clipped,max_eq_right hn,
        min_eq_right (by norm_num : (0 : ℚ)≤ 1)]
  | false =>
      have he : input.decode=(value input.numerator : ℚ)/(value input.denominator : ℚ) := by
        rw [decode_fraction]
        simp only [signedValue,hs,ite_false,Bool.false_eq_true,Int.cast_natCast]
      have hn : 0≤ input.decode := by rw [he];positivity
      simp only [clipUnit,hs,ite_false,Bool.false_eq_true,RationalAcceptanceCoin.clipped,max_eq_left hn]
      split <;> rename_i hb
      · have hc := (subtract_borrow input.numerator input.denominator).mp hb
        have hh : input.decode<1 := by rw [he,div_lt_one hd];exact_mod_cast hc
        exact (min_eq_right hh.le).symm
      · have hc : value input.denominator≤ value input.numerator := by
          exact Nat.le_of_not_gt (fun hh => hb ((subtract_borrow input.numerator input.denominator).mpr hh))
        have hh : 1≤ input.decode := by rw [he,le_div_iff₀ hd];simpa only [one_mul] using (show (value input.denominator : ℚ)≤value input.numerator by exact_mod_cast hc)
        rw [one_value,min_eq_left hh]
open _root_.P2M661a572e renaming h13 → _p2mH13
end AFT.BinaryArithmetic.RationalBits
open _root_.P2M661a572e renaming h13 → _p2mH13
end
open _root_.P2M661a572e renaming h13 → _p2mH13
section
namespace AFT.BinaryArithmetic
open RationalNumerics PermutationProgram BetaReference
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false in
private theorem _root_.P2M661a572e.h549 (bits : ℕ) (input : ℚ) (word : Fin bits → Fin 2) :
    (RationalAcceptanceCoin.draw bits input word).val=
      if (FiniteTicketSampler.bitTicket bits word).val<RationalAcceptanceCoin.count bits input then 0 else 1 := by
  have ht := (FiniteTicketSampler.bitTicket bits word).isLt
  have hc := RationalAcceptanceCoin.count_le bits input
  simp only [RationalAcceptanceCoin.draw,RationalAcceptanceCoin.counts,FiniteTicketSampler.drawBitTable,
    FiniteTicketSampler.drawFin,Fin.val_cast,List.ofFn_succ,List.ofFn_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.cons_val_fin_one]
  rw [FiniteTicketSampler.bucket]
  split_ifs with hfirst
  · rfl
  · have hh : (FiniteTicketSampler.bitTicket bits word).val-RationalAcceptanceCoin.count bits input <
        2^bits-RationalAcceptanceCoin.count bits input := by omega
    simp only [FiniteTicketSampler.bucket,if_pos hh,Nat.add_zero]
open _root_.P2M661a572e renaming h549 → _p2mH549
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false in
theorem _root_.P2M661a572e.h20 (input : RationalBits) (bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryAcceptance input bits word).value=(RationalAcceptanceCoin.draw bits input.decode word).val := by
  rw [_p2mH549]
  have hb := subtract_borrow (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits
  rw [readBitTape_value,RationalBits.dyadicFloor_value,_p2mH13] at hb
  change (if (subtract false (readBitTape bits word).digits (input.clipUnit.data.dyadicFloor bits).digits).borrow
      then 0 else 1)=_
  simp only [RationalAcceptanceCoin.count]
  split_ifs with haccept hthreshold hthreshold
  · simp only [if_pos hthreshold]
  · exact False.elim (hthreshold (hb.mp haccept))
  · exact False.elim (haccept (hb.mpr hthreshold))
  · simp only [if_neg hthreshold]
open _root_.P2M661a572e renaming h20 → _p2mH20
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h20 → _p2mH20
open _root_.P2M661a572e renaming h549 → _p2mH549
end
open _root_.P2M661a572e renaming h20 → _p2mH20
section
namespace AFT
namespace BoundaryCalibration
open scoped BigOperators
section FiniteRepair
variable {Ω : Type*} [Fintype Ω]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h62 (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (hquarter : ‖D‖ ≤ 1 / 4) (f : Ω → ℝ) :
    ‖neumannSolve D hD f - f‖ ≤ ‖f‖ / 3 := by
  let h := neumannSolve D hD f
  have heq : h - f = D h := by
    have hs := neumannSolve_equation D hD f
    change h - D h = f at hs
    exact sub_eq_iff_eq_add.mpr (by rw [← hs]; abel)
  have hnorm : ‖h‖ ≤ ‖h - f‖ + ‖f‖ := by
    simpa only [sub_add_cancel] using norm_add_le (h - f) f
  have hop : ‖h - f‖ ≤ (1 / 4) * ‖h‖ := by
    rw [heq]
    exact (D.le_opNorm h).trans (mul_le_mul_of_nonneg_right hquarter (norm_nonneg _))
  change ‖h - f‖ ≤ _
  nlinarith
open _root_.P2M661a572e renaming h62 → _p2mH62
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h61 (D : (Ω → ℝ) →L[ℝ] (Ω → ℝ))
    (hD : ‖D‖ < 1) (hquarter : ‖D‖ ≤ 1 / 4) (f : Ω → ℝ) :
    ‖neumannSolve D hD f‖ ≤ (4 / 3) * ‖f‖ := by
  have hb := _p2mH62 D hD hquarter f
  have ht := norm_add_le (neumannSolve D hD f - f) f
  rw [sub_add_cancel] at ht
  linarith
open _root_.P2M661a572e renaming h61 → _p2mH61
end FiniteRepair
open _root_.P2M661a572e renaming h61 → _p2mH61
open _root_.P2M661a572e renaming h62 → _p2mH62
section FeatureProjections
open scoped Classical
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I]
end FeatureProjections
section AffineFeatures
variable {F : Type*} [Field F]
end AffineFeatures
section UniformFeatures
open scoped Classical
variable {F : Type*} [Field F] [Fintype F]
variable {I : Type*} [Fintype I]
end UniformFeatures
end BoundaryCalibration
open _root_.P2M661a572e renaming h61 → _p2mH61
open _root_.P2M661a572e renaming h62 → _p2mH62
end AFT
open _root_.P2M661a572e renaming h61 → _p2mH61
open _root_.P2M661a572e renaming h62 → _p2mH62
end
open _root_.P2M661a572e renaming h62 → _p2mH62
open _root_.P2M661a572e renaming h61 → _p2mH61
namespace AFT.HistogramGenerating
end AFT.HistogramGenerating
namespace AFT.V7Calibration.actualBoundaryFraction
end AFT.V7Calibration.actualBoundaryFraction
section
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace FiniteDist
variable {State : Type*} [Fintype State] [Nonempty State]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h80 {Slot : Type*} [Fintype Slot] [DecidableEq Slot] :
    independent (fun _ : Slot => uniform State)=uniform (Slot → State) := by
  ext word
  simp only [independent,uniform_weight,Finset.prod_const,Finset.card_univ,Fintype.card_fun,
    Nat.cast_pow,inv_pow]
open _root_.P2M661a572e renaming h80 → _p2mH80
end FiniteDist
open _root_.P2M661a572e renaming h80 → _p2mH80
namespace HistogramGenerating
variable {G : Type*} [Fintype G] [AddCommGroup G]
end HistogramGenerating
namespace V7Calibration
open GaussianSource HistogramGenerating Filter
open scoped Topology
attribute [local instance] actualModulusNeZero
attribute [local instance] _root_.AFT.V7Calibration.referenceChargeConditionFinDecEq
end V7Calibration
end
open _root_.P2M661a572e renaming h80 → _p2mH80
end AFT
open _root_.P2M661a572e renaming h80 → _p2mH80
end
open _root_.P2M661a572e renaming h80 → _p2mH80
section
namespace AFT.RationalNumerics
open scoped BigOperators
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h554 (first second : ℝ) (hsecond : 0 ≤ second) :
    |max 0 first-second|≤|first-second| := by
  by_cases hfirst : 0≤first
  · rw [max_eq_right hfirst]
  · rw [max_eq_left (by linarith)]
    rw [abs_of_nonpos (by linarith : first-second≤0),abs_of_nonpos (by linarith : 0-second≤0)]
    linarith
open _root_.P2M661a572e renaming h554 → _p2mH554
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h134 {count : ℕ} (raw : Fin (count+1) → ℚ)
    (reference : FiniteDist (Fin (count+1))) (error : ℝ)
    (herror : (∑index,|(raw index : ℝ)-reference.weight index|)≤error) (hsmall : error≤1/2) :
    (∑index,|(positiveProgramLaw raw).weight index-reference.weight index|)≤4*error := by
  let positive := fun index => (positivePartProgram raw index : ℝ)
  have hp (index) : positive index=max 0 (raw index : ℝ) := by simp only [positive,positivePartProgram,Rat.cast_max,Rat.cast_zero]
  have herr : (∑index,|positive index-reference.weight index|)≤error := by
    apply le_trans _ herror
    exact Finset.sum_le_sum (fun index _ => by rw [hp];exact _p2mH554 _ _ (reference.nonneg index))
  have hm := (_p2mH148 positive reference.weight).trans herr
  rw [reference.sum_one] at hm
  have hlower : 1/2≤∑index,positive index := by have h := (abs_le.mp hm).1;linarith
  have hpositive : 0<∑index,positive index := lt_of_lt_of_le (by norm_num) hlower
  have hz : positiveNormalizerProgram raw≠0 := by
    have hcast : (positiveNormalizerProgram raw : ℝ)=∑index,positive index := by simp only [positiveNormalizerProgram,Rat.cast_sum,positive]
    intro hh
    rw [hh,Rat.cast_zero] at hcast
    linarith
  have hnormal := _p2mH149 positive reference.weight reference.nonneg
    hpositive (by rw [reference.sum_one];norm_num)
  have hw (index : Fin (count+1)) : positiveWeightProgram raw index=positivePartProgram raw index/positiveNormalizerProgram raw := if_neg hz
  have heq : (∑index,|(positiveProgramLaw raw).weight index-reference.weight index|)=
      ∑index,|positive index/(∑i,positive i)-reference.weight index/(∑i,reference.weight i)| := by
    simp only [positiveProgramLaw,hw,Rat.cast_div,positiveNormalizerProgram,
      Rat.cast_sum,positive,reference.sum_one,div_one]
  rw [heq]
  apply hnormal.trans
  calc
    _≤2*error/(∑i,positive i) := div_le_div_of_nonneg_right (by linarith) hpositive.le
    _≤2*error/(1/2) := div_le_div_of_nonneg_left (by
      have he0 := (Finset.sum_nonneg fun i (_ : i∈Finset.univ) => abs_nonneg (positive i-reference.weight i)).trans herr
      positivity) (by norm_num) hlower
    _=4*error := by ring
open _root_.P2M661a572e renaming h134 → _p2mH134
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h133 {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ) :
    (FiniteDist.independent (fun _ : Fin (bits+(count+1)+1) => FiniteDist.uniform (Fin 2))).map (positiveNormalizeDraw raw bits)=
      RationalFiniteQuantization.roundedLaw (positiveWeightProgram raw)
        (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^(bits+(count+1)+1)) (by positivity) := by
  exact _p2mH117 _ _ _ _
open _root_.P2M661a572e renaming h133 → _p2mH133
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h132 {count : ℕ} (raw : Fin (count+1) → ℚ) (bits : ℕ) :
    (∑index,|((FiniteDist.independent (fun _ : Fin (bits+(count+1)+1) => FiniteDist.uniform (Fin 2))).map
      (positiveNormalizeDraw raw bits)).weight index-(positiveProgramLaw raw).weight index|)≤1/(2 : ℝ)^bits := by
  rw [_p2mH133]
  have hh := _p2mH121 (positiveWeightProgram raw)
    (positiveWeightProgram_nonneg raw) (positiveWeightProgram_sum raw) (2^(bits+(count+1)+1)) (by positivity)
  apply hh.trans
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  have hp : ((count+1 : ℕ) : ℝ)≤(2 : ℝ)^(count+1) := by exact_mod_cast (Nat.lt_two_pow_self (n:=count+1)).le
  calc
    _≤2*((2 : ℝ)^(count+1))/(2 : ℝ)^(bits+(count+1)+1) := by
      gcongr
      simpa only [Nat.cast_add,Nat.cast_one] using hp
    _=_ := by rw [pow_add,pow_add];field_simp;ring
open _root_.P2M661a572e renaming h132 → _p2mH132
end
open _root_.P2M661a572e renaming h132 → _p2mH132
open _root_.P2M661a572e renaming h133 → _p2mH133
open _root_.P2M661a572e renaming h134 → _p2mH134
open _root_.P2M661a572e renaming h554 → _p2mH554
end AFT.RationalNumerics
open _root_.P2M661a572e renaming h132 → _p2mH132
open _root_.P2M661a572e renaming h133 → _p2mH133
open _root_.P2M661a572e renaming h134 → _p2mH134
open _root_.P2M661a572e renaming h554 → _p2mH554
end
open _root_.P2M661a572e renaming h132 → _p2mH132
open _root_.P2M661a572e renaming h133 → _p2mH133
open _root_.P2M661a572e renaming h134 → _p2mH134
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.explicitMarkedChartDensity
end AFT.BoundaryCalibration.explicitMarkedChartDensity
section
namespace AFT.BoundaryCalibration
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h57 (cutoff modulus : ℕ) (boundary baseline : ℤ)
    (index : Fin ((2*cutoff+1)*(2*cutoff+1))) :
    finiteProtectedPalettes cutoff modulus boundary baseline index =
      TrimmedSlice.paletteSlice modulus boundary (baseline-((finiteInputEquiv cutoff index).2 : ℤ)) := by
  ext color
  simp only [finiteProtectedPalettes, TrimmedSlice.paletteSlice, Finset.mem_filter,
    Finset.mem_univ, true_and, TrimmedSlice.mem_slice]
open _root_.P2M661a572e renaming h57 → _p2mH57
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
variable (modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
end
end AFT.BoundaryCalibration
open _root_.P2M661a572e renaming h57 → _p2mH57
end
open _root_.P2M661a572e renaming h57 → _p2mH57
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
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
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
section
namespace AFT.BoundaryCalibration
open scoped BigOperators
noncomputable section
open scoped Classical Topology
open Filter V7Calibration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h60 (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts))
    (law : FiniteDist (Fin charts)) (hsupport : ∀ point, point∉legal → law.weight point=0) :
    law.map (legalChartIndex charts legal)=law := by
  ext point
  rw [FiniteDist.map_weight]
  calc
    _ = ∑ input,if input=point then law.weight input else 0 := by
      apply Finset.sum_congr rfl
      intro input _
      by_cases hi : input∈legal
      · simp only [legalChartIndex,if_pos hi]
      · simp only [hsupport input hi,ite_self]
    _ = _ := by simp
open _root_.P2M661a572e renaming h60 → _p2mH60
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h59 (charts : ℕ) [NeZero charts] (legal : Finset (Fin charts))
    (approx reference : FiniteDist (Fin charts)) (hsupport : ∀ point, point∉legal → reference.weight point=0) :
    (∑point,|((approx.map (legalChartIndex charts legal)).weight point)-reference.weight point|)≤
      ∑point,|approx.weight point-reference.weight point| := by
  have hh := FiniteDist.l1_map_le approx reference (legalChartIndex charts legal)
  rwa [_p2mH60 charts legal reference hsupport] at hh
open _root_.P2M661a572e renaming h59 → _p2mH59
end
open _root_.P2M661a572e renaming h59 → _p2mH59
open _root_.P2M661a572e renaming h60 → _p2mH60
end AFT.BoundaryCalibration
open _root_.P2M661a572e renaming h59 → _p2mH59
open _root_.P2M661a572e renaming h60 → _p2mH60
end
open _root_.P2M661a572e renaming h59 → _p2mH59
open _root_.P2M661a572e renaming h60 → _p2mH60
namespace AFT.BoundaryCalibration.protectedInputs
end AFT.BoundaryCalibration.protectedInputs
section
namespace AFT.BoundaryCalibration
open GaussianSource
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h56 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (point : Fin (modulus*(modulus*modulus))) :
    (ZMod.finEquiv modulus) (finiteProtectedFeatures cutoff modulus input point)=
      feature (((finiteInputEquiv cutoff input).1 : ℤ) : ZMod modulus) (((finiteInputEquiv cutoff input).2 : ℤ) : ZMod modulus) (finiteChartEquiv modulus point) := by
   simp only [finiteProtectedFeatures,finiteAffineFeature,RingEquiv.apply_symm_apply]
open _root_.P2M661a572e renaming h56 → _p2mH56
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h58 (cutoff modulus : ℕ) [NeZero modulus]
    (boundary baseline : ℤ) (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
    color∈finiteProtectedPalettes cutoff modulus boundary baseline input ↔
      (ZMod.finEquiv modulus) color∈protectedPalettes cutoff modulus boundary baseline (finiteInputEquiv cutoff input) := by
   simp only [_p2mH57,protectedPalettes,fieldPalette,Finset.mem_map,Equiv.toEmbedding_apply]
   constructor
   · intro hc
     exact ⟨color,hc,rfl⟩
   · rintro ⟨other,ho,he⟩
     exact (ZMod.finEquiv modulus).injective he ▸ ho
open _root_.P2M661a572e renaming h58 → _p2mH58
end
open _root_.P2M661a572e renaming h56 → _p2mH56
open _root_.P2M661a572e renaming h58 → _p2mH58
end AFT.BoundaryCalibration
open _root_.P2M661a572e renaming h56 → _p2mH56
open _root_.P2M661a572e renaming h58 → _p2mH58
end
open _root_.P2M661a572e renaming h58 → _p2mH58
open _root_.P2M661a572e renaming h56 → _p2mH56
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h81 {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (first second : FiniteDist Index)
    (conditional conditional' : ∀ index,FiniteDist (Fiber index)) :
    (∑ point,|(dependentJoint first conditional).weight point-(dependentJoint second conditional').weight point|)≤
      (∑ index,|first.weight index-second.weight index|)+
        ∑ index,second.weight index*(∑ point,|(conditional index).weight point-(conditional' index).weight point|) := by
  simp only [dependentJoint,Fintype.sum_sigma]
  calc
    _ ≤ ∑ index,∑ point,(|first.weight index-second.weight index| *(conditional index).weight point+
        second.weight index*|(conditional index).weight point-(conditional' index).weight point|) := by
      apply Finset.sum_le_sum
      intro index _
      apply Finset.sum_le_sum
      intro point _
      have he : first.weight index*(conditional index).weight point-second.weight index*(conditional' index).weight point=
        (first.weight index-second.weight index)*(conditional index).weight point+
          second.weight index*((conditional index).weight point-(conditional' index).weight point) := by ring
      rw [he]
      simpa only [abs_mul,abs_of_nonneg ((conditional index).nonneg point),abs_of_nonneg (second.nonneg index)] using
        abs_add_le ((first.weight index-second.weight index)*(conditional index).weight point)
          (second.weight index*((conditional index).weight point-(conditional' index).weight point))
    _ = _ := by
      simp only [Finset.sum_add_distrib,←Finset.mul_sum]
      simp_rw [(conditional _).sum_one,mul_one]
open _root_.P2M661a572e renaming h81 → _p2mH81
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h82 {Index : Type*} [Fintype Index] {Fiber : Index → Type*}
    [∀ index,Fintype (Fiber index)] (first second : FiniteDist Index)
    (conditional conditional' : ∀ index,FiniteDist (Fiber index)) (error : ℝ)
    (h : ∀ index,(∑ point,|(conditional index).weight point-(conditional' index).weight point|)≤error) :
    (∑ point,|(dependentJoint first conditional).weight point-(dependentJoint second conditional').weight point|)≤
      (∑ index,|first.weight index-second.weight index|)+error := by
  apply (_p2mH81 first second conditional conditional').trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ index,second.weight index*error := Finset.sum_le_sum (fun index _ => mul_le_mul_of_nonneg_left (h index) (second.nonneg index))
    _ = error := by rw [←Finset.sum_mul,second.sum_one,one_mul]
open _root_.P2M661a572e renaming h82 → _p2mH82
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h84 {Input Bits Index : Type*} [Fintype Input] [Fintype Bits] [Fintype Index]
    {Fiber : Index → Type*} [∀ index,Fintype (Fiber index)]
    (input : FiniteDist Input) (bits : FiniteDist Bits) (first : Input → Index)
    (second : ∀ index,Bits → Fiber index) :
    (input.prod bits).map (fun pair => (⟨first pair.1,second (first pair.1) pair.2⟩ : Sigma Fiber))=
      dependentJoint (input.map first) (fun index => bits.map (second index)) := by
  ext output
  rcases output with ⟨index,value⟩
  simp only [map_weight,prod_weight,Fintype.sum_prod_type,dependentJoint,Finset.sum_mul,Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  apply Finset.sum_congr rfl
  intro tape _
  by_cases hi : first point=index
  · subst index
    simp only [Sigma.mk.inj_iff,heq_eq_eq,true_and,if_true]
    split_ifs <;> simp
  · have hne : (⟨first point,second (first point) tape⟩ : Sigma Fiber)≠⟨index,value⟩ :=
      fun hh => hi (congrArg Sigma.fst hh)
    simp only [if_neg hi,if_neg hne,zero_mul]
open _root_.P2M661a572e renaming h84 → _p2mH84
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h95 {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B] :
    uniform (A×B)=(uniform A).prod (uniform B) := by
  ext point
  simp only [uniform_weight,prod_weight,Fintype.card_prod,Nat.cast_mul,mul_inv_rev,mul_comm]
open _root_.P2M661a572e renaming h95 → _p2mH95
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h86 {Input Bits Index Fiber : Type*} [Fintype Input] [Fintype Bits] [Fintype Index] [Fintype Fiber]
    (input : FiniteDist Input) (bits : FiniteDist Bits) (first : Input → Index)
    (second : Index → Bits → Fiber) :
    (input.prod bits).map (fun pair => (first pair.1,second (first pair.1) pair.2))=
      joint (input.map first) (fun index => bits.map (second index)) := by
  have hh := congrArg (fun law : FiniteDist (Sigma (fun _ : Index => Fiber)) => law.map (Equiv.sigmaEquivProd Index Fiber))
    (_p2mH84 input bits first second)
  rw [map_map] at hh
  apply hh.trans
  ext point
  rw [map_equiv_weight]
  rfl
open _root_.P2M661a572e renaming h86 → _p2mH86
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h83 {Index Fiber : Type*} [Fintype Index] [Fintype Fiber]
    (first second : FiniteDist Index) (conditional conditional' : Index → FiniteDist Fiber) (error : ℝ)
    (h : ∀ index,(∑ point,|(conditional index).weight point-(conditional' index).weight point|)≤error) :
    (∑ point,|(joint first conditional).weight point-(joint second conditional').weight point|)≤
      (∑ index,|first.weight index-second.weight index|)+error := by
  have hh := _p2mH82 first second (Fiber:=fun _ => Fiber) conditional conditional' error h
  simpa only [Fintype.sum_sigma,Fintype.sum_prod_type,dependentJoint,joint] using hh
open _root_.P2M661a572e renaming h83 → _p2mH83
end
open _root_.P2M661a572e renaming h81 → _p2mH81
open _root_.P2M661a572e renaming h82 → _p2mH82
open _root_.P2M661a572e renaming h83 → _p2mH83
open _root_.P2M661a572e renaming h84 → _p2mH84
open _root_.P2M661a572e renaming h86 → _p2mH86
open _root_.P2M661a572e renaming h95 → _p2mH95
end AFT.FiniteDist
open _root_.P2M661a572e renaming h81 → _p2mH81
open _root_.P2M661a572e renaming h82 → _p2mH82
open _root_.P2M661a572e renaming h83 → _p2mH83
open _root_.P2M661a572e renaming h84 → _p2mH84
open _root_.P2M661a572e renaming h86 → _p2mH86
open _root_.P2M661a572e renaming h95 → _p2mH95
end
open _root_.P2M661a572e renaming h82 → _p2mH82
open _root_.P2M661a572e renaming h81 → _p2mH81
open _root_.P2M661a572e renaming h86 → _p2mH86
open _root_.P2M661a572e renaming h95 → _p2mH95
open _root_.P2M661a572e renaming h83 → _p2mH83
open _root_.P2M661a572e renaming h84 → _p2mH84
namespace AFT.FiniteDist.joint
end AFT.FiniteDist.joint
section
namespace AFT.RationalRejectionProgram
open FiniteDist FiniteConditionProgram
open scoped BigOperators
variable {State Tape : Type*}
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable [Fintype State] [Fintype Tape] [Nonempty Tape]
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h147 {Random : Type*} [Fintype Random]
    (law : FiniteDist State) (coins : State → FiniteDist (Fin 2))
    (remaining : FiniteDist Random) (output : Random → State) :
    ((joint law coins).prod remaining).map
      (fun pair => if pair.1.2=0 then pair.1.1 else output pair.2)=
      rejectionStep law (fun point => (coins point).weight 0)
        (fun point => ⟨(coins point).nonneg 0,by
          have hh := Finset.single_le_sum (fun index (_ : index∈Finset.univ) => (coins point).nonneg index) (Finset.mem_univ 0)
          simpa only [(coins point).sum_one] using hh⟩) (remaining.map output) := by
  ext target
  have hc (point : State) : (coins point).weight 1=1-(coins point).weight 0 := by
    have hh := (coins point).sum_one
    rw [Fin.sum_univ_two] at hh
    linarith
  simp only [map_weight,prod_weight,joint,Fintype.sum_prod_type,Fin.sum_univ_two]
  simp only [if_true,show ¬(1 : Fin 2)=0 by decide,if_false]
  have hfirst (point : State) :
      (∑ random,if point=target then law.weight point*(coins point).weight 0*remaining.weight random else 0)=
      if point=target then law.weight point*(coins point).weight 0 else 0 := by
    split_ifs with hp
    · rw [←Finset.mul_sum,remaining.sum_one,mul_one]
    · simp
  simp_rw [hfirst]
  have hsecond (point : State) :
      (∑ random,if output random=target then law.weight point*(coins point).weight 1*remaining.weight random else 0)=
      law.weight point*(coins point).weight 1*(remaining.map output).weight target := by
    simp only [map_weight,Finset.mul_sum,mul_ite,mul_zero]
  simp_rw [hsecond]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,←Finset.sum_mul]
  change law.weight target*(coins target).weight 0+_=
    law.weight target*(coins target).weight 0+(1-acceptance law (fun point => (coins point).weight 0))*_
  congr 1
  rw [show (∑point,law.weight point*(coins point).weight 1)=
    1-acceptance law (fun point => (coins point).weight 0) by
      simp only [hc,mul_sub,mul_one,Finset.sum_sub_distrib,law.sum_one,acceptance]]
open _root_.P2M661a572e renaming h147 → _p2mH147
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h146 (law : FiniteDist State) (coins : State → FiniteDist (Fin 2))
    (fallback : State) (attempts : ℕ) :
    (independent (fun _ : Fin attempts => joint law coins)).map (run fallback attempts)=
      cappedRejection law (fun point => (coins point).weight 0)
        (fun point => ⟨(coins point).nonneg 0,by
          have hh := Finset.single_le_sum (fun index (_ : index∈Finset.univ) => (coins point).nonneg index) (Finset.mem_univ 0)
          simpa only [(coins point).sum_one] using hh⟩) (CanonicalMoments.pointLaw fallback) attempts := by
  induction attempts with
  | zero =>
    ext target
    change ((independent (fun _ : Fin 0 => joint law coins)).map (fun _ => fallback)).weight target=_
    rw [_p2mH85]
    rfl
  | succ attempts ih =>
    rw [_p2mH63,FiniteDist.map_map]
    have he : (fun pair => run fallback (attempts+1)
      ((Fin.consEquiv (fun _ : Fin (attempts+1) => State×Fin 2)) pair))=
      (fun pair => if pair.1.2=0 then pair.1.1 else run fallback attempts pair.2) := by
        funext pair;simp only [run,Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]
    rw [he,_p2mH147,ih]
    rfl
open _root_.P2M661a572e renaming h146 → _p2mH146
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h145 (decode : Tape → State) (coin : State → ℚ) (bits : ℕ) :
    (uniform (Tape×(Fin bits → Fin 2))).map (proposal decode coin bits)=
      joint ((uniform Tape).map decode) (fun point => (uniform (Fin bits → Fin 2)).map
        (RationalAcceptanceCoin.draw bits (coin point))) := by
  rw [_p2mH95]
  exact _p2mH86 (uniform Tape) (uniform (Fin bits → Fin 2)) decode
    (fun point => RationalAcceptanceCoin.draw bits (coin point))
open _root_.P2M661a572e renaming h145 → _p2mH145
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h144 (decode : Tape → State) (coin : State → ℚ) (bits attempts : ℕ) (fallback : State) :
    (uniform (Fin attempts → Tape×(Fin bits → Fin 2))).map (draw decode coin bits attempts fallback)=
      cappedRejection ((uniform Tape).map decode) (fun point => RationalAcceptanceCoin.probability bits (coin point))
        (fun point => _p2mH114 bits (coin point)) (CanonicalMoments.pointLaw fallback) attempts := by
  have hi := _p2mH64 (fun _ : Fin attempts => uniform (Tape×(Fin bits → Fin 2)))
    (fun _ => proposal decode coin bits)
  rw [_p2mH65] at hi
  simp only [_p2mH145] at hi
  have hh := congrArg (fun law : FiniteDist (Fin attempts → State×Fin 2) => law.map (run fallback attempts)) hi
  rw [FiniteDist.map_map,_p2mH146] at hh
  have hc (point : State) : ((uniform (Fin bits → Fin 2)).map
      (RationalAcceptanceCoin.draw bits (coin point))).weight 0=RationalAcceptanceCoin.probability bits (coin point) := by
    rw [←_p2mH65]
    exact _p2mH113 bits (coin point)
  simp only [hc] at hh
  convert hh using 1 <;> rfl
open _root_.P2M661a572e renaming h144 → _p2mH144
end
open _root_.P2M661a572e renaming h144 → _p2mH144
open _root_.P2M661a572e renaming h145 → _p2mH145
open _root_.P2M661a572e renaming h146 → _p2mH146
open _root_.P2M661a572e renaming h147 → _p2mH147
end AFT.RationalRejectionProgram
open _root_.P2M661a572e renaming h144 → _p2mH144
open _root_.P2M661a572e renaming h145 → _p2mH145
open _root_.P2M661a572e renaming h146 → _p2mH146
open _root_.P2M661a572e renaming h147 → _p2mH147
end
open _root_.P2M661a572e renaming h144 → _p2mH144
open _root_.P2M661a572e renaming h145 → _p2mH145
open _root_.P2M661a572e renaming h146 → _p2mH146
open _root_.P2M661a572e renaming h147 → _p2mH147
section
namespace AFT.FiniteDist
open scoped BigOperators Classical
noncomputable section
variable {Source Inner Output : Type*} [Fintype Source] [Fintype Inner] [Fintype Output]
set_option maxRecDepth 8192
omit [Fintype Inner] in
theorem _root_.P2M661a572e.h68 (law : FiniteDist Source) {first second : Source → FiniteDist Output}
    {error : ℝ} (hbound : ∀ source,TVBound (first source) (second source) error) :
    TVBound (law.mix first) (law.mix second) error := by
  intro event
  simp only [_p2mH78,← Finset.sum_sub_distrib,← mul_sub]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  simp only [abs_mul,abs_of_nonneg (law.nonneg _)]
  calc
    _ ≤ ∑ source,law.weight source*error :=
      Finset.sum_le_sum fun source _ => mul_le_mul_of_nonneg_left (hbound source event) (law.nonneg source)
    _ = error := by rw [← Finset.sum_mul,law.sum_one,one_mul]
open _root_.P2M661a572e renaming h68 → _p2mH68
end
open _root_.P2M661a572e renaming h68 → _p2mH68
end AFT.FiniteDist
open _root_.P2M661a572e renaming h68 → _p2mH68
end
open _root_.P2M661a572e renaming h68 → _p2mH68
namespace AFT.RationalRejectionProgram
end AFT.RationalRejectionProgram
section
namespace AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h143 {State : Type*} (test : State → CountedValue Bool)
    (input : List State) :
    (countedListAll test input).value=true ↔ ∀ entry∈input,(test entry).value=true := by
  induction input with
  | nil => simp [countedListAll]
  | cons first rest ih => simp [countedListAll,ih]
open _root_.P2M661a572e renaming h143 → _p2mH143
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h142 (count : ℕ) (test : Fin count → CountedValue Bool) :
    (countedFinAll count test).value=true ↔ ∀ index,(test index).value=true := by
  simp [countedFinAll,_p2mH143]
open _root_.P2M661a572e renaming h142 → _p2mH142
end AFT.RationalRejectionProgram
open _root_.P2M661a572e renaming h142 → _p2mH142
open _root_.P2M661a572e renaming h143 → _p2mH143
end
open _root_.P2M661a572e renaming h143 → _p2mH143
open _root_.P2M661a572e renaming h142 → _p2mH142
namespace AFT.BoundaryCalibration.countedProtectedPaletteTest
end AFT.BoundaryCalibration.countedProtectedPaletteTest
section
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h39 (address cutoff modulus : ℕ) (hm : 0 <  modulus) :
     ((modularDifference address cutoff modulus).count : ZMod modulus)=(address : ZMod modulus)-(cutoff : ZMod modulus) := by
   have hcut := (divideCounter_value cutoff modulus hm).2
   have hfinal := (divideCounter_value (addCounter address (differenceCounter modulus (divideCounter cutoff modulus).remainder).count).count modulus hm).2
   dsimp only [modularDifference]
   rw [hfinal]
   simp only [addCounter_value,differenceCounter_value,hcut]
   rw [ZMod.natCast_mod,Nat.cast_add,Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt cutoff hm)),ZMod.natCast_self,ZMod.natCast_mod]
   ring
open _root_.P2M661a572e renaming h39 → _p2mH39
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h40 (cutoff modulus input chart : ℕ) (hm : 0 <  modulus) :
     ((protectedFeatureAddress cutoff modulus input chart).count : ZMod modulus)=
       (chart/(modulus*modulus) : ℕ)+
         ((chart%(modulus*modulus))/modulus : ℕ)*((input/(2*cutoff+1) : ℕ)-(cutoff : ZMod modulus))+
         ((chart%(modulus*modulus))%modulus : ℕ)*((input%(2*cutoff+1) : ℕ)-(cutoff : ZMod modulus)) := by
   dsimp only [protectedFeatureAddress]
   rw [(divideCounter_value _ _ hm).2,ZMod.natCast_mod]
   simp only [addCounter_value,multiplyCounter_value,Nat.cast_add,Nat.cast_mul,_p2mH39 _ _ _ hm]
   simp only [(divideCounter_value _ _ (Nat.mul_pos hm hm)).1,(divideCounter_value _ _ (Nat.mul_pos hm hm)).2,
     (divideCounter_value _ _ hm).1,(divideCounter_value _ _ hm).2,doubleCounter_value]
   rw [(divideCounter_value input (2*cutoff+1) (by omega)).1,(divideCounter_value input (2*cutoff+1) (by omega)).2]
open _root_.P2M661a572e renaming h40 → _p2mH40
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h37 (modulus : ℕ) [NeZero modulus]
     (chart : Fin (modulus*(modulus*modulus))) :
     (finiteChartEquiv modulus chart).1=(chart.val/(modulus*modulus) : ℕ) ∧
       (finiteChartEquiv modulus chart).2.1=((chart.val%(modulus*modulus))/modulus : ℕ) ∧
       (finiteChartEquiv modulus chart).2.2=((chart.val%(modulus*modulus))%modulus : ℕ) := by
   cases modulus with
   | zero => exact (NeZero.ne 0 rfl).elim
   | succ modulus =>
     simp only [finiteChartEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,finProdFinEquiv_symm_apply,
       ZMod.finEquiv,RingEquiv.toEquiv_eq_coe,EquivLike.coe_coe]
     constructor
     · apply Fin.ext
       exact (Nat.mod_eq_of_lt (Fin.divNat chart).isLt).symm
     constructor
     · apply Fin.ext
       exact (Nat.mod_eq_of_lt (Fin.divNat (Fin.modNat chart)).isLt).symm
     · apply Fin.ext
       exact (Nat.mod_eq_of_lt (Fin.modNat (Fin.modNat chart)).isLt).symm
open _root_.P2M661a572e renaming h37 → _p2mH37
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h41 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (chart : Fin (modulus*(modulus*modulus))) :
     (protectedFeature cutoff modulus input chart).value=finiteProtectedFeatures cutoff modulus input chart := by
   have hm : 0 <  modulus := Nat.pos_of_ne_zero (NeZero.ne _)
   have hf := _p2mH40 cutoff modulus input.val chart.val hm
   have hc := _p2mH37 modulus chart
   have hcast (x : Fin modulus) : (ZMod.finEquiv modulus) x=(x.val : ZMod modulus) := by
     cases modulus with
     | zero => exact (NeZero.ne 0 rfl).elim
     | succ n => apply Fin.ext;exact (Nat.mod_eq_of_lt x.isLt).symm
   apply (ZMod.finEquiv modulus).injective
   rw [hcast]
   change ((protectedFeatureAddress cutoff modulus input.val chart.val).count : ZMod modulus)=_
   rw [hf]
   simp only [finiteProtectedFeatures,finiteAffineFeature,RingEquiv.apply_symm_apply,feature,hc.1,hc.2.1,hc.2.2]
   simp only [finiteInputEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,finProdFinEquiv_symm_apply,
     FiniteConvolutionProgram.windowIndexEquiv,Equiv.coe_fn_mk,Prod.map_apply,Int.cast_sub,Int.cast_natCast]
   rfl
open _root_.P2M661a572e renaming h41 → _p2mH41
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h37 → _p2mH37
open _root_.P2M661a572e renaming h39 → _p2mH39
open _root_.P2M661a572e renaming h40 → _p2mH40
open _root_.P2M661a572e renaming h41 → _p2mH41
end
open _root_.P2M661a572e renaming h40 → _p2mH40
open _root_.P2M661a572e renaming h37 → _p2mH37
open _root_.P2M661a572e renaming h39 → _p2mH39
open _root_.P2M661a572e renaming h41 → _p2mH41
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h36 (count : ℕ) (test : Fin count → CountedValue Bool) :
    (countFin count test).count=∑ index,if (test index).value then 1 else 0 := by
  induction count with
  | zero => simp [countFin]
  | succ count ih =>
    simp only [countFin,ih,Fin.sum_univ_castSucc]
    split <;> simp_all
open _root_.P2M661a572e renaming h36 → _p2mH36
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h38 {count : ℕ} (mask : Vector Bool count) :
    (maskCount mask).count=(maskSet mask).card := by
  simp only [maskCount,_p2mH36,readVector_value,maskSet,Finset.card_filter]
open _root_.P2M661a572e renaming h38 → _p2mH38
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h36 → _p2mH36
open _root_.P2M661a572e renaming h38 → _p2mH38
end
open _root_.P2M661a572e renaming h38 → _p2mH38
open _root_.P2M661a572e renaming h36 → _p2mH36
section
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h51 (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input color : ℕ) :
     (protectedPalette cutoff modulus boundarySign baselineSign boundary baseline input color).value=true ↔
       signedValue boundarySign boundary+max (signedValue baselineSign baseline-
         ((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ))) 0≤(color : ℤ) ∧
       (color : ℤ)<(modulus : ℤ)-signedValue boundarySign boundary+
         min (signedValue baselineSign baseline-((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ))) 0 := by
   let source := divideCounter input (doubleCounter cutoff).count.succ
   let address := canonicalCounter source.remainder
   let shiftRadius := canonicalCounter cutoff
   let modulusBits := canonicalCounter modulus
   let colorBits := canonicalCounter color
   let shiftStart := signedAdd baselineSign false baseline shiftRadius.digits
   let shift := signedAdd shiftStart.negative true shiftStart.digits address.digits
   let lower := signedAdd boundarySign shift.negative boundary shift.digits
   let upperStart := signedAdd false (!boundarySign) modulusBits.digits boundary
   let upper := signedAdd upperStart.negative shift.negative upperStart.digits shift.digits
   have hsource : source.remainder=input%(2*cutoff+1) := by
     dsimp only [source];simpa only [doubleCounter_value] using (divideCounter_value input (doubleCounter cutoff).count.succ (Nat.succ_pos _)).2
   have hstart : signedValue shiftStart.negative shiftStart.digits=signedValue baselineSign baseline+(cutoff : ℤ) := by
     dsimp only [shiftStart];rw [signedAdd_value]
     simp only [shiftRadius,signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value]
   have hshift : signedValue shift.negative shift.digits=signedValue baselineSign baseline-
       ((input%(2*cutoff+1) : ℕ)-(cutoff : ℤ)) := by
     dsimp only [shift];rw [signedAdd_value,hstart]
     simp only [address,signedValue,ite_true,canonicalCounter_value,hsource]
     ring
   have hlower := signedAdd_value boundarySign shift.negative boundary shift.digits
   change signedValue lower.negative lower.digits=_ at hlower
   rw [hshift] at hlower
   have hupperStart : signedValue upperStart.negative upperStart.digits=(modulus : ℤ)-signedValue boundarySign boundary := by
     dsimp only [upperStart];rw [signedAdd_value,signedValue_not]
     simp only [modulusBits,signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value,sub_eq_add_neg]
   have hupper := signedAdd_value upperStart.negative shift.negative upperStart.digits shift.digits
   change signedValue upper.negative upper.digits=_ at hupper
   rw [hupperStart,hshift] at hupper
   have hcolor : signedValue false colorBits.digits=(color : ℤ) := by simp [colorBits,signedValue,canonicalCounter_value]
   change ((signedLe boundarySign false boundary colorBits.digits).value &&
     (signedLe lower.negative false lower.digits colorBits.digits).value &&
     !(signedLe upperStart.negative false upperStart.digits colorBits.digits).value &&
     !(signedLe upper.negative false upper.digits colorBits.digits).value)=true ↔ _
   simp only [Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,signedLe_value,hcolor,hlower,hupperStart,hupper]
   omega
open _root_.P2M661a572e renaming h51 → _p2mH51
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h52 (cutoff modulus : ℕ) (boundarySign baselineSign : Bool)
     (boundary baseline : List Bool) (input : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
     (protectedPalette cutoff modulus boundarySign baselineSign boundary baseline input.val color.val).value=true ↔
       color∈finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) input := by
   rw [_p2mH51]
   simp only [_p2mH57,TrimmedSlice.paletteSlice,Finset.mem_filter,Finset.mem_univ,true_and,
     TrimmedSlice.slice,Finset.mem_Ico,finiteInputEquiv,Equiv.trans_apply,Equiv.prodCongr_apply,
     finProdFinEquiv_symm_apply,FiniteConvolutionProgram.windowIndexEquiv,Equiv.coe_fn_mk,Prod.map_apply]
   rfl
open _root_.P2M661a572e renaming h52 → _p2mH52
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h51 → _p2mH51
open _root_.P2M661a572e renaming h52 → _p2mH52
end
open _root_.P2M661a572e renaming h51 → _p2mH51
open _root_.P2M661a572e renaming h52 → _p2mH52
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
namespace IntegerBits
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h2 (count : ℕ) (term : Fin count → CountedValue IntegerBits) :
    (sumFin count term).value.decode=∑ index,(term index).value.decode := by
  induction count with
  | zero => simp [sumFin]
  | succ count ih => simp only [sumFin,add_value,ih,Fin.sum_univ_castSucc]
open _root_.P2M661a572e renaming h2 → _p2mH2
end IntegerBits
open _root_.P2M661a572e renaming h2 → _p2mH2
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h2 → _p2mH2
end
open _root_.P2M661a572e renaming h2 → _p2mH2
section
namespace AFT.BinaryArithmetic.IntegerBits
open AFT.RationalRejectionProgram
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h1 (input : IntegerBits) (modulus : List Bool) (hq : 0 < value modulus)
    (hdiv : (value modulus : ℤ) ∣ input.decode) :
    (exactQuotient input modulus).value.decode=input.decode/(value modulus : ℤ) := by
  have hv := (divide_value input.digits modulus hq).1
  cases hs : input.negative with
  | false => simp only [exactQuotient,decode,signedValue,hs,Bool.false_eq_true,ite_false,hv,Int.natCast_ediv]
  | true =>
      have hd : (value modulus : ℤ) ∣ (value input.digits : ℤ) := by
        simpa only [decode,signedValue,hs,ite_true,dvd_neg] using hdiv
      simp only [exactQuotient,decode,signedValue,hs,ite_true,hv,Int.natCast_ediv,Int.neg_ediv_of_dvd hd]
open _root_.P2M661a572e renaming h1 → _p2mH1
end AFT.BinaryArithmetic.IntegerBits
open _root_.P2M661a572e renaming h1 → _p2mH1
end
open _root_.P2M661a572e renaming h1 → _p2mH1
section
namespace AFT
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h158 {α : Type*} {count : ℕ} (f : Fin count → α) :
    (Vector.ofFn f).get=f := by
  funext index
  exact Vector.get_ofFn f index
open _root_.P2M661a572e renaming h158 → _p2mH158
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h153 (count : ℕ) (load : Vector ℤ (count+1))
    (hload : totalCharge load.get=0) : pathLoad count (pathInverseProgram count load).value.get=load.get := by
  induction count with
  | zero =>
    funext index
    have hi : index=0 := Fin.ext (by omega)
    subst index
    simpa [totalCharge,pathLoad] using hload.symm
  | succ count ih =>
    let tail := Vector.ofFn (fun index : Fin (count+1) => load.get index.succ+if index=0 then load.get 0 else 0)
    have ht : totalCharge tail.get=0 := by
      have hsum : load.get 0+(∑ index : Fin (count+1),load.get index.succ)=0 := by
        simpa only [totalCharge,Fin.sum_univ_succ] using hload
      simpa [tail,totalCharge,Finset.sum_add_distrib,add_comm] using hsum
    have hh := ih tail ht
    funext index
    refine Fin.cases ?_ (fun rest => ?_) index
    · simp only [pathInverseProgram,Vector.get_ofFn,pathLoad,Fin.cons_zero]
    · simp only [pathInverseProgram,_p2mH158,pathLoad,Fin.cons_succ,Fin.tail_cons]
      change pathLoad count (pathInverseProgram count tail).value.get rest -
        (if rest=0 then load.get 0 else 0)=load.get rest.succ
      rw [hh]
      simp [tail]
open _root_.P2M661a572e renaming h153 → _p2mH153
noncomputable section
end
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h154 (count : ℕ) (modulus : ℤ) (injection load : Vector ℤ (count+1))
    (hinjection : totalCharge injection.get=modulus) (hload : modulus ∣ totalCharge load.get) :
    roundingLoad count injection.get
      ((roundingInverseProgram count modulus injection load).value.1.get,
        (roundingInverseProgram count modulus injection load).value.2)=load.get := by
  let charge := totalCharge load.get/modulus
  have hcharge : charge*modulus=totalCharge load.get := Int.ediv_mul_cancel hload
  let shifted := Vector.ofFn (fun index => load.get index-charge*injection.get index)
  have hshift : totalCharge shifted.get=0 := by
    rw [_p2mH158]
    change totalCharge (load.get-charge • injection.get)=0
    rw [totalCharge_sub,totalCharge_smul,hinjection,hcharge,sub_self]
  have hh := _p2mH153 count shifted hshift
  change pathLoad count (pathInverseProgram count shifted).value.get+charge • injection.get=load.get
  rw [hh]
  funext index
  simp only [shifted,Vector.get_ofFn,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring
open _root_.P2M661a572e renaming h154 → _p2mH154
noncomputable section
end
end AFT
open _root_.P2M661a572e renaming h153 → _p2mH153
open _root_.P2M661a572e renaming h154 → _p2mH154
open _root_.P2M661a572e renaming h158 → _p2mH158
end
open _root_.P2M661a572e renaming h158 → _p2mH158
open _root_.P2M661a572e renaming h154 → _p2mH154
open _root_.P2M661a572e renaming h153 → _p2mH153
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h24 {count : ℕ} (load : Vector IntegerBits (count+2)) (first : IntegerBits)
    (index : Fin (count+1)) :
    ((binaryPathTail load first).value.get index).decode=(load.get index.succ).decode+
      if index=0 then first.decode else 0 := by
  simp only [binaryPathTail,storeData_get,pathTailEntry,readVector_value]
  by_cases hi : index=0
  · subst index;simp [IntegerBits.add_value]
  · have hi' : index.val ≠ 0 := fun hh => hi (Fin.ext hh)
    simp [hi,hi']
open _root_.P2M661a572e renaming h24 → _p2mH24
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h23 (count : ℕ) (load : Vector IntegerBits (count+1)) (index : Fin count) :
    ((binaryPathInverse count load).value.get index).decode=
      (AFT.pathInverseProgram count (load.map IntegerBits.decode)).value.get index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      have ht : (binaryPathTail load (load.get 0)).value.map IntegerBits.decode=
          Vector.ofFn (fun slot : Fin (count+1) => (load.map IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map IntegerBits.decode).get 0 else 0) := by
        apply Vector.ext
        intro slot hs
        change ((binaryPathTail load (load.get 0)).value.map IntegerBits.decode).get ⟨slot,hs⟩=
          (Vector.ofFn (fun slot : Fin (count+1) => (load.map IntegerBits.decode).get slot.succ+
            if slot=0 then (load.map IntegerBits.decode).get 0 else 0)).get ⟨slot,hs⟩
        simp only [Vector.get_map,Vector.get_ofFn,_p2mH24]
      refine Fin.cases ?_ (fun rest => ?_) index
      · simp only [binaryPathInverse,storeData_get,Fin.cases_zero,readVector_value,
          AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_zero,Vector.get_map]
      · simp only [binaryPathInverse,storeData_get,Fin.cases_succ,readVector_value,
          AFT.pathInverseProgram,Vector.get_ofFn,Fin.cons_succ]
        rw [ih,ht]
open _root_.P2M661a572e renaming h23 → _p2mH23
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h23 → _p2mH23
open _root_.P2M661a572e renaming h24 → _p2mH24
end
open _root_.P2M661a572e renaming h24 → _p2mH24
open _root_.P2M661a572e renaming h23 → _p2mH23
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h32 {size : ℕ} (charge : IntegerBits) (injection load : Vector IntegerBits size)
    (index : Fin size) :
    ((binaryShiftedLoad charge injection load).value.get index).decode=
      (load.get index).decode-charge.decode*(injection.get index).decode := by
  simp only [binaryShiftedLoad,storeData_get,shiftedLoadEntry,IntegerBits.subtract_value,
    IntegerBits.multiply_value,readVector_value]
open _root_.P2M661a572e renaming h32 → _p2mH32
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h31 (count : ℕ) (modulus : List Bool)
    (injection load : Vector IntegerBits (count+1)) (hq : 0 < value modulus)
    (hdiv : (value modulus : ℤ) ∣ ∑ index,(load.get index).decode) :
    (binaryRoundingInverse count modulus injection load).charge.decode=
      (roundingInverseProgram count (value modulus) (injection.map IntegerBits.decode) (load.map IntegerBits.decode)).value.2 ∧
    ∀ index,((binaryRoundingInverse count modulus injection load).edges.get index).decode=
      ((roundingInverseProgram count (value modulus) (injection.map IntegerBits.decode) (load.map IntegerBits.decode)).value.1.get index) := by
  have htotal : (IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)).value.decode=
      ∑ index,(load.get index).decode := by rw [_p2mH2];simp only [readVector_value]
  have hc := _p2mH1 (IntegerBits.sumFin (count+1) (readVector IntegerBits.zero load)).value
    modulus hq (by rw [htotal];exact hdiv)
  rw [htotal] at hc
  refine ⟨?_,?_⟩
  · simpa only [binaryRoundingInverse,roundingInverseProgram,Vector.get_map] using hc
  · intro index
    simp only [binaryRoundingInverse,_p2mH23,roundingInverseProgram,Vector.get_map]
    congr 3
    apply Vector.ext
    intro slot hs
    change ((binaryShiftedLoad _ injection load).value.map IntegerBits.decode).get ⟨slot,hs⟩=
      (Vector.ofFn (fun index : Fin (count+1) => (load.get index).decode-
        ((∑ point : Fin (count+1),(load.get point).decode)/(value modulus : ℤ))*(injection.get index).decode)).get ⟨slot,hs⟩
    simp only [Vector.get_map,Vector.get_ofFn,_p2mH32,hc]
open _root_.P2M661a572e renaming h31 → _p2mH31
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h31 → _p2mH31
open _root_.P2M661a572e renaming h32 → _p2mH32
end
open _root_.P2M661a572e renaming h32 → _p2mH32
open _root_.P2M661a572e renaming h31 → _p2mH31
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h54 {size : ℕ} (matrix : Vector (Vector IntegerBits size) size)
     (column row : Fin size) : (readIntegerMatrix matrix column row).value=(matrix.get column).get row := by
   simp only [readIntegerMatrix,readList_value]
   rw [List.getElem?_eq_getElem (by simp only [Vector.length_toList];exact column.isLt)]
   simp only [Vector.getElem_toList,readVector_value]
   rfl
open _root_.P2M661a572e renaming h54 → _p2mH54
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h25 (count : ℕ) (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column vertex : Fin (count+1)) :
     (binaryPermutedColumn count matrix permutation column).value.get vertex=
       (matrix.get column).get (permutation.get vertex) := by
   simp only [binaryPermutedColumn,storeData_get,_p2mH54,readVector_value]
open _root_.P2M661a572e renaming h25 → _p2mH25
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h25 → _p2mH25
open _root_.P2M661a572e renaming h54 → _p2mH54
end
open _root_.P2M661a572e renaming h54 → _p2mH54
open _root_.P2M661a572e renaming h25 → _p2mH25
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.CanonicalMoments.twoPoolStatistic
end AFT.CanonicalMoments.twoPoolStatistic
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.chargeWordLaw
end AFT.FiniteDist.chargeWordLaw
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.monomialInputStatistic
end AFT.RepresentedPolynomial.monomialInputStatistic
namespace AFT.RepresentedPolynomial.monomialPairedStatistic
end AFT.RepresentedPolynomial.monomialPairedStatistic
namespace AFT.RepresentedPolynomial.monomialPlacementCount
end AFT.RepresentedPolynomial.monomialPlacementCount
namespace AFT.RepresentedPolynomial.tableBodyScope
end AFT.RepresentedPolynomial.tableBodyScope
namespace AFT.RepresentedPolynomial.tableLocalBound
end AFT.RepresentedPolynomial.tableLocalBound
namespace AFT.RepresentedPolynomial.tableLocalTerm
end AFT.RepresentedPolynomial.tableLocalTerm
namespace AFT.RepresentedPolynomial.tablePairedBodyScope
end AFT.RepresentedPolynomial.tablePairedBodyScope
namespace AFT.RepresentedPolynomial.tablePairedEnvelope
end AFT.RepresentedPolynomial.tablePairedEnvelope
namespace AFT.RepresentedPolynomial.tablePairedLocalTerm
end AFT.RepresentedPolynomial.tablePairedLocalTerm
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix
section
namespace AFT.RationalPaletteSampler
open scoped BigOperators
noncomputable section
open FiniteDist
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h141 (colors : ℕ) (hcolors : 0<colors) (raw : Fin colors → ℚ) (bits : ℕ)
    (reference : FiniteDist (Fin colors)) (error : ℝ)
    (herror : (∑ color,|(raw color : ℝ)-reference.weight color|)≤error) (hsmall : error≤1/2) :
    (∑ color,|((uniform (Fin (bits+colors+1) → Fin 2)).map
      (draw colors hcolors raw bits)).weight color-reference.weight color|)≤1/(2 : ℝ)^bits+4*error := by
  cases colors with
  | zero => omega
  | succ colors =>
    have hr := _p2mH132 raw bits
    have hp := _p2mH134 raw reference error herror hsmall
    rw [_p2mH105] at hr
    apply le_trans _ (add_le_add hr hp)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro color _
    exact abs_sub_le _ ((RationalNumerics.positiveProgramLaw raw).weight color) _
open _root_.P2M661a572e renaming h141 → _p2mH141
end
open _root_.P2M661a572e renaming h141 → _p2mH141
end AFT.RationalPaletteSampler
open _root_.P2M661a572e renaming h141 → _p2mH141
end
open _root_.P2M661a572e renaming h141 → _p2mH141
section
namespace AFT.BinaryArithmetic
open RationalNumerics RationalBits BoundaryCalibration BetaReference
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h27 {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    (binaryPositiveFinDraw raw bits word).value=
      (RationalPaletteSampler.draw count (NeZero.pos _) (fun index => (raw.get index).decode) bits word).val := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred => exact binaryPositiveDraw_value raw bits word
open _root_.P2M661a572e renaming h27 → _p2mH27
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h27 → _p2mH27
end
open _root_.P2M661a572e renaming h27 → _p2mH27
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics RationalBits Polynomial
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h33 (count : ℕ) (hc : 0 < count) (bits : ℕ)
    (word : Fin (bits+count+1) → Fin 2) :
    (binaryUniformDraw count hc bits word).value=
      RationalPaletteSampler.draw count hc (fun _ => (count : ℚ)⁻¹) bits word := by
  letI : NeZero count := ⟨Nat.ne_zero_of_lt hc⟩
  apply Fin.ext
  change (binaryPositiveFinDraw _ bits word).value=_
  rw [_p2mH27]
  simp only [Vector.get_replicate,inverse_value,ofCounter_value]
open _root_.P2M661a572e renaming h33 → _p2mH33
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h33 → _p2mH33
end
open _root_.P2M661a572e renaming h33 → _p2mH33
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.binaryPoolScan
end AFT.BinaryArithmetic.binaryPoolScan
namespace AFT.BinaryArithmetic.binaryPoolScan.match_1
end AFT.BinaryArithmetic.binaryPoolScan.match_1
namespace AFT.BinaryArithmetic.binaryRunPoolScan
end AFT.BinaryArithmetic.binaryRunPoolScan
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h34 (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     (binaryVertexCode legs rest index).value=(blockVertexNumbering legs rest).symm index := by
   apply (blockVertexNumbering legs rest).injective
   rw [Equiv.apply_symm_apply]
   unfold binaryVertexCode
   try dsimp only
   split
   · rename_i h
     apply Fin.ext
     change (divideCounter index.val 3).remainder+3*(divideCounter index.val 3).quotient=index.val
     rw [(divideCounter_value index.val 3 (by omega)).1,(divideCounter_value index.val 3 (by omega)).2]
     exact Nat.mod_add_div _ _
   · rename_i h
     apply Fin.ext
     change legs*3+(0+1*(differenceCounter index.val (multiplyCounter legs 3).count).count)=index.val
     simp only [Nat.zero_add,Nat.one_mul]
     rw [differenceCounter_value,multiplyCounter_value]
     have hi : legs*3 ≤ index.val := by
       have hh : ¬ index.val<(multiplyCounter legs 3).count := fun hi => h ((lessCounter_value _ _).mpr hi)
       rw [multiplyCounter_value] at hh
       omega
     omega
open _root_.P2M661a572e renaming h34 → _p2mH34
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h30 (legs rest : ℕ) (index : Fin legs⊕Fin rest) :
     (binaryRootAddress legs rest index).value=blockNumbering legs rest index := by
   cases index <;> apply Fin.ext <;> simp [binaryRootAddress,blockNumbering,addCounter_value]
open _root_.P2M661a572e renaming h30 → _p2mH30
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h30 → _p2mH30
open _root_.P2M661a572e renaming h34 → _p2mH34
end
open _root_.P2M661a572e renaming h30 → _p2mH30
open _root_.P2M661a572e renaming h34 → _p2mH34
section
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h53 (modulus : ℕ) [NeZero modulus] (chart : Fin (modulus*(modulus*modulus))) :
     (protectedScale modulus chart).value=finiteAffineScale modulus chart := by
   apply (ZMod.finEquiv modulus).injective
   have hcoord := (_p2mH37 modulus chart).2.1
   simp only [finiteAffineScale,RingEquiv.apply_symm_apply,hcoord]
   have hcast (x : Fin modulus) : (ZMod.finEquiv modulus) x=(x.val : ZMod modulus) := by
     cases modulus with
     | zero => exact (NeZero.ne 0 rfl).elim
     | succ n => apply Fin.ext;exact (Nat.mod_eq_of_lt x.isLt).symm
   rw [hcast]
   simp only [protectedScale,protectedScaleAddress_value _ _ (Nat.pos_of_ne_zero (NeZero.ne _))]
open _root_.P2M661a572e renaming h53 → _p2mH53
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h53 → _p2mH53
end
open _root_.P2M661a572e renaming h53 → _p2mH53
section
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h21 (modulus : ℕ) [NeZero modulus]
    (chart : Fin (modulus*(modulus*modulus))) :
    (((binaryChartCoordinates modulus chart.val).offset : ZMod modulus),
      ((binaryChartCoordinates modulus chart.val).scale : ZMod modulus),
      ((binaryChartCoordinates modulus chart.val).shear : ZMod modulus))=
        finiteChartEquiv modulus chart := by
  have hm := NeZero.pos modulus
  rcases binaryChartCoordinates_values modulus chart.val hm with ⟨ho,hs,ht⟩
  rw [ho,hs,ht]
  rcases _p2mH37 modulus chart with ⟨h0,h1,h2⟩
  apply Prod.ext h0.symm
  exact Prod.ext h1.symm h2.symm
open _root_.P2M661a572e renaming h21 → _p2mH21
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h21 → _p2mH21
end
open _root_.P2M661a572e renaming h21 → _p2mH21
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h14 (first second : RationalBits) :
    (difference first second).data.decode=first.decode-second.decode := by
  simp only [difference,add_value,negate_value,sub_eq_add_neg]
open _root_.P2M661a572e renaming h14 → _p2mH14
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h9 (charts : ℕ) (term : Fin charts → RationalResult) :
    (chartExpectation charts term).data.decode=chartExpectationProgram charts (fun index => (term index).data.decode) := by
  simp only [chartExpectation,quotient_value,sumFin_value,ofCounter_value,chartExpectationProgram]
open _root_.P2M661a572e renaming h9 → _p2mH9
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h4 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts)
    (color : Fin colors) (point : Fin charts) :
    (chartConditionalTerm feature profile color point).data.decode=
      if feature.get point=color then (profile.get point).decode else 0 := by
  have he : (equalCounter (readVector 0 feature point).value.val color.val).value=true ↔ feature.get point=color := by
    rw [equalCounter_value,readVector_value]
    exact Fin.val_injective.eq_iff
  by_cases hh : feature.get point=color
  · have hb := he.mpr hh
    simp only [readVector_value] at hb
    simp only [chartConditionalTerm,readVector_value,hb,ite_true,if_pos hh]
  · have hb : (equalCounter (readVector 0 feature point).value.val color.val).value=false := by
      cases hv : (equalCounter (readVector 0 feature point).value.val color.val).value
      · rfl
      · exact False.elim (hh (he.mp hv))
    simp only [chartConditionalTerm,hb,Bool.false_eq_true,ite_false,if_neg hh,zero_value]
open _root_.P2M661a572e renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h5 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts) (color : Fin colors) :
    (chartConditional feature profile color).data.decode=
      chartConditionalProgram charts colors feature.get (fun index => (profile.get index).decode) color := by
  simp only [chartConditional,multiply_value,ofCounter_value,_p2mH9,_p2mH4,chartConditionalProgram]
open _root_.P2M661a572e renaming h5 → _p2mH5
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h3 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (color : Fin colors) :
    (chartAllowedTerm feature allowed profile color).data.decode=
      if color∈maskSet allowed then chartConditionalProgram charts colors feature.get
        (fun index => (profile.get index).decode) color else 0 := by
  simp only [chartAllowedTerm,readVector_value,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
  split <;> simp_all only [_p2mH5,zero_value]
open _root_.P2M661a572e renaming h3 → _p2mH3
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h10 {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (point : Fin charts) :
    (chartFeature feature allowed profile point).data.decode=
      chartFeatureProgram charts colors feature.get (maskSet allowed) (fun index => (profile.get index).decode) point := by
  have htotal : (sumFin colors (chartAllowedTerm feature allowed profile)).data.decode=
      ∑ color∈maskSet allowed,chartConditionalProgram charts colors feature.get
        (fun index => (profile.get index).decode) color := by
    rw [sumFin_value]
    simp only [_p2mH3,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [Finset.sum_filter]
  simp only [chartFeature,readVector_value,chartFeatureProgram]
  split <;> rename_i hactive
  · simp only [_p2mH14,_p2mH5,quotient_value,htotal,ofCounter_value,_p2mH38]
    rw [if_pos (by simpa only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hactive)]
  · simp only [zero_value]
    rw [if_neg (by simpa only [maskSet,Finset.mem_filter,Finset.mem_univ,true_and] using hactive)]
open _root_.P2M661a572e renaming h10 → _p2mH10
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h11 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (point : Fin charts) :
    (chartProjection feature allowed profile point).data.decode=
      chartProjectionProgram charts colors features (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) (fun index => (profile.get index).decode) point := by
  simp only [chartProjection,add_value,_p2mH9,sumFin_value,chartProjectionTerm,
    readVector_value,_p2mH10,chartProjectionProgram]
open _root_.P2M661a572e renaming h11 → _p2mH11
end AFT.BinaryArithmetic.RationalBits
open _root_.P2M661a572e renaming h3 → _p2mH3
open _root_.P2M661a572e renaming h4 → _p2mH4
open _root_.P2M661a572e renaming h5 → _p2mH5
open _root_.P2M661a572e renaming h9 → _p2mH9
open _root_.P2M661a572e renaming h10 → _p2mH10
open _root_.P2M661a572e renaming h11 → _p2mH11
open _root_.P2M661a572e renaming h14 → _p2mH14
end
open _root_.P2M661a572e renaming h14 → _p2mH14
open _root_.P2M661a572e renaming h4 → _p2mH4
open _root_.P2M661a572e renaming h9 → _p2mH9
open _root_.P2M661a572e renaming h11 → _p2mH11
open _root_.P2M661a572e renaming h5 → _p2mH5
open _root_.P2M661a572e renaming h10 → _p2mH10
open _root_.P2M661a572e renaming h3 → _p2mH3
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.cachedLinearIteration
end AFT.RationalNumerics.cachedLinearIteration
namespace AFT.RationalNumerics.cachedLinearIteration.match_1
end AFT.RationalNumerics.cachedLinearIteration.match_1
namespace AFT.RationalNumerics.cachedMatrix
end AFT.RationalNumerics.cachedMatrix
namespace AFT.RationalNumerics.cachedMatrixApply
end AFT.RationalNumerics.cachedMatrixApply
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualCachedInverseProgram
end AFT.V7Calibration.actualCachedInverseProgram
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h18 {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output input : Fin count) :
    (matrixProductTerm matrix profile output input).data.decode=
      ((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [matrixProductTerm,multiply_value,matrixEntry_value,readVector_value]
open _root_.P2M661a572e renaming h18 → _p2mH18
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h19 {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output : Fin count) :
    (matrixRow matrix profile output).data.decode=
      ∑ input,((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [matrixRow,sumFin_value,_p2mH18]
open _root_.P2M661a572e renaming h19 → _p2mH19
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h17 {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output : Fin count) :
    ((matrixApply matrix profile).data.get output).decode=
      ∑ input,((matrix.get output).get input).decode*(profile.get input).decode := by
  simp only [matrixApply,buildArray_get,_p2mH19]
open _root_.P2M661a572e renaming h17 → _p2mH17
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h15 {count : ℕ} (rhs applied : Vector RationalBits count) (output : Fin count) :
    (iterationEntry rhs applied output).data.decode=(rhs.get output).decode-(applied.get output).decode := by
  simp only [iterationEntry,add_value,negate_value,readVector_value,sub_eq_add_neg]
open _root_.P2M661a572e renaming h15 → _p2mH15
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h16 {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (rhs : Vector RationalBits count) (steps : ℕ) (output : Fin count) :
    ((iteration matrix rhs steps).data.get output).decode=
      linearIteration (fun out inp => ((matrix.get out).get inp).decode) (fun out => (rhs.get out).decode) steps output := by
  induction steps generalizing output with
  | zero => simp [iteration,linearIteration]
  | succ steps ih =>
    simp only [iteration,buildArray_get,_p2mH15,_p2mH17,linearIteration,Pi.sub_apply,AFT.RationalNumerics.matrixApply]
    congr 1
    apply Finset.sum_congr rfl
    intro input _
    rw [ih]
open _root_.P2M661a572e renaming h16 → _p2mH16
end AFT.BinaryArithmetic.RationalBits
open _root_.P2M661a572e renaming h15 → _p2mH15
open _root_.P2M661a572e renaming h16 → _p2mH16
open _root_.P2M661a572e renaming h17 → _p2mH17
open _root_.P2M661a572e renaming h18 → _p2mH18
open _root_.P2M661a572e renaming h19 → _p2mH19
end
open _root_.P2M661a572e renaming h16 → _p2mH16
open _root_.P2M661a572e renaming h17 → _p2mH17
open _root_.P2M661a572e renaming h19 → _p2mH19
open _root_.P2M661a572e renaming h18 → _p2mH18
open _root_.P2M661a572e renaming h15 → _p2mH15
section
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h12 {charts : ℕ} (fiber : Vector Bool charts) (point : Fin charts) :
     (chartSpike fiber point).data.decode=chartSpikeProgram charts (maskSet fiber) point := by
   simp only [chartSpike,readVector_value,chartSpikeProgram,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   split <;> simp_all [quotient_value,ofCounter_value,_p2mH38,maskSet]
open _root_.P2M661a572e renaming h12 → _p2mH12
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h6 {charts : ℕ} (safe : Vector Bool charts) (input point : Fin charts) :
     (chartDeletedBasis safe input point).data.decode=
       if point∈maskSet safe then 0 else if point=input then 1 else 0 := by
   have he : (equalCounter point.val input.val).value=true ↔ point=input := by
     rw [equalCounter_value,Fin.val_inj]
   simp only [chartDeletedBasis,readVector_value,maskSet,Finset.mem_filter,Finset.mem_univ,true_and]
   by_cases hs : safe.get point=true
   · simp [hs]
   · simp only [hs,Bool.false_eq_true,ite_false]
     by_cases hi : point=input
     · simp only [he.mpr hi,ite_true,if_pos hi,one_value]
     · have hn : (equalCounter point.val input.val).value=false := Bool.eq_false_iff.mpr (fun h => hi (he.mp h))
       simp [hn,hi]
open _root_.P2M661a572e renaming h6 → _p2mH6
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h7 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (chartDeletionEntry feature allowed safe output input).data.decode=
       chartDeletionMatrixProgram charts colors features (fun i => (feature.get i).get)
         (fun i => maskSet (allowed.get i)) (maskSet safe) output input := by
   simp only [chartDeletionEntry,negate_value,_p2mH11,buildArray_get,_p2mH6,
     chartDeletionMatrixProgram,chartDeletionProgram]
open _root_.P2M661a572e renaming h7 → _p2mH7
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h8 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) :
     (((chartDeletionMatrix feature allowed safe).data.get output).get input).decode=
       chartDeletionMatrixProgram charts colors features (fun i => (feature.get i).get)
         (fun i => maskSet (allowed.get i)) (maskSet safe) output input := by
   simp only [chartDeletionMatrix,Vector.get_map,Vector.get_ofFn,buildArray_get,_p2mH7]
open _root_.P2M661a572e renaming h8 → _p2mH8
end AFT.BinaryArithmetic.RationalBits
open _root_.P2M661a572e renaming h6 → _p2mH6
open _root_.P2M661a572e renaming h7 → _p2mH7
open _root_.P2M661a572e renaming h8 → _p2mH8
open _root_.P2M661a572e renaming h12 → _p2mH12
end
open _root_.P2M661a572e renaming h6 → _p2mH6
open _root_.P2M661a572e renaming h8 → _p2mH8
open _root_.P2M661a572e renaming h7 → _p2mH7
open _root_.P2M661a572e renaming h12 → _p2mH12
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h35 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (point : Fin charts) (index : Fin features) :
     (chartAllowedAt feature allowed point index).value=(allowed.get index).get ((feature.get index).get point) := by
   simp only [chartAllowedAt,readVector_value]
open _root_.P2M661a572e renaming h35 → _p2mH35
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h55 {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (point : Fin charts) :
     (safeChart feature allowed scale point).value=true ↔
       scale.get point≠0 ∧ ∀ index,(allowed.get index).get ((feature.get index).get point)=true := by
   simp only [safeChart,Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq,equalCounter_value,
     readVector_value,_p2mH142,_p2mH35]
   have hzero : (scale.get point).val=0 ↔ scale.get point=0 := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
   rw [hzero]
open _root_.P2M661a572e renaming h55 → _p2mH55
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h35 → _p2mH35
open _root_.P2M661a572e renaming h55 → _p2mH55
end
open _root_.P2M661a572e renaming h55 → _p2mH55
open _root_.P2M661a572e renaming h35 → _p2mH35
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration AFT.BetaReference
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h22 {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) (legal : Finset (Fin charts))
    (hmask : ∀ index,mask.get index=true ↔ index∈legal) :
    (binaryLegalChartIndex mask point).value=legalChartIndex charts legal point := by
  apply Fin.ext
  change (legalChartScan mask point).value=_
  by_cases hp : mask.get point=true
  · have hh := (hmask point).mp hp
    simp only [legalChartScan,readVector_value,hp,↓reduceIte,legalChartIndex,if_pos hh]
  · have hh : point∉legal := fun hi => hp ((hmask point).mpr hi)
    simp only [legalChartScan,readVector_value,if_neg hp,legalChartIndex,if_neg hh]
    cases hf : (firstTrue mask.toList).value with
    | none =>
      have hall := List.findIdx?_eq_none_iff.mp ((firstTrue_value mask.toList).symm.trans hf)
      have hn : ¬legal.Nonempty := by
        rintro ⟨index,hi⟩
        have ht : mask.get index=true := (hmask index).mpr hi
        have hm : mask.get index∈mask.toList := by
          change mask[index.val]∈mask.toList
          rw [← Vector.getElem_toList (xs := mask) (i := index.val) (by simpa only [Vector.length_toList] using index.isLt)]
          exact List.getElem_mem (by simpa only [Vector.length_toList] using index.isLt)
        have hz := hall (mask.get index) hm
        simp only [id_eq,ht] at hz
        contradiction
      simp only [dif_neg hn,Option.getD_none,Fin.val_zero]
    | some index =>
      have hs := List.findIdx?_eq_some_iff_findIdx_eq.mp ((firstTrue_value mask.toList).symm.trans hf)
      have hi : index < charts := by simpa only [Vector.length_toList] using hs.1
      let selected : Fin charts := ⟨index,hi⟩
      have hm : selected∈legal := by
        apply (hmask selected).mp
        have hv := @List.findIdx_getElem Bool id mask.toList (by rw [hs.2];exact hs.1)
        change mask[index]=true
        simpa only [hs.2,id_eq,Vector.getElem_toList] using hv
      have hl : ∀ other∈legal,selected≤other := by
        intro other ho
        by_contra hn
        have ho' : other.val < index := by simpa only [Fin.not_le,Fin.lt_def,selected] using hn
        have hz := @List.not_of_lt_findIdx Bool id mask.toList other.val (by rw [hs.2];exact ho')
        have ht := (hmask other).mpr ho
        have hv : mask.get other=false := by
          change mask[other.val]=false
          simpa only [id_eq,Vector.getElem_toList] using hz
        rw [ht] at hv
        contradiction
      have hne : legal.Nonempty := ⟨selected,hm⟩
      have hmin := (Finset.min'_eq_iff legal hne selected).mpr ⟨hm,hl⟩
      simp only [dif_pos hne,hmin,Option.getD_some,selected]
open _root_.P2M661a572e renaming h22 → _p2mH22
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h22 → _p2mH22
end
open _root_.P2M661a572e renaming h22 → _p2mH22
section
namespace AFT.BinaryArithmetic
open RationalRejectionProgram
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h26 (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (vertex : Fin (count+1)) :
     (binaryPhysicalVertex legs rest count hvertex vertex).value=
       (physicalVertexNumberingProgram legs rest count hvertex).symm vertex :=
   _p2mH34 legs rest _
open _root_.P2M661a572e renaming h26 → _p2mH26
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h26 → _p2mH26
end
open _root_.P2M661a572e renaming h26 → _p2mH26
section
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h44 (cutoff modulus charts features : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (index : Fin features) (point : Fin charts) :
     (((protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value.feature).get index).get point=
       finiteProtectedFeatures cutoff modulus (index.cast hfeatures) (point.cast hcharts) := by
   simp only [protectedMetadataCore,storeData_get,_p2mH41]
open _root_.P2M661a572e renaming h44 → _p2mH44
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h42 (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (index : Fin features) (color : Fin modulus) :
     (((protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value.allowed).get index).get color=true ↔
       color∈finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) (index.cast hfeatures) := by
   simp only [protectedMetadataCore,storeData_get]
   exact _p2mH52 cutoff modulus boundarySign baselineSign boundary baseline (index.cast hfeatures) color
open _root_.P2M661a572e renaming h42 → _p2mH42
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h45 (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) (point : Fin charts) :
     ((protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value.scale).get point=
       finiteAffineScale modulus (point.cast hcharts) := by
   simp only [protectedMetadataCore,storeData_get,_p2mH53]
open _root_.P2M661a572e renaming h45 → _p2mH45
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h43 (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (h : BinaryPublicChartMetadata charts modulus features=
       BinaryPublicChartMetadata (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))) :
     cast h (protectedMetadataCore cutoff modulus charts features hcharts hfeatures boundarySign baselineSign boundary baseline mark).value=
       (protectedMetadataCore cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) rfl rfl
         boundarySign baselineSign boundary baseline mark).value := by
   subst charts
   subst features
   rfl
open _root_.P2M661a572e renaming h43 → _p2mH43
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h50 (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value=
       (protectedMetadataCore cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) rfl rfl
         boundarySign baselineSign boundary baseline mark).value := by
   dsimp only [protectedMetadata]
   exact _p2mH43 cutoff modulus _ _ _ _ boundarySign baselineSign boundary baseline mark _
open _root_.P2M661a572e renaming h50 → _p2mH50
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h42 → _p2mH42
open _root_.P2M661a572e renaming h43 → _p2mH43
open _root_.P2M661a572e renaming h44 → _p2mH44
open _root_.P2M661a572e renaming h45 → _p2mH45
open _root_.P2M661a572e renaming h50 → _p2mH50
end
open _root_.P2M661a572e renaming h44 → _p2mH44
open _root_.P2M661a572e renaming h45 → _p2mH45
open _root_.P2M661a572e renaming h50 → _p2mH50
open _root_.P2M661a572e renaming h43 → _p2mH43
open _root_.P2M661a572e renaming h42 → _p2mH42
section
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h47 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     (fun index point => (((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.feature).get index).get point)=
       finiteProtectedFeatures cutoff modulus := by
   funext index point
   rw [_p2mH50,_p2mH44]
   rfl
open _root_.P2M661a572e renaming h47 → _p2mH47
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h46 (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (index : Fin ((2*cutoff+1)*(2*cutoff+1))) (color : Fin modulus) :
     (((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.allowed).get index).get color=true ↔
       color∈finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) index := by
   rw [_p2mH50,_p2mH42]
   rfl
open _root_.P2M661a572e renaming h46 → _p2mH46
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h49 (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.scale).get=finiteAffineScale modulus := by
   funext point
   rw [_p2mH50,_p2mH45]
   rfl
open _root_.P2M661a572e renaming h49 → _p2mH49
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h48 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
     (point : Fin (modulus*(modulus*modulus))) :
     ((protectedMetadata cutoff modulus boundarySign baselineSign boundary baseline mark).value.safe).get point=true ↔
       point∈finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
         (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline)) := by
   rw [_p2mH50]
   simp only [protectedMetadataCore,storeData_get,_p2mH55,_p2mH53,_p2mH41,
     Fin.cast_refl,id_eq,_p2mH52,finiteMarkedSafe,Finset.mem_filter,Finset.mem_univ,true_and]
open _root_.P2M661a572e renaming h48 → _p2mH48
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h46 → _p2mH46
open _root_.P2M661a572e renaming h47 → _p2mH47
open _root_.P2M661a572e renaming h48 → _p2mH48
open _root_.P2M661a572e renaming h49 → _p2mH49
end
open _root_.P2M661a572e renaming h46 → _p2mH46
open _root_.P2M661a572e renaming h49 → _p2mH49
open _root_.P2M661a572e renaming h47 → _p2mH47
open _root_.P2M661a572e renaming h48 → _p2mH48
section
namespace AFT.BinaryArithmetic
open RationalNumerics RationalRejectionProgram
variable {State Tape : Type*}
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h28 (raw envelope : RationalBits) :
    (binaryPositiveRatio raw envelope).data.decode=max raw.decode 0/envelope.decode := by
  simp only [binaryPositiveRatio,RationalBits.quotient_value,RationalBits.maxZero_value]
open _root_.P2M661a572e renaming h28 → _p2mH28
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h29 (sample : Tape → CountedValue State)
    (score : State → CountedValue RationalBits) (envelope : RationalBits) (envelopeValue bits : ℕ)
    (he : envelope.decode=(envelopeValue : ℚ)) (fallback : CountedValue State)
    (attempts : ℕ) (tape : Fin attempts → Tape×(Fin bits → Fin 2)) :
    (binaryRejectionDraw sample score envelope bits fallback attempts tape).value=
      RationalRejectionProgram.positiveDraw (fun input => (sample input).value)
        (fun point => (score point).value.decode) envelopeValue bits attempts fallback.value tape := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      simp only [binaryRejectionDraw,_p2mH20,_p2mH28,he,
        RationalRejectionProgram.positiveDraw,RationalRejectionProgram.draw,RationalRejectionProgram.run,
        RationalRejectionProgram.proposal]
      have hc : ∀ coin : Fin 2,coin.val=0 ↔ coin=0 := fun coin => by simp only [Fin.ext_iff,Fin.val_zero]
      simp only [hc]
      by_cases ha : RationalAcceptanceCoin.draw bits
          (max (score (sample (tape 0).1).value).value.decode 0 / (envelopeValue : ℚ)) (tape 0).2 = 0
      · simp only [ha, if_true]
      · simpa only [ha, if_false, RationalRejectionProgram.positiveDraw,
          RationalRejectionProgram.draw, RationalRejectionProgram.run,
          RationalRejectionProgram.proposal, Fin.tail] using ih (Fin.tail tape)
open _root_.P2M661a572e renaming h29 → _p2mH29
end AFT.BinaryArithmetic
open _root_.P2M661a572e renaming h28 → _p2mH28
open _root_.P2M661a572e renaming h29 → _p2mH29
end
open _root_.P2M661a572e renaming h29 → _p2mH29
open _root_.P2M661a572e renaming h28 → _p2mH28
section
namespace CurrentAFT
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h545 {weight : ℝ} (hweight : weight ≤ 0) : clip weight = 0 := by
  simp [clip, max_eq_left hweight]
open _root_.P2M661a572e renaming h545 → _p2mH545
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h546 {weight : ℝ} (hweight : 2 ≤ weight) : clip weight = 2 := by
  have hnonneg : 0 ≤ weight := by linarith
  simp [clip, max_eq_right hnonneg, min_eq_left hweight]
open _root_.P2M661a572e renaming h546 → _p2mH546
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h544 {weight : ℝ} (hweight : weight ∈ Set.Icc (0 : ℝ) 2) :
    clip weight = weight := by
  simp [clip, max_eq_right hweight.1, min_eq_right hweight.2]
open _root_.P2M661a572e renaming h544 → _p2mH544
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h558 {left right : ℝ} (horder : left ≤ right) :
    0 ≤ clip right - clip left ∧ clip right - clip left ≤ right - left := by
  rcases le_total left 0 with hleft | hleft
  · rcases le_total right 0 with hright | hright
    · rw [_p2mH545 hleft, _p2mH545 hright]
      constructor <;> linarith
    · rcases le_total right 2 with hright2 | hright2
      · rw [_p2mH545 hleft, _p2mH544 ⟨hright, hright2⟩]
        constructor <;> linarith
      · rw [_p2mH545 hleft, _p2mH546 hright2]
        constructor <;> linarith
  · rcases le_total 2 left with hleft2 | hleft2
    · have hright2 : 2 ≤ right := hleft2.trans horder
      rw [_p2mH546 hleft2, _p2mH546 hright2]
      constructor <;> linarith
    · have hright : 0 ≤ right := hleft.trans horder
      rcases le_total right 2 with hright2 | hright2
      · rw [_p2mH544 ⟨hleft, hleft2⟩,
          _p2mH544 ⟨hright, hright2⟩]
        constructor <;> linarith
      · rw [_p2mH544 ⟨hleft, hleft2⟩, _p2mH546 hright2]
        constructor <;> linarith
open _root_.P2M661a572e renaming h558 → _p2mH558
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h543 (left right : ℝ) :
    |clip left - clip right| ≤ |left - right| := by
  rcases le_total left right with horder | horder
  · obtain ⟨hnonneg, hbound⟩ := _p2mH558 horder
    rw [abs_of_nonpos (by linarith : clip left - clip right ≤ 0),
      abs_of_nonpos (by linarith : left - right ≤ 0)]
    linarith
  · obtain ⟨hnonneg, hbound⟩ := _p2mH558 horder
    rw [abs_of_nonneg (by linarith : 0 ≤ clip left - clip right),
      abs_of_nonneg (by linarith : 0 ≤ left - right)]
    exact hbound
open _root_.P2M661a572e renaming h543 → _p2mH543
open scoped BigOperators
end CurrentAFT
open _root_.P2M661a572e renaming h543 → _p2mH543
open _root_.P2M661a572e renaming h544 → _p2mH544
open _root_.P2M661a572e renaming h545 → _p2mH545
open _root_.P2M661a572e renaming h546 → _p2mH546
open _root_.P2M661a572e renaming h558 → _p2mH558
end
open _root_.P2M661a572e renaming h545 → _p2mH545
open _root_.P2M661a572e renaming h543 → _p2mH543
open _root_.P2M661a572e renaming h544 → _p2mH544
open _root_.P2M661a572e renaming h546 → _p2mH546
section
namespace CurrentAFT.CurrentPhysicalNumbering
open AFT ActualBlockFock
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.bodySize Parameters.legCount Parameters.dimension
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h436 (security : ℕ) (leg : Fin (Parameters.legCount security)) (slot : Fin 3) :
    (numbering security ⟨.inl leg, slot⟩).val = slot.val + 3 * leg.val := by
  rfl
open _root_.P2M661a572e renaming h436 → _p2mH436
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h435 (security : ℕ) (center : Fin (centerCount security)) :
    (numbering security ⟨.inr (.inl center), (0 : Fin 1)⟩).val = Parameters.legCount security * 3 + center.val := by
  rfl
open _root_.P2M661a572e renaming h435 → _p2mH435
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h437 (security : ℕ) (queue : Fin (Parameters.modulus security)) :
    (numbering security ⟨.inr (.inr queue), (0 : Fin 1)⟩).val =
      Parameters.legCount security * 3 + (centerCount security + queue.val) := by
  rfl
open _root_.P2M661a572e renaming h437 → _p2mH437
end CurrentAFT.CurrentPhysicalNumbering
open _root_.P2M661a572e renaming h435 → _p2mH435
open _root_.P2M661a572e renaming h436 → _p2mH436
open _root_.P2M661a572e renaming h437 → _p2mH437
end
open _root_.P2M661a572e renaming h435 → _p2mH435
open _root_.P2M661a572e renaming h436 → _p2mH436
open _root_.P2M661a572e renaming h437 → _p2mH437
section
namespace CurrentAFT.ActualCalibrationRates
open ActualCalibrationFourier ActualCalibrationClipping
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h159 (accuracyOrder : ℕ) : 2 ≤ Parameters.calibrationOrder accuracyOrder := by
  unfold Parameters.calibrationOrder
  omega
open _root_.P2M661a572e renaming h159 → _p2mH159
end
open _root_.P2M661a572e renaming h159 → _p2mH159
end CurrentAFT.ActualCalibrationRates
open _root_.P2M661a572e renaming h159 → _p2mH159
end
open _root_.P2M661a572e renaming h159 → _p2mH159
section
namespace CurrentAFT.AffineFlagCalibration
open AFT AFT.BoundaryCalibration
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.legLawModulusNeZero
attribute [local instance] _root_.CurrentAFT.AffineFlagCalibration.currentModulusPrime
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h555 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (left right : ℚ) (hl0 : 0 ≤ (left : ℝ)) (hlHalf : (left : ℝ) ≤ 1 / 2)
    (hr0 : 0 ≤ (right : ℝ)) (hrHalf : (right : ℝ) ≤ 1 / 2)
    (hcast : (left : ℝ) = (right : ℝ)) :
    hcast ▸ (CurrentFlagProgram.current security baseline hbaseline mark left hl0 hlHalf).model =
      (CurrentFlagProgram.current security baseline hbaseline mark right hr0 hrHalf).model := by
  have heq : left = right := Rat.cast_injective hcast
  subst left
  rfl
open _root_.P2M661a572e renaming h555 → _p2mH555
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h160 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    currentLaw security baseline hbaseline mark (atom : ℝ) ha0 haHalf =
      (CurrentFlagProgram.current security baseline hbaseline mark atom ha0 haHalf).model := by
  unfold currentLaw
  split_ifs with hrational
  · exact _p2mH555 security baseline hbaseline mark (Classical.choose hrational) atom
      _ _ ha0 haHalf (Classical.choose_spec hrational)
  · exact False.elim (hrational ⟨atom, rfl⟩)
open _root_.P2M661a572e renaming h160 → _p2mH160
end
open _root_.P2M661a572e renaming h160 → _p2mH160
open _root_.P2M661a572e renaming h555 → _p2mH555
end CurrentAFT.AffineFlagCalibration
open _root_.P2M661a572e renaming h160 → _p2mH160
open _root_.P2M661a572e renaming h555 → _p2mH555
end
open _root_.P2M661a572e renaming h160 → _p2mH160
section
namespace CurrentAFT.LobsterCoordinates
open AFT PublicCharge LobsterIncidence
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h481 (bodyEdges legs : ℕ) (placement : Equiv.Perm (Fin (bodyEdges + 1)))
    (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) (index : Fin (bodyEdges + (legs + legs) + 1)) :
    (relabeledBasis bodyEdges legs placement attachment relabeling input).val index =
      LobsterIncidence.load placement attachment (edgeCoordinates ℤ bodyEdges legs input)
        ((vertexIndex bodyEdges legs).symm (relabeling.symm index)) := rfl
open _root_.P2M661a572e renaming h481 → _p2mH481
end
open _root_.P2M661a572e renaming h481 → _p2mH481
end CurrentAFT.LobsterCoordinates
open _root_.P2M661a572e renaming h481 → _p2mH481
end
open _root_.P2M661a572e renaming h481 → _p2mH481
namespace CurrentAFT
end CurrentAFT
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
section
namespace CurrentAFT.LobsterMixerMatrix
open AFT LobsterCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Scalar : Type*} [CommRing Scalar]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h483 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : Fin (bodyEdges + (legs + legs)) → Scalar)
    (index : Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) :
    (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs index) =
      (blockMatrix bodyEdges legs scale shear).mulVec (input ∘ edgeIndex bodyEdges legs) index := by
  simp only [numberedMatrix, Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  rw [← Equiv.sum_comp (edgeIndex bodyEdges legs)]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]
open _root_.P2M661a572e renaming h483 → _p2mH483
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h482 (bodyEdges legs : ℕ) (scale shear : Fin legs → Scalar)
    (input : (Fin bodyEdges ⊕ (Fin legs ⊕ Fin legs)) → Scalar) :
    (blockMatrix bodyEdges legs scale shear).mulVec input =
      Sum.elim (fun vertex => input (.inl vertex))
        (Sum.elim (fun leg => scale leg * input (.inr (.inl leg)) + shear leg * input (.inr (.inr leg)))
          (fun leg => input (.inr (.inr leg)))) := by
  ext index
  rcases index with vertex | (leg | leg) <;>
    simp [blockMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.one_apply, Matrix.diagonal_apply]
open _root_.P2M661a572e renaming h482 → _p2mH482
end
open _root_.P2M661a572e renaming h482 → _p2mH482
open _root_.P2M661a572e renaming h483 → _p2mH483
end CurrentAFT.LobsterMixerMatrix
open _root_.P2M661a572e renaming h482 → _p2mH482
open _root_.P2M661a572e renaming h483 → _p2mH483
end
open _root_.P2M661a572e renaming h483 → _p2mH483
open _root_.P2M661a572e renaming h482 → _p2mH482
section
namespace CurrentAFT.AffineRealization
open AFT LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h163 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) :
    pathLoad _ (extensionCorrection bodyEdges legs modulus queues relabeling) =
      queueColumn bodyEdges legs modulus queues relabeling - injectionColumn _ modulus :=
  (Classical.choose_spec (exists_extension_correction _
    (injectionColumn _ modulus) (queueColumn bodyEdges legs modulus queues relabeling)
    ((queueColumn_charge bodyEdges legs modulus queues relabeling).trans
      (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues)).symm))).1
open _root_.P2M661a572e renaming h163 → _p2mH163
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h164 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    roundingLoad _ (injectionColumn _ modulus)
      (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input) =
      (relabeledBasis bodyEdges legs placement attachment relabeling
        ((numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
          input.2 • queueColumn bodyEdges legs modulus queues relabeling :=
  _p2mH157 _ _ _ _ _ _
    (_p2mH163 bodyEdges legs modulus queues relabeling) input
open _root_.P2M661a572e renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h166 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (closureScalar : ℤ)
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (hcharge : PublicCharge.PublicChargeTest modulus centers shift) :
    roundingLoad _ (injectionColumn _ modulus)
      (offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
        numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling :=
  (Classical.choose_spec (offset_integral_preimage bodyEdges legs modulus (NeZero.ne modulus)
    (injectionColumn _ modulus) (totalCharge_injectionColumn _ modulus (queue_modulus_le bodyEdges legs modulus queues))
    centers shift intercept placement closureScalar relabeling hcharge)).1
open _root_.P2M661a572e renaming h166 → _p2mH166
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h161 (bodyEdges legs modulus : ℕ) [NeZero modulus]
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (centers : Fin (bodyEdges + 1) → ℤ) (shift intercept : Fin legs → ℤ)
    (closureScalar : ℤ) (hcharge : PublicCharge.PublicChargeTest modulus centers shift)
    (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    roundingLoad _ (injectionColumn _ modulus)
      (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input +
        offsetCoordinates bodyEdges legs modulus queues centers shift intercept placement closureScalar relabeling hcharge) =
      (relabeledBasis bodyEdges legs placement attachment relabeling
        ((numberedMatrix bodyEdges legs scale shear).mulVec input.1)).val +
        input.2 • queueColumn bodyEdges legs modulus queues relabeling +
        numberedOffset bodyEdges legs modulus centers shift intercept placement closureScalar relabeling := by
  have hadd (n : ℕ) (column : Fin (n + 1) → ℤ) (first second : (Fin n → ℤ) × ℤ) :
      roundingLoad n column (first + second) = roundingLoad n column first + roundingLoad n column second := by
    simp only [roundingLoad, Prod.fst_add, Prod.snd_add, pathLoad_add, add_smul]
    abel
  rw [hadd, _p2mH164, _p2mH166]
open _root_.P2M661a572e renaming h161 → _p2mH161
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h162 (count : ℕ) (basis : (Fin count → ℤ) ≃ₗ[ℤ] zeroSumLattice count)
    (input : Fin count → ℤ) :
    (edgeBasisChangeMatrix count basis).mulVec input = edgeBasisChange count basis input := by
  have hrepr (v : Fin count → ℤ) : ⇑((Pi.basisFun ℤ (Fin count)).repr v) = v := by
    funext i
    exact Pi.basisFun_repr ℤ (Fin count) v i
  simpa only [edgeBasisChangeMatrix, hrepr, LinearEquiv.coe_coe] using
    LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℤ (Fin count)) (Pi.basisFun ℤ (Fin count))
      (edgeBasisChange count basis).toLinearMap input
open _root_.P2M661a572e renaming h162 → _p2mH162
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h165 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (placement : Equiv.Perm (Fin (bodyEdges + 1))) (attachment : Fin legs → Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1)))
    (scale shear : Fin legs → ℤ) (input : (Fin (bodyEdges + (legs + legs)) → ℤ) × ℤ) :
    (matrix bodyEdges legs modulus queues placement attachment relabeling scale shear).mulVec
      (Sum.elim input.1 (fun _ : Unit => input.2)) =
      Sum.elim (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).1
        (fun _ : Unit => (linearPart bodyEdges legs modulus queues placement attachment relabeling scale shear input).2) := by
  rw [matrix, transportBlockMatrix, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, ← Matrix.mulVec_mulVec, _p2mH162,
    linearPart, blockTransport, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply]
  congr 1
  ext index
  simp [Matrix.mulVec, dotProduct, mul_comm]
open _root_.P2M661a572e renaming h165 → _p2mH165
end
open _root_.P2M661a572e renaming h161 → _p2mH161
open _root_.P2M661a572e renaming h162 → _p2mH162
open _root_.P2M661a572e renaming h163 → _p2mH163
open _root_.P2M661a572e renaming h164 → _p2mH164
open _root_.P2M661a572e renaming h165 → _p2mH165
open _root_.P2M661a572e renaming h166 → _p2mH166
end CurrentAFT.AffineRealization
open _root_.P2M661a572e renaming h161 → _p2mH161
open _root_.P2M661a572e renaming h162 → _p2mH162
open _root_.P2M661a572e renaming h163 → _p2mH163
open _root_.P2M661a572e renaming h164 → _p2mH164
open _root_.P2M661a572e renaming h165 → _p2mH165
open _root_.P2M661a572e renaming h166 → _p2mH166
end
open _root_.P2M661a572e renaming h164 → _p2mH164
open _root_.P2M661a572e renaming h166 → _p2mH166
open _root_.P2M661a572e renaming h161 → _p2mH161
open _root_.P2M661a572e renaming h162 → _p2mH162
open _root_.P2M661a572e renaming h165 → _p2mH165
open _root_.P2M661a572e renaming h163 → _p2mH163
section
namespace CurrentAFT.BinaryArrayRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
variable {State Tape : Type*} [Inhabited Tape]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h167 (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State)
    (attempts : ℕ) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    (run sample score envelope bits fallback attempts words).value =
      (binaryRejectionDraw sample score envelope bits fallback attempts words.get).value := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [run, binaryRejectionDraw, readVector_value]
    split_ifs
    · rfl
    · rw [ih]
      have htail : (storeData attempts (fun index => readVector (default : Tape × (Fin bits → Fin 2)) words index.succ)).value.get =
          Fin.tail words.get := by
        funext index
        exact storeData_get _ _ index |>.trans (readVector_value _ _ _)
      rw [htail]
open _root_.P2M661a572e renaming h167 → _p2mH167
end CurrentAFT.BinaryArrayRejection
open _root_.P2M661a572e renaming h167 → _p2mH167
end
open _root_.P2M661a572e renaming h167 → _p2mH167
section
namespace CurrentAFT.WindowGaussianSampler
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h540 (security : ℕ) : 0 < squaredWidth security := by
  unfold squaredWidth
  positivity
open _root_.P2M661a572e renaming h540 → _p2mH540
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h541 (security : ℕ) :
    (squaredWidth security : ℝ) = (Parameters.sourceWidth security : ℝ)^2 := by
  unfold squaredWidth Parameters.sourceWidth Parameters.base
  push_cast
  rfl
open _root_.P2M661a572e renaming h541 → _p2mH541
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h538 (security cutoff bits : ℕ) :
    (∑ point, |((FiniteDist.independent (fun _ : Fin (windowTicketBits cutoff bits) =>
      FiniteDist.uniform (Fin 2))).map (draw security cutoff bits)).weight point -
        (windowGaussian (Parameters.sourceWidth security) cutoff).weight point|) ≤ 1 / (2 : ℝ)^bits := by
  rw [show draw security cutoff bits = windowGaussianDraw (squaredWidth security) cutoff bits from rfl,
    _p2mH137]
  exact _p2mH138 _ _ _ _ (_p2mH540 security) (_p2mH541 security)
open _root_.P2M661a572e renaming h538 → _p2mH538
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h539 (security bits : ℕ) :
    (∑ point, |((FiniteDist.independent
      (fun _ : Fin (windowTicketBits (edgeCutoff security) bits) => FiniteDist.uniform (Fin 2))).map
        (draw security (edgeCutoff security) bits)).weight point - (edgeLaw security).weight point|) ≤
          1 / (2 : ℝ)^bits := _p2mH538 security _ bits
open _root_.P2M661a572e renaming h539 → _p2mH539
end
open _root_.P2M661a572e renaming h538 → _p2mH538
open _root_.P2M661a572e renaming h539 → _p2mH539
end CurrentAFT.WindowGaussianSampler
open _root_.P2M661a572e renaming h538 → _p2mH538
open _root_.P2M661a572e renaming h539 → _p2mH539
open _root_.P2M661a572e renaming h540 → _p2mH540
open _root_.P2M661a572e renaming h541 → _p2mH541
end
open _root_.P2M661a572e renaming h541 → _p2mH541
open _root_.P2M661a572e renaming h540 → _p2mH540
open _root_.P2M661a572e renaming h538 → _p2mH538
open _root_.P2M661a572e renaming h539 → _p2mH539
section
namespace CurrentAFT.CyclePatternProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h477 {State : Type*} [Fintype State] (first second : FiniteDist State)
    (test : State → ℝ) (bound : ℝ) (htest : ∀ state, |test state| ≤ bound) :
    |first.expectation test - second.expectation test| ≤
      bound * ∑ state, |first.weight state - second.weight state| := by
  unfold FiniteDist.expectation
  rw [← Finset.sum_sub_distrib]
  calc
    _ = |∑ state, (first.weight state - second.weight state) * test state| := by
      congr 1
      apply Finset.sum_congr rfl
      intro state _
      ring
    _ ≤ ∑ state, |(first.weight state - second.weight state) * test state| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ state, bound * |first.weight state - second.weight state| := by
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (htest state) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm
open _root_.P2M661a572e renaming h477 → _p2mH477
end
open _root_.P2M661a572e renaming h477 → _p2mH477
end CurrentAFT.CyclePatternProgram
open _root_.P2M661a572e renaming h477 → _p2mH477
end
open _root_.P2M661a572e renaming h477 → _p2mH477
section
namespace CurrentAFT.LocalPairProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles LocalReferenceEnergy
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h484 (security bits : ℕ) :
    |(activationApprox security bits : ℝ) - DiffuseProfiles.activation security| ≤ (1/2:ℝ) * (1 / (2:ℝ)^bits) := by
  let law := windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits
  have hsum : (∑ point, |law.weight point - (scalarLaw security).weight point|) ≤ 1 / (2:ℝ)^bits :=
    _p2mH136 _ _ _ _ (_p2mH540 security)
      (_p2mH541 security).symm
  have hatom := Finset.single_le_sum (f := fun point => |law.weight point - (scalarLaw security).weight point|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (windowZero (Parameters.sourceCutoff security - 1)))
  have heq : (activationApprox security bits : ℝ) = (1/2:ℝ)*law.weight (windowZero _) := by
    simp only [activationApprox, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    rfl
  rw [heq]
  unfold DiffuseProfiles.activation
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
  exact mul_le_mul_of_nonneg_left (hatom.trans hsum) (by norm_num)
open _root_.P2M661a572e renaming h484 → _p2mH484
end
open _root_.P2M661a572e renaming h484 → _p2mH484
end CurrentAFT.LocalPairProgram
open _root_.P2M661a572e renaming h484 → _p2mH484
end
open _root_.P2M661a572e renaming h484 → _p2mH484
section
namespace CurrentAFT.RationalProposalProgram
open AFT GaussianSource RationalNumerics DiffuseProfiles ProposalPrimary
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h524 (security bits : ℕ) (primary output : FirstHistogram.Palette security) :
    |(anchor security bits primary.val output.val : ℝ) -
      (InwardAnchor.smoothedAnchorLaw security primary).weight output| ≤ 1 / (2 : ℝ)^bits := by
  rw [anchor_cast]
  have hl1 := _p2mH136 (WindowGaussianSampler.squaredWidth security)
    (Parameters.sourceWidth security) (Parameters.sourceCutoff security - 1) bits
    (_p2mH540 security) (_p2mH541 security).symm
  have h := _p2mH477
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
    (fun scalar => (InwardAnchor.shiftedAnchorLaw security primary scalar.val
      (InwardAnchor.scalar_bound security scalar)).weight output) 1 (fun scalar => by
      rw [abs_of_nonneg ((InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).nonneg output)]
      exact (InwardAnchor.shiftedAnchorLaw security primary scalar.val
        (InwardAnchor.scalar_bound security scalar)).atom_le_one output)
  exact h.trans (by simpa only [one_mul,scalarLaw] using hl1)
open _root_.P2M661a572e renaming h524 → _p2mH524
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h535 (security bits : ℕ) :
    (∑ seed, |(approximateSeedLaw security bits).weight seed - (actualSeedLaw security).weight seed|) ≤
      3 / (2 : ℝ)^bits := by
  have he := _p2mH136 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (edgeCutoff security) bits (_p2mH540 security)
    (_p2mH541 security).symm
  have hs := _p2mH136 (WindowGaussianSampler.squaredWidth security) (Parameters.sourceWidth security)
    (Parameters.sourceCutoff security - 1) bits (_p2mH540 security)
    (_p2mH541 security).symm
  have hp := FiniteDist.l1_prod_le
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits)
    (edgeLaw security)
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits) (edgeLaw security)
  have hall := FiniteDist.l1_prod_le
    ((windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits).prod
      (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (edgeCutoff security) bits))
    ((edgeLaw security).prod (edgeLaw security))
    (windowApproxLaw (WindowGaussianSampler.squaredWidth security) (Parameters.sourceCutoff security - 1) bits)
    (scalarLaw security)
  exact hall.trans ((add_le_add (hp.trans (add_le_add he he)) hs).trans_eq (by ring))
open _root_.P2M661a572e renaming h535 → _p2mH535
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h525 (security bits : ℕ) (includeScalar : Bool) (output : FirstHistogram.Palette security) :
    |(body security bits includeScalar output.val : ℝ) - (bodyLaw security includeScalar).weight output| ≤
      3 / (2 : ℝ)^bits := by
  rw [body_cast]
  exact (_p2mH477 (approximateSeedLaw security bits)
    (actualSeedLaw security) (fun seed => ((safeLaw security).map
      (shiftEquiv security (actualBlur security seed + if includeScalar then actualSecond security seed else 0))).weight output)
      1 (fun seed => by
        rw [abs_of_nonneg (FiniteDist.nonneg _ _)]
        exact FiniteDist.atom_le_one _ _)).trans (by simpa only [one_mul] using _p2mH535 security bits)
open _root_.P2M661a572e renaming h525 → _p2mH525
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h529 (colors width output : ℕ) (blur second : ℤ) :
    |(diffuseKernel colors width blur second output : ℝ)| ≤ 1 := by
  have hp := _p2mH150 colors 1
    ((width : ℤ) + blur) second width output
  have hm := _p2mH150 colors 1
    (-2 * (width : ℤ) + 1 + blur) second width output
  simp only [diffuseKernel, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (by linarith only [hp, hm])
open _root_.P2M661a572e renaming h529 → _p2mH529
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h530 (security bits : ℕ) (output : FirstHistogram.Palette security) :
    |(diffuse security bits output.val : ℝ) - diffuseMean security output| ≤ 3 / (2 : ℝ)^bits := by
  rw [diffuse_cast]
  change |fairProfile security (approximateSeedLaw security bits) output -
    fairProfile security (actualSeedLaw security) output| ≤ _
  rw [fairProfile_expectation, fairProfile_expectation]
  exact (_p2mH477 _ _ _ 1
    (fun seed => _p2mH529 _ _ _ _ _)).trans
      (by simpa only [one_mul] using _p2mH535 security bits)
open _root_.P2M661a572e renaming h530 → _p2mH530
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h566
    (free legs colors dimension rate activation bzero bone diffuse primary
      bzero' bone' diffuse' epsilon : ℝ)
    (hfree : 0 ≤ free) (hlegs : 0 ≤ legs) (hcolors : 0 ≤ colors)
    (hdimension : free + 3 * legs + colors = dimension)
    (hrate : 0 ≤ rate ∧ rate ≤ 1) (hepsilon : 0 ≤ epsilon)
    (hbzero : 0 ≤ bzero ∧ bzero ≤ 1) (hdiffuse : 0 ≤ diffuse ∧ diffuse ≤ 1)
    (hprimary : 0 ≤ primary ∧ primary ≤ 1)
    (hzeroError : |bzero - bzero'| ≤ 3 * epsilon)
    (honeError : |bone - bone'| ≤ 3 * epsilon)
    (hdiffuseError : |diffuse - diffuse'| ≤ 3 * epsilon)
    (hrateError : |rate - activation| ≤ epsilon / 2)
    (hbalance : dimension / colors - (free + legs * activation) * bzero -
      (legs + colors) * bone - 2 * legs * (1 - activation) * diffuse = legs * activation * primary) :
    |dimension / colors - (free + legs * rate) * bzero' - (legs + colors) * bone' -
      2 * legs * (1 - rate) * diffuse' - legs * rate * primary| ≤ 8 * dimension * epsilon := by
  have hrateNonneg := hrate.1
  have hgap : |-bzero + 2 * diffuse - primary| ≤ 4 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hzero : |(free + legs * rate) * (bzero - bzero')| ≤ (free + legs) * (3 * epsilon) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ free + legs * rate)]
    exact mul_le_mul (by nlinarith) hzeroError (abs_nonneg _) (by positivity)
  have hone : |(legs + colors) * (bone - bone')| ≤ (legs + colors) * (3 * epsilon) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ legs + colors)]
    exact mul_le_mul_of_nonneg_left honeError (by positivity)
  have hdiff : |(2 * legs * (1 - rate)) * (diffuse - diffuse')| ≤ (2 * legs) * (3 * epsilon) := by
    have hcoef : 0 ≤ 2 * legs * (1 - rate) := mul_nonneg (by positivity) (by linarith only [hrate.2])
    rw [abs_mul, abs_of_nonneg hcoef]
    exact mul_le_mul (by nlinarith [hrate.1]) hdiffuseError (abs_nonneg _) (by positivity)
  have hrateTerm : |legs * (rate - activation) * (-bzero + 2 * diffuse - primary)| ≤
      (legs * (epsilon / 2)) * 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hlegs]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hrateError hlegs) hgap (abs_nonneg _) (by positivity)
  have hdecompose : dimension / colors - (free + legs * rate) * bzero' - (legs + colors) * bone' -
      2 * legs * (1 - rate) * diffuse' - legs * rate * primary =
      (free + legs * rate) * (bzero - bzero') + (legs + colors) * (bone - bone') +
        (2 * legs * (1 - rate)) * (diffuse - diffuse') +
          legs * (rate - activation) * (-bzero + 2 * diffuse - primary) := by
    linear_combination hbalance
  rw [hdecompose]
  calc
    _ ≤ |(free + legs * rate) * (bzero - bzero')| + |(legs + colors) * (bone - bone')| +
        |(2 * legs * (1 - rate)) * (diffuse - diffuse')| +
          |legs * (rate - activation) * (-bzero + 2 * diffuse - primary)| :=
      (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (free + legs) * (3 * epsilon) + (legs + colors) * (3 * epsilon) +
        (2 * legs) * (3 * epsilon) + (legs * (epsilon / 2)) * 4 :=
      add_le_add (add_le_add (add_le_add hzero hone) hdiff) hrateTerm
    _ = (3 * free + 14 * legs + 3 * colors) * epsilon := by ring
    _ ≤ (8 * dimension) * epsilon :=
      mul_le_mul_of_nonneg_right (by nlinarith only [hdimension, hfree, hlegs, hcolors]) hepsilon
    _ = _ := by ring
open _root_.P2M661a572e renaming h566 → _p2mH566
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h532 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ))) :
    |(primaryRaw security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let rate : ℝ := LocalPairProgram.activationApprox security bits
  have hepsilon : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have hb := FirstResponse.base_pos security
  have hrate := LocalPairProgram.activationApprox_bounds security bits
  have hrateError : |rate - DiffuseProfiles.activation security| ≤ epsilon / 2 := by
    exact (_p2mH484 security bits).trans_eq (by dsimp only [epsilon]; ring)
  have hrateLower : 1 / (8 * (Parameters.base security : ℝ)) ≤ rate := by
    have ha := FirstResponse.activation_lower_simple security
    have hfrac : 1 / (8 * (Parameters.base security : ℝ)) = (1 / (4 * (Parameters.base security : ℝ))) / 2 := by ring
    rw [hfrac]
    linarith [(abs_le.mp hrateError).1, hprecision]
  have hlegsPos : (0 : ℝ) < Parameters.legCount security := by
    exact_mod_cast (show 0 < Parameters.legCount security by
      rw [Parameters.legCount_eq]; exact pow_pos (Parameters.base_pos security) _)
  have hlegsOne : (1 : ℝ) ≤ Parameters.legCount security := by
    exact_mod_cast (show 1 ≤ Parameters.legCount security by
      have h : 0 < Parameters.legCount security := Nat.cast_pos.mp hlegsPos; omega)
  have hden : 0 < (Parameters.legCount security : ℝ) * rate :=
    mul_pos hlegsPos (activationApprox_pos security bits)
  have hdenLower : 1 / (8 * (Parameters.base security : ℝ)) ≤
      (Parameters.legCount security : ℝ) * rate :=
    hrateLower.trans (by nlinarith [activationApprox_pos security bits])
  have hdimension : freeMass security + 3 * (Parameters.legCount security : ℝ) +
      Parameters.modulus security = Parameters.dimension security := by
    unfold freeMass Parameters.dimension
    push_cast
    ring
  have hbalance : (Parameters.dimension security : ℝ) / Parameters.modulus security -
      (freeMass security + (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security) * (bodyLaw security false).weight output -
      ((Parameters.legCount security : ℝ) + Parameters.modulus security) * (bodyLaw security true).weight output -
      2 * Parameters.legCount security * (1 - DiffuseProfiles.activation security) * diffuseMean security output =
      (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security * primaryProfile security output := by
    unfold primaryProfile markMass
    field_simp [(DiffuseProfiles.activation_pos security).ne', hlegsPos.ne']
  have hprimary : 0 ≤ primaryProfile security output ∧ primaryProfile security output ≤ 1 :=
    ⟨(primaryLaw security).nonneg output, (primaryLaw security).atom_le_one output⟩
  have hdiffuse : 0 ≤ diffuseMean security output ∧ diffuseMean security output ≤ 1 := by
    refine ⟨diffuseMean_nonneg security output, ?_⟩
    rw [← diffuseMean_mass security]
    exact Finset.single_le_sum (fun color _ => diffuseMean_nonneg security color) (Finset.mem_univ output)
  have hzeroError : |(bodyLaw security false).weight output - (approximateBodyLaw security bits false).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (_p2mH525 security bits false output).trans_eq (by dsimp only [epsilon]; ring)
  have honeError : |(bodyLaw security true).weight output - (approximateBodyLaw security bits true).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← body_cast]
    exact (_p2mH525 security bits true output).trans_eq (by dsimp only [epsilon]; ring)
  have hdiffuseError : |diffuseMean security output - (approximateDiffuseLaw security bits).weight output| ≤
      3 * epsilon := by
    rw [abs_sub_comm, ← diffuse_cast]
    exact (_p2mH530 security bits output).trans_eq (by dsimp only [epsilon]; ring)
  have hresidual := _p2mH566 (freeMass security) (Parameters.legCount security)
    (Parameters.modulus security) (Parameters.dimension security) rate (DiffuseProfiles.activation security)
    ((bodyLaw security false).weight output) ((bodyLaw security true).weight output)
    (diffuseMean security output) (primaryProfile security output)
    ((approximateBodyLaw security bits false).weight output) ((approximateBodyLaw security bits true).weight output)
    ((approximateDiffuseLaw security bits).weight output) epsilon (freeMass_nonneg security) hlegsPos.le
    (Nat.cast_nonneg _) hdimension ⟨hrate.1, by linarith only [hrate.2]⟩ hepsilon
    ⟨(bodyLaw security false).nonneg output, (bodyLaw security false).atom_le_one output⟩ hdiffuse hprimary
    hzeroError honeError hdiffuseError hrateError hbalance
  rw [primaryRaw_cast]
  have hquotient (numerator : ℝ) : |numerator / ((Parameters.legCount security : ℝ) * rate) -
      primaryProfile security output| =
      |numerator - (Parameters.legCount security : ℝ) * rate * primaryProfile security output| /
        ((Parameters.legCount security : ℝ) * rate) := by
    rw [div_sub' hden.ne', abs_div, abs_of_pos hden]
  rw [hquotient]
  calc
    _ ≤ (8 * Parameters.dimension security * epsilon) / ((Parameters.legCount security : ℝ) * rate) :=
      div_le_div_of_nonneg_right hresidual hden.le
    _ ≤ (8 * Parameters.dimension security * epsilon) / (1 / (8 * (Parameters.base security : ℝ))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenLower
    _ = _ := by dsimp only [epsilon]; field_simp; ring
open _root_.P2M661a572e renaming h532 → _p2mH532
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h533 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) (output : FirstHistogram.Palette security) :
    1 / (4 * (Parameters.modulus security : ℝ)) ≤ (primaryRaw security bits output.val : ℝ) := by
  have herr := (abs_le.mp (_p2mH532 security bits output hprecision)).1
  have hp := primaryProfile_atom_lower security output
  have hfrac : (1 : ℝ) / (2 * Parameters.modulus security) = 2 * (1 / (4 * Parameters.modulus security)) := by ring
  rw [hfrac] at hp
  linarith
open _root_.P2M661a572e renaming h533 → _p2mH533
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h531 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) : primaryGood security bits := by
  unfold primaryGood
  rw [PublicParameterProgram.modulus_value]
  intro output
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    _p2mH533 security bits hprecision hbudget output
open _root_.P2M661a572e renaming h531 → _p2mH531
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h534 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(primary security bits output.val : ℝ) - primaryProfile security output| ≤
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) := by
  rw [primary, if_pos (_p2mH531 security bits hprecision hbudget)]
  exact _p2mH532 security bits output hprecision
open _root_.P2M661a572e renaming h534 → _p2mH534
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h528 (security bits : ℕ) : (compensationApprox security bits : ℝ) ≤ 1 := by
  apply (compensationApprox_le_leg_body security bits).trans
  apply (div_le_one (bodySize_pos security)).mpr
  exact_mod_cast (show Parameters.legCount security ≤ Parameters.bodySize security by
    have := population_room security; omega)
open _root_.P2M661a572e renaming h528 → _p2mH528
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h527 (security bits : ℕ) :
    |(compensationApprox security bits : ℝ) - compensation security| ≤ (1 / (2 : ℝ)^bits) / 2 := by
  have hfree := freeMass_pos security
  have hLfree : (Parameters.legCount security : ℝ) ≤ freeMass security := by
    have hp := Nat.cast_le (α := ℝ).mpr (population_room security)
    push_cast at hp
    unfold freeMass
    linarith
  have hratio : (Parameters.legCount security : ℝ) / freeMass security ≤ 1 := (div_le_one hfree).mpr hLfree
  rw [compensationApprox_cast]
  unfold compensation markMass
  have hrewrite : (Parameters.legCount security : ℝ) * LocalPairProgram.activationApprox security bits / freeMass security -
      (Parameters.legCount security : ℝ) * DiffuseProfiles.activation security / freeMass security =
      ((Parameters.legCount security : ℝ) / freeMass security) *
        ((LocalPairProgram.activationApprox security bits : ℝ) - DiffuseProfiles.activation security) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hfree.le)]
  calc
    _ ≤ ((Parameters.legCount security : ℝ) / freeMass security) *
        ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) :=
      mul_le_mul_of_nonneg_left (_p2mH484 security bits)
        (div_nonneg (Nat.cast_nonneg _) hfree.le)
    _ ≤ 1 * ((1 / 2 : ℝ) * (1 / (2 : ℝ)^bits)) := mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = _ := by ring
open _root_.P2M661a572e renaming h527 → _p2mH527
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h523 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(anchorPrimary security bits output.val : ℝ) - (anchorPrimaryLaw security).weight output| ≤
      (Parameters.modulus security : ℝ) *
        (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits := by
  let epsilon : ℝ := 1 / (2 : ℝ)^bits
  let error : ℝ := 64 * (Parameters.base security : ℝ) * Parameters.dimension security * epsilon
  have hpoint (color : FirstHistogram.Palette security) :
      |(approximatePrimaryLaw security bits).weight color * (approximateAnchorLaw security bits color).weight output -
        (primaryLaw security).weight color * (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤
          error + (primaryLaw security).weight color * epsilon := by
    have hp : |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| ≤ error :=
      _p2mH534 security bits color hprecision hbudget
    have hk : |(approximateAnchorLaw security bits color).weight output -
        (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ epsilon := by
      rw [← anchor_cast]
      exact _p2mH524 security bits color output
    calc
      _ = |((approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color) *
          (approximateAnchorLaw security bits color).weight output +
          (primaryLaw security).weight color * ((approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output)| := by congr 1; ring
      _ ≤ |(approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color| *
          (approximateAnchorLaw security bits color).weight output +
          (primaryLaw security).weight color * |(approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output| := by
        simpa only [abs_mul, abs_of_nonneg (FiniteDist.nonneg _ _)] using abs_add_le
          (((approximatePrimaryLaw security bits).weight color - (primaryLaw security).weight color) *
            (approximateAnchorLaw security bits color).weight output)
          ((primaryLaw security).weight color * ((approximateAnchorLaw security bits color).weight output -
            (InwardAnchor.smoothedAnchorLaw security color).weight output))
      _ ≤ error * 1 + (primaryLaw security).weight color * epsilon :=
        add_le_add (mul_le_mul hp ((approximateAnchorLaw security bits color).atom_le_one output)
          (FiniteDist.nonneg _ _) (by dsimp only [error, epsilon]; positivity))
          (mul_le_mul_of_nonneg_left hk ((primaryLaw security).nonneg color))
      _ = _ := by ring
  rw [anchorPrimary_cast]
  change |(∑ color, (approximatePrimaryLaw security bits).weight color *
    (approximateAnchorLaw security bits color).weight output) -
    ∑ color, (primaryLaw security).weight color * (InwardAnchor.smoothedAnchorLaw security color).weight output| ≤ _
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ color, (error + (primaryLaw security).weight color * epsilon) :=
      Finset.sum_le_sum (fun color _ => hpoint color)
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.sum_mul, FiniteDist.sum_one, one_mul]
      rfl
open _root_.P2M661a572e renaming h523 → _p2mH523
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h526 (security bits : ℕ) (output : FirstHistogram.Palette security)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    |(center security bits output.val : ℝ) - centerProfile security output| ≤
      (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
        (1 / (2 : ℝ)^bits) := by
  have hcomp := _p2mH527 security bits
  have hanchor := _p2mH523 security bits output hprecision hbudget
  rw [anchorPrimary_cast] at hanchor
  have hgap : |(safeLaw security).weight output - (anchorPrimaryLaw security).weight output| ≤ 2 := by
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg ((safeLaw security).nonneg output),
        abs_of_nonneg ((anchorPrimaryLaw security).nonneg output)]
      linarith [(safeLaw security).atom_le_one output, (anchorPrimaryLaw security).atom_le_one output])
  rw [center_cast]
  have hdecompose : approximateCenterProfile security bits output - centerProfile security output =
      ((compensationApprox security bits : ℝ) - compensation security) *
        ((safeLaw security).weight output - (anchorPrimaryLaw security).weight output) -
      (compensationApprox security bits : ℝ) *
        ((approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output) := by
    unfold approximateCenterProfile centerProfile
    ring
  rw [hdecompose]
  calc
    _ ≤ |(compensationApprox security bits : ℝ) - compensation security| *
        |(safeLaw security).weight output - (anchorPrimaryLaw security).weight output| +
      (compensationApprox security bits : ℝ) *
        |(approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output| := by
      simpa only [abs_mul, abs_of_nonneg (compensationApprox_nonneg security bits)] using abs_sub
        (((compensationApprox security bits : ℝ) - compensation security) *
          ((safeLaw security).weight output - (anchorPrimaryLaw security).weight output))
        ((compensationApprox security bits : ℝ) *
          ((approximateAnchorPrimaryLaw security bits).weight output - (anchorPrimaryLaw security).weight output))
    _ ≤ ((1 / (2 : ℝ)^bits) / 2) * 2 + 1 *
        ((Parameters.modulus security : ℝ) *
          (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) +
          1 / (2 : ℝ)^bits) :=
      add_le_add (mul_le_mul hcomp hgap (abs_nonneg _) (by positivity))
        (mul_le_mul (_p2mH528 security bits) hanchor (abs_nonneg _) (by positivity))
    _ = _ := by ring
open _root_.P2M661a572e renaming h526 → _p2mH526
end
open _root_.P2M661a572e renaming h523 → _p2mH523
open _root_.P2M661a572e renaming h524 → _p2mH524
open _root_.P2M661a572e renaming h525 → _p2mH525
open _root_.P2M661a572e renaming h526 → _p2mH526
open _root_.P2M661a572e renaming h527 → _p2mH527
open _root_.P2M661a572e renaming h528 → _p2mH528
open _root_.P2M661a572e renaming h529 → _p2mH529
open _root_.P2M661a572e renaming h530 → _p2mH530
open _root_.P2M661a572e renaming h531 → _p2mH531
open _root_.P2M661a572e renaming h532 → _p2mH532
open _root_.P2M661a572e renaming h533 → _p2mH533
open _root_.P2M661a572e renaming h534 → _p2mH534
open _root_.P2M661a572e renaming h535 → _p2mH535
open _root_.P2M661a572e renaming h566 → _p2mH566
end CurrentAFT.RationalProposalProgram
open _root_.P2M661a572e renaming h523 → _p2mH523
open _root_.P2M661a572e renaming h524 → _p2mH524
open _root_.P2M661a572e renaming h525 → _p2mH525
open _root_.P2M661a572e renaming h526 → _p2mH526
open _root_.P2M661a572e renaming h527 → _p2mH527
open _root_.P2M661a572e renaming h528 → _p2mH528
open _root_.P2M661a572e renaming h529 → _p2mH529
open _root_.P2M661a572e renaming h530 → _p2mH530
open _root_.P2M661a572e renaming h531 → _p2mH531
open _root_.P2M661a572e renaming h532 → _p2mH532
open _root_.P2M661a572e renaming h533 → _p2mH533
open _root_.P2M661a572e renaming h534 → _p2mH534
open _root_.P2M661a572e renaming h535 → _p2mH535
open _root_.P2M661a572e renaming h566 → _p2mH566
end
open _root_.P2M661a572e renaming h525 → _p2mH525
open _root_.P2M661a572e renaming h528 → _p2mH528
open _root_.P2M661a572e renaming h530 → _p2mH530
open _root_.P2M661a572e renaming h532 → _p2mH532
open _root_.P2M661a572e renaming h534 → _p2mH534
open _root_.P2M661a572e renaming h535 → _p2mH535
open _root_.P2M661a572e renaming h527 → _p2mH527
open _root_.P2M661a572e renaming h524 → _p2mH524
open _root_.P2M661a572e renaming h529 → _p2mH529
open _root_.P2M661a572e renaming h533 → _p2mH533
open _root_.P2M661a572e renaming h531 → _p2mH531
open _root_.P2M661a572e renaming h526 → _p2mH526
open _root_.P2M661a572e renaming h523 → _p2mH523
section
namespace CurrentAFT.BinaryReferenceTables
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter multiplyCounter PublicParameterProgram.modulus BinaryActivationProgram.cutoff
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h199 (security bits : ℕ) (primary output : Fin (PublicParameterProgram.modulus security).count) :
    (((current security bits).anchor.get primary).get output).decode =
      RationalProposalProgram.anchor security bits primary.val output.val :=
  BinaryAnchorTable.current_value security bits primary output
open _root_.P2M661a572e renaming h199 → _p2mH199
noncomputable section
end
end CurrentAFT.BinaryReferenceTables
open _root_.P2M661a572e renaming h199 → _p2mH199
end
open _root_.P2M661a572e renaming h199 → _p2mH199
section
namespace CurrentAFT.CurrentProbabilityArrayDraw
open AFT AFT.RationalNumerics AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h442 (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ)
    (word : Fin (bits + (count + 1) + 1) → Fin 2) :
    (draw count table bits word).value = RationalFiniteQuantization.draw (fun index => (table.data.get index).decode)
      table.nonneg table.mass (bits + (count + 1) + 1) word := by
  apply Fin.ext
  simp only [draw, binaryRationalDraw_cast]
  exact binaryRationalDraw_value table.data table.nonneg table.mass _ _
open _root_.P2M661a572e renaming h442 → _p2mH442
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h441 (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ) :
    (FiniteDist.uniform (Fin (bits + (count + 1) + 1) → Fin 2)).map (fun word => (draw count table bits word).value) =
      RationalFiniteQuantization.roundedLaw (fun index => (table.data.get index).decode) table.nonneg table.mass
        (2 ^ (bits + (count + 1) + 1)) (by positivity) := by
  simp only [_p2mH442]
  rw [← _p2mH105]
  exact _p2mH117 _ _ _ _
open _root_.P2M661a572e renaming h441 → _p2mH441
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h440 (count : ℕ) (table : ProbabilityArray (count + 1)) (bits : ℕ) :
    (∑ index, |((FiniteDist.uniform (Fin (bits + (count + 1) + 1) → Fin 2)).map
      (fun word => (draw count table bits word).value)).weight index - (law table).weight index|) ≤ 1 / (2 : ℝ) ^ bits := by
  rw [_p2mH441]
  have h := _p2mH121 (fun index => (table.data.get index).decode)
    table.nonneg table.mass (2 ^ (bits + (count + 1) + 1)) (by positivity)
  apply h.trans
  have hc : ((count + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (count + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := count + 1)).le
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc
    2 * (count + 1) / (2 : ℝ) ^ (bits + (count + 1) + 1) ≤ 2 * (2 : ℝ) ^ (count + 1) / (2 : ℝ) ^ (bits + (count + 1) + 1) := by
      gcongr
      simpa only [Nat.cast_add, Nat.cast_one] using hc
    _ = 1 / (2 : ℝ) ^ bits := by rw [pow_add, pow_add]; field_simp; ring
open _root_.P2M661a572e renaming h440 → _p2mH440
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h443 (count : ℕ) (hpositive : 0 < count) (table : ProbabilityArray count) (bits : ℕ) :
    (∑ index, |((FiniteDist.uniform (Fin (bits + count + 1) → Fin 2)).map
      (fun word => (positiveDraw count hpositive table bits word).value)).weight index - (law table).weight index|) ≤
      1 / (2 : ℝ) ^ bits := by
  cases count with
  | zero => omega
  | succ count => exact _p2mH440 count table bits
open _root_.P2M661a572e renaming h443 → _p2mH443
end
open _root_.P2M661a572e renaming h440 → _p2mH440
open _root_.P2M661a572e renaming h441 → _p2mH441
open _root_.P2M661a572e renaming h443 → _p2mH443
end CurrentAFT.CurrentProbabilityArrayDraw
open _root_.P2M661a572e renaming h440 → _p2mH440
open _root_.P2M661a572e renaming h441 → _p2mH441
open _root_.P2M661a572e renaming h442 → _p2mH442
open _root_.P2M661a572e renaming h443 → _p2mH443
end
open _root_.P2M661a572e renaming h442 → _p2mH442
open _root_.P2M661a572e renaming h443 → _p2mH443
open _root_.P2M661a572e renaming h440 → _p2mH440
open _root_.P2M661a572e renaming h441 → _p2mH441
section
namespace CurrentAFT.CurrentSafePaletteIndex
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h474 (security : ℕ) (color : ActualControls.SafePalette security) :
    (uniformLaw security).weight color = ((count security : ℕ) : ℝ)⁻¹ := by
  simp only [uniformLaw, FiniteDist.map_equiv_weight, FiniteDist.uniform_weight, Fintype.card_fin]
open _root_.P2M661a572e renaming h474 → _p2mH474
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h473 (security : ℕ) :
    (uniformLaw security).map Subtype.val = ProposalPrimary.safeLaw security := by
  letI : DecidableEq (Fin (Parameters.modulus security)) := Classical.decEq _
  ext color
  rw [FiniteDist.map_weight, ProposalPrimary.safeLaw_weight]
  by_cases hsafe : InwardAnchor.SafeColor security color
  · rw [if_pos hsafe]
    have heq (source : ActualControls.SafePalette security) : source.val = color ↔ source = ⟨color, hsafe⟩ :=
      ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
    change (∑ source : ActualControls.SafePalette security,
      if source.val = color then (uniformLaw security).weight source else 0) = _
    simp_rw [heq]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _), _p2mH474]
    unfold ProposalPrimary.safeHeight
    have hc := ProposalPrimary.safe_clearance security
    have he : ((count security : ℕ) : ℝ) = (Parameters.modulus security : ℝ) -
        2 * Parameters.safeMargin security := by
      rw [count, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
    rw [he, one_div]
  · rw [if_neg hsafe]
    apply Finset.sum_eq_zero
    intro source _
    have hv : source.val ≠ color := by
      intro he
      exact hsafe (he ▸ source.property)
    simp only [if_neg hv]
open _root_.P2M661a572e renaming h473 → _p2mH473
end
open _root_.P2M661a572e renaming h473 → _p2mH473
open _root_.P2M661a572e renaming h474 → _p2mH474
end CurrentAFT.CurrentSafePaletteIndex
open _root_.P2M661a572e renaming h473 → _p2mH473
open _root_.P2M661a572e renaming h474 → _p2mH474
end
open _root_.P2M661a572e renaming h473 → _p2mH473
open _root_.P2M661a572e renaming h474 → _p2mH474
section
namespace CurrentAFT.CurrentReferenceDraw
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw
open scoped BigOperators
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryReferenceTables.current
attribute [local instance] _root_.CurrentAFT.CurrentReferenceDraw.safeFintype
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h462 (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (word : Fin (drawBits + (counts security).safe + 1) → Fin 2) :
    (bodyDraw security tableBits drawBits cache word).value =
      bodyEquiv security (positiveDraw _ (safe_positive security) cache.body drawBits word).value := by
  apply Subtype.ext
  apply Fin.ext
  change (addCounter (counts security).margin _).count = _
  rw [addCounter_value, bodyEquiv_value]
open _root_.P2M661a572e renaming h462 → _p2mH462
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h465 (security bits : ℕ) (cache : Cache security bits) :
    (law cache.primary).map (primaryEquiv security) = RationalProposalProgram.approximatePrimaryLaw security bits := by
  ext color
  rw [FiniteDist.map_equiv_weight]
  change ((cache.primary.data.get ((primaryEquiv security).symm color)).decode : ℝ) = _
  rw [cache.primary_value]
  rfl
open _root_.P2M661a572e renaming h465 → _p2mH465
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h463 (security bits : ℕ) (cache : Cache security bits) :
    (law cache.body).map (bodyEquiv security) = RationalProposalProgram.approximateBodyReference security bits := by
  ext color
  rw [FiniteDist.map_equiv_weight]
  change ((cache.body.data.get ((bodyEquiv security).symm color)).decode : ℝ) = _
  rw [cache.body_value, Equiv.apply_symm_apply]
  rfl
open _root_.P2M661a572e renaming h463 → _p2mH463
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h464 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ color, |(primaryDrawLaw security tableBits drawBits cache).weight color -
      (RationalProposalProgram.approximatePrimaryLaw security tableBits).weight color|) ≤ 1 / (2 : ℝ) ^ drawBits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (drawBits + (PublicParameterProgram.modulus security).count + 1) → Fin 2)).map
      (fun word => (positiveDraw _ (colors_positive security) cache.primary drawBits word).value))
    (law cache.primary) (primaryEquiv security)
  rw [_p2mH465] at h
  simp only [FiniteDist.map_map] at h
  exact h.trans (_p2mH443 _ (colors_positive security) cache.primary drawBits)
open _root_.P2M661a572e renaming h464 → _p2mH464
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h461 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ color, |(bodyDrawLaw security tableBits drawBits cache).weight color -
      (RationalProposalProgram.approximateBodyReference security tableBits).weight color|) ≤ 1 / (2 : ℝ) ^ drawBits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (drawBits + (counts security).safe + 1) → Fin 2)).map
      (fun word => (positiveDraw _ (safe_positive security) cache.body drawBits word).value))
    (law cache.body) (bodyEquiv security)
  rw [_p2mH463] at h
  simp only [FiniteDist.map_map] at h
  have he : bodyDrawLaw security tableBits drawBits cache =
      ((FiniteDist.uniform (Fin (drawBits + (counts security).safe + 1) → Fin 2)).map
        (fun word => bodyEquiv security (positiveDraw _ (safe_positive security) cache.body drawBits word).value)) := by
    simp only [bodyDrawLaw, _p2mH462]
  rw [he]
  exact h.trans (_p2mH443 _ (safe_positive security) cache.body drawBits)
open _root_.P2M661a572e renaming h461 → _p2mH461
end
open _root_.P2M661a572e renaming h461 → _p2mH461
open _root_.P2M661a572e renaming h463 → _p2mH463
open _root_.P2M661a572e renaming h464 → _p2mH464
open _root_.P2M661a572e renaming h465 → _p2mH465
end CurrentAFT.CurrentReferenceDraw
open _root_.P2M661a572e renaming h461 → _p2mH461
open _root_.P2M661a572e renaming h462 → _p2mH462
open _root_.P2M661a572e renaming h463 → _p2mH463
open _root_.P2M661a572e renaming h464 → _p2mH464
open _root_.P2M661a572e renaming h465 → _p2mH465
end
open _root_.P2M661a572e renaming h464 → _p2mH464
open _root_.P2M661a572e renaming h463 → _p2mH463
open _root_.P2M661a572e renaming h465 → _p2mH465
open _root_.P2M661a572e renaming h461 → _p2mH461
open _root_.P2M661a572e renaming h462 → _p2mH462
section
namespace CurrentAFT.CurrentActivationDraw
open AFT AFT.BinaryArithmetic AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentProbabilityArrayDraw CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h231 (security tableBits : ℕ) (cache : Cache security tableBits) :
    (law (table security tableBits cache).value).map finTwoEquiv = approximateLaw security tableBits := by
  ext flag
  rw [FiniteDist.map_equiv_weight]
  cases flag <;>
    norm_num [law, table, Vector.get_ofFn, finTwoEquiv, RationalBits.add_value, negate_value, one_value,
      cache.activation_value, approximateLaw, sub_eq_add_neg]
open _root_.P2M661a572e renaming h231 → _p2mH231
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h230 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ flag, |(drawLaw security tableBits drawBits cache).weight flag -
      (approximateLaw security tableBits).weight flag|) ≤ 1 / (2 : ℝ)^drawBits := by
  have h := FiniteDist.l1_map_le
    ((FiniteDist.uniform (Fin (drawBits + 2 + 1) → Fin 2)).map
      (fun word => (positiveDraw 2 (by decide) (table security tableBits cache).value drawBits word).value))
    (law (table security tableBits cache).value) finTwoEquiv
  rw [_p2mH231] at h
  simp only [FiniteDist.map_map] at h
  exact h.trans (_p2mH443 2 (by decide) (table security tableBits cache).value drawBits)
open _root_.P2M661a572e renaming h230 → _p2mH230
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h228 (security tableBits : ℕ) :
    (∑ flag, |(approximateLaw security tableBits).weight flag -
      (ActualPublicLegCharge.activationLaw security).weight flag|) ≤ 1 / (2 : ℝ)^tableBits := by
  have h := _p2mH484 security tableBits
  simp only [Fintype.sum_bool, approximateLaw, ActualPublicLegCharge.activationLaw,
    Bool.false_eq_true, if_false, if_true]
  have he : |(1 - (LocalPairProgram.activationApprox security tableBits : ℝ)) -
      (1 - DiffuseProfiles.activation security)| =
      |(LocalPairProgram.activationApprox security tableBits : ℝ) - DiffuseProfiles.activation security| := by
    rw [show (1 - (LocalPairProgram.activationApprox security tableBits : ℝ)) -
      (1 - DiffuseProfiles.activation security) = -((LocalPairProgram.activationApprox security tableBits : ℝ) -
      DiffuseProfiles.activation security) by ring, abs_neg]
  rw [he]
  linarith
open _root_.P2M661a572e renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h229 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ flag, |(drawLaw security tableBits drawBits cache).weight flag -
      (ActualPublicLegCharge.activationLaw security).weight flag|) ≤
      1 / (2 : ℝ)^drawBits + 1 / (2 : ℝ)^tableBits := by
  apply le_trans _ (add_le_add (_p2mH230 security tableBits drawBits cache) (_p2mH228 security tableBits))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun flag _ => abs_sub_le _ ((approximateLaw security tableBits).weight flag) _)
open _root_.P2M661a572e renaming h229 → _p2mH229
end
open _root_.P2M661a572e renaming h228 → _p2mH228
open _root_.P2M661a572e renaming h229 → _p2mH229
open _root_.P2M661a572e renaming h230 → _p2mH230
open _root_.P2M661a572e renaming h231 → _p2mH231
end CurrentAFT.CurrentActivationDraw
open _root_.P2M661a572e renaming h228 → _p2mH228
open _root_.P2M661a572e renaming h229 → _p2mH229
open _root_.P2M661a572e renaming h230 → _p2mH230
open _root_.P2M661a572e renaming h231 → _p2mH231
end
open _root_.P2M661a572e renaming h230 → _p2mH230
open _root_.P2M661a572e renaming h229 → _p2mH229
open _root_.P2M661a572e renaming h228 → _p2mH228
open _root_.P2M661a572e renaming h231 → _p2mH231
section
namespace CurrentAFT.CurrentUniformDraw
open AFT AFT.BinaryArithmetic
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h475 (count : ℕ) (hpositive : 0 < count) (bits : ℕ) :
    (∑ index, |(law count hpositive bits).weight index -
      (letI : Nonempty (Fin count) := ⟨⟨0, hpositive⟩⟩; FiniteDist.uniform (Fin count)).weight index|) ≤ 1 / (2 : ℝ)^bits := by
  letI : Nonempty (Fin count) := ⟨⟨0, hpositive⟩⟩
  have he : (∑ color : Fin count, |(((count : ℚ)⁻¹ : ℚ) : ℝ) -
      (FiniteDist.uniform (Fin count)).weight color|) ≤ (0 : ℝ) := by
    simp only [Rat.cast_inv, Rat.cast_natCast, FiniteDist.uniform_weight, Fintype.card_fin,
      sub_self, abs_zero, Finset.sum_const_zero, le_refl]
  have h := _p2mH141 count hpositive (fun _ => (count : ℚ)⁻¹) bits
    (FiniteDist.uniform (Fin count)) 0 he (by norm_num)
  simpa only [law, _p2mH33, mul_zero, add_zero] using h
open _root_.P2M661a572e renaming h475 → _p2mH475
end
open _root_.P2M661a572e renaming h475 → _p2mH475
end CurrentAFT.CurrentUniformDraw
open _root_.P2M661a572e renaming h475 → _p2mH475
end
open _root_.P2M661a572e renaming h475 → _p2mH475
section
namespace CurrentAFT.CurrentAnchorIndexDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentAnchorIndexDraw.anchorNonempty
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h245 (security bits : ℕ) :
    (∑ index, |(law security bits).weight index -
      (FiniteDist.uniform (InwardAnchor.Index security)).weight index|) ≤ 1 / (2 : ℝ)^bits := by
  letI : Nonempty (Fin (width security).count) := ⟨⟨0, width_positive security⟩⟩
  have h := FiniteDist.l1_map_le (CurrentUniformDraw.law _ (width_positive security) bits)
    (FiniteDist.uniform (Fin (width security).count)) (indexEquiv security)
  rw [FiniteDist.uniform_map_equiv] at h
  simp only [CurrentUniformDraw.law, FiniteDist.map_map] at h
  exact h.trans (_p2mH475 _ (width_positive security) bits)
open _root_.P2M661a572e renaming h245 → _p2mH245
end
open _root_.P2M661a572e renaming h245 → _p2mH245
end CurrentAFT.CurrentAnchorIndexDraw
open _root_.P2M661a572e renaming h245 → _p2mH245
end
open _root_.P2M661a572e renaming h245 → _p2mH245
section
namespace CurrentAFT.CurrentWindowDraw
open AFT GaussianSource RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open AFT.RationalRejectionProgram AFT.FiniteConvolutionProgram
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h565 {count : ℕ} (first second : Fin (count + 1) → ℚ) (heq : first = second)
    (hn : ∀ index, 0 ≤ first index) (hs : ∑ index, first index = 1)
    (hn' : ∀ index, 0 ≤ second index) (hs' : ∑ index, second index = 1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    RationalFiniteQuantization.draw first hn hs bits word = RationalFiniteQuantization.draw second hn' hs' bits word := by
  subst second
  rfl
open _root_.P2M661a572e renaming h565 → _p2mH565
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h476 (security cutoff bits : ℕ) (word : Fin (windowTicketBits cutoff bits) → Fin 2) :
    (draw security cutoff bits word).value = WindowGaussianSampler.draw security cutoff bits word := by
  let weights := CurrentGaussianBits.table security cutoff (bits + 1)
  let selected := binaryRationalDraw weights.data (windowTicketBits cutoff bits) word
  have hw : (fun index => (weights.data.get index).decode) =
      windowGaussianWeights (WindowGaussianSampler.squaredWidth security) cutoff (bits + 1) :=
    funext (CurrentGaussianBits.table_value security cutoff (bits + 1))
  have hs := binaryRationalDraw_value weights.data (table_nonneg security cutoff (bits + 1))
    (table_sum security cutoff (bits + 1)) (windowTicketBits cutoff bits) word
  rw [_p2mH565 _ _ hw (table_nonneg security cutoff (bits + 1)) (table_sum security cutoff (bits + 1))
    (windowGaussianWeights_nonneg _ _ _) (windowGaussianWeights_sum _ _ _) _ _] at hs
  have hi : selected.value = ((windowIndexEquiv cutoff).symm (WindowGaussianSampler.draw security cutoff bits word)).val := by
    simpa only [WindowGaussianSampler.draw, windowGaussianDraw, Equiv.symm_apply_apply] using hs
  apply Subtype.ext
  change (integerDifference selected.value cutoff).value = (WindowGaussianSampler.draw security cutoff bits word).val
  rw [integerDifference_value, hi]
  exact congrArg Subtype.val ((windowIndexEquiv cutoff).apply_symm_apply (WindowGaussianSampler.draw security cutoff bits word))
open _root_.P2M661a572e renaming h476 → _p2mH476
noncomputable section
open scoped Classical
end
end CurrentAFT.CurrentWindowDraw
open _root_.P2M661a572e renaming h476 → _p2mH476
open _root_.P2M661a572e renaming h565 → _p2mH565
end
open _root_.P2M661a572e renaming h476 → _p2mH476
section
namespace CurrentAFT.CurrentEdgeDrawProgram
open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h309 (security first second bits : ℕ) (h : first = second)
    (word : Fin (windowTicketBits second bits) → Fin 2) :
    castWindow h (CurrentWindowDraw.draw security first bits
      (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) h.symm) word)) =
      CurrentWindowDraw.draw security second bits word := by
  subst second
  rfl
open _root_.P2M661a572e renaming h309 → _p2mH309
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h311 (security bits : ℕ) (word : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) → Fin 2) :
    (draw security bits word).value = WindowGaussianSampler.draw security (DiffuseProfiles.edgeCutoff security) bits word := by
  change (castWindow (cutoff_value security) (CurrentWindowDraw.draw security (cutoffProgram security).quotient bits
    (cast (congrArg (fun cutoff => Fin (windowTicketBits cutoff bits) → Fin 2) (cutoff_value security).symm) word))).value = _
  rw [_p2mH309, _p2mH476]
open _root_.P2M661a572e renaming h311 → _p2mH311
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h310 (security bits : ℕ) :
    (∑ point, |((FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) bits) => FiniteDist.uniform (Fin 2))).map
      (fun word => (draw security bits word).value)).weight point - (DiffuseProfiles.edgeLaw security).weight point|) ≤
      1 / (2 : ℝ) ^ bits := by
  simpa only [_p2mH311] using _p2mH539 security bits
open _root_.P2M661a572e renaming h310 → _p2mH310
end
open _root_.P2M661a572e renaming h310 → _p2mH310
end CurrentAFT.CurrentEdgeDrawProgram
open _root_.P2M661a572e renaming h309 → _p2mH309
open _root_.P2M661a572e renaming h310 → _p2mH310
open _root_.P2M661a572e renaming h311 → _p2mH311
end
open _root_.P2M661a572e renaming h309 → _p2mH309
open _root_.P2M661a572e renaming h311 → _p2mH311
open _root_.P2M661a572e renaming h310 → _p2mH310
section
namespace CurrentAFT.CurrentPublicSeedDraw
open AFT AFT.GaussianSource AFT.RationalNumerics AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 800000
attribute [local irreducible] Parameters.anchorWidth Parameters.base
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentPublicSeedDraw.anchorNonempty
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h455 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    law security tableBits drawBits cache =
      (productLaw security tableBits drawBits cache).map (ActualPublicLegCharge.seedEquiv security).symm := by
  let value : Tape security drawBits → ActualPublicLegCharge.SeedProduct security := fun word =>
    ((CurrentActivationDraw.draw security tableBits drawBits cache word.1).value, (word.2.1,
      ((CurrentAnchorIndexDraw.draw security drawBits word.2.2.1).value,
        ((CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.1).value,
          (CurrentEdgeDrawProgram.draw security drawBits word.2.2.2.2).value))))
  have he : (tapeLaw security drawBits).map value = productLaw security tableBits drawBits cache := by
    let edgeValue := fun word : EdgeTape security drawBits => (CurrentEdgeDrawProgram.draw security drawBits word).value
    let anchorValue := fun word : CurrentAnchorIndexDraw.Tape security drawBits => (CurrentAnchorIndexDraw.draw security drawBits word).value
    let activationValue := fun word : Fin (drawBits + 2 + 1) → Fin 2 => (CurrentActivationDraw.draw security tableBits drawBits cache word).value
    have hfirst := _p2mH87
      (FiniteDist.uniform (EdgeTape security drawBits)) (FiniteDist.uniform (EdgeTape security drawBits)) edgeValue edgeValue
    have hsecond := _p2mH87
      (FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security drawBits))
      ((FiniteDist.uniform (EdgeTape security drawBits)).prod (FiniteDist.uniform (EdgeTape security drawBits)))
      anchorValue (fun pair => (edgeValue pair.1, edgeValue pair.2))
    rw [hfirst] at hsecond
    have hthird := _p2mH87 (FiniteDist.uniform Bool)
      ((FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security drawBits)).prod
        ((FiniteDist.uniform (EdgeTape security drawBits)).prod (FiniteDist.uniform (EdgeTape security drawBits))))
      id (fun pair => (anchorValue pair.1, (edgeValue pair.2.1, edgeValue pair.2.2)))
    have hid : (FiniteDist.uniform Bool).map id = FiniteDist.uniform Bool := by
      ext flag
      simp
    rw [hsecond, hid] at hthird
    simp only [id_eq] at hthird
    have hfourth := _p2mH87
      (FiniteDist.uniform (Fin (drawBits + 2 + 1) → Fin 2))
      ((FiniteDist.uniform Bool).prod ((FiniteDist.uniform (CurrentAnchorIndexDraw.Tape security drawBits)).prod
        ((FiniteDist.uniform (EdgeTape security drawBits)).prod (FiniteDist.uniform (EdgeTape security drawBits)))))
      activationValue (fun pair => (pair.1, (anchorValue pair.2.1, (edgeValue pair.2.2.1, edgeValue pair.2.2.2))))
    rw [hthird] at hfourth
    exact hfourth
  have h := congrArg (fun distribution => distribution.map (ActualPublicLegCharge.seedEquiv security).symm) he
  simpa only [FiniteDist.map_map, law, value, draw, ActualPublicLegCharge.seedEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk] using h
open _root_.P2M661a572e renaming h455 → _p2mH455
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h454 (security bits : ℕ) :
    (∑ point, |(edgeLaw security bits).weight point - (DiffuseProfiles.edgeLaw security).weight point|) ≤ 1 / (2 : ℝ)^bits := by
  have h := _p2mH310 security bits
  rw [_p2mH105] at h
  exact h
open _root_.P2M661a572e renaming h454 → _p2mH454
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h456 (security tableBits drawBits : ℕ) (cache : Cache security tableBits) :
    (∑ seed, |(law security tableBits drawBits cache).weight seed -
      (ActualPublicLegCharge.seedLaw security).weight seed|) ≤
        4 * (1 / (2 : ℝ)^drawBits) + 1 / (2 : ℝ)^tableBits := by
  have ha := _p2mH229 security tableBits drawBits cache
  have hi := _p2mH245 security drawBits
  have he := _p2mH454 security drawBits
  have hb := FiniteDist.l1_prod_le (edgeLaw security drawBits) (DiffuseProfiles.edgeLaw security)
    (edgeLaw security drawBits) (DiffuseProfiles.edgeLaw security)
  have hc := FiniteDist.l1_prod_le (CurrentAnchorIndexDraw.law security drawBits)
    (FiniteDist.uniform (InwardAnchor.Index security)) ((edgeLaw security drawBits).prod (edgeLaw security drawBits))
    (LocalReferenceEnergy.publicBlurLaw security)
  have hd := FiniteDist.l1_prod_le (FiniteDist.uniform Bool) (FiniteDist.uniform Bool)
    ((CurrentAnchorIndexDraw.law security drawBits).prod ((edgeLaw security drawBits).prod (edgeLaw security drawBits)))
    ((FiniteDist.uniform (InwardAnchor.Index security)).prod (LocalReferenceEnergy.publicBlurLaw security))
  have hf := FiniteDist.l1_prod_le (CurrentActivationDraw.drawLaw security tableBits drawBits cache)
    (ActualPublicLegCharge.activationLaw security)
    ((FiniteDist.uniform Bool).prod ((CurrentAnchorIndexDraw.law security drawBits).prod
      ((edgeLaw security drawBits).prod (edgeLaw security drawBits))))
    ((FiniteDist.uniform Bool).prod ((FiniteDist.uniform (InwardAnchor.Index security)).prod
      (LocalReferenceEnergy.publicBlurLaw security)))
  have hm := FiniteDist.l1_map_le (productLaw security tableBits drawBits cache)
    ((ActualPublicLegCharge.activationLaw security).prod ((FiniteDist.uniform Bool).prod
      ((FiniteDist.uniform (InwardAnchor.Index security)).prod (LocalReferenceEnergy.publicBlurLaw security))))
    (ActualPublicLegCharge.seedEquiv security).symm
  rw [← _p2mH455] at hm
  change (∑ seed, |(law security tableBits drawBits cache).weight seed -
    (ActualPublicLegCharge.seedLaw security).weight seed|) ≤ _ at hm
  simp only [sub_self, abs_zero, Finset.sum_const_zero] at hd
  change (∑ pair, |((edgeLaw security drawBits).prod (edgeLaw security drawBits)).weight pair -
    (LocalReferenceEnergy.publicBlurLaw security).weight pair|) ≤ _ at hb
  change (∑ seed, |(productLaw security tableBits drawBits cache).weight seed - _|) ≤ _ at hf
  linarith
open _root_.P2M661a572e renaming h456 → _p2mH456
end
open _root_.P2M661a572e renaming h454 → _p2mH454
open _root_.P2M661a572e renaming h455 → _p2mH455
open _root_.P2M661a572e renaming h456 → _p2mH456
end CurrentAFT.CurrentPublicSeedDraw
open _root_.P2M661a572e renaming h454 → _p2mH454
open _root_.P2M661a572e renaming h455 → _p2mH455
open _root_.P2M661a572e renaming h456 → _p2mH456
end
open _root_.P2M661a572e renaming h455 → _p2mH455
open _root_.P2M661a572e renaming h456 → _p2mH456
open _root_.P2M661a572e renaming h454 → _p2mH454
section
namespace CurrentAFT.CurrentSafeDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentReferenceDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h470 (security bits : ℕ) (word : Tape security bits) :
    (draw security bits word).value = (bodyEquiv security
      (binaryUniformDraw (counts security).safe (safe_positive security) bits word).value).val := by
  apply Fin.ext
  change (addCounter (counts security).margin _).count = _
  rw [addCounter_value, bodyEquiv_value]
open _root_.P2M661a572e renaming h470 → _p2mH470
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h472 (security : ℕ) :
    (letI : Nonempty (Fin (counts security).safe) := ⟨⟨0, safe_positive security⟩⟩;
      FiniteDist.uniform (Fin (counts security).safe)).map
        (fun index => (bodyEquiv security index).val) = ProposalPrimary.safeLaw security := by
  letI : Nonempty (Fin (counts security).safe) := ⟨⟨0, safe_positive security⟩⟩
  letI : Nonempty (ActualControls.SafePalette security) := ⟨bodyEquiv security ⟨0, safe_positive security⟩⟩
  have he : (FiniteDist.uniform (Fin (counts security).safe)).map (bodyEquiv security) =
      CurrentSafePaletteIndex.uniformLaw security := by
    rw [FiniteDist.uniform_map_equiv]
    exact (FiniteDist.uniform_map_equiv (CurrentSafePaletteIndex.equiv security)).symm
  simpa only [← he, FiniteDist.map_map, Function.comp_def] using _p2mH473 security
open _root_.P2M661a572e renaming h472 → _p2mH472
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h471 (security bits : ℕ) :
    (∑ color, |(law security bits).weight color - (ProposalPrimary.safeLaw security).weight color|) ≤
      1 / (2 : ℝ)^bits := by
  letI : Nonempty (Fin (counts security).safe) := ⟨⟨0, safe_positive security⟩⟩
  have h := FiniteDist.l1_map_le (CurrentUniformDraw.law (counts security).safe (safe_positive security) bits)
    (FiniteDist.uniform (Fin (counts security).safe)) (fun index => (bodyEquiv security index).val)
  rw [_p2mH472] at h
  simp only [CurrentUniformDraw.law, FiniteDist.map_map] at h
  have he : law security bits =
      (FiniteDist.uniform (Tape security bits)).map (fun word => (bodyEquiv security
        (binaryUniformDraw (counts security).safe (safe_positive security) bits word).value).val) := by
    simp only [law, _p2mH470]
  rw [he]
  exact h.trans (_p2mH475 (counts security).safe (safe_positive security) bits)
open _root_.P2M661a572e renaming h471 → _p2mH471
end
open _root_.P2M661a572e renaming h471 → _p2mH471
open _root_.P2M661a572e renaming h472 → _p2mH472
end CurrentAFT.CurrentSafeDraw
open _root_.P2M661a572e renaming h470 → _p2mH470
open _root_.P2M661a572e renaming h471 → _p2mH471
open _root_.P2M661a572e renaming h472 → _p2mH472
end
open _root_.P2M661a572e renaming h470 → _p2mH470
open _root_.P2M661a572e renaming h472 → _p2mH472
open _root_.P2M661a572e renaming h471 → _p2mH471
section
namespace CurrentAFT.CurrentPublicIndexProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram CurrentProposalDimensions
set_option maxHeartbeats 500000
attribute [local irreducible] CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h453 (security : ℕ) (index : Fin (current security).controls) :
    (decode security index).value = controlsEquiv security index := by
  apply finSumFinEquiv.injective
  have he : finSumFinEquiv (controlsEquiv security index) =
      (finCongr (current_values security).2.2.2.2.2) index := by
    simp only [controlsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [he]
  apply Fin.ext
  dsimp only [decode]
  split_ifs with h
  · rfl
  · have hh : ¬index.val < (current security).legs := by simpa only [← lessCounter_value] using h
    rw [(current_values security).2.1] at hh
    simp only [subtractCounter_value, (current_values security).2.1, finSumFinEquiv, Equiv.coe_fn_mk,
      Sum.elim_inr, Fin.natAdd_mk, Fin.val_mk, finCongr_apply, Fin.val_cast]
    change Parameters.legCount security + (index.val - Parameters.legCount security) = index.val
    omega
open _root_.P2M661a572e renaming h453 → _p2mH453
end CurrentAFT.CurrentPublicIndexProgram
open _root_.P2M661a572e renaming h453 → _p2mH453
end
open _root_.P2M661a572e renaming h453 → _p2mH453
section
namespace CurrentAFT.CurrentPermutationDraw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 700000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h431 (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) (index : Fin count) :
    (draw count bits tape).value.forward.get index = PermutationProgram.draw count bits tape.get index :=
  binaryPermutationFromTape_value count bits tape index
open _root_.P2M661a572e renaming h431 → _p2mH431
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h430 (count bits : ℕ) (tape : Vector (Fin 2) (count * bits)) :
    (draw count bits tape).value.toEquiv = PermutationProgram.draw count bits tape.get := by
  apply Equiv.ext
  exact _p2mH431 count bits tape
open _root_.P2M661a572e renaming h430 → _p2mH430
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h432 (count bits : ℕ) : law count bits = PermutationProgram.permutationLaw count bits := by
  unfold law
  simp only [_p2mH430]
  convert _p2mH110 count bits using 1
  congr 1
  funext word
  congr 1
  funext index
  exact Vector.get_ofFn word index
open _root_.P2M661a572e renaming h432 → _p2mH432
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h434 (count bits : ℕ) :
    FiniteDist.TVBound (law count bits) (FiniteDist.uniform (Equiv.Perm (Fin count)))
      ((count : ℝ) ^ 2 / (2 : ℝ) ^ bits) := by
  rw [_p2mH432]
  exact _p2mH112 count bits
open _root_.P2M661a572e renaming h434 → _p2mH434
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h433 (count bits : ℕ) :
    (∑ permutation, |(law count bits).weight permutation -
      (FiniteDist.uniform (Equiv.Perm (Fin count))).weight permutation|) ≤
      2 * (count : ℝ) ^ 2 / (2 : ℝ) ^ bits := by
  have h := _p2mH434 count bits
  rw [_p2mH93, FiniteDist.totalVariation_eq_half_l1] at h
  calc
    _ ≤ 2 * ((count : ℝ) ^ 2 / (2 : ℝ) ^ bits) := by linarith
    _ = _ := by ring
open _root_.P2M661a572e renaming h433 → _p2mH433
end
open _root_.P2M661a572e renaming h432 → _p2mH432
open _root_.P2M661a572e renaming h433 → _p2mH433
open _root_.P2M661a572e renaming h434 → _p2mH434
end CurrentAFT.CurrentPermutationDraw
open _root_.P2M661a572e renaming h430 → _p2mH430
open _root_.P2M661a572e renaming h431 → _p2mH431
open _root_.P2M661a572e renaming h432 → _p2mH432
open _root_.P2M661a572e renaming h433 → _p2mH433
open _root_.P2M661a572e renaming h434 → _p2mH434
end
open _root_.P2M661a572e renaming h434 → _p2mH434
open _root_.P2M661a572e renaming h430 → _p2mH430
open _root_.P2M661a572e renaming h431 → _p2mH431
open _root_.P2M661a572e renaming h433 → _p2mH433
open _root_.P2M661a572e renaming h432 → _p2mH432
section
namespace CurrentAFT.CurrentFlagIteration
open AFT AFT.BoundaryCalibration AFT.RationalNumerics
open AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
variable {Ω C I : Type*} [Fintype Ω] [Fintype C] [Fintype I] [DecidableEq Ω]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h371 (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    matrixApply (iterationMatrix features allowed safe) profile =
      responseQ features allowed safe profile - profile := by
  change (LinearMap.toMatrix' (responseQ features allowed safe - LinearMap.id)).mulVec profile = _
  rw [LinearMap.toMatrix'_mulVec]
  rfl
open _root_.P2M661a572e renaming h371 → _p2mH371
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h370 [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    realVector (iterate features allowed safe target (steps + 1)) =
      realVector target + deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe
        (realVector (iterate features allowed safe target steps)) := by
  have he : iterate features allowed safe target (steps + 1) =
      target - (responseQ features allowed safe (iterate features allowed safe target steps) -
        iterate features allowed safe target steps) := by
    exact congrArg (fun value => target - value) (_p2mH371 features allowed safe _)
  rw [he]
  have hr := responseQ_cast features allowed safe (iterate features allowed safe target steps)
  funext x
  have hx := congrFun hr x
  simp only [realVector, Pi.sub_apply, Rat.cast_sub, Pi.add_apply] at hx ⊢
  linarith
open _root_.P2M661a572e renaming h370 → _p2mH370
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h368 [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hD : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ < 1)
    (bound : ℝ) (hbound : 0 ≤ bound)
    (hop : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ bound)
    (target : Ω → ℚ) (steps : ℕ) :
    ‖realVector (iterate features allowed safe target steps) - realVector (solve features allowed safe target)‖ ≤
      bound ^ steps * ‖realVector (solve features allowed safe target)‖ := by
  let D := deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe
  let exactValue := realVector (solve features allowed safe target)
  have hfixed : realVector target + D exactValue = exactValue := by
    have h := congrArg realVector (solve_equation features allowed safe hD target)
    rw [responseQ_cast] at h
    change exactValue - D exactValue = realVector target at h
    linear_combination -h
  induction steps with
  | zero =>
    have hz : realVector (0 : Ω → ℚ) = 0 := by ext x; simp [realVector]
    simp only [iterate, linearIteration, hz, zero_sub, norm_neg, pow_zero, one_mul, le_refl]
  | succ steps ih =>
    have hid : realVector (iterate features allowed safe target (steps + 1)) - exactValue =
        D (realVector (iterate features allowed safe target steps) - exactValue) := by
      rw [_p2mH370, map_sub]
      change realVector target + D _ - exactValue = D _ - D exactValue
      linear_combination hfixed
    change ‖realVector (iterate features allowed safe target (steps + 1)) - exactValue‖ ≤ _
    rw [hid]
    calc
      ‖D (realVector (iterate features allowed safe target steps) - exactValue)‖ ≤
          bound * ‖realVector (iterate features allowed safe target steps) - exactValue‖ :=
        (D.le_opNorm _).trans (mul_le_mul_of_nonneg_right hop (norm_nonneg _))
      _ ≤ bound * (bound ^ steps * ‖exactValue‖) := mul_le_mul_of_nonneg_left ih hbound
      _ = bound ^ (steps + 1) * ‖exactValue‖ := by rw [pow_succ]; ring
open _root_.P2M661a572e renaming h368 → _p2mH368
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h369 [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ 1 / 4)
    (target : Ω → ℚ) (steps : ℕ) :
    ‖realVector (iterate features allowed safe target steps) - realVector (solve features allowed safe target)‖ ≤
      (1 / 4 : ℝ) ^ steps * ((4 / 3) * ‖realVector target‖) := by
  have hD := hquarter.trans_lt (by norm_num : (1 / 4 : ℝ) < 1)
  apply (_p2mH368 features allowed safe hD (1 / 4) (by norm_num) hquarter target steps).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [solve_cast features allowed safe hD]
  exact _p2mH61 _ hD hquarter _
open _root_.P2M661a572e renaming h369 → _p2mH369
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h372 [Nonempty Ω] (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ)
    (hquarter : ‖deletion (chartProjection (FiniteDist.uniform Ω) features allowed) safe‖ ≤ 1 / 4)
    (steps : ℕ) (point : Ω) :
    |(regularIterate features allowed line safe atom spike steps point : ℝ) -
        (regularDensityQ features allowed line safe atom spike point : ℝ)| ≤
      (1 / 4 : ℝ) ^ steps * ((4 / 3) *
        ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike)‖) := by
  by_cases hs : safe point
  · simp only [regularIterate, regularDensityQ, if_pos hs]
    exact (norm_le_pi_norm
      (realVector (iterate features allowed safe _ steps) - realVector (solve features allowed safe _)) point).trans
        (_p2mH369 features allowed safe hquarter _ steps)
  · simp only [regularIterate, regularDensityQ, if_neg hs, Rat.cast_zero, sub_self, abs_zero]
    positivity
open _root_.P2M661a572e renaming h372 → _p2mH372
section ActualParameters
variable {F J : Type*} [Field F] [Fintype F] [Fintype J]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h366 (inputs : J → F × F) (hinj : Function.Injective inputs)
    (allowed : J → Finset F) (δ : ℝ) (hδ : 0 ≤ δ)
    (hbudget : affineDeletionBudget allowed ≤ δ)
    (hsmall : (2 * Fintype.card J + 1) * δ ≤ 1 / 4) :
    ‖deletion (chartProjection (FiniteDist.uniform (Chart F)) (affineFeatures inputs) allowed)
      (affineSafe inputs allowed)‖ ≤ 1 / 4 := by
  let p := FiniteDist.uniform (Chart F)
  have hfeature (i : J) : p.map (affineFeatures inputs i) = FiniteDist.uniform F := feature_uniform _ _
  have hpair (i j : J) (hij : i ≠ j) :
      p.map (fun x => (affineFeatures inputs i x, affineFeatures inputs j x)) =
        (FiniteDist.uniform F).prod (FiniteDist.uniform F) :=
    feature_pair_uniform (inputs i) (inputs j) (fun h => hij (hinj h))
  have hauxpair (i : J) : p.map (fun x => (affineFeatures inputs i x, x.2.1)) =
      (FiniteDist.uniform F).prod (FiniteDist.uniform F) := feature_scale_uniform _ _
  have hbudgetFormula : expectation (FiniteDist.uniform F) (paletteFailure (Finset.univ.erase 0)) +
      ∑ i, expectation (FiniteDist.uniform F) (paletteFailure (allowed i)) = affineDeletionBudget allowed := by
    rw [nonzero_palette_failure]
    simp only [uniform_palette_failure, affineDeletionBudget]
  have hglobal : expectation p (badIndicator (affineSafe inputs allowed)) ≤ δ := by
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_global_budget p (fun chart => chart.2.1) (Finset.univ.erase 0)
      (affineFeatures inputs) allowed scale_uniform hfeature
  have hconditional : ∀ i c, c ∈ allowed i →
      conditional p (affineFeatures inputs i) (badIndicator (affineSafe inputs allowed)) c ≤ δ := by
    intro i c hc
    apply le_trans _ hbudget
    rw [← hbudgetFormula]
    exact legalChart_conditional_budget p _ _ (affineFeatures inputs) allowed hfeature hpair hauxpair i c hc
  exact (chartDeletion_norm p (affineFeatures inputs) allowed (affineSafe inputs allowed)
    δ hδ hglobal hconditional).trans hsmall
open _root_.P2M661a572e renaming h366 → _p2mH366
attribute [local instance] _root_.CurrentAFT.CurrentFlagIteration.iterationPrime
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h367 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) :
    ‖deletion (chartProjection (FiniteDist.uniform (Chart (ZMod (Parameters.modulus security))))
      (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline))
      (affineSafe (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline))‖ ≤ 1 / 4 := by
  have hb := leg_budget_conditions security
  exact _p2mH366 _ (protectedInputs_injective _ _ (leg_input_separation security)) _
    (legDeletionUpper security) hb.1 (protectedPalette_current_budget security baseline hbaseline) hb.2.2.1
open _root_.P2M661a572e renaming h367 → _p2mH367
end ActualParameters
open _root_.P2M661a572e renaming h366 → _p2mH366
open _root_.P2M661a572e renaming h367 → _p2mH367
end
open _root_.P2M661a572e renaming h366 → _p2mH366
open _root_.P2M661a572e renaming h367 → _p2mH367
open _root_.P2M661a572e renaming h368 → _p2mH368
open _root_.P2M661a572e renaming h369 → _p2mH369
open _root_.P2M661a572e renaming h370 → _p2mH370
open _root_.P2M661a572e renaming h371 → _p2mH371
open _root_.P2M661a572e renaming h372 → _p2mH372
end CurrentAFT.CurrentFlagIteration
open _root_.P2M661a572e renaming h366 → _p2mH366
open _root_.P2M661a572e renaming h367 → _p2mH367
open _root_.P2M661a572e renaming h368 → _p2mH368
open _root_.P2M661a572e renaming h369 → _p2mH369
open _root_.P2M661a572e renaming h370 → _p2mH370
open _root_.P2M661a572e renaming h371 → _p2mH371
open _root_.P2M661a572e renaming h372 → _p2mH372
end
open _root_.P2M661a572e renaming h367 → _p2mH367
open _root_.P2M661a572e renaming h369 → _p2mH369
open _root_.P2M661a572e renaming h366 → _p2mH366
open _root_.P2M661a572e renaming h371 → _p2mH371
open _root_.P2M661a572e renaming h372 → _p2mH372
open _root_.P2M661a572e renaming h368 → _p2mH368
open _root_.P2M661a572e renaming h370 → _p2mH370
section
namespace CurrentAFT.CurrentFlagArray
open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators
variable {C I : Type*} [Fintype C] [Fintype I] [DecidableEq C]
noncomputable section
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h322 (charts : ℕ) (profile : Fin charts → ℚ) :
    mean charts profile = expectationQ profile := by
  simp only [mean, expectationQ, LinearMap.coe_mk, AddHom.coe_mk, Fintype.card_fin, div_eq_mul_inv]
  ring
open _root_.P2M661a572e renaming h322 → _p2mH322
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h318 (charts : ℕ) (feature : Fin charts → C) (profile : Fin charts → ℚ) (color : C) :
    conditional charts feature profile color = conditionalQ feature profile color := by
  simp only [conditional, _p2mH322, conditionalQ, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  apply congrArg expectationQ
  funext point
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h318 → _p2mH318
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h317 (charts : ℕ) (feature : Fin charts → C) (allowed : Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) :
    component charts feature allowed profile point = featureProjectionQ feature allowed profile point := by
  simp only [component, _p2mH318, featureProjectionQ, LinearMap.comp_apply, LinearMap.funLeft_apply,
    centerAllowedQ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h317 → _p2mH317
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h323 (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (profile : Fin charts → ℚ) (point : Fin charts) :
    projection charts features allowed profile point = projectionQ features allowed profile point := by
  simp only [projection, _p2mH322, _p2mH317, projectionQ, LinearMap.coe_mk, AddHom.coe_mk]
open _root_.P2M661a572e renaming h323 → _p2mH323
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h320 (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (profile : Fin charts → ℚ) (point : Fin charts) :
    deletion charts features allowed safe profile point =
      projectionQ features allowed (badMaskQ (fun input => safe input = true) profile) point := by
  rw [deletion, _p2mH323]
  apply congrArg (fun value => projectionQ features allowed value point)
  funext input
  simp only [badMaskQ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h320 → _p2mH320
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h319 (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (spike : Fin charts → ℚ) :
    defect charts features allowed line spike = offLineDefectQ features allowed (fun index => line index = true) spike := by
  funext point
  simp only [defect, offLineDefectQ, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> first | rfl | exact _p2mH317 charts _ _ _ _
open _root_.P2M661a572e renaming h319 → _p2mH319
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h325 (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (atom : ℚ) (spike : Fin charts → ℚ) :
    target charts features allowed line atom spike =
      1 - (atom / (1 - atom)) • offLineDefectQ features allowed (fun index => line index = true) spike := by
  rw [← _p2mH319 charts features allowed line spike]
  rfl
open _root_.P2M661a572e renaming h325 → _p2mH325
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h321 (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (safe : Fin charts → Bool) (rhs : Fin charts → ℚ) (steps : ℕ) (point : Fin charts) :
    (iterate charts features allowed safe rhs steps).get point =
      CurrentFlagIteration.iterate features allowed (fun input => safe input = true) rhs steps point := by
  induction steps generalizing point with
  | zero => simp [iterate, CurrentFlagIteration.iterate, AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    simp only [iterate, Vector.get_ofFn]
    have he : (iterate charts features allowed safe rhs steps).get =
        CurrentFlagIteration.iterate features allowed (fun input => safe input = true) rhs steps := funext ih
    rw [he, _p2mH320]
    change _ = (rhs - AFT.RationalNumerics.matrixApply
      (CurrentFlagIteration.iterationMatrix features allowed (fun input => safe input = true))
      (CurrentFlagIteration.iterate features allowed (fun input => safe input = true) rhs steps)) point
    rw [_p2mH371]
    simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Pi.sub_apply]
    ring
open _root_.P2M661a572e renaming h321 → _p2mH321
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h324 (charts : ℕ) (features : I → Fin charts → C) (allowed : I → Finset C)
    (line : I → Bool) (safe : Fin charts → Bool) (atom : ℚ) (spike : Fin charts → ℚ)
    (steps : ℕ) (point : Fin charts) :
    (regular charts features allowed line safe atom spike steps).get point =
      CurrentFlagIteration.regularIterate features allowed (fun index => line index = true)
        (fun input => safe input = true) atom spike steps point := by
  simp only [regular, Vector.get_ofFn, CurrentFlagIteration.regularIterate]
  split_ifs <;> simp only [_p2mH321, _p2mH325]
open _root_.P2M661a572e renaming h324 → _p2mH324
end
open _root_.P2M661a572e renaming h317 → _p2mH317
open _root_.P2M661a572e renaming h318 → _p2mH318
open _root_.P2M661a572e renaming h319 → _p2mH319
open _root_.P2M661a572e renaming h320 → _p2mH320
open _root_.P2M661a572e renaming h321 → _p2mH321
open _root_.P2M661a572e renaming h322 → _p2mH322
open _root_.P2M661a572e renaming h323 → _p2mH323
open _root_.P2M661a572e renaming h324 → _p2mH324
open _root_.P2M661a572e renaming h325 → _p2mH325
end CurrentAFT.CurrentFlagArray
open _root_.P2M661a572e renaming h317 → _p2mH317
open _root_.P2M661a572e renaming h318 → _p2mH318
open _root_.P2M661a572e renaming h319 → _p2mH319
open _root_.P2M661a572e renaming h320 → _p2mH320
open _root_.P2M661a572e renaming h321 → _p2mH321
open _root_.P2M661a572e renaming h322 → _p2mH322
open _root_.P2M661a572e renaming h323 → _p2mH323
open _root_.P2M661a572e renaming h324 → _p2mH324
open _root_.P2M661a572e renaming h325 → _p2mH325
end
open _root_.P2M661a572e renaming h325 → _p2mH325
open _root_.P2M661a572e renaming h324 → _p2mH324
open _root_.P2M661a572e renaming h322 → _p2mH322
open _root_.P2M661a572e renaming h320 → _p2mH320
open _root_.P2M661a572e renaming h319 → _p2mH319
open _root_.P2M661a572e renaming h317 → _p2mH317
open _root_.P2M661a572e renaming h321 → _p2mH321
open _root_.P2M661a572e renaming h318 → _p2mH318
open _root_.P2M661a572e renaming h323 → _p2mH323
section
namespace CurrentAFT.CurrentFlagBinary
open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h327 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts)
    (point : Fin charts) (index : Fin features) :
    (defectTerm feature allowed line spike point index).data.decode =
      if line.get index then 0 else chartFeatureProgram charts colors (feature.get index).get
        (maskSet (allowed.get index)) (fun input => (spike.get input).decode) point := by
  simp only [defectTerm, readVector_value]
  split <;> simp_all only [zero_value, chartProjectionTerm, readVector_value, _p2mH10]
open _root_.P2M661a572e renaming h327 → _p2mH327
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h326 (charts colors : ℕ) (feature : Fin charts → Fin colors) (allowed : Finset (Fin colors))
    (profile : Fin charts → ℚ) (point : Fin charts) :
    chartFeatureProgram charts colors feature allowed profile point =
      CurrentFlagArray.component charts feature allowed profile point := by
  simp only [chartFeatureProgram, CurrentFlagArray.component, CurrentFlagArray.conditional,
    CurrentFlagArray.mean, chartConditionalProgram, chartExpectationProgram, Fintype.card_fin]
open _root_.P2M661a572e renaming h326 → _p2mH326
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h328 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (spike : Vector RationalBits charts) (point : Fin charts) :
    (defect feature allowed line spike point).data.decode =
      CurrentFlagArray.defect charts (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) line.get (fun input => (spike.get input).decode) point := by
  simp only [defect, sumFin_value, _p2mH327, _p2mH326, CurrentFlagArray.defect]
open _root_.P2M661a572e renaming h328 → _p2mH328
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h335 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (atom : RationalBits) (spike : Vector RationalBits charts)
    (point : Fin charts) :
    (targetEntry feature allowed line atom spike point).data.decode =
      CurrentFlagArray.target charts (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) line.get atom.decode
        (fun input => (spike.get input).decode) point := by
  simp only [targetEntry, _p2mH14, quotient_value, RationalBits.multiply_value, one_value,
    _p2mH328, CurrentFlagArray.target]
open _root_.P2M661a572e renaming h335 → _p2mH335
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h330 {charts : ℕ} (safe : Vector Bool charts) (profile : Vector RationalBits charts)
    (point : Fin charts) :
    (maskedEntry safe profile point).data.decode = if safe.get point then (profile.get point).decode else 0 := by
  simp only [maskedEntry, readVector_value]
  split <;> simp_all only [zero_value]
open _root_.P2M661a572e renaming h330 → _p2mH330
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h334 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits)
    (steps : ℕ) (point : Fin charts) :
    ((regular feature allowed line safe fiber atom steps).data.get point).decode =
      if safe.get point then
        linearIteration
          (chartDeletionMatrixProgram charts colors features (fun index => (feature.get index).get)
            (fun index => maskSet (allowed.get index)) (maskSet safe))
          (CurrentFlagArray.target charts (fun index => (feature.get index).get)
            (fun index => maskSet (allowed.get index)) line.get atom.decode
            (chartSpikeProgram charts (maskSet fiber))) steps point else 0 := by
  simp only [regular, buildArray_get, _p2mH330, _p2mH16, _p2mH8,
    _p2mH335, _p2mH12]
open _root_.P2M661a572e renaming h334 → _p2mH334
end CurrentAFT.CurrentFlagBinary
open _root_.P2M661a572e renaming h326 → _p2mH326
open _root_.P2M661a572e renaming h327 → _p2mH327
open _root_.P2M661a572e renaming h328 → _p2mH328
open _root_.P2M661a572e renaming h330 → _p2mH330
open _root_.P2M661a572e renaming h334 → _p2mH334
open _root_.P2M661a572e renaming h335 → _p2mH335
end
open _root_.P2M661a572e renaming h327 → _p2mH327
open _root_.P2M661a572e renaming h335 → _p2mH335
open _root_.P2M661a572e renaming h328 → _p2mH328
open _root_.P2M661a572e renaming h330 → _p2mH330
open _root_.P2M661a572e renaming h334 → _p2mH334
open _root_.P2M661a572e renaming h326 → _p2mH326
section
namespace CurrentAFT.CurrentFlagBinary
open AFT AFT.RationalNumerics AFT.BoundaryCalibration AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h332 (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (profile : Fin charts → ℚ) (point : Fin charts) :
    chartProjectionProgram charts colors features feature allowed profile point =
      projectionQ feature allowed profile point := by
  rw [← _p2mH323 charts feature allowed profile point]
  simp only [chartProjectionProgram, chartExpectationProgram, CurrentFlagArray.projection,
    CurrentFlagArray.mean, _p2mH326]
open _root_.P2M661a572e renaming h332 → _p2mH332
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h329 (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) (profile : Fin charts → ℚ) (point : Fin charts) :
    chartDeletionProgram charts colors features feature allowed safe profile point =
      projectionQ feature allowed (badMaskQ (fun input => input ∈ safe) profile) point := by
  rw [chartDeletionProgram, _p2mH332]
  apply congrArg (fun value => projectionQ feature allowed value point)
  funext input
  simp only [badMaskQ, LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h329 → _p2mH329
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h331 (charts colors features : ℕ)
    (feature : Fin features → Fin charts → Fin colors) (allowed : Fin features → Finset (Fin colors))
    (safe : Finset (Fin charts)) :
    chartDeletionMatrixProgram charts colors features feature allowed safe =
      iterationMatrix feature allowed (fun input => input ∈ safe) := by
  funext output input
  have hb : (fun point : Fin charts => if point = input then (1 : ℚ) else 0) = Pi.single input 1 := by
    funext point
    by_cases hp : point = input
    · subst point
      simp
    · simp only [if_neg hp, Pi.single_eq_of_ne hp]
  rw [chartDeletionMatrixProgram, hb, _p2mH329]
  simp only [iterationMatrix, LinearMap.toMatrix'_apply, LinearMap.sub_apply, LinearMap.id_apply,
    responseQ, LinearMap.comp_apply, Pi.sub_apply]
  ring
open _root_.P2M661a572e renaming h331 → _p2mH331
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h333 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (safe fiber : Vector Bool charts) (atom : RationalBits)
    (steps : ℕ) (point : Fin charts) :
    ((regular feature allowed line safe fiber atom steps).data.get point).decode =
      (CurrentFlagArray.regular charts (fun index => (feature.get index).get)
        (fun index => maskSet (allowed.get index)) line.get safe.get atom.decode
        (chartSpikeProgram charts (maskSet fiber)) steps).get point := by
  have hs : (fun input => input ∈ maskSet safe) = (fun input => safe.get input = true) := by
    funext input
    apply propext
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [_p2mH334, _p2mH324, _p2mH331, hs]
  simp only [_p2mH325, regularIterate, CurrentFlagIteration.iterate]
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h333 → _p2mH333
end
open _root_.P2M661a572e renaming h329 → _p2mH329
open _root_.P2M661a572e renaming h331 → _p2mH331
open _root_.P2M661a572e renaming h332 → _p2mH332
open _root_.P2M661a572e renaming h333 → _p2mH333
end CurrentAFT.CurrentFlagBinary
open _root_.P2M661a572e renaming h329 → _p2mH329
open _root_.P2M661a572e renaming h331 → _p2mH331
open _root_.P2M661a572e renaming h332 → _p2mH332
open _root_.P2M661a572e renaming h333 → _p2mH333
end
open _root_.P2M661a572e renaming h332 → _p2mH332
open _root_.P2M661a572e renaming h331 → _p2mH331
open _root_.P2M661a572e renaming h329 → _p2mH329
open _root_.P2M661a572e renaming h333 → _p2mH333
section
namespace CurrentAFT.CurrentFlagBinaryMasks
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h338 (cutoff : ℕ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    (onLine cutoff index).value = true ↔ ((finiteInputEquiv cutoff index).1 : ℤ) = 0 := by
  simp only [onLine, equalCounter_value, doubleCounter_value, Nat.succ_eq_add_one,
    (divideCounter_value index.val (2 * cutoff + 1) (by omega)).1]
  simp only [finiteInputEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, finProdFinEquiv_symm_apply,
    FiniteConvolutionProgram.windowIndexEquiv, Equiv.coe_fn_mk, Prod.map_apply]
  change index.val / (2 * cutoff + 1) = cutoff ↔
    ((index.val / (2 * cutoff + 1) : ℕ) : ℤ) - cutoff = 0
  omega
open _root_.P2M661a572e renaming h338 → _p2mH338
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h337 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (point : Fin charts) (index : Fin features) :
    (offLineAllowed feature allowed line point index).value = true ↔
      line.get index ≠ true → (allowed.get index).get ((feature.get index).get point) = true := by
  simp only [offLineAllowed, readVector_value, _p2mH35, Bool.or_eq_true, or_iff_not_imp_left]
open _root_.P2M661a572e renaming h337 → _p2mH337
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h336 {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (line : Vector Bool features) (base scale shear : Vector (Fin colors) charts)
    (mark : Fin colors) (point : Fin charts) :
    (fiberAt feature allowed line base scale shear mark point).value = true ↔
      base.get point = mark ∧ scale.get point ≠ 0 ∧ shear.get point = 0 ∧
        ∀ index, line.get index ≠ true → (allowed.get index).get ((feature.get index).get point) = true := by
  simp only [fiberAt, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, readVector_value,
    equalCounter_value, _p2mH142, _p2mH337, and_assoc]
  have hscale : (scale.get point).val = 0 ↔ scale.get point = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hshear : (shear.get point).val = 0 ↔ shear.get point = 0 :=
    ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
  have hn : (equalCounter (scale.get point).val 0).value ≠ true ↔ scale.get point ≠ 0 :=
    not_congr ((equalCounter_value _ _).trans hscale)
  simp only [Fin.val_inj, hn, hshear]
open _root_.P2M661a572e renaming h336 → _p2mH336
end CurrentAFT.CurrentFlagBinaryMasks
open _root_.P2M661a572e renaming h336 → _p2mH336
open _root_.P2M661a572e renaming h337 → _p2mH337
open _root_.P2M661a572e renaming h338 → _p2mH338
end
open _root_.P2M661a572e renaming h338 → _p2mH338
open _root_.P2M661a572e renaming h336 → _p2mH336
open _root_.P2M661a572e renaming h337 → _p2mH337
section
namespace CurrentAFT.CurrentFlagBinaryMetadata
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits CurrentFlagBinaryMasks
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h345 (modulus : ℕ) [NeZero modulus] (value : Fin modulus) :
    (ZMod.finEquiv modulus) value = (value.val : ZMod modulus) := by
  cases modulus with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ modulus => apply Fin.ext; exact (Nat.mod_eq_of_lt value.isLt).symm
open _root_.P2M661a572e renaming h345 → _p2mH345
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h344 (modulus : ℕ) [NeZero modulus]
    (point : Fin (modulus * (modulus * modulus))) :
    ((ZMod.finEquiv modulus) (coordinates modulus point).value.1,
      (ZMod.finEquiv modulus) (coordinates modulus point).value.2.1,
      (ZMod.finEquiv modulus) (coordinates modulus point).value.2.2) = finiteChartEquiv modulus point := by
  simp only [coordinates, _p2mH345]
  exact _p2mH21 modulus point
open _root_.P2M661a572e renaming h344 → _p2mH344
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h340 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
    (fun index point => (((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.feature).get index).get point) =
      finiteProtectedFeatures cutoff modulus := by
  exact _p2mH47 cutoff modulus boundarySign baselineSign boundary baseline mark
open _root_.P2M661a572e renaming h340 → _p2mH340
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h339 (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) (color : Fin modulus) :
    (((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.allowed).get index).get color = true ↔
      color ∈ finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) index := by
  exact _p2mH46 cutoff modulus boundarySign baselineSign boundary baseline mark index color
open _root_.P2M661a572e renaming h339 → _p2mH339
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h343 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (point : Fin (modulus * (modulus * modulus))) :
    ((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.safe).get point = true ↔
      point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
        (finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline)) := by
  exact _p2mH48 cutoff modulus boundarySign baselineSign boundary baseline mark point
open _root_.P2M661a572e renaming h343 → _p2mH343
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h342 (cutoff modulus : ℕ) [NeZero modulus]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    ((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.line).get index = true ↔
      ((finiteInputEquiv cutoff index).1 : ℤ) = 0 := by
  simp only [build, storeData_get]
  exact _p2mH338 cutoff index
open _root_.P2M661a572e renaming h342 → _p2mH342
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h341 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus)
    (point : Fin (modulus * (modulus * modulus))) :
    ((build cutoff modulus boundarySign baselineSign boundary baseline mark).value.fiber).get point = true ↔
      (coordinates modulus point).value.1 = mark ∧ finiteAffineScale modulus point ≠ 0 ∧
        (coordinates modulus point).value.2.2 = 0 ∧
        ∀ index, ((finiteInputEquiv cutoff index).1 : ℤ) ≠ 0 →
          finiteProtectedFeatures cutoff modulus index point ∈
            finiteProtectedPalettes cutoff modulus (signedValue boundarySign boundary) (signedValue baselineSign baseline) index := by
  simp only [build, storeData_get, _p2mH336]
  rw [_p2mH49]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  apply forall_congr'
  intro index
  apply imp_congr (not_congr (_p2mH338 cutoff index))
  have hf := congrFun (congrFun (_p2mH47 cutoff modulus boundarySign baselineSign boundary baseline mark) index) point
  rw [hf]
  exact _p2mH46 cutoff modulus boundarySign baselineSign boundary baseline mark index _
open _root_.P2M661a572e renaming h341 → _p2mH341
end CurrentAFT.CurrentFlagBinaryMetadata
open _root_.P2M661a572e renaming h339 → _p2mH339
open _root_.P2M661a572e renaming h340 → _p2mH340
open _root_.P2M661a572e renaming h341 → _p2mH341
open _root_.P2M661a572e renaming h342 → _p2mH342
open _root_.P2M661a572e renaming h343 → _p2mH343
open _root_.P2M661a572e renaming h344 → _p2mH344
open _root_.P2M661a572e renaming h345 → _p2mH345
end
open _root_.P2M661a572e renaming h342 → _p2mH342
open _root_.P2M661a572e renaming h341 → _p2mH341
open _root_.P2M661a572e renaming h339 → _p2mH339
open _root_.P2M661a572e renaming h345 → _p2mH345
open _root_.P2M661a572e renaming h343 → _p2mH343
open _root_.P2M661a572e renaming h340 → _p2mH340
open _root_.P2M661a572e renaming h344 → _p2mH344
section
namespace CurrentAFT.CurrentFlagReindex
open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
variable {Ω Ω' C I : Type*} [Fintype Ω] [Fintype Ω'] [Fintype C] [Fintype I]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h396 (e : Ω' ≃ Ω) (profile : Ω → ℚ) :
    expectationQ (profile ∘ e) = expectationQ profile := by
  simp only [expectationQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [Fintype.card_congr e, Equiv.sum_comp e profile]
open _root_.P2M661a572e renaming h396 → _p2mH396
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h392 (e : Ω' ≃ Ω) (feature : Ω → C) (profile : Ω → ℚ) :
    conditionalQ (feature ∘ e) (profile ∘ e) = conditionalQ feature profile := by
  funext color
  change (Fintype.card C : ℚ) * expectationQ
    ((fun x => if feature x = color then profile x else 0) ∘ e) = _
  rw [_p2mH396]
  rfl
open _root_.P2M661a572e renaming h392 → _p2mH392
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h390 (e : Ω' ≃ Ω) (feature : Ω → C) (allowed : Finset C)
    (profile : Ω → ℚ) (point : Ω') :
    featureProjectionQ (feature ∘ e) allowed (profile ∘ e) point =
      featureProjectionQ feature allowed profile (e point) := by
  change centerAllowedQ allowed (conditionalQ (feature ∘ e) (profile ∘ e)) (feature (e point)) = _
  rw [_p2mH392]
  rfl
open _root_.P2M661a572e renaming h390 → _p2mH390
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h402 (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (profile : Ω → ℚ) (point : Ω') :
    projectionQ (fun index => features index ∘ e) allowed (profile ∘ e) point =
      projectionQ features allowed profile (e point) := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, _p2mH396, _p2mH390]
open _root_.P2M661a572e renaming h402 → _p2mH402
set_option maxRecDepth 8192
omit [Fintype Ω] [Fintype Ω'] in
theorem _root_.P2M661a572e.h388 (e : Ω' ≃ Ω) (safe : Ω → Prop) (profile : Ω → ℚ) :
    badMaskQ (safe ∘ e) (profile ∘ e) = badMaskQ safe profile ∘ e := by
  funext point
  simp only [badMaskQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
open _root_.P2M661a572e renaming h388 → _p2mH388
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h408 (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    responseQ (fun index => features index ∘ e) allowed (safe ∘ e) (profile ∘ e) =
      responseQ features allowed safe profile ∘ e := by
  funext point
  simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, Function.comp_apply]
  rw [_p2mH388, _p2mH402]
open _root_.P2M661a572e renaming h408 → _p2mH408
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h395 (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    offLineDefectQ (fun index => features index ∘ e) allowed line (spike ∘ e) =
      offLineDefectQ features allowed line spike ∘ e := by
  funext point
  simp only [offLineDefectQ, Finset.sum_apply, Function.comp_apply]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> first | rfl | exact _p2mH390 e _ _ _ _
open _root_.P2M661a572e renaming h395 → _p2mH395
variable [DecidableEq Ω] [DecidableEq Ω']
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h399 (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate (fun index => features index ∘ e) allowed (safe ∘ e)
        (target ∘ e) steps = CurrentFlagIteration.iterate features allowed safe target steps ∘ e := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    simp only [CurrentFlagIteration.iterate] at ih
    change (target ∘ e) - AFT.RationalNumerics.matrixApply _ _ =
      (target - AFT.RationalNumerics.matrixApply _ _) ∘ e
    rw [_p2mH371, _p2mH371, ih, _p2mH408]
    rfl
open _root_.P2M661a572e renaming h399 → _p2mH399
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h405 (e : Ω' ≃ Ω) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) :
    regularIterate (fun index => features index ∘ e) allowed line (safe ∘ e) atom (spike ∘ e) steps =
      regularIterate features allowed line safe atom spike steps ∘ e := by
  have ht : (1 - (atom / (1 - atom)) •
      offLineDefectQ (fun index => features index ∘ e) allowed line (spike ∘ e)) =
      (1 - (atom / (1 - atom)) • offLineDefectQ features allowed line spike) ∘ e := by
    rw [_p2mH395]
    rfl
  funext point
  simp only [regularIterate, Function.comp_apply]
  split_ifs
  · rw [ht, _p2mH399]
    rfl
  · rfl
open _root_.P2M661a572e renaming h405 → _p2mH405
end
open _root_.P2M661a572e renaming h388 → _p2mH388
open _root_.P2M661a572e renaming h390 → _p2mH390
open _root_.P2M661a572e renaming h392 → _p2mH392
open _root_.P2M661a572e renaming h395 → _p2mH395
open _root_.P2M661a572e renaming h396 → _p2mH396
open _root_.P2M661a572e renaming h399 → _p2mH399
open _root_.P2M661a572e renaming h402 → _p2mH402
open _root_.P2M661a572e renaming h405 → _p2mH405
open _root_.P2M661a572e renaming h408 → _p2mH408
end CurrentAFT.CurrentFlagReindex
open _root_.P2M661a572e renaming h388 → _p2mH388
open _root_.P2M661a572e renaming h390 → _p2mH390
open _root_.P2M661a572e renaming h392 → _p2mH392
open _root_.P2M661a572e renaming h395 → _p2mH395
open _root_.P2M661a572e renaming h396 → _p2mH396
open _root_.P2M661a572e renaming h399 → _p2mH399
open _root_.P2M661a572e renaming h402 → _p2mH402
open _root_.P2M661a572e renaming h405 → _p2mH405
open _root_.P2M661a572e renaming h408 → _p2mH408
end
open _root_.P2M661a572e renaming h388 → _p2mH388
open _root_.P2M661a572e renaming h405 → _p2mH405
open _root_.P2M661a572e renaming h396 → _p2mH396
open _root_.P2M661a572e renaming h395 → _p2mH395
open _root_.P2M661a572e renaming h402 → _p2mH402
open _root_.P2M661a572e renaming h399 → _p2mH399
open _root_.P2M661a572e renaming h408 → _p2mH408
open _root_.P2M661a572e renaming h392 → _p2mH392
open _root_.P2M661a572e renaming h390 → _p2mH390
namespace CurrentAFT.CurrentFlagIteration
end CurrentAFT.CurrentFlagIteration
namespace CurrentAFT.CurrentFlagIteration.regularIterate
end CurrentAFT.CurrentFlagIteration.regularIterate
namespace CurrentAFT.CurrentFlagReindex
end CurrentAFT.CurrentFlagReindex
section
namespace CurrentAFT.CurrentFlagReindex
open AFT AFT.BoundaryCalibration CurrentRationalFlagLaw CurrentFlagIteration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 200000
variable {Ω C C' I I' : Type*} [Fintype Ω] [Fintype C] [Fintype C'] [Fintype I] [Fintype I']
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h391 (e : C' ≃ C) (feature : Ω → C) (profile : Ω → ℚ) (color : C') :
    conditionalQ (e.symm ∘ feature) profile color = conditionalQ feature profile (e color) := by
  simp only [conditionalQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [Fintype.card_congr e]
  apply congrArg (fun value : ℚ => (Fintype.card C : ℚ) * value)
  apply congrArg expectationQ
  funext point
  have hp : e.symm (feature point) = color ↔ feature point = e color := by
    exact e.symm_apply_eq
  simp only [hp]
open _root_.P2M661a572e renaming h391 → _p2mH391
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h389 (e : C' ≃ C) (feature : Ω → C) (allowed : Finset C)
    (profile : Ω → ℚ) (point : Ω) :
    featureProjectionQ (e.symm ∘ feature) (allowed.map e.symm.toEmbedding) profile point =
      featureProjectionQ feature allowed profile point := by
  have hc : conditionalQ (e.symm ∘ feature) profile = conditionalQ feature profile ∘ e :=
    funext (_p2mH391 e feature profile)
  have hm : e.symm (feature point) ∈ allowed.map e.symm.toEmbedding ↔ feature point ∈ allowed := by simp
  change (if e.symm (feature point) ∈ allowed.map e.symm.toEmbedding then
    conditionalQ (e.symm ∘ feature) profile (e.symm (feature point)) -
      (∑ color ∈ allowed.map e.symm.toEmbedding, conditionalQ (e.symm ∘ feature) profile color) /
        (allowed.map e.symm.toEmbedding).card else 0) = _
  rw [hc]
  simp only [Finset.card_map, Finset.sum_map, Function.comp_apply, Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply]
  change (if e.symm (feature point) ∈ allowed.map e.symm.toEmbedding then
    conditionalQ feature profile (feature point) -
      (∑ color ∈ allowed, conditionalQ feature profile color) / allowed.card else 0) = _
  simp only [hm]
  rfl
open _root_.P2M661a572e renaming h389 → _p2mH389
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h400 (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (profile : Ω → ℚ) (point : Ω) :
    projectionQ (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      profile point = projectionQ features allowed profile point := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, _p2mH389]
open _root_.P2M661a572e renaming h400 → _p2mH400
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h406 (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    responseQ (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      safe profile = responseQ features allowed safe profile := by
  funext point
  simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, _p2mH400]
open _root_.P2M661a572e renaming h406 → _p2mH406
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h393 (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    offLineDefectQ (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      line spike = offLineDefectQ features allowed line spike := by
  funext point
  simp only [offLineDefectQ, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro index _
  split_ifs <;> first | rfl | exact _p2mH389 e _ _ _ _
open _root_.P2M661a572e renaming h393 → _p2mH393
variable [DecidableEq Ω]
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h563 (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate features allowed safe target (steps + 1) =
      target - (responseQ features allowed safe (CurrentFlagIteration.iterate features allowed safe target steps) -
        CurrentFlagIteration.iterate features allowed safe target steps) := by
  exact congrArg (fun value => target - value) (_p2mH371 features allowed safe _)
open _root_.P2M661a572e renaming h563 → _p2mH563
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h397 (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate (fun index => e.symm ∘ features index)
      (fun index => (allowed index).map e.symm.toEmbedding) safe target steps =
      CurrentFlagIteration.iterate features allowed safe target steps := by
  induction steps with
  | zero => simp only [CurrentFlagIteration.iterate, AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    rw [_p2mH563, _p2mH563, ih, _p2mH406 e features allowed safe _]
open _root_.P2M661a572e renaming h397 → _p2mH397
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h403 (e : C' ≃ C) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) :
    regularIterate (fun index => e.symm ∘ features index) (fun index => (allowed index).map e.symm.toEmbedding)
      line safe atom spike steps = regularIterate features allowed line safe atom spike steps := by
  funext point
  simp only [regularIterate]
  rw [_p2mH393 e features allowed line spike,
    _p2mH397 e features allowed safe _ steps]
open _root_.P2M661a572e renaming h403 → _p2mH403
set_option maxRecDepth 8192
omit [DecidableEq Ω] in
theorem _root_.P2M661a572e.h401 (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (profile : Ω → ℚ) (point : Ω) :
    projectionQ (features ∘ e) (allowed ∘ e) profile point = projectionQ features allowed profile point := by
  simp only [projectionQ, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
  rw [Equiv.sum_comp e (fun index => featureProjectionQ (features index) (allowed index) profile point)]
open _root_.P2M661a572e renaming h401 → _p2mH401
set_option maxRecDepth 8192
omit [DecidableEq Ω] in
theorem _root_.P2M661a572e.h407 (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (profile : Ω → ℚ) :
    responseQ (features ∘ e) (allowed ∘ e) safe profile = responseQ features allowed safe profile := by
  funext point
  simp only [responseQ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, _p2mH401]
open _root_.P2M661a572e renaming h407 → _p2mH407
set_option maxRecDepth 8192
omit [DecidableEq Ω] in
theorem _root_.P2M661a572e.h394 (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (spike : Ω → ℚ) :
    offLineDefectQ (features ∘ e) (allowed ∘ e) (line ∘ e) spike = offLineDefectQ features allowed line spike := by
  funext point
  simp only [offLineDefectQ, Finset.sum_apply, Function.comp_apply, ite_apply, Pi.zero_apply]
  exact Equiv.sum_comp e (fun index => if line index then 0 else featureProjectionQ (features index) (allowed index) spike point)
open _root_.P2M661a572e renaming h394 → _p2mH394
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h398 (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (safe : Ω → Prop) (target : Ω → ℚ) (steps : ℕ) :
    CurrentFlagIteration.iterate (features ∘ e) (allowed ∘ e) safe target steps =
      CurrentFlagIteration.iterate features allowed safe target steps := by
  induction steps with
  | zero => simp only [CurrentFlagIteration.iterate, AFT.RationalNumerics.linearIteration]
  | succ steps ih =>
    rw [_p2mH563, _p2mH563, ih, _p2mH407 e features allowed safe _]
open _root_.P2M661a572e renaming h398 → _p2mH398
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h404 (e : I' ≃ I) (features : I → Ω → C) (allowed : I → Finset C)
    (line : I → Prop) (safe : Ω → Prop) (atom : ℚ) (spike : Ω → ℚ) (steps : ℕ) :
    regularIterate (features ∘ e) (allowed ∘ e) (line ∘ e) safe atom spike steps =
      regularIterate features allowed line safe atom spike steps := by
  funext point
  simp only [regularIterate]
  rw [_p2mH394 e features allowed line spike, _p2mH398 e features allowed safe _ steps]
open _root_.P2M661a572e renaming h404 → _p2mH404
end
open _root_.P2M661a572e renaming h389 → _p2mH389
open _root_.P2M661a572e renaming h391 → _p2mH391
open _root_.P2M661a572e renaming h393 → _p2mH393
open _root_.P2M661a572e renaming h394 → _p2mH394
open _root_.P2M661a572e renaming h397 → _p2mH397
open _root_.P2M661a572e renaming h398 → _p2mH398
open _root_.P2M661a572e renaming h400 → _p2mH400
open _root_.P2M661a572e renaming h401 → _p2mH401
open _root_.P2M661a572e renaming h403 → _p2mH403
open _root_.P2M661a572e renaming h404 → _p2mH404
open _root_.P2M661a572e renaming h406 → _p2mH406
open _root_.P2M661a572e renaming h407 → _p2mH407
open _root_.P2M661a572e renaming h563 → _p2mH563
end CurrentAFT.CurrentFlagReindex
open _root_.P2M661a572e renaming h389 → _p2mH389
open _root_.P2M661a572e renaming h391 → _p2mH391
open _root_.P2M661a572e renaming h393 → _p2mH393
open _root_.P2M661a572e renaming h394 → _p2mH394
open _root_.P2M661a572e renaming h397 → _p2mH397
open _root_.P2M661a572e renaming h398 → _p2mH398
open _root_.P2M661a572e renaming h400 → _p2mH400
open _root_.P2M661a572e renaming h401 → _p2mH401
open _root_.P2M661a572e renaming h403 → _p2mH403
open _root_.P2M661a572e renaming h404 → _p2mH404
open _root_.P2M661a572e renaming h406 → _p2mH406
open _root_.P2M661a572e renaming h407 → _p2mH407
open _root_.P2M661a572e renaming h563 → _p2mH563
end
open _root_.P2M661a572e renaming h401 → _p2mH401
open _root_.P2M661a572e renaming h394 → _p2mH394
open _root_.P2M661a572e renaming h397 → _p2mH397
open _root_.P2M661a572e renaming h406 → _p2mH406
open _root_.P2M661a572e renaming h398 → _p2mH398
open _root_.P2M661a572e renaming h404 → _p2mH404
open _root_.P2M661a572e renaming h407 → _p2mH407
open _root_.P2M661a572e renaming h391 → _p2mH391
open _root_.P2M661a572e renaming h393 → _p2mH393
open _root_.P2M661a572e renaming h403 → _p2mH403
open _root_.P2M661a572e renaming h389 → _p2mH389
open _root_.P2M661a572e renaming h400 → _p2mH400
section
namespace CurrentAFT.CurrentFlagMarkedArray
open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 300000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I]
set_option maxRecDepth 8192
omit [Fintype I] in
theorem _root_.P2M661a572e.h378 {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) :
    (fiber chartEquiv inputs allowed mark).card = (markedScaleSet inputs allowed mark).card := by
  simp only [fiber, Finset.card_map]
open _root_.P2M661a572e renaming h378 → _p2mH378
set_option maxRecDepth 8192
omit [Fintype I] in
theorem _root_.P2M661a572e.h379 {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) (point : Fin charts) :
    point ∈ fiber chartEquiv inputs allowed mark ↔
      (chartEquiv point).1 = mark ∧ (chartEquiv point).2.2 = 0 ∧
        markedScaleSafe inputs allowed mark (chartEquiv point).2.1 := by
  constructor
  · intro hm
    rcases Finset.mem_map.mp hm with ⟨chart, hchart, hpoint⟩
    rcases Finset.mem_map.mp hchart with ⟨scale, hs, he⟩
    have hc : chartEquiv point = (mark, scale, 0) := by
      rw [← hpoint, Equiv.toEmbedding_apply, Equiv.apply_symm_apply, ← he]
      rfl
    rw [hc]
    exact ⟨rfl, rfl, (Finset.mem_filter.mp hs).2⟩
  · rintro ⟨hb, hh, hs⟩
    apply Finset.mem_map.mpr
    refine ⟨chartEquiv point, ?_, chartEquiv.symm_apply_apply point⟩
    apply Finset.mem_map.mpr
    refine ⟨(chartEquiv point).2.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs⟩, ?_⟩
    apply Prod.ext
    · exact hb.symm
    · exact Prod.ext rfl hh.symm
open _root_.P2M661a572e renaming h379 → _p2mH379
set_option maxRecDepth 8192
omit [Fintype I] in
theorem _root_.P2M661a572e.h380 {charts : ℕ} (chartEquiv : Fin charts ≃ Chart F) (inputs : I → F × F)
    (allowed : I → Finset F) (mark : F) (point : Fin charts) :
    chartSpikeProgram charts (fiber chartEquiv inputs allowed mark) point =
      markedDensityQ inputs allowed mark (chartEquiv point) := by
  have hc : charts = Fintype.card F ^ 3 := by
    have hh := Fintype.card_congr chartEquiv
    simpa only [Fintype.card_fin, Chart, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using hh
  have hcast : (charts : ℚ) = (Fintype.card F : ℚ) ^ 3 := by exact_mod_cast hc
  rw [chartSpikeProgram, _p2mH378]
  have hm := _p2mH379 chartEquiv inputs allowed mark point
  simp only [markedDensityQ, markedSurvivalQ]
  by_cases hs : (chartEquiv point).1 = mark ∧ (chartEquiv point).2.2 = 0 ∧
      markedScaleSafe inputs allowed mark (chartEquiv point).2.1
  · rw [if_pos (hm.mpr hs), if_pos hs, mul_one, hcast, div_div_eq_mul_div]
    ring
  · rw [if_neg (fun h => hs (hm.mp h)), if_neg hs, mul_zero]
open _root_.P2M661a572e renaming h380 → _p2mH380
attribute [local instance] _root_.CurrentAFT.CurrentFlagMarkedArray.markedArrayPrime
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h377 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    (CurrentFlagProgram.current security baseline hbaseline mark atom ha0 haHalf).table =
      CurrentFlagProgram.table
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        mark atom := by
  rw [CurrentFlagProgram.current, CurrentFlagProgram.make]
open _root_.P2M661a572e renaming h377 → _p2mH377
end
open _root_.P2M661a572e renaming h377 → _p2mH377
open _root_.P2M661a572e renaming h378 → _p2mH378
open _root_.P2M661a572e renaming h379 → _p2mH379
open _root_.P2M661a572e renaming h380 → _p2mH380
end CurrentAFT.CurrentFlagMarkedArray
open _root_.P2M661a572e renaming h377 → _p2mH377
open _root_.P2M661a572e renaming h378 → _p2mH378
open _root_.P2M661a572e renaming h379 → _p2mH379
open _root_.P2M661a572e renaming h380 → _p2mH380
end
open _root_.P2M661a572e renaming h377 → _p2mH377
open _root_.P2M661a572e renaming h379 → _p2mH379
open _root_.P2M661a572e renaming h378 → _p2mH378
open _root_.P2M661a572e renaming h380 → _p2mH380
section
namespace CurrentAFT.CurrentFlagCompletion
open AFT AffineFlagCalibration ActualPublicLegCharge
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.CurrentFlagCompletion.completionTablePrime
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h352 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : PublicSeed security) :
    completionLaw security primary seed = (model security primary seed).model.joint := by
  have hm := _p2mH160 security (publicShift security primary seed)
    (by simpa only [legOffsetBound, add_sub_assoc] using publicShift_bound security primary seed)
    ((ZMod.finEquiv (Parameters.modulus security)) primary) (1 / 2 : ℚ) (by norm_num) (by norm_num)
  convert congrArg (fun law => law.joint) hm using 1
  norm_num [completionLaw, model]
  congr 2 <;> norm_num
  all_goals rfl
open _root_.P2M661a572e renaming h352 → _p2mH352
end
open _root_.P2M661a572e renaming h352 → _p2mH352
end CurrentAFT.CurrentFlagCompletion
open _root_.P2M661a572e renaming h352 → _p2mH352
end
open _root_.P2M661a572e renaming h352 → _p2mH352
section
namespace CurrentAFT.CurrentFlagFiniteResponse
open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIteration CurrentFlagReindex CurrentFlagMarkedArray
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h363 {charts colors inputsCount : ℕ}
    (chartEquiv : Fin charts ≃ Chart F) (colorEquiv : Fin colors ≃ F) (inputEquiv : Fin inputsCount ≃ I)
    (inputs : I → F × F) (allowed : I → Finset F) (mark : F) (atom : ℚ) (steps : ℕ) :
    finiteRegular chartEquiv colorEquiv inputEquiv inputs allowed mark atom steps =
      regularIterate (affineFeatures inputs) allowed (fun index => (inputs index).1 = 0)
        (affineSafe inputs allowed) atom (markedDensityQ inputs allowed mark) steps ∘ chartEquiv := by
  have hs : chartSpikeProgram charts (fiber chartEquiv inputs allowed mark) =
      markedDensityQ inputs allowed mark ∘ chartEquiv := funext (_p2mH380 chartEquiv inputs allowed mark)
  unfold finiteRegular
  rw [hs]
  change regularIterate
    ((fun index => colorEquiv.symm ∘ (affineFeatures inputs index ∘ chartEquiv)) ∘ inputEquiv)
    ((fun index => (allowed index).map colorEquiv.symm.toEmbedding) ∘ inputEquiv)
    ((fun index => (inputs index).1 = 0) ∘ inputEquiv)
    (affineSafe inputs allowed ∘ chartEquiv) atom (markedDensityQ inputs allowed mark ∘ chartEquiv) steps = _
  rw [_p2mH404 inputEquiv, _p2mH403 colorEquiv,
    _p2mH405 chartEquiv]
open _root_.P2M661a572e renaming h363 → _p2mH363
attribute [local instance] _root_.CurrentAFT.CurrentFlagFiniteResponse.finiteResponseZModDecidableEq
attribute [local instance] _root_.CurrentAFT.CurrentFlagFiniteResponse.finiteResponsePrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagFiniteResponse.finiteResponseNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h362 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (steps : ℕ)
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    |(currentRegular security baseline mark atom steps point : ℝ) -
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        mark atom (finiteChartEquiv (Parameters.modulus security) point) : ℝ)| ≤
      (1 / 4 : ℝ) ^ steps * ((4 / 3) *
        ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ
          (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
          (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
          (fun index => (protectedInputs (Parameters.sourceCutoff security - 1)
            (Parameters.modulus security) index).1 = 0)
          (markedDensityQ (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
            (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline) mark))‖) := by
  unfold currentRegular
  rw [_p2mH363]
  simpa only [Function.comp_apply, CurrentFlagProgram.regularDensity] using _p2mH372
    (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    (fun index => (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security) index).1 = 0)
    (affineSafe (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline))
    atom (markedDensityQ (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline) mark)
    (_p2mH367 security baseline hbaseline) steps (finiteChartEquiv (Parameters.modulus security) point)
open _root_.P2M661a572e renaming h362 → _p2mH362
end
open _root_.P2M661a572e renaming h362 → _p2mH362
open _root_.P2M661a572e renaming h363 → _p2mH363
end CurrentAFT.CurrentFlagFiniteResponse
open _root_.P2M661a572e renaming h362 → _p2mH362
open _root_.P2M661a572e renaming h363 → _p2mH363
end
open _root_.P2M661a572e renaming h362 → _p2mH362
open _root_.P2M661a572e renaming h363 → _p2mH363
namespace AFT.BoundaryCalibration.ProtectedChartSupport
end AFT.BoundaryCalibration.ProtectedChartSupport
namespace AFT.BoundaryCalibration.chartPaletteFeature
end AFT.BoundaryCalibration.chartPaletteFeature
namespace AFT.BoundaryCalibration.finiteAffineFeature
end AFT.BoundaryCalibration.finiteAffineFeature
namespace AFT.BoundaryCalibration.finiteAffineScale
end AFT.BoundaryCalibration.finiteAffineScale
namespace AFT.BoundaryCalibration.finiteProtectedFeatures
end AFT.BoundaryCalibration.finiteProtectedFeatures
namespace AFT.BoundaryCalibration.finiteProtectedMark
end AFT.BoundaryCalibration.finiteProtectedMark
namespace AFT.BoundaryCalibration.v7ProtectedPalettes
end AFT.BoundaryCalibration.v7ProtectedPalettes
section
namespace CurrentAFT.CurrentFlagFiniteCoordinates
open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIteration CurrentFlagFiniteResponse CurrentFlagMarkedArray
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000
variable (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
set_option maxRecDepth 8192
omit [Fact modulus.Prime] in
theorem _root_.P2M661a572e.h360 (baseline : ℤ) (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    finiteProtectedPalettes cutoff modulus 1 baseline index =
      (protectedPalettes cutoff modulus 1 baseline (finiteInputEquiv cutoff index)).map
        (ZMod.finEquiv modulus).toEquiv.symm.toEmbedding := by
  ext color
  rw [Finset.mem_map_equiv]
  exact _p2mH58 cutoff modulus 1 baseline index color
open _root_.P2M661a572e renaming h360 → _p2mH360
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h361 (baseline : ℤ) (point : Fin (modulus * (modulus * modulus))) :
    point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus 1 baseline) ↔
    affineSafe (protectedInputs cutoff modulus) (protectedPalettes cutoff modulus 1 baseline)
      (finiteChartEquiv modulus point) := by
  have hscale : finiteAffineScale modulus point ≠ 0 ↔ (finiteChartEquiv modulus point).2.1 ≠ 0 := by
    simp only [finiteAffineScale, ne_eq, RingEquiv.symm_apply_eq]
    rw [map_zero]
  simp only [finiteMarkedSafe, Finset.mem_filter, Finset.mem_univ, true_and, affineSafe, legalChart,
    Finset.mem_erase, and_true]
  rw [hscale]
  apply and_congr_right
  intro _
  constructor
  · intro h input
    let index := (finiteInputEquiv cutoff).symm input
    have hh := (_p2mH58 cutoff modulus 1 baseline index _).mp (h index)
    rw [_p2mH56] at hh
    simpa only [index, Equiv.apply_symm_apply, affineFeatures, protectedInputs] using hh
  · intro h index
    apply (_p2mH58 cutoff modulus 1 baseline index _).mpr
    rw [_p2mH56]
    exact h (finiteInputEquiv cutoff index)
open _root_.P2M661a572e renaming h361 → _p2mH361
set_option maxRecDepth 8192
omit [NeZero modulus] in
theorem _root_.P2M661a572e.h358 (hsize : 2 * cutoff < modulus)
    (index : Fin ((2 * cutoff + 1) * (2 * cutoff + 1))) :
    (((finiteInputEquiv cutoff index).1 : ℤ) : ZMod modulus) = 0 ↔
      ((finiteInputEquiv cutoff index).1 : ℤ) = 0 := by
  let value := (finiteInputEquiv cutoff index).1
  let zero := GaussianSource.windowZero cutoff
  constructor
  · intro hc
    have hz : value = zero := window_cast_injective cutoff modulus hsize
      (by simpa only [zero, GaussianSource.windowZero, Int.cast_zero] using hc)
    exact congrArg Subtype.val hz
  · intro hc
    rw [hc, Int.cast_zero]
open _root_.P2M661a572e renaming h358 → _p2mH358
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h359 (baseline : ℤ) (mark : ZMod modulus) (atom : ℚ) (steps : ℕ) :
    nativeRegular cutoff modulus baseline mark atom steps =
      finiteRegular (finiteChartEquiv modulus) (ZMod.finEquiv modulus).toEquiv (finiteInputEquiv cutoff)
        (protectedInputs cutoff modulus) (protectedPalettes cutoff modulus 1 baseline) mark atom steps := by
  have ha : finiteProtectedPalettes cutoff modulus 1 baseline =
      fun index => (protectedPalettes cutoff modulus 1 baseline (finiteInputEquiv cutoff index)).map
        (ZMod.finEquiv modulus).toEquiv.symm.toEmbedding := funext (_p2mH360 cutoff modulus baseline)
  have hs : (fun point => point ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
      (finiteProtectedPalettes cutoff modulus 1 baseline)) =
      (fun point => affineSafe (protectedInputs cutoff modulus) (protectedPalettes cutoff modulus 1 baseline)
        (finiteChartEquiv modulus point)) := funext (fun point => propext (_p2mH361 cutoff modulus baseline point))
  unfold nativeRegular finiteRegular
  rw [hs, ha]
  rfl
open _root_.P2M661a572e renaming h359 → _p2mH359
end
open _root_.P2M661a572e renaming h358 → _p2mH358
open _root_.P2M661a572e renaming h359 → _p2mH359
open _root_.P2M661a572e renaming h360 → _p2mH360
open _root_.P2M661a572e renaming h361 → _p2mH361
end CurrentAFT.CurrentFlagFiniteCoordinates
open _root_.P2M661a572e renaming h358 → _p2mH358
open _root_.P2M661a572e renaming h359 → _p2mH359
open _root_.P2M661a572e renaming h360 → _p2mH360
open _root_.P2M661a572e renaming h361 → _p2mH361
end
open _root_.P2M661a572e renaming h360 → _p2mH360
open _root_.P2M661a572e renaming h359 → _p2mH359
open _root_.P2M661a572e renaming h361 → _p2mH361
open _root_.P2M661a572e renaming h358 → _p2mH358
section
namespace CurrentAFT.CurrentFlagMetadataSemantics
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open AFT.BinaryArithmetic.RationalBits AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagMarkedArray CurrentFlagFiniteCoordinates CurrentFlagBinaryMetadata
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h381 : signedValue false [true] = 1 := by decide
open _root_.P2M661a572e renaming h381 → _p2mH381
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h382 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (hsize : 2 * cutoff < modulus) (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus) :
    maskSet (build cutoff modulus false baselineSign [true] baseline mark).value.fiber =
      fiber (finiteChartEquiv modulus) (protectedInputs cutoff modulus)
        (protectedPalettes cutoff modulus 1 (signedValue baselineSign baseline)) ((ZMod.finEquiv modulus) mark) := by
  ext point
  simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [_p2mH341, _p2mH379]
  have hc := _p2mH344 modulus point
  have hb : (coordinates modulus point).value.1 = mark ↔
      (finiteChartEquiv modulus point).1 = (ZMod.finEquiv modulus) mark := by
    have hfirst := congrArg Prod.fst hc
    rw [← hfirst]
    exact (ZMod.finEquiv modulus).injective.eq_iff.symm
  have ht : (coordinates modulus point).value.2.2 = 0 ↔ (finiteChartEquiv modulus point).2.2 = 0 := by
    have hlast := congrArg (fun word => word.2.2) hc
    change (ZMod.finEquiv modulus) (coordinates modulus point).value.2.2 =
      (finiteChartEquiv modulus point).2.2 at hlast
    rw [← hlast]
    exact (map_eq_zero_iff (ZMod.finEquiv modulus) (ZMod.finEquiv modulus).injective).symm
  have hs : finiteAffineScale modulus point ≠ 0 ↔ (finiteChartEquiv modulus point).2.1 ≠ 0 := by
    simp only [finiteAffineScale, ne_eq, RingEquiv.symm_apply_eq]
    rw [map_zero]
  rw [hb, ht, hs, _p2mH381]
  constructor
  · rintro ⟨hb, hs, ht, hall⟩
    refine ⟨hb, ht, hs, ?_⟩
    intro input hfirst
    let index := (finiteInputEquiv cutoff).symm input
    have hi : ((finiteInputEquiv cutoff index).1 : ℤ) ≠ 0 := by
      intro hz
      apply hfirst
      change (((input.1 : ℤ) : ZMod modulus)) = 0
      have hz' : (input.1 : ℤ) = 0 := by simpa only [index, Equiv.apply_symm_apply] using hz
      rw [hz', Int.cast_zero]
    have hallowed := (_p2mH58 cutoff modulus 1
      (signedValue baselineSign baseline) index _).mp (hall index hi)
    rw [_p2mH56] at hallowed
    simpa only [index, Equiv.apply_symm_apply, feature, hb, ht, zero_mul, add_zero, protectedInputs] using hallowed
  · rintro ⟨hb, ht, hs, hall⟩
    refine ⟨hb, hs, ht, ?_⟩
    intro index hi
    apply (_p2mH58 cutoff modulus 1 (signedValue baselineSign baseline) index _).mpr
    rw [_p2mH56]
    have hfirst : (protectedInputs cutoff modulus (finiteInputEquiv cutoff index)).1 ≠ 0 := by
      exact (not_congr (_p2mH358 cutoff modulus hsize index)).mpr hi
    have hallowed := hall (finiteInputEquiv cutoff index) hfirst
    simpa only [feature, hb, ht, zero_mul, add_zero, protectedInputs] using hallowed
open _root_.P2M661a572e renaming h382 → _p2mH382
end
open _root_.P2M661a572e renaming h381 → _p2mH381
open _root_.P2M661a572e renaming h382 → _p2mH382
end CurrentAFT.CurrentFlagMetadataSemantics
open _root_.P2M661a572e renaming h381 → _p2mH381
open _root_.P2M661a572e renaming h382 → _p2mH382
end
open _root_.P2M661a572e renaming h381 → _p2mH381
open _root_.P2M661a572e renaming h382 → _p2mH382
section
namespace CurrentAFT.CurrentFlagTargetNorm
open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentRationalFlagLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
variable {F I : Type*} [Field F] [Fintype F] [Fintype I]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h409 (inputs : I → F × F) (allowed : I → Finset F) (mark : F)
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hbudget : affineDeletionBudget allowed ≤ δ) (atom : ℚ)
    (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ (affineFeatures inputs) allowed
      (fun index => (inputs index).1 = 0) (markedDensityQ inputs allowed mark))‖ ≤ 1 + 2 * Fintype.card I := by
  have hδ1 : δ < 1 := by linarith
  have hsurvival : 0 < markedSurvival inputs allowed mark := by
    have hl := markedSurvival_lower inputs allowed mark
    linarith
  let marked := markedChartLaw inputs allowed mark hsurvival
  have hspike : realVector (markedDensityQ inputs allowed mark) = AffineFlagCalibration.uniformDensity marked :=
    markedDensityQ_cast inputs allowed mark hsurvival
  have hsallowed (index : I) (hi : ¬ (inputs index).1 = 0) (chart : Chart F)
      (hc : affineFeatures inputs index chart ∉ allowed index) : AffineFlagCalibration.uniformDensity marked chart = 0 := by
    have hz := markedChartLaw_support inputs allowed mark hsurvival chart
      (by rintro ⟨_, _, _, hh⟩; exact hc (hh index hi))
    simp only [marked, AffineFlagCalibration.uniformDensity, hz, mul_zero]
  have hsbound (index : I) (hi : ¬ (inputs index).1 = 0) (color : F) :
      conditional (FiniteDist.uniform (Chart F)) (affineFeatures inputs index) (AffineFlagCalibration.uniformDensity marked) color ≤
        1 / (1 - δ) := markedDensity_bound inputs allowed mark δ hδ1 hbudget hsurvival index hi color
  have hd := (offLineDefect_bounds (FiniteDist.uniform (Chart F)) (affineFeatures inputs) allowed
    (fun index => (inputs index).1 = 0) (AffineFlagCalibration.uniformDensity marked) (AffineFlagCalibration.uniformDensity_mean marked)
    (AffineFlagCalibration.uniformDensity_nonneg marked) hsallowed δ hδ0 hδ1 hsbound).1
  have hodds0 : 0 ≤ (atom : ℝ) / (1 - (atom : ℝ)) := div_nonneg ha0 (by linarith)
  have hodds1 : (atom : ℝ) / (1 - (atom : ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - (atom : ℝ)), one_mul]
    linarith
  have ht : realVector (1 - (atom / (1 - atom)) • offLineDefectQ (affineFeatures inputs) allowed
      (fun index => (inputs index).1 = 0) (markedDensityQ inputs allowed mark)) =
      1 - ((atom : ℝ) / (1 - (atom : ℝ))) • offLineDefect (FiniteDist.uniform (Chart F))
        (affineFeatures inputs) allowed (fun index => (inputs index).1 = 0) (AffineFlagCalibration.uniformDensity marked) := by
    have hc := offLineDefectQ_cast (affineFeatures inputs) allowed (fun index => (inputs index).1 = 0)
      (markedDensityQ inputs allowed mark)
    rw [hspike] at hc
    funext chart
    have hh := congrFun hc chart
    simp only [realVector, Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul, Rat.cast_sub,
      Rat.cast_mul, Rat.cast_div, Rat.cast_one] at hh ⊢
    rw [hh]
  rw [ht]
  apply (norm_sub_le _ _).trans
  rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg hodds0]
  have hden : (Fintype.card I : ℝ) / (1 - δ) ≤ 2 * Fintype.card I := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 - δ)]
    nlinarith [mul_le_mul_of_nonneg_left hδhalf (Nat.cast_nonneg (Fintype.card I) : (0 : ℝ) ≤ _)]
  have ho := mul_le_mul_of_nonneg_right hodds1
    (norm_nonneg (offLineDefect (FiniteDist.uniform (Chart F)) (affineFeatures inputs) allowed
      (fun index => (inputs index).1 = 0) (AffineFlagCalibration.uniformDensity marked)))
  nlinarith
open _root_.P2M661a572e renaming h409 → _p2mH409
attribute [local instance] _root_.CurrentAFT.CurrentFlagTargetNorm.targetNormPrime
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h411 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) :
    ‖realVector (1 - (atom / (1 - atom)) • offLineDefectQ
      (affineFeatures (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security)))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
      (fun index => (protectedInputs (Parameters.sourceCutoff security - 1)
        (Parameters.modulus security) index).1 = 0)
      (markedDensityQ (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline) mark))‖ ≤
      1 + 2 * ((2 * (Parameters.sourceCutoff security - 1) + 1) ^ 2 : ℕ) := by
  have hb := leg_budget_conditions security
  have hhalf : legDeletionUpper security ≤ 1 / 2 := by
    have hn : (0 : ℝ) ≤ Fintype.card (ProtectedInput security) := Nat.cast_nonneg _
    have hh := hb.2.2.1
    nlinarith [mul_nonneg hn hb.1]
  simpa only [protectedInputs_card] using _p2mH409
    (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
    (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
    mark (legDeletionUpper security) hb.1 hhalf
    (protectedPalette_current_budget security baseline hbaseline) atom ha0 haHalf
open _root_.P2M661a572e renaming h411 → _p2mH411
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h412 (inputs bits : ℕ) :
    (1 / 4 : ℝ) ^ (bits + (4 * inputs + 4)) * ((4 / 3) * (1 + 2 * inputs)) ≤ 1 / (2 : ℝ) ^ bits := by
  let extra := 4 * inputs + 4
  have hcoeff : (4 / 3 : ℝ) * (1 + 2 * inputs) ≤ extra := by dsimp [extra]; push_cast; nlinarith
  have hpower : (extra : ℝ) ≤ (2 : ℝ) ^ extra := by exact_mod_cast (Nat.lt_two_pow_self (n := extra)).le
  calc
    (1 / 4 : ℝ) ^ (bits + extra) * ((4 / 3) * (1 + 2 * inputs)) ≤
        (1 / 4 : ℝ) ^ (bits + extra) * (2 : ℝ) ^ extra :=
      mul_le_mul_of_nonneg_left (hcoeff.trans hpower) (by positivity)
    _ = (1 / 4 : ℝ) ^ bits * (1 / 2 : ℝ) ^ extra := by
      rw [pow_add, mul_assoc, ← mul_pow]
      norm_num
    _ ≤ (1 / 4 : ℝ) ^ bits := mul_le_of_le_one_right (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    _ ≤ (1 / 2 : ℝ) ^ bits := pow_le_pow_left₀ (by norm_num) (by norm_num) bits
    _ = 1 / (2 : ℝ) ^ bits := by simp only [div_pow, one_pow]
open _root_.P2M661a572e renaming h412 → _p2mH412
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h410 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ legOffsetBound security) (mark : ZMod (Parameters.modulus security))
    (atom : ℚ) (ha0 : 0 ≤ (atom : ℝ)) (haHalf : (atom : ℝ) ≤ 1 / 2) (bits : ℕ)
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    |(CurrentFlagFiniteResponse.currentRegular security baseline mark atom
        (precisionSteps (Parameters.sourceCutoff security - 1) bits) point : ℝ) -
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        mark atom (finiteChartEquiv (Parameters.modulus security) point) : ℝ)| ≤ 1 / (2 : ℝ) ^ bits := by
  apply (_p2mH362 security baseline hbaseline mark atom
    (precisionSteps (Parameters.sourceCutoff security - 1) bits) point).trans
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (_p2mH411 security baseline hbaseline mark atom ha0 haHalf)
      (by norm_num : (0 : ℝ) ≤ 4 / 3)) (by positivity))
  exact _p2mH412 ((2 * (Parameters.sourceCutoff security - 1) + 1) ^ 2) bits
open _root_.P2M661a572e renaming h410 → _p2mH410
end
open _root_.P2M661a572e renaming h409 → _p2mH409
open _root_.P2M661a572e renaming h410 → _p2mH410
open _root_.P2M661a572e renaming h411 → _p2mH411
open _root_.P2M661a572e renaming h412 → _p2mH412
end CurrentAFT.CurrentFlagTargetNorm
open _root_.P2M661a572e renaming h409 → _p2mH409
open _root_.P2M661a572e renaming h410 → _p2mH410
open _root_.P2M661a572e renaming h411 → _p2mH411
open _root_.P2M661a572e renaming h412 → _p2mH412
end
open _root_.P2M661a572e renaming h409 → _p2mH409
open _root_.P2M661a572e renaming h410 → _p2mH410
open _root_.P2M661a572e renaming h411 → _p2mH411
open _root_.P2M661a572e renaming h412 → _p2mH412
namespace CurrentAFT.CurrentFlagBinary
end CurrentAFT.CurrentFlagBinary
namespace CurrentAFT.CurrentFlagBinaryMetadata
end CurrentAFT.CurrentFlagBinaryMetadata
namespace CurrentAFT.CurrentFlagBinaryMetadata.build
end CurrentAFT.CurrentFlagBinaryMetadata.build
namespace CurrentAFT.CurrentFlagIteration.iterationMatrix
end CurrentAFT.CurrentFlagIteration.iterationMatrix
namespace CurrentAFT.CurrentFlagMetadataSemantics
end CurrentAFT.CurrentFlagMetadataSemantics
section
namespace CurrentAFT.CurrentFlagPublicProgram
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagFiniteCoordinates CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h385 : half.data.decode = (1 / 2 : ℚ) := by
  norm_num [half, quotient_value, one_value, ofCounter_value]
open _root_.P2M661a572e renaming h385 → _p2mH385
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h384 (cutoff modulus : ℕ) [NeZero modulus] [Fact modulus.Prime]
    (hsize : 2 * cutoff < modulus) (baselineSign : Bool) (baseline : List Bool) (mark : Fin modulus)
    (steps : ℕ) (point : Fin (modulus * (modulus * modulus))) :
    ((evaluate cutoff modulus baselineSign baseline mark steps).data.get point).decode =
      nativeRegular cutoff modulus (signedValue baselineSign baseline) ((ZMod.finEquiv modulus) mark)
        (1 / 2) steps point := by
  let metadata := build cutoff modulus false baselineSign [true] baseline mark
  have hf : (fun index point => (metadata.value.feature.get index).get point) = finiteProtectedFeatures cutoff modulus :=
    _p2mH340 cutoff modulus false baselineSign [true] baseline mark
  have ha : (fun index => maskSet (metadata.value.allowed.get index)) =
      finiteProtectedPalettes cutoff modulus 1 (signedValue baselineSign baseline) := by
    funext index
    ext color
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (_p2mH339 cutoff modulus false baselineSign [true] baseline mark index color).trans
      (by rw [_p2mH381])
  have hl : (fun index => metadata.value.line.get index = true) =
      (fun index => (((finiteInputEquiv cutoff index).1 : ℤ) : ZMod modulus) = 0) := by
    funext index
    apply propext
    exact (_p2mH342 cutoff modulus false baselineSign [true] baseline mark index).trans
      (_p2mH358 cutoff modulus hsize index).symm
  have hs : (fun input => metadata.value.safe.get input = true) =
      (fun input => input ∈ finiteMarkedSafe (finiteProtectedFeatures cutoff modulus) (finiteAffineScale modulus)
        (finiteProtectedPalettes cutoff modulus 1 (signedValue baselineSign baseline))) := by
    funext input
    apply propext
    exact (_p2mH343 cutoff modulus false baselineSign [true] baseline mark input).trans
      (by rw [_p2mH381])
  have hsp := _p2mH382 cutoff modulus hsize baselineSign baseline mark
  change ((CurrentFlagBinary.regular metadata.value.feature metadata.value.allowed metadata.value.line
    metadata.value.safe metadata.value.fiber half.data steps).data.get point).decode = _
  rw [_p2mH333, _p2mH324, _p2mH385, hf, ha, hl, hs, hsp]
  rfl
open _root_.P2M661a572e renaming h384 → _p2mH384
attribute [local instance] _root_.CurrentAFT.CurrentFlagPublicProgram.publicProgramPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagPublicProgram.publicProgramNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h383 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (bits : ℕ)
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    |(((evaluate (Parameters.sourceCutoff security - 1) (Parameters.modulus security) baselineSign baseline mark
        (CurrentFlagTargetNorm.precisionSteps (Parameters.sourceCutoff security - 1) bits)).data.get point).decode : ℝ) -
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1
          (signedValue baselineSign baseline)) ((ZMod.finEquiv (Parameters.modulus security)) mark)
        (1 / 2) (finiteChartEquiv (Parameters.modulus security) point) : ℝ)| ≤ 1 / (2 : ℝ) ^ bits := by
  rw [_p2mH384 _ _ (AffineFlagCalibration.leg_input_separation security), _p2mH359]
  exact _p2mH410 security (signedValue baselineSign baseline) hbaseline
    ((ZMod.finEquiv (Parameters.modulus security)) mark) (1 / 2) (by norm_num) (by norm_num) bits point
open _root_.P2M661a572e renaming h383 → _p2mH383
end
open _root_.P2M661a572e renaming h383 → _p2mH383
open _root_.P2M661a572e renaming h384 → _p2mH384
end CurrentAFT.CurrentFlagPublicProgram
open _root_.P2M661a572e renaming h383 → _p2mH383
open _root_.P2M661a572e renaming h384 → _p2mH384
open _root_.P2M661a572e renaming h385 → _p2mH385
end
open _root_.P2M661a572e renaming h384 → _p2mH384
open _root_.P2M661a572e renaming h385 → _p2mH385
open _root_.P2M661a572e renaming h383 → _p2mH383
section
namespace CurrentAFT.CurrentFlagIdealArrays
open AFT AFT.BoundaryCalibration AffineFlagCalibration CurrentFlagMarkedArray
open CurrentRationalFlagLaw AFT.BinaryArithmetic
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000
attribute [local instance] _root_.CurrentAFT.CurrentFlagIdealArrays.idealArrayPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagIdealArrays.idealArrayNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h365 (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    (regularLaw security baseline hbaseline mark).weight point =
      (CurrentFlagProgram.regularDensity
        (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
        (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
        ((ZMod.finEquiv (Parameters.modulus security)) mark) (1 / 2)
        (finiteChartEquiv (Parameters.modulus security) point) : ℝ) /
      (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)) := by
  rw [regularLaw, FiniteDist.map_equiv_weight]
  have ht := (model security baseline hbaseline mark).table_cast
    (false, finiteChartEquiv (Parameters.modulus security) point)
  change ((CurrentFlagProgram.current security baseline hbaseline _ (1 / 2) _ _).table _ : ℝ) = _ at ht
  rw [_p2mH377, CurrentFlagProgram.table] at ht
  rw [(model security baseline hbaseline mark).model.decomposition] at ht
  norm_num only [Bool.false_eq_true, if_false, Rat.cast_sub, Rat.cast_one, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] at ht
  have hc := Fintype.card_congr (finiteChartEquiv (Parameters.modulus security))
  simp only [Fintype.card_fin] at hc
  rw [← hc] at ht
  simp only [Equiv.symm_symm, Nat.cast_mul, div_eq_mul_inv] at ht ⊢
  nlinarith [ht]
open _root_.P2M661a572e renaming h365 → _p2mH365
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h364 (security : ℕ) (baseline : ℤ) (hbaseline : |baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    (markedLaw security baseline hbaseline mark).weight point =
      (chartSpikeProgram (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))
        (fiber (finiteChartEquiv (Parameters.modulus security))
          (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
          (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1 baseline)
          ((ZMod.finEquiv (Parameters.modulus security)) mark)) point : ℝ) /
      (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)) := by
  rw [markedLaw, FiniteDist.map_equiv_weight, _p2mH380]
  have ht := (model security baseline hbaseline mark).table_cast
    (true, finiteChartEquiv (Parameters.modulus security) point)
  change ((CurrentFlagProgram.current security baseline hbaseline _ (1 / 2) _ _).table _ : ℝ) = _ at ht
  rw [_p2mH377, CurrentFlagProgram.table] at ht
  rw [(model security baseline hbaseline mark).model.decomposition] at ht
  norm_num only [if_true, Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_one, Rat.cast_ofNat] at ht
  have hc := Fintype.card_congr (finiteChartEquiv (Parameters.modulus security))
  simp only [Fintype.card_fin] at hc
  rw [← hc] at ht
  simp only [Equiv.symm_symm, Nat.cast_mul, div_eq_mul_inv] at ht ⊢
  nlinarith [ht]
open _root_.P2M661a572e renaming h364 → _p2mH364
end
open _root_.P2M661a572e renaming h364 → _p2mH364
open _root_.P2M661a572e renaming h365 → _p2mH365
end CurrentAFT.CurrentFlagIdealArrays
open _root_.P2M661a572e renaming h364 → _p2mH364
open _root_.P2M661a572e renaming h365 → _p2mH365
end
open _root_.P2M661a572e renaming h365 → _p2mH365
open _root_.P2M661a572e renaming h364 → _p2mH364
section
namespace CurrentAFT.CurrentFlagWeightArray
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits CurrentFlagPublicProgram CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h413 {charts : ℕ} (raw : Vector RationalBits charts) (point : Fin charts) :
    (entry raw point).data.decode = (raw.get point).decode / charts := by
  simp only [entry, quotient_value, readVector_value, ofCounter_value]
open _root_.P2M661a572e renaming h413 → _p2mH413
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h416 {charts : ℕ} (raw : Vector RationalBits charts) (point : Fin charts) :
    ((scale raw).data.get point).decode = (raw.get point).decode / charts := by
  simp only [scale, buildArray_get, _p2mH413]
open _root_.P2M661a572e renaming h416 → _p2mH416
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagWeightArray.flagWeightPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagWeightArray.flagWeightNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h415 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (bits : ℕ) :
    (∑ point, |(((regularWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      baselineSign baseline mark (CurrentFlagTargetNorm.precisionSteps (Parameters.sourceCutoff security - 1) bits)).data.get point).decode : ℝ) -
      (CurrentFlagIdealArrays.regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ bits := by
  let N := Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)
  have hN : (0 : ℝ) < N := by dsimp [N]; exact_mod_cast Nat.mul_pos (NeZero.pos _) (Nat.mul_pos (NeZero.pos _) (NeZero.pos _))
  have hp (point : Fin N) :
      |(((regularWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark (CurrentFlagTargetNorm.precisionSteps (Parameters.sourceCutoff security - 1) bits)).data.get point).decode : ℝ) -
        (CurrentFlagIdealArrays.regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point| ≤
      (1 / (2 : ℝ) ^ bits) / N := by
    have he := _p2mH383 security baselineSign baseline hbaseline mark bits point
    simp only [regularWeights, _p2mH416, Rat.cast_div, Rat.cast_natCast, _p2mH365]
    simp only [← Nat.cast_mul]
    rw [← sub_div, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right he hN.le
  have hsum : (∑ _point : Fin N, (1 / (2 : ℝ) ^ bits) / N) = 1 / (2 : ℝ) ^ bits := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hN.ne']
  exact (Finset.sum_le_sum (fun point _ => hp point)).trans_eq hsum
open _root_.P2M661a572e renaming h415 → _p2mH415
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h414 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security))) :
    (((markedWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      baselineSign baseline mark).data.get point).decode : ℝ) =
      (CurrentFlagIdealArrays.markedLaw security (signedValue baselineSign baseline) hbaseline mark).weight point := by
  simp only [markedWeights, _p2mH416, buildArray_get, _p2mH12, Rat.cast_div, Rat.cast_natCast]
  rw [_p2mH382 _ _ (AffineFlagCalibration.leg_input_separation security),
    _p2mH364]
  push_cast
  rfl
open _root_.P2M661a572e renaming h414 → _p2mH414
end
open _root_.P2M661a572e renaming h414 → _p2mH414
open _root_.P2M661a572e renaming h415 → _p2mH415
end CurrentAFT.CurrentFlagWeightArray
open _root_.P2M661a572e renaming h413 → _p2mH413
open _root_.P2M661a572e renaming h414 → _p2mH414
open _root_.P2M661a572e renaming h415 → _p2mH415
open _root_.P2M661a572e renaming h416 → _p2mH416
end
open _root_.P2M661a572e renaming h415 → _p2mH415
open _root_.P2M661a572e renaming h416 → _p2mH416
open _root_.P2M661a572e renaming h413 → _p2mH413
open _root_.P2M661a572e renaming h414 → _p2mH414
section
namespace CurrentAFT.CurrentFlagDraw
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h357 {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (bits : ℕ) (word : Fin (bits + charts + 1) → Fin 2) :
    (draw raw mask bits word).value = legalChartIndex charts (maskSet mask)
      (RationalPaletteSampler.draw charts (NeZero.pos _) (fun point => (raw.get point).decode) bits word) := by
  have hp : (⟨(binaryPositiveFinDraw raw bits word).value, binaryPositiveFinDraw_lt raw bits word⟩ : Fin charts) =
      RationalPaletteSampler.draw charts (NeZero.pos _) (fun point => (raw.get point).decode) bits word := by
    apply Fin.ext
    exact _p2mH27 raw bits word
  unfold draw
  try dsimp only
  rw [_p2mH22 _ _ (maskSet mask) (fun _ => by
    simp only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and]), hp]
open _root_.P2M661a572e renaming h357 → _p2mH357
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h356 {charts : ℕ} [NeZero charts] (raw : Vector RationalBits charts) (mask : Vector Bool charts)
    (reference : FiniteDist (Fin charts))
    (hsupport : ∀ point, point ∉ maskSet mask → reference.weight point = 0)
    (error : ℝ) (herror : (∑ point, |((raw.get point).decode : ℝ) - reference.weight point|) ≤ error)
    (hsmall : error ≤ 1 / 2) (bits : ℕ) :
    (∑ point, |((FiniteDist.uniform (Fin (bits + charts + 1) → Fin 2)).map
      (fun word => (draw raw mask bits word).value)).weight point - reference.weight point|) ≤
      1 / (2 : ℝ) ^ bits + 4 * error := by
  have hp := _p2mH141 charts (NeZero.pos _) (fun point => (raw.get point).decode)
    bits reference error herror hsmall
  have hl := _p2mH59 charts (maskSet mask)
    ((FiniteDist.uniform (Fin (bits + charts + 1) → Fin 2)).map
      (RationalPaletteSampler.draw charts (NeZero.pos _) (fun point => (raw.get point).decode) bits))
    reference hsupport
  rw [FiniteDist.map_map] at hl
  simpa only [Function.comp_def, _p2mH357] using hl.trans hp
open _root_.P2M661a572e renaming h356 → _p2mH356
end
open _root_.P2M661a572e renaming h356 → _p2mH356
end CurrentAFT.CurrentFlagDraw
open _root_.P2M661a572e renaming h356 → _p2mH356
open _root_.P2M661a572e renaming h357 → _p2mH357
end
open _root_.P2M661a572e renaming h357 → _p2mH357
open _root_.P2M661a572e renaming h356 → _p2mH356
section
namespace CurrentAFT.CurrentFlagReferenceSupport
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AffineFlagCalibration CurrentRationalFlagLaw
open CurrentFlagIdealArrays CurrentFlagBinaryMetadata CurrentFlagFiniteCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 400000
attribute [local instance] _root_.CurrentAFT.CurrentFlagReferenceSupport.referenceSupportPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagReferenceSupport.referenceSupportNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h387 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)))
    (hnot : point ∉ maskSet (build (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      false baselineSign [true] baseline mark).value.safe) :
    (regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point = 0 := by
  rw [regularLaw, FiniteDist.map_equiv_weight]
  simp only [Equiv.symm_symm]
  apply (model security (signedValue baselineSign baseline) hbaseline mark).model.regular_support
  intro hs
  have hs' : affineSafe (protectedInputs (Parameters.sourceCutoff security - 1) (Parameters.modulus security))
      (protectedPalettes (Parameters.sourceCutoff security - 1) (Parameters.modulus security) 1
        (signedValue baselineSign baseline)) (finiteChartEquiv (Parameters.modulus security) point) := by
    simpa only [affineSafe, legalChart, affineFeatures, Finset.mem_erase, Finset.mem_univ, and_true] using hs
  have hm := (_p2mH361 (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
    (signedValue baselineSign baseline) point).mpr hs'
  have hb := (_p2mH343 (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
    false baselineSign [true] baseline mark point).mpr
      (by simpa only [_p2mH381] using hm)
  exact hnot (by simpa only [maskSet, Finset.mem_filter, Finset.mem_univ, true_and] using hb)
open _root_.P2M661a572e renaming h387 → CurrentAFT.CurrentFlagReferenceSupport.regular_support
open _root_.P2M661a572e renaming h387 → _p2mH387
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h386 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ legOffsetBound security)
    (mark : Fin (Parameters.modulus security))
    (point : Fin (Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security)))
    (hnot : point ∉ maskSet (build (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
      false baselineSign [true] baseline mark).value.fiber) :
    (markedLaw security (signedValue baselineSign baseline) hbaseline mark).weight point = 0 := by
  rw [_p2mH382 _ _ (leg_input_separation security)] at hnot
  rw [_p2mH364, chartSpikeProgram, if_neg hnot, Rat.cast_zero, zero_div]
open _root_.P2M661a572e renaming h386 → _p2mH386
end
open _root_.P2M661a572e renaming h386 → _p2mH386
open _root_.P2M661a572e renaming h387 → CurrentAFT.CurrentFlagReferenceSupport.regular_support
open _root_.P2M661a572e renaming h387 → _p2mH387
end CurrentAFT.CurrentFlagReferenceSupport
open _root_.P2M661a572e renaming h386 → _p2mH386
open _root_.P2M661a572e renaming h387 → CurrentAFT.CurrentFlagReferenceSupport.regular_support
open _root_.P2M661a572e renaming h387 → _p2mH387
end
open _root_.P2M661a572e renaming h387 → CurrentAFT.CurrentFlagReferenceSupport.regular_support
open _root_.P2M661a572e renaming h387 → _p2mH387
open _root_.P2M661a572e renaming h386 → _p2mH386
section
namespace CurrentAFT.CurrentFlagBranchDraw
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBinaryMetadata CurrentFlagWeightArray
open scoped BigOperators
set_option maxHeartbeats 500000
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagBranchDraw.branchDrawPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagBranchDraw.branchDrawNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h346 (bits : ℕ) (hbits : 1 ≤ bits) : 1 / (2 : ℝ) ^ bits ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ (2 : ℝ) ^ bits := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hbits
  exact one_div_le_one_div_of_le (by norm_num) hp
open _root_.P2M661a572e renaming h346 → _p2mH346
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h348 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((FiniteDist.uniform (Fin (drawBits + Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security) + 1) → Fin 2)).map
      (fun word => (regular (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value)).weight point -
      (CurrentFlagIdealArrays.regularLaw security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  exact _p2mH356 _ _ _ (_p2mH387 security baselineSign baseline hbaseline mark)
    (1 / (2 : ℝ) ^ precisionBits) (_p2mH415 security baselineSign baseline hbaseline mark precisionBits)
    (_p2mH346 precisionBits hprecision) drawBits
open _root_.P2M661a572e renaming h348 → _p2mH348
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h347 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (drawBits : ℕ) :
    (∑ point, |((FiniteDist.uniform (Fin (drawBits + Parameters.modulus security * (Parameters.modulus security * Parameters.modulus security) + 1) → Fin 2)).map
      (fun word => (marked (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark drawBits word).value)).weight point -
      (CurrentFlagIdealArrays.markedLaw security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits := by
  have he := _p2mH356
    (markedWeights (Parameters.sourceCutoff security - 1) (Parameters.modulus security) baselineSign baseline mark).data
    (build (Parameters.sourceCutoff security - 1) (Parameters.modulus security) false baselineSign [true] baseline mark).value.fiber
    (CurrentFlagIdealArrays.markedLaw security (signedValue baselineSign baseline) hbaseline mark)
    (_p2mH386 security baselineSign baseline hbaseline mark) 0
    (by simp only [_p2mH414 security baselineSign baseline hbaseline mark, sub_self, abs_zero, Finset.sum_const_zero, le_refl])
    (by norm_num) drawBits
  simpa only [marked, mul_zero, add_zero] using he
open _root_.P2M661a572e renaming h347 → _p2mH347
end
open _root_.P2M661a572e renaming h346 → _p2mH346
open _root_.P2M661a572e renaming h347 → _p2mH347
open _root_.P2M661a572e renaming h348 → _p2mH348
end CurrentAFT.CurrentFlagBranchDraw
open _root_.P2M661a572e renaming h346 → _p2mH346
open _root_.P2M661a572e renaming h347 → _p2mH347
open _root_.P2M661a572e renaming h348 → _p2mH348
end
open _root_.P2M661a572e renaming h348 → _p2mH348
open _root_.P2M661a572e renaming h346 → _p2mH346
open _root_.P2M661a572e renaming h347 → _p2mH347
section
namespace CurrentAFT.CurrentFlagJointDraw
open AFT AFT.BoundaryCalibration AFT.RationalNumerics AFT.BinaryArithmetic
open AFT.BinaryArithmetic.RationalBits AFT.RationalRejectionProgram
open CurrentFlagBranchDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h374 (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value =
      (word.1, if word.1 then (marked cutoff modulus baselineSign baseline mark drawBits word.2).value
        else (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word.2).value) := by
  cases h : word.1 <;> simp only [draw, h, Bool.false_eq_true, if_false, if_true]
open _root_.P2M661a572e renaming h374 → _p2mH374
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h373 (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) :
    (tapeLaw modulus drawBits).map (fun word => (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value) =
      FiniteDist.joint (FiniteDist.uniform Bool) (branchLaw cutoff modulus baselineSign baseline mark precisionBits drawBits) := by
  simp only [_p2mH374, tapeLaw]
  have h := _p2mH86 (FiniteDist.uniform Bool)
    (FiniteDist.uniform (Fin (drawBits + modulus * (modulus * modulus) + 1) → Fin 2)) id
    (fun flag word => if flag then (marked cutoff modulus baselineSign baseline mark drawBits word).value
      else (regular cutoff modulus baselineSign baseline mark precisionBits drawBits word).value)
  have hid : (FiniteDist.uniform Bool).map id = FiniteDist.uniform Bool := by
    ext flag
    simp
  unfold branchLaw
  simpa only [hid, id_eq] using h
open _root_.P2M661a572e renaming h373 → _p2mH373
attribute [local instance] _root_.CurrentAFT.CurrentFlagJointDraw.jointDrawPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagJointDraw.jointDrawNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h376 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value)).weight point -
      (indexedReference security (signedValue baselineSign baseline) hbaseline mark).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  rw [_p2mH373]
  have h := _p2mH83 (FiniteDist.uniform Bool) (FiniteDist.uniform Bool)
    (branchLaw (Parameters.sourceCutoff security - 1) (Parameters.modulus security) baselineSign baseline mark precisionBits drawBits)
    (referenceBranches security (signedValue baselineSign baseline) hbaseline mark)
    (1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits)) (fun flag => ?_)
  · simpa only [indexedReference, sub_self, abs_zero, Finset.sum_const_zero, zero_add] using h
  · cases flag
    · simpa only [branchLaw, referenceBranches, Bool.false_eq_true, if_false] using
        _p2mH348 security baselineSign baseline hbaseline mark precisionBits drawBits hprecision
    · apply le_trans _ (le_add_of_nonneg_right (by positivity : (0 : ℝ) ≤ 4 * (1 / (2 : ℝ) ^ precisionBits)))
      simpa only [branchLaw, referenceBranches, if_true] using _p2mH347 security baselineSign baseline hbaseline mark drawBits
open _root_.P2M661a572e renaming h376 → _p2mH376
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h375 (security : ℕ) (baseline : ℤ)
    (hbaseline : |baseline| ≤ AffineFlagCalibration.legOffsetBound security) (mark : Fin (Parameters.modulus security)) :
    (indexedReference security baseline hbaseline mark).map
      ((Equiv.refl Bool).prodCongr (finiteChartEquiv (Parameters.modulus security))) =
      (CurrentFlagIdealArrays.model security baseline hbaseline mark).model.joint := by
  ext point
  rw [FiniteDist.map_equiv_weight]
  rw [(CurrentFlagIdealArrays.model security baseline hbaseline mark).model.decomposition]
  cases flagEq : point.1 <;>
    simp [indexedReference, referenceBranches, FiniteDist.joint, CurrentFlagIdealArrays.regularLaw,
      CurrentFlagIdealArrays.markedLaw, FiniteDist.map_equiv_weight, FiniteDist.uniform_weight,
      Equiv.prodCongr_symm, flagEq]
  norm_num
open _root_.P2M661a572e renaming h375 → _p2mH375
end
open _root_.P2M661a572e renaming h373 → _p2mH373
open _root_.P2M661a572e renaming h375 → _p2mH375
open _root_.P2M661a572e renaming h376 → _p2mH376
end CurrentAFT.CurrentFlagJointDraw
open _root_.P2M661a572e renaming h373 → _p2mH373
open _root_.P2M661a572e renaming h374 → _p2mH374
open _root_.P2M661a572e renaming h375 → _p2mH375
open _root_.P2M661a572e renaming h376 → _p2mH376
end
open _root_.P2M661a572e renaming h374 → _p2mH374
open _root_.P2M661a572e renaming h375 → _p2mH375
open _root_.P2M661a572e renaming h373 → _p2mH373
open _root_.P2M661a572e renaming h376 → _p2mH376
section
namespace CurrentAFT.CurrentFlagChartDraw
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw CurrentFlagBinaryMetadata
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h351 (cutoff modulus : ℕ) [NeZero modulus] (baselineSign : Bool) (baseline : List Bool)
    (mark : Fin modulus) (precisionBits drawBits : ℕ) (word : Tape modulus drawBits) :
    (draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value =
      ((Equiv.refl Bool).prodCongr (finiteChartEquiv modulus))
        (CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word).value := by
  let selected := CurrentFlagJointDraw.draw cutoff modulus baselineSign baseline mark precisionBits drawBits word
  have hc := _p2mH344 modulus selected.value.2
  change (selected.value.1, (ZMod.finEquiv modulus) (coordinates modulus selected.value.2).value.1,
    (ZMod.finEquiv modulus) (coordinates modulus selected.value.2).value.2.1,
    (ZMod.finEquiv modulus) (coordinates modulus selected.value.2).value.2.2) =
      (selected.value.1, finiteChartEquiv modulus selected.value.2)
  exact congrArg (fun chart => (selected.value.1, chart)) hc
open _root_.P2M661a572e renaming h351 → _p2mH351
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagChartDraw.chartDrawPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagChartDraw.chartDrawNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h350 (security : ℕ) (baselineSign : Bool) (baseline : List Bool)
    (hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security)
    (mark : Fin (Parameters.modulus security)) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value)).weight point -
      (CurrentFlagIdealArrays.model security (signedValue baselineSign baseline) hbaseline mark).model.joint.weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  have hi := _p2mH376 security baselineSign baseline hbaseline mark precisionBits drawBits hprecision
  have hm := FiniteDist.l1_map_le
    ((tapeLaw (Parameters.modulus security) drawBits).map (fun word =>
      (CurrentFlagJointDraw.draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline mark precisionBits drawBits word).value))
    (indexedReference security (signedValue baselineSign baseline) hbaseline mark)
    ((Equiv.refl Bool).prodCongr (finiteChartEquiv (Parameters.modulus security)))
  rw [_p2mH375, FiniteDist.map_map] at hm
  simpa only [_p2mH351, Function.comp_def] using hm.trans hi
open _root_.P2M661a572e renaming h350 → _p2mH350
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h349 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (baselineSign : Bool) (baseline : List Bool)
    (hencoding : signedValue baselineSign baseline = ActualPublicLegCharge.publicShift security primary seed)
    (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        baselineSign baseline primary precisionBits drawBits word).value)).weight point -
      (AffineFlagCalibration.completionLaw security primary seed).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  have hbaseline : |signedValue baselineSign baseline| ≤ AffineFlagCalibration.legOffsetBound security := by
    rw [hencoding]
    simpa only [AffineFlagCalibration.legOffsetBound, add_sub_assoc] using
      ActualPublicLegCharge.publicShift_bound security primary seed
  have h := _p2mH350 security baselineSign baseline hbaseline primary precisionBits drawBits hprecision
  rw [_p2mH352]
  let left : {value : ℤ // |value| ≤ AffineFlagCalibration.legOffsetBound security} :=
    ⟨signedValue baselineSign baseline, hbaseline⟩
  let right : {value : ℤ // |value| ≤ AffineFlagCalibration.legOffsetBound security} :=
    ⟨ActualPublicLegCharge.publicShift security primary seed,
      by simpa only [AffineFlagCalibration.legOffsetBound, add_sub_assoc] using
        ActualPublicLegCharge.publicShift_bound security primary seed⟩
  have heq : left = right := Subtype.ext hencoding
  have hmodel := congrArg (fun value : {value : ℤ // |value| ≤ AffineFlagCalibration.legOffsetBound security} =>
    (CurrentFlagProgram.current security value.val value.property ((ZMod.finEquiv (Parameters.modulus security)) primary)
      (1 / 2 : ℚ) (by norm_num) (by norm_num)).model.joint) heq
  change (CurrentFlagIdealArrays.model security (signedValue baselineSign baseline) hbaseline primary).model.joint =
    (CurrentFlagCompletion.model security primary seed).model.joint at hmodel
  rw [← hmodel]
  exact h
open _root_.P2M661a572e renaming h349 → _p2mH349
end
open _root_.P2M661a572e renaming h349 → _p2mH349
open _root_.P2M661a572e renaming h350 → _p2mH350
end CurrentAFT.CurrentFlagChartDraw
open _root_.P2M661a572e renaming h349 → _p2mH349
open _root_.P2M661a572e renaming h350 → _p2mH350
open _root_.P2M661a572e renaming h351 → _p2mH351
end
open _root_.P2M661a572e renaming h351 → _p2mH351
open _root_.P2M661a572e renaming h350 → _p2mH350
open _root_.P2M661a572e renaming h349 → _p2mH349
section
namespace CurrentAFT.CurrentPublicShiftProgram
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h459 (value : ℤ) : (encode value).value.decode = value := by
  cases value with
  | ofNat value => simp [encode, IntegerBits.decode, signedValue, canonicalCounter_value]
  | negSucc value =>
    simp [encode, IntegerBits.decode, signedValue, canonicalCounter_value]
    omega
open _root_.P2M661a572e renaming h459 → _p2mH459
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h458 (modulus primary : ℕ) (coin : Bool) :
    (direction modulus primary coin).value =
      if 2 * primary < modulus - 1 then false else if modulus - 1 < 2 * primary then true else coin := by
  simp only [direction, doubleCounter_value, differenceCounter_value, lessCounter_value]
open _root_.P2M661a572e renaming h458 → _p2mH458
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h460 (modulus width primary index : ℕ) (coin : Bool) (blurFirst blurSecond : ℤ) :
    (program modulus width primary index coin blurFirst blurSecond).value.decode =
      (if (direction modulus primary coin).value then ((width + index : ℕ) : ℤ) else -((width + index : ℕ) : ℤ)) +
        blurFirst - blurSecond := by
  simp only [program]
  rw [IntegerBits.add_value, IntegerBits.subtract_value, _p2mH459, _p2mH459]
  simp only [IntegerBits.decode, signedValue, canonicalCounter_value, addCounter_value]
  cases (direction modulus primary coin).value <;> simp <;> ring
open _root_.P2M661a572e renaming h460 → _p2mH460
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h457 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) :
    (current security primary seed).value.decode = ActualPublicLegCharge.publicShift security primary seed := by
  simp only [current, _p2mH460, PublicParameterProgram.modulus_value, addCounter_value,
    powerCounter_value, _p2mH458, ActualPublicLegCharge.publicShift, ActualPublicLegCharge.signedOffset,
    InwardAnchor.positiveDirection, InwardAnchor.offset, Parameters.anchorWidth, Parameters.scale, Parameters.base,
    ← pow_mul, Nat.cast_add]
open _root_.P2M661a572e renaming h457 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2M661a572e renaming h457 → _p2mH457
end CurrentAFT.CurrentPublicShiftProgram
open _root_.P2M661a572e renaming h457 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2M661a572e renaming h457 → _p2mH457
open _root_.P2M661a572e renaming h458 → _p2mH458
open _root_.P2M661a572e renaming h459 → _p2mH459
open _root_.P2M661a572e renaming h460 → _p2mH460
end
open _root_.P2M661a572e renaming h460 → _p2mH460
open _root_.P2M661a572e renaming h458 → _p2mH458
open _root_.P2M661a572e renaming h457 → CurrentAFT.CurrentPublicShiftProgram.current_value
open _root_.P2M661a572e renaming h457 → _p2mH457
open _root_.P2M661a572e renaming h459 → _p2mH459
section
namespace CurrentAFT.CurrentFlagCompletionProgram
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h353 (cutoff first second : ℕ) [NeZero first] [NeZero second] (h : first = second)
    (baselineSign : Bool) (baseline : List Bool) (mark : Fin second) (precisionBits drawBits : ℕ)
    (word : Tape second drawBits) :
    castChart h (CurrentFlagChartDraw.draw cutoff first baselineSign baseline (mark.cast h.symm)
      precisionBits drawBits (cast (congrArg (fun modulus => Tape modulus drawBits) h.symm) word)) =
      CurrentFlagChartDraw.draw cutoff second baselineSign baseline mark precisionBits drawBits word := by
  subst second
  rfl
open _root_.P2M661a572e renaming h353 → _p2mH353
noncomputable section
open scoped Classical
attribute [local instance] _root_.CurrentAFT.CurrentFlagCompletionProgram.completionProgramPrime
attribute [local instance] _root_.CurrentAFT.CurrentFlagCompletionProgram.completionProgramNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h355 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ)
    (word : Tape (Parameters.modulus security) drawBits) :
    (draw security primary seed precisionBits drawBits word).value =
      (CurrentFlagChartDraw.draw (Parameters.sourceCutoff security - 1) (Parameters.modulus security)
        (CurrentPublicShiftProgram.current security primary seed).value.negative
        (CurrentPublicShiftProgram.current security primary seed).value.digits primary precisionBits drawBits word).value := by
  let modulus := PublicParameterProgram.modulus security
  let base := addCounter security 2
  let width := powerCounter base.count 2
  let cutoff := differenceCounter width.count 1
  let shift := CurrentPublicShiftProgram.current security primary seed
  have hm : modulus.count = Parameters.modulus security := PublicParameterProgram.modulus_value security
  have hc : cutoff.count = Parameters.sourceCutoff security - 1 := by
    simp only [cutoff, width, base, differenceCounter_value, powerCounter_value, addCounter_value,
      Parameters.sourceCutoff, Parameters.base]
  change (castChart hm (CurrentFlagChartDraw.draw cutoff.count modulus.count shift.value.negative shift.value.digits
    (primary.cast hm.symm) precisionBits drawBits
      (cast (congrArg (fun modulus => Tape modulus drawBits) hm.symm) word))).value = _
  rw [_p2mH353, hc]
open _root_.P2M661a572e renaming h355 → _p2mH355
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h354 (security : ℕ) (primary : AffineFlagCalibration.Palette security)
    (seed : ActualPublicLegCharge.PublicSeed security) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ point, |((tapeLaw (Parameters.modulus security) drawBits).map
      (fun word => (draw security primary seed precisionBits drawBits word).value)).weight point -
        (AffineFlagCalibration.completionLaw security primary seed).weight point|) ≤
      1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits) := by
  have hencoding : signedValue (CurrentPublicShiftProgram.current security primary seed).value.negative
      (CurrentPublicShiftProgram.current security primary seed).value.digits = ActualPublicLegCharge.publicShift security primary seed :=
    _p2mH457 security primary seed
  simpa only [_p2mH355] using _p2mH349 security primary seed _ _ hencoding
    precisionBits drawBits hprecision
open _root_.P2M661a572e renaming h354 → _p2mH354
end
open _root_.P2M661a572e renaming h354 → _p2mH354
open _root_.P2M661a572e renaming h355 → _p2mH355
end CurrentAFT.CurrentFlagCompletionProgram
open _root_.P2M661a572e renaming h353 → _p2mH353
open _root_.P2M661a572e renaming h354 → _p2mH354
open _root_.P2M661a572e renaming h355 → _p2mH355
end
open _root_.P2M661a572e renaming h355 → _p2mH355
open _root_.P2M661a572e renaming h353 → _p2mH353
open _root_.P2M661a572e renaming h354 → _p2mH354
namespace CurrentAFT.CyclePathClosure
end CurrentAFT.CyclePathClosure
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
theorem _root_.P2M661a572e.h237 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (core : Core security) (vertex : AssemblyIndex security) :
    dimensionEquiv security (relabeling security layout core (naturalNumbering security vertex)) =
      core.endpointPermutation.symm (endpointFlatten security layout vertex) := by
  simp [relabeling]
open _root_.P2M661a572e renaming h237 → _p2mH237
end
open _root_.P2M661a572e renaming h237 → _p2mH237
end CurrentAFT.CurrentAffineGeometry
open _root_.P2M661a572e renaming h237 → _p2mH237
end
open _root_.P2M661a572e renaming h237 → _p2mH237
section
namespace CurrentAFT.CurrentChartsDraw
open AFT AFT.BoundaryCalibration AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentAffineData ActualPublicCharge CurrentFlagJointDraw
open scoped BigOperators
set_option maxHeartbeats 500000
attribute [local irreducible] Parameters.legCount CurrentFlagCompletionProgram.draw
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h293 (security : ℕ) (inputs : InputVector security) (precisionBits drawBits : ℕ)
    (word : Tapes security drawBits) (leg : Fin (Parameters.legCount security)) :
    (draw security inputs precisionBits drawBits word).value leg =
      (CurrentFlagCompletionProgram.draw security (inputs.get leg).1 (inputs.get leg).2
        precisionBits drawBits (word leg)).value := by
  simp only [draw, drawStored, Vector.get_cast, storeData_get, readVector_value, Fin.cast_cast, Fin.cast_eq_self]
open _root_.P2M661a572e renaming h293 → _p2mH293
attribute [local irreducible] draw
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h292 (security : ℕ) (inputs : InputVector security) (precisionBits drawBits : ℕ) :
    (tapeLaw security drawBits).map (fun word => (draw security inputs precisionBits drawBits word).value) =
      FiniteDist.independent (fun leg => (CurrentFlagJointDraw.tapeLaw (Parameters.modulus security) drawBits).map
        (fun word => (CurrentFlagCompletionProgram.draw security (inputs.get leg).1 (inputs.get leg).2 precisionBits drawBits word).value)) := by
  have hv : (fun word => (draw security inputs precisionBits drawBits word).value) =
      (fun word leg => (CurrentFlagCompletionProgram.draw security (inputs.get leg).1 (inputs.get leg).2
        precisionBits drawBits (word leg)).value) := by
    funext word leg
    exact _p2mH293 security inputs precisionBits drawBits word leg
  rw [hv]
  exact _p2mH64
    (Index := Fin (Parameters.legCount security)) (Random := Tape (Parameters.modulus security) drawBits)
    (State := Bool × Chart (ZMod (Parameters.modulus security)))
    (fun _ => CurrentFlagJointDraw.tapeLaw (Parameters.modulus security) drawBits)
    (fun leg word => (CurrentFlagCompletionProgram.draw security (inputs.get leg).1 (inputs.get leg).2
      precisionBits drawBits word).value)
open _root_.P2M661a572e renaming h292 → _p2mH292
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h291 (security : ℕ) (core : Core security) (precisionBits drawBits : ℕ) (hprecision : 1 ≤ precisionBits) :
    (∑ charts, |((tapeLaw security drawBits).map
      (fun word => (draw security (inputsOfCore security core) precisionBits drawBits word).value)).weight charts -
        (CurrentPublicAffineSample.chartsLaw security core).weight charts|) ≤
      (Parameters.legCount security : ℝ) * (1 / (2 : ℝ) ^ drawBits + 4 * (1 / (2 : ℝ) ^ precisionBits)) := by
  rw [_p2mH292]
  apply (FiniteDist.l1_independent_fin_le (Parameters.legCount security) _ _).trans
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun leg _ =>
    _p2mH354 security ((core.controls (.inl leg)).1) ((core.legs leg).1)
      precisionBits drawBits hprecision)
  simpa only [inputsOfCore, Vector.get_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    CurrentPublicAffineSample.chartsLaw] using hsum
open _root_.P2M661a572e renaming h291 → _p2mH291
end
open _root_.P2M661a572e renaming h291 → _p2mH291
open _root_.P2M661a572e renaming h292 → _p2mH292
end CurrentAFT.CurrentChartsDraw
open _root_.P2M661a572e renaming h291 → _p2mH291
open _root_.P2M661a572e renaming h292 → _p2mH292
open _root_.P2M661a572e renaming h293 → _p2mH293
end
open _root_.P2M661a572e renaming h292 → _p2mH292
open _root_.P2M661a572e renaming h291 → _p2mH291
open _root_.P2M661a572e renaming h293 → _p2mH293
section
namespace CurrentAFT.CurrentPublicCompletion
open AFT GaussianSource RationalNumerics BinaryArithmetic AFT.RationalRejectionProgram
open CurrentAffineData ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 600000
attribute [local irreducible] Parameters.legCount CurrentChartsDraw.draw CurrentEdgeDrawProgram.draw
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h448 (security precisionBits drawBits edgeBits : ℕ) (word : Tapes security drawBits edgeBits) :
    (complete security none precisionBits drawBits edgeBits word).value = none := rfl
open _root_.P2M661a572e renaming h448 → _p2mH448
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h449 (security : ℕ) (cached : CachedCore security) (precisionBits drawBits edgeBits : ℕ)
    (word : Tapes security drawBits edgeBits) :
    (complete security (some cached) precisionBits drawBits edgeBits word).value =
      some ((cached.core, (CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word.1).value),
        (CurrentEdgeDrawProgram.draw security edgeBits word.2).value) := rfl
open _root_.P2M661a572e renaming h449 → _p2mH449
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h451 (security precisionBits drawBits edgeBits : ℕ) :
    kernel security precisionBits drawBits edgeBits none = targetKernel security none := by
  ext point
  cases point <;> simp [kernel, _p2mH448, targetKernel, CanonicalMoments.pointLaw, _p2mH85]
open _root_.P2M661a572e renaming h451 → _p2mH451
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h452 (security : ℕ) (cached : CachedCore security) (precisionBits drawBits edgeBits : ℕ) :
    kernel security precisionBits drawBits edgeBits (some cached) =
      (((CurrentChartsDraw.tapeLaw security drawBits).map
        (fun word => (CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word).value)).prod
        ((FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) => FiniteDist.uniform (Fin 2))).map
          (fun word => (CurrentEdgeDrawProgram.draw security edgeBits word).value))).map
        (fun pair => some ((cached.core, pair.1), pair.2)) := by
  simp only [kernel, tapeLaw, _p2mH449]
  rw [← _p2mH87, FiniteDist.map_map]
open _root_.P2M661a572e renaming h452 → _p2mH452
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h450 (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (input : Option (CachedCore security)) :
    (∑ sample, |(kernel security precisionBits drawBits edgeBits input).weight sample -
      (targetKernel security input).weight sample|) ≤ errorBound security precisionBits drawBits edgeBits := by
  cases input with
  | none =>
    rw [_p2mH451]
    simp only [sub_self, abs_zero, Finset.sum_const_zero]
    unfold errorBound
    positivity
  | some cached =>
    rw [_p2mH452]
    let approxCharts := (CurrentChartsDraw.tapeLaw security drawBits).map
      (fun word => (CurrentChartsDraw.draw security cached.inputs precisionBits drawBits word).value)
    let approxEdge := (FiniteDist.independent (fun _ : Fin (windowTicketBits (DiffuseProfiles.edgeCutoff security) edgeBits) => FiniteDist.uniform (Fin 2))).map
      (fun word => (CurrentEdgeDrawProgram.draw security edgeBits word).value)
    let exactCharts := CurrentPublicAffineSample.chartsLaw security cached.core
    let exactEdge := DiffuseProfiles.edgeLaw security
    have hm := FiniteDist.l1_map_le (approxCharts.prod approxEdge) (exactCharts.prod exactEdge)
      (fun pair => some ((cached.core, pair.1), pair.2))
    have hp := FiniteDist.l1_prod_le approxCharts exactCharts approxEdge exactEdge
    have hc := _p2mH291 security cached.core precisionBits drawBits hprecision
    rw [← cached.correct] at hc
    exact hm.trans (hp.trans (add_le_add hc (_p2mH310 security edgeBits)))
open _root_.P2M661a572e renaming h450 → _p2mH450
end
open _root_.P2M661a572e renaming h450 → _p2mH450
open _root_.P2M661a572e renaming h451 → _p2mH451
open _root_.P2M661a572e renaming h452 → _p2mH452
end CurrentAFT.CurrentPublicCompletion
open _root_.P2M661a572e renaming h448 → _p2mH448
open _root_.P2M661a572e renaming h449 → _p2mH449
open _root_.P2M661a572e renaming h450 → _p2mH450
open _root_.P2M661a572e renaming h451 → _p2mH451
open _root_.P2M661a572e renaming h452 → _p2mH452
end
open _root_.P2M661a572e renaming h449 → _p2mH449
open _root_.P2M661a572e renaming h452 → _p2mH452
open _root_.P2M661a572e renaming h448 → _p2mH448
open _root_.P2M661a572e renaming h451 → _p2mH451
open _root_.P2M661a572e renaming h450 → _p2mH450
section
namespace CurrentAFT.CurrentCoreProposal
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge CurrentReferenceDraw CurrentProposalDimensions
open scoped BigOperators
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentPublicSeedDraw.draw CurrentSafeDraw.draw CurrentReferenceDraw.primaryDraw CurrentReferenceDraw.bodyDraw
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h296 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (word : Tapes security bits) (index : PublicOutputExperiment.PublicIndex security) :
    ((draw security tableBits bits cache word).value.core).controls index =
      (controlDraw security tableBits bits cache (word.1.1.1.1 index)).value := by
  simp only [draw, MaterializedCore.core, decode, storeData_get, _p2mH453, Equiv.apply_symm_apply]
open _root_.P2M661a572e renaming h296 → _p2mH296
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h298 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (word : Tapes security bits) (index : Fin (Parameters.legCount security)) :
    ((draw security tableBits bits cache word).value.core).legs index =
      (legDraw security tableBits bits cache (word.1.1.1.2 index)).value := by
  simp only [draw, MaterializedCore.core, decode, storeData_get, _p2mH453, Equiv.apply_symm_apply]
open _root_.P2M661a572e renaming h298 → _p2mH298
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h294 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (word : Tapes security bits) (index : Fin (Parameters.modulus security)) :
    ((draw security tableBits bits cache word).value.core).queueBaselines index =
      (CurrentSafeDraw.draw security bits (word.1.1.2 index)).value := by
  simp only [draw, MaterializedCore.core, decode, storeData_get, _p2mH453, Equiv.apply_symm_apply]
open _root_.P2M661a572e renaming h294 → _p2mH294
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h295 (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    ((draw security tableBits bits cache word).value.core).bodyPermutation =
      (CurrentProposalDimensions.bodyEquiv security).permCongr (PermutationProgram.draw (current security).body bits word.1.2) := by
  change (CurrentProposalDimensions.bodyEquiv security).permCongr ((CurrentPermutationDraw.draw _ _ (Vector.ofFn word.1.2)).value.toEquiv) = _
  rw [_p2mH430]
  congr 1
  congr 1
  funext index
  exact Vector.get_ofFn _ _
open _root_.P2M661a572e renaming h295 → _p2mH295
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h297 (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    ((draw security tableBits bits cache word).value.core).endpointPermutation =
      (endpointEquiv security).permCongr (PermutationProgram.draw (current security).dimension bits word.2) := by
  change (endpointEquiv security).permCongr ((CurrentPermutationDraw.draw _ _ (Vector.ofFn word.2)).value.toEquiv) = _
  rw [_p2mH430]
  congr 1
  congr 1
  funext index
  exact Vector.get_ofFn _ _
open _root_.P2M661a572e renaming h297 → _p2mH297
end CurrentAFT.CurrentCoreProposal
open _root_.P2M661a572e renaming h294 → _p2mH294
open _root_.P2M661a572e renaming h295 → _p2mH295
open _root_.P2M661a572e renaming h296 → _p2mH296
open _root_.P2M661a572e renaming h297 → _p2mH297
open _root_.P2M661a572e renaming h298 → _p2mH298
end
open _root_.P2M661a572e renaming h295 → _p2mH295
open _root_.P2M661a572e renaming h297 → _p2mH297
open _root_.P2M661a572e renaming h298 → _p2mH298
open _root_.P2M661a572e renaming h294 → _p2mH294
open _root_.P2M661a572e renaming h296 → _p2mH296
section
namespace CurrentAFT.BinaryCoreCharge
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions ActualPublicCharge
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h171 (security : ℕ) (core : Core security) :
    (numerator security core : ZMod (Parameters.modulus security)) = chargeValue security core := by
  unfold numerator chargeValue
  simp only [Fintype.sum_sum_type, Int.cast_sum, Int.cast_add, Int.cast_sub,
    Int.cast_natCast, Finset.sum_add_distrib]
  push_cast
  ring
open _root_.P2M661a572e renaming h171 → _p2mH171
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h168 (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).controls) :
    (controlTerm security data index).value.decode =
      ((data.core.controls (controlsEquiv security index)).2.val.val : ℤ) := by
  simp only [controlTerm, _p2mH459, readVector_value,
    MaterializedCore.core, decode, Equiv.symm_apply_apply]
open _root_.P2M661a572e renaming h168 → _p2mH168
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h170 (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) :
    (legTerm security data index).value.decode =
      ((data.core.legs (legEquiv security index)).2.val : ℤ) + legShift security data.core (legEquiv security index) := by
  simp only [legTerm, IntegerBits.add_value, _p2mH459,
    _p2mH457, readVector_value, data.inputs_correct,
    legShift, MaterializedCore.core, decode, Equiv.symm_apply_apply]
open _root_.P2M661a572e renaming h170 → _p2mH170
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h172 (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).colors) :
    (queueTerm security data index).value.decode =
      ((data.core.queueBaselines (queueEquiv security index)).val : ℤ) := by
  simp only [queueTerm, _p2mH459, readVector_value,
    MaterializedCore.core, decode, Equiv.symm_apply_apply]
open _root_.P2M661a572e renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h173 (security : ℕ) (data : MaterializedCore security) :
    (total security data).value.decode = numerator security data.core := by
  simp only [total, IntegerBits.subtract_value, IntegerBits.add_value, _p2mH2,
    _p2mH459, _p2mH168, _p2mH170, _p2mH172]
  rw [Equiv.sum_comp (controlsEquiv security) (fun index => ((data.core.controls index).2.val.val : ℤ)),
    Equiv.sum_comp (legEquiv security) (fun leg => ((data.core.legs leg).2.val : ℤ) + legShift security data.core leg),
    Equiv.sum_comp (queueEquiv security) (fun index => ((data.core.queueBaselines index).val : ℤ)),
    (current_values security).2.1]
  unfold numerator
  norm_cast
open _root_.P2M661a572e renaming h173 → _p2mH173
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h169 (security : ℕ) (data : MaterializedCore security) :
    (current security data).value = true ↔ publicCharge security data.core := by
  have hq : 0 < value (canonicalCounter (PublicParameterProgram.modulus security).count).digits := by
    rw [canonicalCounter_value, PublicParameterProgram.modulus_value]
    exact (Parameters.modulus_spec security).2.pos
  have hr := IntegerBits.residue_value (total security data).value
    (canonicalCounter (PublicParameterProgram.modulus security).count).digits hq
  rw [_p2mH173, canonicalCounter_value, PublicParameterProgram.modulus_value] at hr
  change (normalize (IntegerBits.residue (total security data).value
    (canonicalCounter (PublicParameterProgram.modulus security).count).digits).digits).digits.isEmpty = true ↔ _
  rw [List.isEmpty_iff, normalize_nil_iff]
  have he : value (IntegerBits.residue (total security data).value
      (canonicalCounter (PublicParameterProgram.modulus security).count).digits).digits = 0 ↔
      numerator security data.core % (Parameters.modulus security : ℤ) = 0 := by
    rw [PublicParameterProgram.modulus_value]
    omega
  rw [he, ← Int.dvd_iff_emod_eq_zero]
  unfold publicCharge
  rw [← _p2mH171]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm
open _root_.P2M661a572e renaming h169 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2M661a572e renaming h169 → _p2mH169
end
open _root_.P2M661a572e renaming h168 → _p2mH168
open _root_.P2M661a572e renaming h169 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2M661a572e renaming h169 → _p2mH169
open _root_.P2M661a572e renaming h170 → _p2mH170
open _root_.P2M661a572e renaming h171 → _p2mH171
open _root_.P2M661a572e renaming h172 → _p2mH172
open _root_.P2M661a572e renaming h173 → _p2mH173
end CurrentAFT.BinaryCoreCharge
open _root_.P2M661a572e renaming h168 → _p2mH168
open _root_.P2M661a572e renaming h169 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2M661a572e renaming h169 → _p2mH169
open _root_.P2M661a572e renaming h170 → _p2mH170
open _root_.P2M661a572e renaming h171 → _p2mH171
open _root_.P2M661a572e renaming h172 → _p2mH172
open _root_.P2M661a572e renaming h173 → _p2mH173
end
open _root_.P2M661a572e renaming h171 → _p2mH171
open _root_.P2M661a572e renaming h173 → _p2mH173
open _root_.P2M661a572e renaming h170 → _p2mH170
open _root_.P2M661a572e renaming h168 → _p2mH168
open _root_.P2M661a572e renaming h172 → _p2mH172
open _root_.P2M661a572e renaming h169 → CurrentAFT.BinaryCoreCharge.current_value
open _root_.P2M661a572e renaming h169 → _p2mH169
section
namespace CurrentAFT.BinaryPairedScore
open AFT AFT.RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h187 {count : ℕ} (primary score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (center color : Fin count) :
    (term primary score anchor center color).data.decode =
      (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode := by
  simp only [term, RationalBits.multiply_value, readVector_value, matrixEntry_value]
open _root_.P2M661a572e renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h186 {count : ℕ} (primary centerLaw score : Vector RationalBits count)
    (anchor : Vector (Vector RationalBits count) count) (rate : RationalBits) (input center : Fin count) :
    (current primary centerLaw score anchor rate input center).data.decode =
      (score.get input).decode - rate.decode *
        (∑ color, (primary.get color).decode * (score.get color).decode * ((anchor.get color).get center).decode) /
          (centerLaw.get center).decode := by
  simp only [current, RationalBits.add_value, negate_value, RationalBits.multiply_value, inverse_value, readVector_value,
    sumFin_value, _p2mH187, div_eq_mul_inv, sub_eq_add_neg]
open _root_.P2M661a572e renaming h186 → CurrentAFT.BinaryPairedScore.current_value
open _root_.P2M661a572e renaming h186 → _p2mH186
end CurrentAFT.BinaryPairedScore
open _root_.P2M661a572e renaming h186 → CurrentAFT.BinaryPairedScore.current_value
open _root_.P2M661a572e renaming h186 → _p2mH186
open _root_.P2M661a572e renaming h187 → _p2mH187
end
open _root_.P2M661a572e renaming h186 → CurrentAFT.BinaryPairedScore.current_value
open _root_.P2M661a572e renaming h186 → _p2mH186
open _root_.P2M661a572e renaming h187 → _p2mH187
section
namespace CurrentAFT.BinaryTupleSum
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h204 {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) (index : Fin (count+1)) :
    ((prepend head tail).value.get index) = Fin.cons (α := fun _ => Value) head tail.get index := by
  refine Fin.cases ?_ (fun rest => ?_) index
  · simp [prepend]
  · simp [prepend, readVector_value]
open _root_.P2M661a572e renaming h204 → _p2mH204
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h205 {Value : Type*} {count : ℕ} (head : Value) (tail : Vector Value count) :
    (prepend head tail).value = Vector.ofFn (Fin.cons (α := fun _ => Value) head tail.get) := by
  apply Vector.ext
  intro index hi
  simpa only [Vector.get_eq_getElem, Vector.getElem_ofFn] using _p2mH204 head tail ⟨index, hi⟩
open _root_.P2M661a572e renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h203 {Value : Type*} {count : ℕ} (word : Fin count → Value) :
    (Vector.ofFn word).get = word := by
  funext index
  exact Vector.get_ofFn word index
open _root_.P2M661a572e renaming h203 → _p2mH203
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h202 (pool count : ℕ) (kernel : Vector (Fin pool) count → RationalResult) :
    (current pool count kernel).data.decode =
      ∑ word : Fin count → Fin pool, (kernel (Vector.ofFn word)).data.decode := by
  induction count with
  | zero =>
    simp only [current, Fintype.sum_unique]
    congr 2
  | succ count ih =>
    rw [current, sumFin_value]
    simp_rw [ih]
    simp only [_p2mH205, _p2mH203]
    simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
      (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (count+1) => Fin pool))
        (fun word => (kernel (Vector.ofFn word)).data.decode))
open _root_.P2M661a572e renaming h202 → CurrentAFT.BinaryTupleSum.current_value
open _root_.P2M661a572e renaming h202 → _p2mH202
end CurrentAFT.BinaryTupleSum
open _root_.P2M661a572e renaming h202 → CurrentAFT.BinaryTupleSum.current_value
open _root_.P2M661a572e renaming h202 → _p2mH202
open _root_.P2M661a572e renaming h203 → _p2mH203
open _root_.P2M661a572e renaming h204 → _p2mH204
open _root_.P2M661a572e renaming h205 → _p2mH205
end
open _root_.P2M661a572e renaming h204 → _p2mH204
open _root_.P2M661a572e renaming h203 → _p2mH203
open _root_.P2M661a572e renaming h205 → _p2mH205
open _root_.P2M661a572e renaming h202 → CurrentAFT.BinaryTupleSum.current_value
open _root_.P2M661a572e renaming h202 → _p2mH202
section
namespace CurrentAFT.BinaryPairedTensor
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h189 {Value : Type*} {count : ℕ} (fallback : Value) (word : Vector Value (count+1)) (index : Fin count) :
    (dropFirst fallback word).value.get index = word.get index.succ := by simp [dropFirst, readVector_value]
open _root_.P2M661a572e renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h188 {colors : ℕ} (primary center : Vector RationalBits colors)
    (anchor : Vector (Vector RationalBits colors) colors) (rate : RationalBits) (fallback : Fin colors × Fin colors)
    (count : ℕ) (kernel : Vector (Fin colors) count → RationalResult) (groups : Vector (Fin colors × Fin colors) count) :
    (current primary center anchor rate fallback count kernel groups).data.decode =
      value primary center anchor rate count (fun word => (kernel (Vector.ofFn word)).data.decode) groups.get := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [current, _p2mH186, buildArray_get, readVector_value]
    simp_rw [ih]
    simp only [value, lift]
    have htail : (dropFirst fallback groups).value.get = fun index => groups.get index.succ := by
      funext index; exact _p2mH189 fallback groups index
    rw [htail]
    simp only [_p2mH205, _p2mH203]
open _root_.P2M661a572e renaming h188 → CurrentAFT.BinaryPairedTensor.current_value
open _root_.P2M661a572e renaming h188 → _p2mH188
end CurrentAFT.BinaryPairedTensor
open _root_.P2M661a572e renaming h188 → CurrentAFT.BinaryPairedTensor.current_value
open _root_.P2M661a572e renaming h188 → _p2mH188
open _root_.P2M661a572e renaming h189 → _p2mH189
end
open _root_.P2M661a572e renaming h189 → _p2mH189
open _root_.P2M661a572e renaming h188 → CurrentAFT.BinaryPairedTensor.current_value
open _root_.P2M661a572e renaming h188 → _p2mH188
section
namespace CurrentAFT.BinaryWeightCoordinates
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] multiplyCounter addCounter powerCounter
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h209 {First Second : Type*} {count : ℕ} (word : Vector First count) (f : First → Second) :
    (word.map f).get = fun index => f (word.get index) := by
  funext index
  simp only [Vector.get_map]
open _root_.P2M661a572e renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h210 (base order r s : ℕ) (hb : 0 < base) (hdegree : r+s ≤ order)
    (table : Table base order) (primary : Vector (Fin base) r) (body : Vector (Fin base) s) :
    (read base order r s hb hdegree table primary body).data.decode =
      ((table.get (WeightCoordinates.arityIndex order ⟨r, by omega⟩ ⟨s, by omega⟩)).get
        (WeightCoordinates.wordIndex base order r s hb hdegree primary.get body.get)).decode := by
  simp only [read, readVector_value]
  congr 3
  · apply Fin.ext
    exact arity_value order r s
  · simpa only [WeightCoordinates.wordIndex, _p2mH209, Function.comp_def] using joint_value base r s (primary.map Fin.val) (body.map Fin.val)
open _root_.P2M661a572e renaming h210 → _p2mH210
end CurrentAFT.BinaryWeightCoordinates
open _root_.P2M661a572e renaming h209 → _p2mH209
open _root_.P2M661a572e renaming h210 → _p2mH210
end
open _root_.P2M661a572e renaming h209 → _p2mH209
open _root_.P2M661a572e renaming h210 → _p2mH210
section
namespace CurrentAFT.BinaryWeightLocal
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open scoped BigOperators
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h212 {Value : Type*} {pool count : ℕ} (fallback : Value) (hp : 0 < pool)
    (values : Vector Value pool) (sites : Vector (Fin pool) count) (slot : Fin count) :
    (gather fallback hp values sites).value.get slot = values.get (sites.get slot) := by
  simp [gather, readVector_value]
open _root_.P2M661a572e renaming h212 → _p2mH212
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h213 (security order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order) (primary : Fin arity.val.1.val → Fin (colors security))
    (body : Fin arity.val.2.val → Fin (colors security)) :
    rawTable security order table arity (fun index => (primary index).val) (fun index => (body index).val) =
      ((table.get (WeightCoordinates.arityIndex order arity.val.1 arity.val.2)).get
        (WeightCoordinates.wordIndex (colors security) order arity.val.1.val arity.val.2.val
          (colors_pos security)
          arity.property primary body)).decode := by
  unfold rawTable
  rw [dif_pos ⟨fun index => (primary index).isLt, fun index => (body index).isLt⟩]
  rfl
open _root_.P2M661a572e renaming h213 → _p2mH213
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h556 {count colors : ℕ} (color : Fin colors) (rest : Fin count → Fin colors) :
    (fun index : Fin (count+1) => (Fin.cons (α := fun _ => Fin colors) color rest index).val) =
      Fin.cons color.val (fun index => (rest index).val) := by
  funext index
  exact Fin.cases rfl (fun _ => rfl) index
open _root_.P2M661a572e renaming h556 → _p2mH556
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h214 (security bits count : ℕ) (kernel : (Fin count → Fin (colors security)) → ℚ)
    (ideal : (Fin count → ℕ) → ℚ)
    (hk : ∀ word, kernel word = ideal (fun index => (word index).val))
    (groups : Fin count → Fin (colors security) × Fin (colors security)) :
    BinaryPairedTensor.value (BinaryReferenceTables.current security bits).primary (BinaryReferenceTables.current security bits).center
      (BinaryReferenceTables.current security bits).anchor (BinaryReferenceTables.current security bits).activation count kernel groups =
      RationalWeightProgram.pairedTensor security bits count ideal
        (fun index => ((groups index).1.val, (groups index).2.val)) := by
  induction count with
  | zero =>
    simp only [BinaryPairedTensor.value, RationalWeightProgram.pairedTensor]
    exact (hk Fin.elim0).trans (congrArg ideal (Subsingleton.elim _ _))
  | succ count ih =>
    simp only [BinaryPairedTensor.value, BinaryPairedTensor.lift, RationalWeightProgram.pairedTensor,
      RationalPairedLiftProgram.current, RationalPairedLiftProgram.anchorProfile]
    simp_rw [BinaryReferenceTables.primary_value, _p2mH199]
    rw [BinaryReferenceTables.center_value, BinaryReferenceTables.activation_value]
    have hchild (color : Fin (colors security)) := ih
      (fun rest => kernel (Fin.cons color rest)) (fun rest => ideal (Fin.cons color.val rest))
      (fun rest => (hk (Fin.cons color rest)).trans (congrArg ideal (_p2mH556 color rest)))
      (fun index => groups index.succ)
    simp_rw [hchild]
open _root_.P2M661a572e renaming h214 → _p2mH214
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h211 (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) arity.val.1.val)
    (centers : Vector (Fin (colors security)) arity.val.2.val) :
    (current security bits order (BinaryReferenceTables.current security bits) table arity groups centers).data.decode =
      RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => rawTable security order table arity primary (fun index => (centers.get index).val))
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) := by
  rw [current, _p2mH188]
  apply _p2mH214
  intro primary
  rw [_p2mH210, _p2mH213]
  simp only [_p2mH203]
open _root_.P2M661a572e renaming h211 → CurrentAFT.BinaryWeightLocal.current_value
open _root_.P2M661a572e renaming h211 → _p2mH211
end CurrentAFT.BinaryWeightLocal
open _root_.P2M661a572e renaming h211 → CurrentAFT.BinaryWeightLocal.current_value
open _root_.P2M661a572e renaming h211 → _p2mH211
open _root_.P2M661a572e renaming h212 → _p2mH212
open _root_.P2M661a572e renaming h213 → _p2mH213
open _root_.P2M661a572e renaming h214 → _p2mH214
open _root_.P2M661a572e renaming h556 → _p2mH556
end
open _root_.P2M661a572e renaming h212 → _p2mH212
open _root_.P2M661a572e renaming h213 → _p2mH213
open _root_.P2M661a572e renaming h211 → CurrentAFT.BinaryWeightLocal.current_value
open _root_.P2M661a572e renaming h211 → _p2mH211
open _root_.P2M661a572e renaming h214 → _p2mH214
section
namespace CurrentAFT.BinaryDistinctTuples
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] lessCounter
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h184 (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) (first second : Fin count) :
    (pairCheck pool count hp word first second).value = true ↔
      (first.val < second.val → word.get first ≠ word.get second) := by
  simp only [pairCheck, readVector_value]
  by_cases hpos : (lessCounter first.val second.val).value = true
  · rw [if_pos hpos, Bool.or_eq_true, lessCounter_value, lessCounter_value]
    have hlt := (lessCounter_value _ _).mp hpos
    constructor
    · intro h _ he
      have he' := congrArg Fin.val he
      omega
    · intro h
      have hn := h hlt
      have hn' : (word.get first).val ≠ (word.get second).val := fun he => hn (Fin.ext he)
      omega
  · rw [if_neg hpos]
    have hnot : ¬ first.val < second.val := fun h => hpos ((lessCounter_value _ _).mpr h)
    simp only [hnot, false_implies]
open _root_.P2M661a572e renaming h184 → _p2mH184
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h181 (pool count : ℕ) (hp : 0 < pool) (word : Vector (Fin pool) count) :
    (current pool count hp word).value = true ↔ Function.Injective word.get := by
  simp only [current, BinaryProposalGuard.allFin_value, _p2mH184]
  constructor
  · intro h first second he
    by_contra hn
    have hv : first.val ≠ second.val := fun hv => hn (Fin.ext hv)
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · exact h first second hlt he
    · exact h second first hgt he.symm
  · intro h first second hlt he
    have hi := h he
    have hv := congrArg Fin.val hi
    omega
open _root_.P2M661a572e renaming h181 → CurrentAFT.BinaryDistinctTuples.current_value
open _root_.P2M661a572e renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h182 (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult)
    (word : Vector (Fin pool) count) :
    (guarded pool count hp kernel word).data.decode =
      if Function.Injective word.get then (kernel word).data.decode else 0 := by
  unfold guarded
  try dsimp only
  by_cases h : (current pool count hp word).value = true
  · simp only [if_pos h, if_pos ((_p2mH181 _ _ _ _).mp h)]
  · simp only [if_neg h, if_neg (fun h' => h ((_p2mH181 _ _ _ _).mpr h')), zero_value]
open _root_.P2M661a572e renaming h182 → _p2mH182
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h185 (pool count : ℕ) (hp : 0 < pool) (kernel : Vector (Fin pool) count → RationalResult) :
    (sum pool count hp kernel).data.decode =
      ∑ selection : Fin count ↪ Fin pool, (kernel (Vector.ofFn selection)).data.decode := by
  letI : Fintype {word : Fin count → Fin pool // Function.Injective word} := Fintype.ofFinite _
  rw [sum, _p2mH202]
  simp only [_p2mH182, _p2mH203]
  have hs := (Finset.sum_subtype (p := fun word : Fin count → Fin pool => Function.Injective word) (F := inferInstance)
    (Finset.univ.filter Function.Injective) (by simp) (fun word => (kernel (Vector.ofFn word)).data.decode))
  rw [Finset.sum_filter] at hs
  rw [hs]
  exact (Equiv.sum_comp (CyclePatternProgram.selectionEquiv pool count)
    (fun word => (kernel (Vector.ofFn word.val)).data.decode)).symm
open _root_.P2M661a572e renaming h185 → _p2mH185
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h183 (pool count : ℕ) (hp : 0 < pool) :
    (normalizer pool count hp).data.decode = (pool.descFactorial count:ℚ) := by
  rw [normalizer, _p2mH185]
  simp only [one_value, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq, Fintype.card_fin]
open _root_.P2M661a572e renaming h183 → _p2mH183
end
open _root_.P2M661a572e renaming h183 → _p2mH183
open _root_.P2M661a572e renaming h185 → _p2mH185
end CurrentAFT.BinaryDistinctTuples
open _root_.P2M661a572e renaming h181 → CurrentAFT.BinaryDistinctTuples.current_value
open _root_.P2M661a572e renaming h181 → _p2mH181
open _root_.P2M661a572e renaming h182 → _p2mH182
open _root_.P2M661a572e renaming h183 → _p2mH183
open _root_.P2M661a572e renaming h184 → _p2mH184
open _root_.P2M661a572e renaming h185 → _p2mH185
end
open _root_.P2M661a572e renaming h182 → _p2mH182
open _root_.P2M661a572e renaming h183 → _p2mH183
open _root_.P2M661a572e renaming h181 → CurrentAFT.BinaryDistinctTuples.current_value
open _root_.P2M661a572e renaming h181 → _p2mH181
open _root_.P2M661a572e renaming h185 → _p2mH185
open _root_.P2M661a572e renaming h184 → _p2mH184
section
namespace CurrentAFT.BinaryTwoPoolAverage
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits
open scoped BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h206 (primaryPool bodyPool r s : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (kernel : Vector (Fin primaryPool) r → Vector (Fin bodyPool) s → RationalResult) :
    (current primaryPool bodyPool r s hp hb kernel).data.decode =
      (∑ primary : Fin r ↪ Fin primaryPool, ∑ body : Fin s ↪ Fin bodyPool,
        (kernel (Vector.ofFn primary) (Vector.ofFn body)).data.decode)/
        ((primaryPool.descFactorial r:ℚ)*(bodyPool.descFactorial s:ℚ)) := by
  simp only [current, quotient_value, RationalBits.multiply_value, _p2mH183,
    _p2mH185]
open _root_.P2M661a572e renaming h206 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2M661a572e renaming h206 → _p2mH206
end
open _root_.P2M661a572e renaming h206 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2M661a572e renaming h206 → _p2mH206
end CurrentAFT.BinaryTwoPoolAverage
open _root_.P2M661a572e renaming h206 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2M661a572e renaming h206 → _p2mH206
end
open _root_.P2M661a572e renaming h206 → CurrentAFT.BinaryTwoPoolAverage.current_value
open _root_.P2M661a572e renaming h206 → _p2mH206
section
namespace CurrentAFT.BinaryWeightBlock
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus BinaryWeightLocal.current BinaryTwoPoolAverage.current BinaryReferenceTables.current
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h208 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool)
    (first : Vector (Fin primaryPool) arity.val.1.val) (second : Vector (Fin bodyPool) arity.val.2.val) :
    (selected security bits order primaryPool bodyPool hp hb (BinaryReferenceTables.current security bits) table arity groups centers first second).data.decode =
      RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => rawTable security order table arity primary (fun index => (centers.get (second.get index)).val))
        (fun index => ((groups.get (first.get index)).1.val, (groups.get (first.get index)).2.val)) := by
  unfold selected
  rw [_p2mH211]
  simp only [_p2mH212]
open _root_.P2M661a572e renaming h208 → _p2mH208
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h207 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order) (arity : TruncatedArity order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) :
    (current security bits order primaryPool bodyPool hp hb (BinaryReferenceTables.current security bits) table arity groups centers).data.decode =
      RationalWeightProgram.average arity.val.1.val arity.val.2.val primaryPool bodyPool
        (fun selected selectedCenters => RationalWeightProgram.pairedTensor security bits arity.val.1.val
          (fun primary => rawTable security order table arity primary selectedCenters) selected)
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val) := by
  rw [current, _p2mH206]
  simp_rw [_p2mH208]
  simp only [Vector.get_ofFn]
  unfold RationalWeightProgram.average
  apply congrArg (fun numerator : ℚ => numerator /
    ((primaryPool.descFactorial arity.val.1.val:ℚ)*(bodyPool.descFactorial arity.val.2.val:ℚ)))
  letI := CyclePatternProgram.selectionFintype primaryPool arity.val.1.val
  letI := CyclePatternProgram.selectionFintype bodyPool arity.val.2.val
  have hprod : (∑ pair : (Fin arity.val.1.val ↪ Fin primaryPool) × (Fin arity.val.2.val ↪ Fin bodyPool),
      RationalWeightProgram.pairedTensor security bits arity.val.1.val
        (fun primary => rawTable security order table arity primary (fun index => (centers.get (pair.2 index)).val))
        (fun index => ((groups.get (pair.1 index)).1.val, (groups.get (pair.1 index)).2.val))) =
      ∑ first : Fin arity.val.1.val ↪ Fin primaryPool, ∑ second : Fin arity.val.2.val ↪ Fin bodyPool,
        RationalWeightProgram.pairedTensor security bits arity.val.1.val
          (fun primary => rawTable security order table arity primary (fun index => (centers.get (second index)).val))
          (fun index => ((groups.get (first index)).1.val, (groups.get (first index)).2.val)) := by
    rw [Fintype.sum_prod_type]
  apply Eq.trans ?_ hprod.symm
  apply Finset.sum_congr (by ext; simp)
  intro first _
  apply Finset.sum_congr (by ext; simp)
  intro second _
  rfl
open _root_.P2M661a572e renaming h207 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2M661a572e renaming h207 → _p2mH207
end
open _root_.P2M661a572e renaming h207 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2M661a572e renaming h207 → _p2mH207
open _root_.P2M661a572e renaming h208 → _p2mH208
end CurrentAFT.BinaryWeightBlock
open _root_.P2M661a572e renaming h207 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2M661a572e renaming h207 → _p2mH207
open _root_.P2M661a572e renaming h208 → _p2mH208
end
open _root_.P2M661a572e renaming h207 → CurrentAFT.BinaryWeightBlock.current_value
open _root_.P2M661a572e renaming h207 → _p2mH207
open _root_.P2M661a572e renaming h208 → _p2mH208
namespace AFT.LocalTensors.atomLinear
end AFT.LocalTensors.atomLinear
section
namespace CurrentAFT.PhysicalPolynomialAverages
open AFT AFT.RepresentedPolynomial HistogramNormalization GradedControlAlgebra
  ControlCoordinates CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h509 (order : ℕ) : Function.Bijective (arityOptionMap order) := by
  constructor
  · intro left right hequal
    cases left with
    | none =>
      cases right with
      | none => rfl
      | some arity =>
        have h := congrArg (fun a : TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change 0 + 0 = arity.val.1.val + arity.val.2.val at h
        omega
    | some arity =>
      cases right with
      | none =>
        have h := congrArg (fun a : TruncatedArity order => a.val.1.val + a.val.2.val) hequal
        have hp := arity.property.1
        change arity.val.1.val + arity.val.2.val = 0 + 0 at h
        omega
      | some other =>
        apply congrArg some
        apply Subtype.ext
        exact congrArg (fun a : TruncatedArity order => a.val) hequal
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
open _root_.P2M661a572e renaming h509 → _p2mH509
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h510 {Value : Type*} [AddCommMonoid Value] (order : ℕ)
    (test : TruncatedArity order → Value) :
    (∑ arity, test arity) = test (zeroArity order) +
      ∑ arity : PositiveArity order, test (positiveArity order arity) := by
  rw [← (Equiv.ofBijective (arityOptionMap order) (_p2mH509 order)).sum_comp]
  exact Fintype.sum_option _
open _root_.P2M661a572e renaming h510 → _p2mH510
end
open _root_.P2M661a572e renaming h509 → _p2mH509
open _root_.P2M661a572e renaming h510 → _p2mH510
end CurrentAFT.PhysicalPolynomialAverages
open _root_.P2M661a572e renaming h509 → _p2mH509
open _root_.P2M661a572e renaming h510 → _p2mH510
end
open _root_.P2M661a572e renaming h509 → _p2mH509
open _root_.P2M661a572e renaming h510 → _p2mH510
section
namespace CurrentAFT.BinaryWeightProgram
open AFT RationalNumerics BinaryArithmetic BinaryArithmetic.RationalBits RationalRejectionProgram GradedControlAlgebra ControlCoordinates
open BinaryWeightLocal
open scoped BigOperators
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] addCounter lessCounter PublicParameterProgram.modulus BinaryWeightBlock.current BinaryReferenceTables.current BinaryWeightBlock.height BinaryWeightBlock.work
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h217 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) (r s : Fin (order+1)) :
    (term security bits order primaryPool bodyPool hp hb (BinaryReferenceTables.current security bits) table groups centers r s).data.decode =
      if h : r.val+s.val ≤ order then idealBlock security bits order primaryPool bodyPool table groups centers ⟨(r, s), h⟩ else 0 := by
  have ha : (lessCounter (addCounter r.val s.val).count (order+1)).value = true ↔ r.val+s.val ≤ order := by
    rw [lessCounter_value, addCounter_value]
    omega
  unfold term
  try dsimp only
  by_cases hd : r.val+s.val ≤ order
  · simp only [dif_pos (ha.mpr hd), dif_pos hd]
    exact _p2mH207 security bits order primaryPool bodyPool hp hb table ⟨(r, s), hd⟩ groups centers
  · simp only [dif_neg (fun h => hd (ha.mp h)), dif_neg hd, zero_value]
open _root_.P2M661a572e renaming h217 → _p2mH217
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h216 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) :
    (current security bits order primaryPool bodyPool hp hb table groups centers).data.decode =
      ∑ arity : TruncatedArity order, idealBlock security bits order primaryPool bodyPool table groups centers arity := by
  rw [current, sumFin_value]
  simp_rw [sumFin_value, _p2mH217]
  have hsum := Finset.sum_subtype (p := fun pair : Fin (order+1) × Fin (order+1) => pair.1.val+pair.2.val ≤ order)
    (F := inferInstance) (Finset.univ.filter (fun pair => pair.1.val+pair.2.val ≤ order)) (by simp)
    (fun pair => if h : pair.1.val+pair.2.val ≤ order then
      idealBlock security bits order primaryPool bodyPool table groups centers ⟨pair, h⟩ else 0)
  rw [Finset.sum_filter] at hsum
  have hh : (∑ pair : Fin (order+1) × Fin (order+1),
      if h : pair.1.val+pair.2.val ≤ order then idealBlock security bits order primaryPool bodyPool table groups centers ⟨pair, h⟩ else 0) =
      ∑ arity : TruncatedArity order, idealBlock security bits order primaryPool bodyPool table groups centers arity := by
    convert hsum using 1
    · apply Finset.sum_congr rfl
      intro pair _
      by_cases hd : pair.1.val+pair.2.val ≤ order <;> simp [hd]
    · apply Finset.sum_congr rfl
      intro arity _
      rw [dif_pos arity.property]
  exact (Fintype.sum_prod_type _).symm.trans hh
open _root_.P2M661a572e renaming h216 → _p2mH216
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h557 (primaryPool bodyPool : ℕ) (kernel : (Fin 0 → ℕ × ℕ) → (Fin 0 → ℕ) → ℚ)
    (groups : Fin primaryPool → ℕ × ℕ) (centers : Fin bodyPool → ℕ) :
    RationalWeightProgram.average 0 0 primaryPool bodyPool kernel groups centers = kernel Fin.elim0 Fin.elim0 := by
  letI := CyclePatternProgram.selectionFintype primaryPool 0
  letI := CyclePatternProgram.selectionFintype bodyPool 0
  let first : Fin 0 ↪ Fin primaryPool := ⟨Fin.elim0, fun index => Fin.elim0 index⟩
  let second : Fin 0 ↪ Fin bodyPool := ⟨Fin.elim0, fun index => Fin.elim0 index⟩
  unfold RationalWeightProgram.average
  simp only [Nat.descFactorial_zero, Nat.cast_one, mul_one, div_one]
  rw [Fintype.sum_subsingleton _ (first, second)]
  exact congrArg₂ kernel (Subsingleton.elim _ _) (Subsingleton.elim _ _)
open _root_.P2M661a572e renaming h557 → _p2mH557
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h215 (security bits order primaryPool bodyPool : ℕ) (hp : 0 < primaryPool) (hb : 0 < bodyPool)
    (table : BinaryWeightCoordinates.Table (colors security) order)
    (groups : Vector (Fin (colors security) × Fin (colors security)) primaryPool)
    (centers : Vector (Fin (colors security)) bodyPool) :
    (current security bits order primaryPool bodyPool hp hb table groups centers).data.decode =
      RationalWeightProgram.current security bits order primaryPool bodyPool (rawTable security order table)
        (fun index => ((groups.get index).1.val, (groups.get index).2.val)) (fun index => (centers.get index).val) := by
  rw [_p2mH216, _p2mH510]
  unfold RationalWeightProgram.current
  apply congrArg₂ (·+·)
  · unfold idealBlock
    simp only [zeroArity, Fin.val_zero]
    rw [_p2mH557, RationalWeightProgram.pairedTensor]
  · rfl
open _root_.P2M661a572e renaming h215 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2M661a572e renaming h215 → _p2mH215
end
open _root_.P2M661a572e renaming h215 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2M661a572e renaming h215 → _p2mH215
open _root_.P2M661a572e renaming h216 → _p2mH216
open _root_.P2M661a572e renaming h217 → _p2mH217
open _root_.P2M661a572e renaming h557 → _p2mH557
end CurrentAFT.BinaryWeightProgram
open _root_.P2M661a572e renaming h215 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2M661a572e renaming h215 → _p2mH215
open _root_.P2M661a572e renaming h216 → _p2mH216
open _root_.P2M661a572e renaming h217 → _p2mH217
open _root_.P2M661a572e renaming h557 → _p2mH557
end
open _root_.P2M661a572e renaming h216 → _p2mH216
open _root_.P2M661a572e renaming h215 → CurrentAFT.BinaryWeightProgram.current_value
open _root_.P2M661a572e renaming h215 → _p2mH215
open _root_.P2M661a572e renaming h217 → _p2mH217
section
namespace CurrentAFT.BinaryCoreWeightData
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentProposalDimensions BinaryWeightLocal
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.legCount Parameters.bodySize Parameters.dimension
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h180 (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).legs) :
    primaryAddress security index = (controlsEquiv security).symm (.inl (legEquiv security index)) := by
  apply Fin.ext
  rfl
open _root_.P2M661a572e renaming h180 → _p2mH180
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h178 (security : ℕ) (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    (ordinaryAddress security index).value = (controlsEquiv security).symm (.inr (ordinaryEquiv security index)) := by
  apply Fin.ext
  simp only [ordinaryAddress, addCounter_value, (current_values security).2.1]
  rfl
open _root_.P2M661a572e renaming h178 → _p2mH178
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h177 (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).legs) :
    ((groups security data).value.get index).1.val = (data.core.controls (.inl (legEquiv security index))).1.val ∧
    ((groups security data).value.get index).2.val = (data.core.controls (.inl (legEquiv security index))).2.val.val := by
  simp only [groups, storeData_get, primaryEntry, readVector_value, _p2mH180, color,
    Fin.val_cast, MaterializedCore.core, decode, and_self]
open _root_.P2M661a572e renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h174 (security : ℕ) (data : MaterializedCore security)
    (index : Fin (CurrentProposalDimensions.current security).ordinary) :
    ((centers security data).value.get index).val =
      (data.core.controls (.inr (ordinaryEquiv security index))).2.val.val := by
  simp only [centers, storeData_get, ordinaryEntry, readVector_value, _p2mH178, color,
    Fin.val_cast, MaterializedCore.core, decode]
open _root_.P2M661a572e renaming h174 → _p2mH174
noncomputable section
open scoped Classical
attribute [local irreducible] RationalWeightProgram.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h175 (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (data : MaterializedCore security) :
    (current security bits order table data).value.decode =
      RationalWeightProgram.current security bits order (CurrentProposalDimensions.current security).legs
        (CurrentProposalDimensions.current security).ordinary (rawTable security order table)
        (fun index => ((data.core.controls (.inl (legEquiv security index))).1.val,
          (data.core.controls (.inl (legEquiv security index))).2.val.val))
        (fun index => (data.core.controls (.inr (ordinaryEquiv security index))).2.val.val) := by
  simp only [current, _p2mH215, (_p2mH177 security data _).1,
    (_p2mH177 security data _).2, _p2mH174]
open _root_.P2M661a572e renaming h175 → CurrentAFT.BinaryCoreWeightData.current_value
open _root_.P2M661a572e renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h179 (security bits order primary body actualPrimary actualBody : ℕ)
    (hp : primary = actualPrimary) (hb : body = actualBody) (table : RationalWeightProgram.RawTable order)
    (groups : Fin actualPrimary → ℕ × ℕ) (centers : Fin actualBody → ℕ) :
    RationalWeightProgram.current security bits order primary body table
      (fun index => groups (index.cast hp)) (fun index => centers (index.cast hb)) =
      RationalWeightProgram.current security bits order actualPrimary actualBody table groups centers := by
  cases hp
  cases hb
  rfl
open _root_.P2M661a572e renaming h179 → _p2mH179
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h176 (security bits order : ℕ) (table : BinaryWeightCoordinates.Table (colors security) order)
    (data : MaterializedCore security) :
    (current security bits order table data).value.decode =
      RationalWeightProgram.current security bits order (Parameters.legCount security)
        (BackgroundRates.ordinaryPool security) (rawTable security order table)
        (fun index => ((data.core.controls (.inl index)).1.val, (data.core.controls (.inl index)).2.val.val))
        (fun index => (data.core.controls (.inr index)).2.val.val) := by
  rw [_p2mH175]
  have h := _p2mH179 security bits order (CurrentProposalDimensions.current security).legs
    (CurrentProposalDimensions.current security).ordinary (Parameters.legCount security)
    (BackgroundRates.ordinaryPool security) (current_values security).2.1 (current_values security).2.2.2.2.1
    (rawTable security order table)
    (fun index => ((data.core.controls (.inl index)).1.val, (data.core.controls (.inl index)).2.val.val))
    (fun index => (data.core.controls (.inr index)).2.val.val)
  exact h
open _root_.P2M661a572e renaming h176 → _p2mH176
end
open _root_.P2M661a572e renaming h175 → CurrentAFT.BinaryCoreWeightData.current_value
open _root_.P2M661a572e renaming h175 → _p2mH175
open _root_.P2M661a572e renaming h176 → _p2mH176
open _root_.P2M661a572e renaming h179 → _p2mH179
end CurrentAFT.BinaryCoreWeightData
open _root_.P2M661a572e renaming h174 → _p2mH174
open _root_.P2M661a572e renaming h175 → CurrentAFT.BinaryCoreWeightData.current_value
open _root_.P2M661a572e renaming h175 → _p2mH175
open _root_.P2M661a572e renaming h176 → _p2mH176
open _root_.P2M661a572e renaming h177 → _p2mH177
open _root_.P2M661a572e renaming h178 → _p2mH178
open _root_.P2M661a572e renaming h179 → _p2mH179
open _root_.P2M661a572e renaming h180 → _p2mH180
end
open _root_.P2M661a572e renaming h178 → _p2mH178
open _root_.P2M661a572e renaming h175 → CurrentAFT.BinaryCoreWeightData.current_value
open _root_.P2M661a572e renaming h175 → _p2mH175
open _root_.P2M661a572e renaming h177 → _p2mH177
open _root_.P2M661a572e renaming h174 → _p2mH174
open _root_.P2M661a572e renaming h180 → _p2mH180
open _root_.P2M661a572e renaming h179 → _p2mH179
open _root_.P2M661a572e renaming h176 → _p2mH176
section
namespace CurrentAFT.CurrentReferenceDrawRates
open AFT ProposalPrimary CurrentReferenceDraw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 600000
attribute [local instance] _root_.CurrentAFT.CurrentReferenceDrawRates.safeFintype
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h469 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color, |(RationalProposalProgram.approximatePrimaryLaw security bits).weight color -
      (primaryLaw security).weight color|) ≤
      (Parameters.modulus security : ℝ) * (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun color _ =>
    _p2mH534 security bits color hprecision hbudget)
  simpa only [FiniteDist.weight, RationalProposalProgram.approximatePrimaryLaw, primaryLaw,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
open _root_.P2M661a572e renaming h469 → _p2mH469
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h467 (security bits : ℕ)
    (hprecision : 1 / (2 : ℝ)^bits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color : ActualControls.SafePalette security,
      |(RationalProposalProgram.approximateBodyReference security bits).weight color -
        (ActualControls.bodyReference security).weight color|) ≤
      (Parameters.modulus security : ℝ) * ((64 * (Parameters.base security : ℝ) * Parameters.dimension security *
        Parameters.modulus security + 2) * (1 / (2 : ℝ)^bits)) := by
  let error := (64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
    (1 / (2 : ℝ)^bits)
  have he : 0 ≤ error := by dsimp [error]; positivity
  have h := Finset.sum_le_sum (s := Finset.univ) (fun color : ActualControls.SafePalette security => fun _ =>
    _p2mH526 security bits color.val hprecision hbudget)
  have hc : Fintype.card (ActualControls.SafePalette security) ≤ Parameters.modulus security := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      (Subtype.val : ActualControls.SafePalette security → FirstHistogram.Palette security) Subtype.val_injective
  change (∑ color : ActualControls.SafePalette security,
    |(RationalProposalProgram.center security bits color.val.val : ℝ) - centerProfile security color.val|) ≤ _
  calc
    _ ≤ (Fintype.card (ActualControls.SafePalette security) : ℝ) * error := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
    _ ≤ (Parameters.modulus security : ℝ) * error := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) he
open _root_.P2M661a572e renaming h467 → _p2mH467
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h468 (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (hprecision : 1 / (2 : ℝ)^tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^tableBits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color, |(primaryDrawLaw security tableBits drawBits cache).weight color - (primaryLaw security).weight color|) ≤
      1 / (2 : ℝ)^drawBits + (Parameters.modulus security : ℝ) *
        (64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^tableBits)) := by
  apply le_trans _ (add_le_add (_p2mH464 security tableBits drawBits cache)
    (_p2mH469 security tableBits hprecision hbudget))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun color _ => abs_sub_le _
    ((RationalProposalProgram.approximatePrimaryLaw security tableBits).weight color) _)
open _root_.P2M661a572e renaming h468 → _p2mH468
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h466 (security tableBits drawBits : ℕ) (cache : Cache security tableBits)
    (hprecision : 1 / (2 : ℝ)^tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * (1 / (2 : ℝ)^tableBits) ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ color, |(bodyDrawLaw security tableBits drawBits cache).weight color - (ActualControls.bodyReference security).weight color|) ≤
      1 / (2 : ℝ)^drawBits + (Parameters.modulus security : ℝ) *
        ((64 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security + 2) *
          (1 / (2 : ℝ)^tableBits)) := by
  apply le_trans _ (add_le_add (_p2mH461 security tableBits drawBits cache)
    (_p2mH467 security tableBits hprecision hbudget))
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun color _ => abs_sub_le _
    ((RationalProposalProgram.approximateBodyReference security tableBits).weight color) _)
open _root_.P2M661a572e renaming h466 → _p2mH466
end
open _root_.P2M661a572e renaming h466 → _p2mH466
open _root_.P2M661a572e renaming h467 → _p2mH467
open _root_.P2M661a572e renaming h468 → _p2mH468
open _root_.P2M661a572e renaming h469 → _p2mH469
end CurrentAFT.CurrentReferenceDrawRates
open _root_.P2M661a572e renaming h466 → _p2mH466
open _root_.P2M661a572e renaming h467 → _p2mH467
open _root_.P2M661a572e renaming h468 → _p2mH468
open _root_.P2M661a572e renaming h469 → _p2mH469
end
open _root_.P2M661a572e renaming h469 → _p2mH469
open _root_.P2M661a572e renaming h468 → _p2mH468
open _root_.P2M661a572e renaming h467 → _p2mH467
open _root_.P2M661a572e renaming h466 → _p2mH466
section
namespace CurrentAFT.CurrentCoreProposalLaw
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge CurrentReferenceDraw CurrentProposalDimensions CurrentCoreProposal
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentCoreProposal.draw CurrentPermutationDraw.draw
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h561 {security : ℕ} (first second : Core security)
    (hc : first.controls = second.controls) (hl : first.legs = second.legs)
    (hq : first.queueBaselines = second.queueBaselines) (hb : first.bodyPermutation = second.bodyPermutation)
    (he : first.endpointPermutation = second.endpointPermutation) : first = second := by
  cases first
  cases second
  cases hc
  cases hl
  cases hq
  cases hb
  cases he
  rfl
open _root_.P2M661a572e renaming h561 → _p2mH561
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h299 (security tableBits bits : ℕ) (cache : Cache security tableBits) (word : Tapes security bits) :
    (draw security tableBits bits cache word).value.core = assemble security (sourceValue security tableBits bits cache word) := by
  apply _p2mH561
  · funext index; exact _p2mH296 security tableBits bits cache word index
  · funext index; exact _p2mH298 security tableBits bits cache word index
  · funext index; exact _p2mH294 security tableBits bits cache word index
  · exact _p2mH295 security tableBits bits cache word
  · exact _p2mH297 security tableBits bits cache word
open _root_.P2M661a572e renaming h299 → _p2mH299
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h301 (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    (tapeLaw security bits).map (sourceValue security tableBits bits cache) = sourceLaw security tableBits bits cache := by
  let controlValue := fun word : PublicOutputExperiment.PublicIndex security → ControlTape security bits =>
    fun index => (controlDraw security tableBits bits cache (word index)).value
  let legValue := fun word : Fin (Parameters.legCount security) → LegTape security bits =>
    fun index => (legDraw security tableBits bits cache (word index)).value
  let queueValue := fun word : Fin (Parameters.modulus security) → CurrentSafeDraw.Tape security bits =>
    fun index => (CurrentSafeDraw.draw security bits (word index)).value
  let bodyValue := fun word : Fin ((current security).body * bits) → Fin 2 =>
    (CurrentProposalDimensions.bodyEquiv security).permCongr (PermutationProgram.draw (current security).body bits word)
  let endpointValue := fun word : Fin ((current security).dimension * bits) → Fin 2 =>
    (endpointEquiv security).permCongr (PermutationProgram.draw (current security).dimension bits word)
  have hcontrol := _p2mH64
    (Index := PublicOutputExperiment.PublicIndex security) (Random := ControlTape security bits)
    (State := SafeControlGroups.SafeGroup security)
    (fun _ => controlTapeLaw security bits) (fun _ word => (controlDraw security tableBits bits cache word).value)
  have hleg := _p2mH64
    (Index := Fin (Parameters.legCount security)) (Random := LegTape security bits) (State := LegCore security)
    (fun _ => legTapeLaw security bits) (fun _ word => (legDraw security tableBits bits cache word).value)
  have hqueue := _p2mH64
    (Index := Fin (Parameters.modulus security)) (Random := CurrentSafeDraw.Tape security bits)
    (State := FirstHistogram.Palette security)
    (fun _ => FiniteDist.uniform (CurrentSafeDraw.Tape security bits))
    (fun _ word => (CurrentSafeDraw.draw security bits word).value)
  have hbody : (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2)).map bodyValue =
      bodyPermutationLaw security bits := by
    unfold bodyPermutationLaw CurrentPermutationDraw.law
    rw [FiniteDist.map_map]
    congr 1
    funext word
    dsimp only [bodyValue]
    rw [_p2mH430]
    congr 1
    congr 1
    funext index
    exact (Vector.get_ofFn word index).symm
  have hendpoint : (FiniteDist.uniform (Fin ((current security).dimension * bits) → Fin 2)).map endpointValue =
      endpointPermutationLaw security bits := by
    unfold endpointPermutationLaw CurrentPermutationDraw.law
    rw [FiniteDist.map_map]
    congr 1
    funext word
    dsimp only [endpointValue]
    rw [_p2mH430]
    congr 1
    congr 1
    funext index
    exact (Vector.get_ofFn word index).symm
  have hfirst := _p2mH87
    (FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits))
    (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits)) controlValue legValue
  rw [hcontrol, hleg] at hfirst
  have hsecond := _p2mH87
    ((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits)))
    (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits)))
    (fun pair => (controlValue pair.1, legValue pair.2)) queueValue
  rw [hfirst, hqueue] at hsecond
  have hthird := _p2mH87
    (((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits))))
    (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2))
    (fun pair => ((controlValue pair.1.1, legValue pair.1.2), queueValue pair.2)) bodyValue
  rw [hsecond, hbody] at hthird
  have hfourth := _p2mH87
    ((((FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security => controlTapeLaw security bits)).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legTapeLaw security bits))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => FiniteDist.uniform (CurrentSafeDraw.Tape security bits)))).prod
      (FiniteDist.uniform (Fin ((current security).body * bits) → Fin 2)))
    (FiniteDist.uniform (Fin ((current security).dimension * bits) → Fin 2))
    (fun pair => (((controlValue pair.1.1.1, legValue pair.1.1.2), queueValue pair.1.2), bodyValue pair.2)) endpointValue
  rw [hthird, hendpoint] at hfourth
  exact hfourth
open _root_.P2M661a572e renaming h301 → _p2mH301
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h300 (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    law security tableBits bits cache = (sourceLaw security tableBits bits cache).map (assemble security) := by
  simp only [law, _p2mH299, ← FiniteDist.map_map, _p2mH301]
open _root_.P2M661a572e renaming h300 → _p2mH300
end
open _root_.P2M661a572e renaming h299 → _p2mH299
open _root_.P2M661a572e renaming h300 → _p2mH300
open _root_.P2M661a572e renaming h301 → _p2mH301
open _root_.P2M661a572e renaming h561 → _p2mH561
end CurrentAFT.CurrentCoreProposalLaw
open _root_.P2M661a572e renaming h299 → _p2mH299
open _root_.P2M661a572e renaming h300 → _p2mH300
open _root_.P2M661a572e renaming h301 → _p2mH301
open _root_.P2M661a572e renaming h561 → _p2mH561
end
open _root_.P2M661a572e renaming h301 → _p2mH301
open _root_.P2M661a572e renaming h299 → _p2mH299
open _root_.P2M661a572e renaming h300 → _p2mH300
section
namespace CurrentAFT.CurrentCoreProposalRates
open AFT ActualPublicCharge CurrentReferenceDraw CurrentReferenceDrawRates CurrentProposalDimensions
  CurrentCoreProposal CurrentCoreProposalLaw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h304 (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    controlLaw security tableBits bits cache =
      (primaryDrawLaw security tableBits bits cache).prod (bodyDrawLaw security tableBits bits cache) := by
  exact _p2mH87
    (FiniteDist.uniform (Fin (bits + (PublicParameterProgram.modulus security).count + 1) → Fin 2))
    (FiniteDist.uniform (Fin (bits + (CurrentReferenceDraw.counts security).safe + 1) → Fin 2))
    (fun word => (CurrentReferenceDraw.primaryDraw security tableBits bits cache word).value)
    (fun word => (CurrentReferenceDraw.bodyDraw security tableBits bits cache word).value)
open _root_.P2M661a572e renaming h304 → _p2mH304
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h307 (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    legLaw security tableBits bits cache =
      (CurrentPublicSeedDraw.law security tableBits bits cache).prod (CurrentSafeDraw.law security bits) := by
  exact _p2mH87 (CurrentPublicSeedDraw.tapeLaw security bits)
    (FiniteDist.uniform (CurrentSafeDraw.Tape security bits))
    (fun word => (CurrentPublicSeedDraw.draw security tableBits bits cache word).value)
    (fun word => (CurrentSafeDraw.draw security bits word).value)
open _root_.P2M661a572e renaming h307 → _p2mH307
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h303 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (hprecision : ticketError tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError tableBits ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ group, |(controlLaw security tableBits bits cache).weight group -
      (SafeControlGroups.reference security).weight group|) ≤ controlError security tableBits bits := by
  rw [_p2mH304]
  apply (FiniteDist.l1_prod_le _ (ProposalPrimary.primaryLaw security) _ (ActualControls.bodyReference security)).trans
  have hp := _p2mH468 security tableBits bits cache hprecision hbudget
  have hb := _p2mH466 security tableBits bits cache hprecision hbudget
  unfold controlError ticketError
  linarith
open _root_.P2M661a572e renaming h303 → _p2mH303
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h306 (security tableBits bits : ℕ) (cache : Cache security tableBits) :
    (∑ leg, |(legLaw security tableBits bits cache).weight leg - (legCoreLaw security).weight leg|) ≤
      5 * ticketError bits + ticketError tableBits := by
  rw [_p2mH307]
  have h := FiniteDist.l1_prod_le (CurrentPublicSeedDraw.law security tableBits bits cache)
    (ActualPublicLegCharge.seedLaw security) (CurrentSafeDraw.law security bits) (ProposalPrimary.safeLaw security)
  have hs := _p2mH456 security tableBits bits cache
  have hb := _p2mH471 security bits
  unfold ticketError
  change (∑ leg, |((CurrentPublicSeedDraw.law security tableBits bits cache).prod (CurrentSafeDraw.law security bits)).weight leg -
    ((ActualPublicLegCharge.seedLaw security).prod (ProposalPrimary.safeLaw security)).weight leg|) ≤ _
  linarith
open _root_.P2M661a572e renaming h306 → _p2mH306
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h302 (security bits : ℕ) :
    (∑ permutation, |(CurrentCoreProposalLaw.bodyPermutationLaw security bits).weight permutation -
      (FiniteDist.uniform (Equiv.Perm (ActualCycleMeanMGF.BodyIndex security))).weight permutation|) ≤
      2 * ((current security).body : ℝ)^2 * ticketError bits := by
  have h := FiniteDist.l1_map_le (CurrentPermutationDraw.law (current security).body bits)
    (FiniteDist.uniform (Equiv.Perm (Fin (current security).body))) (CurrentProposalDimensions.bodyEquiv security).permCongr
  rw [FiniteDist.uniform_map_equiv] at h
  exact h.trans (by simpa only [ticketError, div_eq_mul_inv, one_mul] using _p2mH433 (current security).body bits)
open _root_.P2M661a572e renaming h302 → _p2mH302
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h305 (security bits : ℕ) :
    (∑ permutation, |(CurrentCoreProposalLaw.endpointPermutationLaw security bits).weight permutation -
      (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security)))).weight permutation|) ≤
      2 * ((current security).dimension : ℝ)^2 * ticketError bits := by
  have h := FiniteDist.l1_map_le (CurrentPermutationDraw.law (current security).dimension bits)
    (FiniteDist.uniform (Equiv.Perm (Fin (current security).dimension))) (endpointEquiv security).permCongr
  rw [FiniteDist.uniform_map_equiv] at h
  exact h.trans (by simpa only [ticketError, div_eq_mul_inv, one_mul] using _p2mH433 (current security).dimension bits)
open _root_.P2M661a572e renaming h305 → _p2mH305
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h308 (security tableBits bits : ℕ) (cache : Cache security tableBits)
    (hprecision : ticketError tableBits ≤ 1 / (4 * (Parameters.base security : ℝ)))
    (hbudget : 64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError tableBits ≤
      1 / (4 * (Parameters.modulus security : ℝ))) :
    (∑ core, |(CurrentCoreProposalLaw.law security tableBits bits cache).weight core -
      (proposal security).weight core|) ≤ error security tableBits bits := by
  have hcontrol := FiniteDist.l1_independent_le
    (fun _ : PublicOutputExperiment.PublicIndex security => controlLaw security tableBits bits cache)
    (fun _ => SafeControlGroups.reference security)
  have hc : (∑ controls, |(FiniteDist.independent (fun _ : PublicOutputExperiment.PublicIndex security =>
        controlLaw security tableBits bits cache)).weight controls - (PublicOutputExperiment.reference security).weight controls|) ≤
      ((current security).controls : ℝ) * controlError security tableBits bits := by
    apply hcontrol.trans
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun _ : PublicOutputExperiment.PublicIndex security => fun _ => _p2mH303 security tableBits bits cache hprecision hbudget)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul,
      (current_values security).2.2.2.2.2, Nat.cast_add] using hsum
  have hl := FiniteDist.l1_independent_fin_le (Parameters.legCount security)
    (fun _ => legLaw security tableBits bits cache) (fun _ => legCoreLaw security)
  have hl' : (∑ legs, |(FiniteDist.independent (fun _ : Fin (Parameters.legCount security) =>
      legLaw security tableBits bits cache)).weight legs -
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security)).weight legs|) ≤
      (Parameters.legCount security : ℝ) * (5 * ticketError bits + ticketError tableBits) := by
    apply hl.trans
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun _ : Fin (Parameters.legCount security) => fun _ => _p2mH306 security tableBits bits cache)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  have hq := FiniteDist.l1_independent_fin_le (Parameters.modulus security)
    (fun _ => CurrentSafeDraw.law security bits) (fun _ => ProposalPrimary.safeLaw security)
  have hq' : (∑ baselines, |(FiniteDist.independent (fun _ : Fin (Parameters.modulus security) =>
      CurrentSafeDraw.law security bits)).weight baselines -
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => ProposalPrimary.safeLaw security)).weight baselines|) ≤
      (Parameters.modulus security : ℝ) * ticketError bits := by
    apply hq.trans
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun _ : Fin (Parameters.modulus security) => fun _ => _p2mH471 security bits)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hsum
  let target : FiniteDist (Source security) :=
    ((((PublicOutputExperiment.reference security).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.legCount security) => legCoreLaw security))).prod
      (FiniteDist.independent (fun _ : Fin (Parameters.modulus security) => ProposalPrimary.safeLaw security))).prod
      (FiniteDist.uniform (Equiv.Perm (ActualCycleMeanMGF.BodyIndex security)))).prod
      (FiniteDist.uniform (Equiv.Perm (Fin (Parameters.dimension security))))
  rw [_p2mH300]
  have he : proposal security = target.map (assemble security) := rfl
  rw [he]
  apply (FiniteDist.l1_map_le _ _ (assemble security)).trans
  unfold sourceLaw target
  apply (FiniteDist.l1_prod_le _ _ _ _).trans
  apply add_le_add _ (_p2mH305 security bits)
  apply (FiniteDist.l1_prod_le _ _ _ _).trans
  apply add_le_add _ (_p2mH302 security bits)
  apply (FiniteDist.l1_prod_le _ _ _ _).trans
  apply add_le_add _ hq'
  exact (FiniteDist.l1_prod_le _ _ _ _).trans (add_le_add hc hl')
open _root_.P2M661a572e renaming h308 → _p2mH308
end
open _root_.P2M661a572e renaming h302 → _p2mH302
open _root_.P2M661a572e renaming h303 → _p2mH303
open _root_.P2M661a572e renaming h304 → _p2mH304
open _root_.P2M661a572e renaming h305 → _p2mH305
open _root_.P2M661a572e renaming h306 → _p2mH306
open _root_.P2M661a572e renaming h307 → _p2mH307
open _root_.P2M661a572e renaming h308 → _p2mH308
end CurrentAFT.CurrentCoreProposalRates
open _root_.P2M661a572e renaming h302 → _p2mH302
open _root_.P2M661a572e renaming h303 → _p2mH303
open _root_.P2M661a572e renaming h304 → _p2mH304
open _root_.P2M661a572e renaming h305 → _p2mH305
open _root_.P2M661a572e renaming h306 → _p2mH306
open _root_.P2M661a572e renaming h307 → _p2mH307
open _root_.P2M661a572e renaming h308 → _p2mH308
end
open _root_.P2M661a572e renaming h304 → _p2mH304
open _root_.P2M661a572e renaming h307 → _p2mH307
open _root_.P2M661a572e renaming h303 → _p2mH303
open _root_.P2M661a572e renaming h308 → _p2mH308
open _root_.P2M661a572e renaming h306 → _p2mH306
open _root_.P2M661a572e renaming h302 → _p2mH302
open _root_.P2M661a572e renaming h305 → _p2mH305
section
namespace CurrentAFT.CurrentProposalPrecision
open AFT CurrentCoreProposalRates CurrentReferenceDraw
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h445 (security : ℕ) :
    256 * Parameters.base security * Parameters.dimension security * Parameters.modulus security ≤ padding security := by
  have hb : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by decide)
  calc
    _ ≤ 256 * Parameters.base security * (131074 * Parameters.base security^160) *
        (131072 * Parameters.base security^64) := by
      gcongr
      · exact (Parameters.dimension_bounds security).2
      · exact (Parameters.modulus_bounds security).2
    _ = (256 * 131074 * 131072) * Parameters.base security^225 := by
      rw [show (225 : ℕ) = 1 + 160 + 64 from rfl, pow_add, pow_add, pow_one]
      ac_rfl
    _ ≤ 2^44 * Parameters.base security^226 := Nat.mul_le_mul (by norm_num)
      (Nat.pow_le_pow_right hb (by decide))
    _ = padding security := by simp only [padding, Parameters.base]
open _root_.P2M661a572e renaming h445 → _p2mH445
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h444 (security : ℕ) : 4 * Parameters.base security ≤ padding security := by
  have hb : 1 ≤ Parameters.base security := (Parameters.base_ge_two security).trans' (by decide)
  have h := Nat.mul_le_mul (by norm_num : 4 ≤ 2^44)
    (Nat.pow_le_pow_right hb (by decide : 1 ≤ 226))
  simpa only [pow_one, Parameters.base] using h
open _root_.P2M661a572e renaming h444 → _p2mH444
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h564 (security bits : ℕ) :
    (padding security : ℝ) ≤ (2 : ℝ)^tableBits security bits := by
  have h := (Nat.lt_two_pow_self (n := padding security)).le.trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by change padding security ≤ bits + padding security; omega : padding security ≤ tableBits security bits))
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr h
open _root_.P2M661a572e renaming h564 → _p2mH564
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h446 (security bits : ℕ) :
    ticketError (tableBits security bits) ≤ 1 / (4 * (Parameters.base security : ℝ)) ∧
    64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError (tableBits security bits) ≤
      1 / (4 * (Parameters.modulus security : ℝ)) := by
  have hb : (0 : ℝ) < Parameters.base security := Nat.cast_pos.mpr (Parameters.base_pos security)
  have hq : (0 : ℝ) < Parameters.modulus security := Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos
  have hfour₀ : (4 : ℝ) * Parameters.base security ≤ (padding security : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr (_p2mH444 security)
  have hfull₀ : (256 : ℝ) * Parameters.base security * Parameters.dimension security * Parameters.modulus security ≤
      (padding security : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr (_p2mH445 security)
  have hfour : (4 : ℝ) * Parameters.base security ≤ (2 : ℝ)^tableBits security bits :=
    hfour₀.trans (_p2mH564 security bits)
  have hfull : (256 : ℝ) * Parameters.base security * Parameters.dimension security * Parameters.modulus security ≤
      (2 : ℝ)^tableBits security bits := hfull₀.trans (_p2mH564 security bits)
  constructor
  · exact one_div_le_one_div_of_le (by positivity) hfour
  · apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Parameters.modulus security)).mpr
    calc
      64 * (Parameters.base security : ℝ) * Parameters.dimension security * ticketError (tableBits security bits) *
          (4 * Parameters.modulus security) =
          (256 * (Parameters.base security : ℝ) * Parameters.dimension security * Parameters.modulus security) /
            (2 : ℝ)^tableBits security bits := by
              unfold ticketError
              rw [div_eq_mul_inv, div_eq_mul_inv, one_mul, show (256 : ℝ) = 64 * 4 by norm_num]
              ac_rfl
      _ ≤ 1 := (div_le_one₀ (by positivity)).mpr hfull
open _root_.P2M661a572e renaming h446 → _p2mH446
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h447 (security bits : ℕ) (cache : Cache security (tableBits security bits)) :
    (∑ core, |(CurrentCoreProposalLaw.law security (tableBits security bits) bits cache).weight core -
      (ActualPublicCharge.proposal security).weight core|) ≤ error security (tableBits security bits) bits :=
  _p2mH308 security (tableBits security bits) bits cache
    (_p2mH446 security bits).1 (_p2mH446 security bits).2
open _root_.P2M661a572e renaming h447 → _p2mH447
end
open _root_.P2M661a572e renaming h444 → _p2mH444
open _root_.P2M661a572e renaming h445 → _p2mH445
open _root_.P2M661a572e renaming h446 → _p2mH446
open _root_.P2M661a572e renaming h447 → _p2mH447
open _root_.P2M661a572e renaming h564 → _p2mH564
end CurrentAFT.CurrentProposalPrecision
open _root_.P2M661a572e renaming h444 → _p2mH444
open _root_.P2M661a572e renaming h445 → _p2mH445
open _root_.P2M661a572e renaming h446 → _p2mH446
open _root_.P2M661a572e renaming h447 → _p2mH447
open _root_.P2M661a572e renaming h564 → _p2mH564
end
open _root_.P2M661a572e renaming h446 → _p2mH446
open _root_.P2M661a572e renaming h447 → _p2mH447
open _root_.P2M661a572e renaming h445 → _p2mH445
open _root_.P2M661a572e renaming h444 → _p2mH444
section
namespace CurrentAFT.BinaryProposalPrecision
open AFT BinaryArithmetic Polynomial
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
attribute [local irreducible] addCounter powerCounter multiplyCounter
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h190 (security bits : ℕ) :
    (current security bits).count = CurrentProposalPrecision.tableBits security bits := by
  simp only [current, addCounter_value, powerCounter_value, multiplyCounter_value]
open _root_.P2M661a572e renaming h190 → CurrentAFT.BinaryProposalPrecision.current_value
open _root_.P2M661a572e renaming h190 → _p2mH190
end CurrentAFT.BinaryProposalPrecision
open _root_.P2M661a572e renaming h190 → CurrentAFT.BinaryProposalPrecision.current_value
open _root_.P2M661a572e renaming h190 → _p2mH190
end
open _root_.P2M661a572e renaming h190 → CurrentAFT.BinaryProposalPrecision.current_value
open _root_.P2M661a572e renaming h190 → _p2mH190
section
namespace CurrentAFT.CurrentPreparedCoreProposal
open AFT AFT.BinaryArithmetic AFT.RationalNumerics AFT.RationalRejectionProgram
open CurrentReferenceDraw CurrentCoreProposal CurrentProposalResources
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentCoreProposal.draw BinaryReferenceTables.current
  CurrentReferenceDraw.counts PublicParameterProgram.modulus
noncomputable section
open scoped Classical
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h438 (security tableBits bits : ℕ) :
    (law security tableBits bits).map MaterializedCore.core =
      CurrentCoreProposalLaw.law security tableBits bits (cache security tableBits) := by
  rw [law, FiniteDist.map_map]
  rfl
open _root_.P2M661a572e renaming h438 → _p2mH438
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h439 (security bits : ℕ) :
    (∑ core, |((law security (CurrentProposalPrecision.tableBits security bits) bits).map MaterializedCore.core).weight core -
      (ActualPublicCharge.proposal security).weight core|) ≤
      CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security bits) bits := by
  rw [_p2mH438]
  exact _p2mH447 security bits (cache security _)
open _root_.P2M661a572e renaming h439 → _p2mH439
end
open _root_.P2M661a572e renaming h438 → _p2mH438
open _root_.P2M661a572e renaming h439 → _p2mH439
end CurrentAFT.CurrentPreparedCoreProposal
open _root_.P2M661a572e renaming h438 → _p2mH438
open _root_.P2M661a572e renaming h439 → _p2mH439
end
open _root_.P2M661a572e renaming h439 → _p2mH439
open _root_.P2M661a572e renaming h438 → _p2mH438
section
namespace CurrentAFT.RejectionProjection
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 400000
variable {State Output Tape : Type*}
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h537 (decode : State → Output) (fallback : State) (attempts : ℕ)
    (proposals : Fin attempts → State × Fin 2) :
    decode (RationalRejectionProgram.run fallback attempts proposals) =
      RationalRejectionProgram.run (decode fallback) attempts
        (fun index => (decode (proposals index).1, (proposals index).2)) := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
    simp only [RationalRejectionProgram.run]
    split_ifs
    · rfl
    · exact ih (fun index => proposals index.succ)
open _root_.P2M661a572e renaming h537 → _p2mH537
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h536 [Inhabited Tape] (decode : State → Output) (sample : Tape → CountedValue State)
    (score : State → CountedValue RationalBits) (targetScore : Output → ℚ)
    (hscore : ∀ state, (score state).value.decode = targetScore (decode state))
    (envelope : RationalBits) (envelopeValue bits : ℕ) (he : envelope.decode = (envelopeValue : ℚ))
    (fallback : CountedValue State) (attempts : ℕ) (words : Vector (Tape × (Fin bits → Fin 2)) attempts) :
    decode (BinaryArrayRejection.run sample score envelope bits fallback attempts words).value =
      RationalRejectionProgram.positiveDraw (fun input => decode (sample input).value) targetScore
        envelopeValue bits attempts (decode fallback.value) words.get := by
  rw [_p2mH167, _p2mH29 sample score envelope envelopeValue bits he]
  unfold RationalRejectionProgram.positiveDraw RationalRejectionProgram.draw
  rw [_p2mH537 decode]
  congr 1
  funext index
  simp only [RationalRejectionProgram.proposal, hscore]
open _root_.P2M661a572e renaming h536 → _p2mH536
end CurrentAFT.RejectionProjection
open _root_.P2M661a572e renaming h536 → _p2mH536
open _root_.P2M661a572e renaming h537 → _p2mH537
end
open _root_.P2M661a572e renaming h536 → _p2mH536
open _root_.P2M661a572e renaming h537 → _p2mH537
section
namespace CurrentAFT
open AFT
open scoped BigOperators Classical
noncomputable section
variable {Core : Type*} [Fintype Core]
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h547 (proposal : FiniteDist Core)
    (weight : Core → ℝ) (charge : Core → Prop) :
    proposal.acceptance (clippedChargeCoin weight charge) =
      publicCoreMass proposal weight charge / 2 := by
  unfold FiniteDist.acceptance publicCoreMass clippedPublicCoreWeight clippedChargeCoin
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro core _
  split_ifs <;> ring
open _root_.P2M661a572e renaming h547 → _p2mH547
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h542 (proposal : FiniteDist Core)
    (weight : Core → ℝ) (charge : Core → Prop)
    (hpositive : 0 < publicCoreMass proposal weight charge) :
    proposal.acceptedLaw (clippedChargeCoin weight charge)
      (fun core => (clippedChargeCoin_bounds weight charge core).1)
      (by rw [_p2mH547]; positivity) =
        positivePublicCoreLaw proposal weight charge hpositive := by
  ext core
  change proposal.weight core * clippedChargeCoin weight charge core /
      proposal.acceptance (clippedChargeCoin weight charge) =
    clippedPublicCoreWeight proposal weight charge core / publicCoreMass proposal weight charge
  rw [_p2mH547]
  unfold clippedChargeCoin clippedPublicCoreWeight
  by_cases hcharge : charge core
  · simp only [if_pos hcharge]
    field_simp [hpositive.ne']
  · simp [hcharge]
open _root_.P2M661a572e renaming h542 → _p2mH542
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h548 (proposal : FiniteDist Core)
    (weight : Core → ℝ) (charge : Core → Prop) (q : ℝ) (hq : 0 < q)
    (hmass : 1 / (4 * q) ≤ publicCoreMass proposal weight charge)
    (fallback : FiniteDist Core) (trials : ℕ) :
    FiniteDist.TVBound
      (proposal.cappedRejection (clippedChargeCoin weight charge)
        (clippedChargeCoin_bounds weight charge) fallback trials)
      (positivePublicCoreLaw proposal weight charge
        (lt_of_lt_of_le (by positivity) hmass))
      (Real.exp (-(trials : ℝ) / (8 * q))) := by
  have hpositive : 0 < publicCoreMass proposal weight charge :=
    lt_of_lt_of_le (by positivity) hmass
  have haccept : 0 < proposal.acceptance (clippedChargeCoin weight charge) := by
    rw [_p2mH547]
    positivity
  have hlower : 1 / (8 * q) ≤ proposal.acceptance (clippedChargeCoin weight charge) := by
    rw [_p2mH547]
    have hhalf : (1 / (4 * q)) / 2 = 1 / (8 * q) := by ring
    linarith
  have hbound := _p2mH72 proposal (clippedChargeCoin weight charge)
    (clippedChargeCoin_bounds weight charge) haccept fallback trials
  rw [_p2mH542 proposal weight charge hpositive] at hbound
  apply hbound.mono
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlower (Nat.cast_nonneg trials)
  calc
    _ = -((trials : ℝ) * proposal.acceptance (clippedChargeCoin weight charge)) := by ring
    _ ≤ -((trials : ℝ) * (1 / (8 * q))) := neg_le_neg h
    _ = _ := by ring
open _root_.P2M661a572e renaming h548 → _p2mH548
end
open _root_.P2M661a572e renaming h542 → _p2mH542
open _root_.P2M661a572e renaming h547 → _p2mH547
open _root_.P2M661a572e renaming h548 → _p2mH548
end CurrentAFT
open _root_.P2M661a572e renaming h542 → _p2mH542
open _root_.P2M661a572e renaming h547 → _p2mH547
open _root_.P2M661a572e renaming h548 → _p2mH548
end
open _root_.P2M661a572e renaming h542 → _p2mH542
open _root_.P2M661a572e renaming h547 → _p2mH547
open _root_.P2M661a572e renaming h548 → _p2mH548
section
namespace CurrentAFT.OptionRejection
open AFT
open scoped BigOperators Classical
noncomputable section
variable {Core : Type*} [Fintype Core]
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h507 (proposal : FiniteDist Core) : (proposal.map some).weight none = 0 := by
  simp [FiniteDist.map_weight]
open _root_.P2M661a572e renaming h507 → _p2mH507
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h508 (proposal : FiniteDist Core) (core : Core) :
    (proposal.map some).weight (some core) = proposal.weight core := by
  simp [FiniteDist.map_weight]
open _root_.P2M661a572e renaming h508 → _p2mH508
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h505 (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop) :
    publicCoreMass (proposal.map some) (weight value) (charge predicate) =
      publicCoreMass proposal value predicate := by
  simp only [publicCoreMass, Fintype.sum_option, clippedPublicCoreWeight, charge, weight,
    if_false, zero_add, _p2mH508]
open _root_.P2M661a572e renaming h505 → CurrentAFT.OptionRejection.mass
open _root_.P2M661a572e renaming h505 → _p2mH505
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h506 (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop)
    (hpositive : 0 < publicCoreMass proposal value predicate) :
    positivePublicCoreLaw (proposal.map some) (weight value) (charge predicate)
      (by rw [_p2mH505]; exact hpositive) = (positivePublicCoreLaw proposal value predicate hpositive).map some := by
  ext output
  cases output with
  | none =>
    simp [positivePublicCoreLaw, FiniteDist.normalize, clippedPublicCoreWeight, charge, _p2mH507]
  | some core =>
    rw [_p2mH508]
    change clippedPublicCoreWeight (proposal.map some) (weight value) (charge predicate) (some core) /
      publicCoreMass (proposal.map some) (weight value) (charge predicate) =
      clippedPublicCoreWeight proposal value predicate core / publicCoreMass proposal value predicate
    rw [_p2mH505]
    simp only [clippedPublicCoreWeight, charge, weight, _p2mH508]
open _root_.P2M661a572e renaming h506 → _p2mH506
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h504 (proposal : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop)
    (q : ℝ) (hq : 0 < q) (hmass : 1/(4*q) ≤ publicCoreMass proposal value predicate) (trials : ℕ) :
    FiniteDist.TVBound (ideal proposal value predicate trials)
      ((positivePublicCoreLaw proposal value predicate (lt_of_lt_of_le (by positivity) hmass)).map some)
      (Real.exp (-(trials : ℝ)/(8*q))) := by
  have h := _p2mH548 (proposal.map some) (weight value) (charge predicate)
    q hq (by rw [_p2mH505]; exact hmass) (CanonicalMoments.pointLaw none) trials
  rw [_p2mH506] at h
  exact h
open _root_.P2M661a572e renaming h504 → _p2mH504
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h503 (proposal approximation : FiniteDist Core) (value : Core → ℝ) (predicate : Core → Prop)
    (coin : Option Core → ℝ) (hcoin : ∀ core, 0 ≤ coin core ∧ coin core ≤ 1)
    (q proposalError coinError : ℝ) (hq : 0 < q)
    (hmass : 1/(4*q) ≤ publicCoreMass proposal value predicate)
    (hproposal : FiniteDist.TVBound approximation proposal proposalError)
    (herror : ∀ core, |coin core-clippedChargeCoin (weight value) (charge predicate) core| ≤ coinError)
    (trials : ℕ) :
    FiniteDist.TVBound
      ((approximation.map some).cappedRejection coin hcoin (CanonicalMoments.pointLaw none) trials)
      ((positivePublicCoreLaw proposal value predicate (lt_of_lt_of_le (by positivity) hmass)).map some)
      ((trials : ℝ)*(proposalError+coinError)+Real.exp (-(trials : ℝ)/(8*q))) := by
  have hp := _p2mH73 (approximation.map some) (proposal.map some)
    coin hcoin (CanonicalMoments.pointLaw none) proposalError (hproposal.map some) trials
  have hc := _p2mH71 (proposal.map some) coin
    (clippedChargeCoin (weight value) (charge predicate)) hcoin
    (clippedChargeCoin_bounds (weight value) (charge predicate)) (CanonicalMoments.pointLaw none)
    coinError herror trials
  have ht := _p2mH504 proposal value predicate q hq hmass trials
  convert (hp.triangle hc).triangle ht using 1
  ring
open _root_.P2M661a572e renaming h503 → _p2mH503
end
open _root_.P2M661a572e renaming h503 → _p2mH503
open _root_.P2M661a572e renaming h504 → _p2mH504
open _root_.P2M661a572e renaming h505 → CurrentAFT.OptionRejection.mass
open _root_.P2M661a572e renaming h505 → _p2mH505
open _root_.P2M661a572e renaming h506 → _p2mH506
open _root_.P2M661a572e renaming h507 → _p2mH507
open _root_.P2M661a572e renaming h508 → _p2mH508
end CurrentAFT.OptionRejection
open _root_.P2M661a572e renaming h503 → _p2mH503
open _root_.P2M661a572e renaming h504 → _p2mH504
open _root_.P2M661a572e renaming h505 → CurrentAFT.OptionRejection.mass
open _root_.P2M661a572e renaming h505 → _p2mH505
open _root_.P2M661a572e renaming h506 → _p2mH506
open _root_.P2M661a572e renaming h507 → _p2mH507
open _root_.P2M661a572e renaming h508 → _p2mH508
end
open _root_.P2M661a572e renaming h505 → CurrentAFT.OptionRejection.mass
open _root_.P2M661a572e renaming h505 → _p2mH505
open _root_.P2M661a572e renaming h508 → _p2mH508
open _root_.P2M661a572e renaming h503 → _p2mH503
open _root_.P2M661a572e renaming h507 → _p2mH507
open _root_.P2M661a572e renaming h504 → _p2mH504
open _root_.P2M661a572e renaming h506 → _p2mH506
section
set_option backward.isDefEq.respectTransparency false
namespace CurrentAFT.ClippedRejectionCoin
open AFT
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h223 (bits : ℕ) (accepted : Bool) (score : ℚ) :
    0 ≤ probability bits accepted score ∧ probability bits accepted score ≤ 1 :=
  _p2mH114 _ _
open _root_.P2M661a572e renaming h223 → _p2mH223
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h224 (score : ℚ) :
    (RationalAcceptanceCoin.clipped (max score 0 / 2) : ℝ) = clip (score : ℝ)/2 := by
  have hn : (0 : ℝ) ≤ max (score : ℝ) 0 / 2 := by positivity
  simp only [RationalAcceptanceCoin.clipped, Rat.cast_min, Rat.cast_max, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_zero, Rat.cast_one]
  rw [max_eq_left hn]
  rw [show (1 : ℝ) = 2/2 by norm_num]
  rw [min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [clip, max_comm]
open _root_.P2M661a572e renaming h224 → _p2mH224
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h227 (bits : ℕ) (accepted : Bool) (score : ℚ) (target error : ℝ)
    (he : 0 ≤ error) (herror : |(score : ℝ)-target| ≤ error) :
    |probability bits accepted score - (if accepted then clip target/2 else 0)| ≤
      1/(2 : ℝ)^bits+error/2 := by
  cases accepted with
  | false =>
    norm_num [probability, raw, RationalAcceptanceCoin.probability, RationalAcceptanceCoin.count,
      RationalAcceptanceCoin.clipped]
    positivity
  | true =>
    simp only [probability, raw, if_true]
    have hf := _p2mH115 bits (max score 0/2)
    rw [_p2mH224] at hf
    have hc : |clip (score : ℝ)/2-clip target/2| ≤ error/2 := by
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact div_le_div_of_nonneg_right ((_p2mH543 _ _).trans herror) (by norm_num)
    exact (abs_sub_le _ _ _).trans (add_le_add hf hc)
open _root_.P2M661a572e renaming h227 → _p2mH227
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h225 {Core : Type*} (bits : ℕ) (accepted : Core → Bool) (score : Core → ℚ) :
    ∀ core, 0 ≤ optionCoin bits accepted score core ∧ optionCoin bits accepted score core ≤ 1 := by
  intro core
  cases core with
  | none => exact ⟨le_rfl, by norm_num [optionCoin]⟩
  | some core => exact _p2mH223 bits (accepted core) (score core)
open _root_.P2M661a572e renaming h225 → _p2mH225
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h226 {Core : Type*} (bits : ℕ) (accepted : Core → Bool) (score : Core → ℚ)
    (target : Core → ℝ) (predicate : Core → Prop) (error : ℝ) (he : 0 ≤ error)
    (haccepted : ∀ core, accepted core = true ↔ predicate core)
    (herror : ∀ core, |(score core : ℝ)-target core| ≤ error) (core : Option Core) :
    |optionCoin bits accepted score core -
      clippedChargeCoin (OptionRejection.weight target) (OptionRejection.charge predicate) core| ≤
      1/(2 : ℝ)^bits+error/2 := by
  cases core with
  | none => simp only [optionCoin, clippedChargeCoin, OptionRejection.charge, if_false, sub_self, abs_zero]; positivity
  | some core =>
    have h := _p2mH227 bits (accepted core) (score core) (target core) error he (herror core)
    simpa only [optionCoin, clippedChargeCoin, OptionRejection.charge, OptionRejection.weight, haccepted] using h
open _root_.P2M661a572e renaming h226 → _p2mH226
end
open _root_.P2M661a572e renaming h223 → _p2mH223
open _root_.P2M661a572e renaming h224 → _p2mH224
open _root_.P2M661a572e renaming h225 → _p2mH225
open _root_.P2M661a572e renaming h226 → _p2mH226
open _root_.P2M661a572e renaming h227 → _p2mH227
end CurrentAFT.ClippedRejectionCoin
open _root_.P2M661a572e renaming h223 → _p2mH223
open _root_.P2M661a572e renaming h224 → _p2mH224
open _root_.P2M661a572e renaming h225 → _p2mH225
open _root_.P2M661a572e renaming h226 → _p2mH226
open _root_.P2M661a572e renaming h227 → _p2mH227
end
open _root_.P2M661a572e renaming h224 → _p2mH224
open _root_.P2M661a572e renaming h225 → _p2mH225
open _root_.P2M661a572e renaming h226 → _p2mH226
open _root_.P2M661a572e renaming h227 → _p2mH227
open _root_.P2M661a572e renaming h223 → _p2mH223
namespace CurrentAFT.RejectionProjection
end CurrentAFT.RejectionProjection
section
namespace CurrentAFT.BinaryPublicRejection
open AFT RationalNumerics BinaryArithmetic RationalRejectionProgram CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentPreparedCoreProposal.draw BinaryCoreWeightData.current BinaryCoreCharge.current
noncomputable section
open scoped Classical
attribute [local irreducible] RationalWeightProgram.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h198 (security weightBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (input : Option (MaterializedCore security)) :
    (score security weightBits order table input).value.decode =
      coreScore security weightBits order table (decodeResult security input) := by
  cases input with
  | none => rfl
  | some core =>
    change (if (BinaryCoreCharge.current security core).value = true then
      (BinaryCoreWeightData.current security weightBits order table core).value else RationalBits.zero).decode = _
    by_cases h : (BinaryCoreCharge.current security core).value = true
    · rw [if_pos h, _p2mH176]
      exact (if_pos ((_p2mH169 security core).mp h)).symm
    · rw [if_neg h, RationalBits.zero_value]
      exact (if_neg (fun hc => h ((_p2mH169 security core).mpr hc))).symm
open _root_.P2M661a572e renaming h198 → _p2mH198
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h195 (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Vector (Tapes security drawBits × (Fin coinBits → Fin 2)) attempts) :
    decodeResult security (current security tableBits drawBits weightBits coinBits order attempts table words).value =
      RationalRejectionProgram.positiveDraw
        (fun word => some (CurrentPreparedCoreProposal.draw security tableBits drawBits word).value.core)
        (coreScore security weightBits order table) 2 coinBits attempts none words.get := by
  exact _p2mH536 (decodeResult security) (sample security tableBits drawBits)
    (score security weightBits order table) (coreScore security weightBits order table)
    (_p2mH198 security weightBits order table) (RationalBits.ofCounter 2).data 2 coinBits
    (RationalBits.ofCounter_value 2) ⟨none, 1⟩ attempts words
open _root_.P2M661a572e renaming h195 → CurrentAFT.BinaryPublicRejection.current_value
open _root_.P2M661a572e renaming h195 → _p2mH195
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h196 (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (words : Fin attempts → Tapes security drawBits × (Fin coinBits → Fin 2)) :
    decodeResult security (draw security tableBits drawBits weightBits coinBits order attempts table words).value =
      RationalRejectionProgram.positiveDraw
        (fun word => some (CurrentPreparedCoreProposal.draw security tableBits drawBits word).value.core)
        (coreScore security weightBits order table) 2 coinBits attempts none words := by
  change decodeResult security (current security tableBits drawBits weightBits coinBits order attempts table
    (storeData attempts (fun index => ⟨words index, 1⟩)).value).value = _
  rw [_p2mH195]
  congr 1
  funext index
  exact storeData_get _ _ index
open _root_.P2M661a572e renaming h196 → _p2mH196
end
open _root_.P2M661a572e renaming h195 → CurrentAFT.BinaryPublicRejection.current_value
open _root_.P2M661a572e renaming h195 → _p2mH195
open _root_.P2M661a572e renaming h196 → _p2mH196
open _root_.P2M661a572e renaming h198 → _p2mH198
end CurrentAFT.BinaryPublicRejection
open _root_.P2M661a572e renaming h195 → CurrentAFT.BinaryPublicRejection.current_value
open _root_.P2M661a572e renaming h195 → _p2mH195
open _root_.P2M661a572e renaming h196 → _p2mH196
open _root_.P2M661a572e renaming h198 → _p2mH198
end
open _root_.P2M661a572e renaming h195 → CurrentAFT.BinaryPublicRejection.current_value
open _root_.P2M661a572e renaming h195 → _p2mH195
open _root_.P2M661a572e renaming h196 → _p2mH196
open _root_.P2M661a572e renaming h198 → _p2mH198
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
theorem _root_.P2M661a572e.h244 (security : ℕ) (input : (Fin (edgeCount security) → ℤ) × ℤ) :
    splitSource security (packSource security input) = input := by
  simp [splitSource, packSource]
open _root_.P2M661a572e renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h242 (security : ℕ) (input : Fin (Parameters.dimension security) → ℤ) :
    packSource security (splitSource security input) = input := by
  funext index
  obtain ⟨edge | point, rfl⟩ := (coordinateNumbering security).surjective index
  · simp [packSource, splitSource]
  · cases point
    simp [packSource, splitSource]
open _root_.P2M661a572e renaming h242 → _p2mH242
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h243 (security : ℕ) (first second : Fin (Parameters.dimension security) → ℤ) :
    splitSource security (first + second) = splitSource security first + splitSource security second := rfl
open _root_.P2M661a572e renaming h243 → _p2mH243
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h239 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    (CurrentAffineGeometry.matrix security layout core scale shear).mulVec input =
      packSource security
        (AffineRealization.linearPart (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
          (queues security layout) (placement security core) (attachments security layout)
          (relabeling security layout core) scale shear (splitSource security input)) := by
  change (Matrix.reindex _ _ _).mulVecLin input = _
  rw [Matrix.mulVecLin_reindex]
  change (fun index => (AffineRealization.matrix (bodyEdges security) (Parameters.legCount security)
    (Parameters.modulus security) (queues security layout) (placement security core) (attachments security layout)
      (relabeling security layout core) scale shear).mulVec (input ∘ coordinateNumbering security)
        ((coordinateNumbering security).symm index)) = _
  have hinput : input ∘ coordinateNumbering security =
      Sum.elim (splitSource security input).1 (fun _ : Unit => (splitSource security input).2) := by
    funext index
    rcases index with edge | point
    · rfl
    · cases point; rfl
  rw [hinput, _p2mH165]
  rfl
open _root_.P2M661a572e renaming h239 → _p2mH239
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h240 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    splitSource security ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      AffineRealization.linearPart (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security)
        (queues security layout) (placement security core) (attachments security layout)
        (relabeling security layout core) scale shear (splitSource security input) := by
  rw [_p2mH239, _p2mH244]
open _root_.P2M661a572e renaming h240 → _p2mH240
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h241 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : publicCharge security core) :
    splitSource security (CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
      AffineRealization.offsetCoordinates (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (centers security layout core)
        (legShift security core) intercept (placement security core) closureScalar (relabeling security layout core)
        (centers_charge security layout core hcharge) := by
  exact _p2mH244 security _
open _root_.P2M661a572e renaming h241 → _p2mH241
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h238 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear intercept : Fin (Parameters.legCount security) → ℤ) (closureScalar : ℤ)
    (hcharge : publicCharge security core) (input : Fin (Parameters.dimension security) → ℤ) :
    rounding security ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec input +
      CurrentAffineGeometry.offset security layout core intercept closureScalar hcharge) =
        load security layout core scale shear intercept closureScalar input := by
  unfold rounding
  rw [_p2mH243, _p2mH240, _p2mH241, _p2mH161]
  rfl
open _root_.P2M661a572e renaming h238 → _p2mH238
end
open _root_.P2M661a572e renaming h238 → _p2mH238
open _root_.P2M661a572e renaming h239 → _p2mH239
open _root_.P2M661a572e renaming h240 → _p2mH240
open _root_.P2M661a572e renaming h241 → _p2mH241
open _root_.P2M661a572e renaming h242 → _p2mH242
open _root_.P2M661a572e renaming h243 → _p2mH243
open _root_.P2M661a572e renaming h244 → _p2mH244
end CurrentAFT.CurrentAffineLoad
open _root_.P2M661a572e renaming h238 → _p2mH238
open _root_.P2M661a572e renaming h239 → _p2mH239
open _root_.P2M661a572e renaming h240 → _p2mH240
open _root_.P2M661a572e renaming h241 → _p2mH241
open _root_.P2M661a572e renaming h242 → _p2mH242
open _root_.P2M661a572e renaming h243 → _p2mH243
open _root_.P2M661a572e renaming h244 → _p2mH244
end
open _root_.P2M661a572e renaming h242 → _p2mH242
open _root_.P2M661a572e renaming h238 → _p2mH238
open _root_.P2M661a572e renaming h240 → _p2mH240
open _root_.P2M661a572e renaming h241 → _p2mH241
open _root_.P2M661a572e renaming h244 → _p2mH244
open _root_.P2M661a572e renaming h243 → _p2mH243
open _root_.P2M661a572e renaming h239 → _p2mH239
section
namespace CurrentAFT.LobsterAffineLoad
open AFT PublicCharge LobsterCoordinates LobsterMixerMatrix AffineBaseline AffineRealization
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h478 (bodyEdges legs : ℕ) (scale shear : Fin legs → ℤ)
    (input : Fin (bodyEdges + (legs + legs)) → ℤ) :
    edgeCoordinates ℤ bodyEdges legs ((numberedMatrix bodyEdges legs scale shear).mulVec input) =
      ((edgeCoordinates ℤ bodyEdges legs input).1,
        (fun leg => scale leg * (edgeCoordinates ℤ bodyEdges legs input).2.1 leg +
          shear leg * (edgeCoordinates ℤ bodyEdges legs input).2.2 leg,
         (edgeCoordinates ℤ bodyEdges legs input).2.2)) := by
  apply Prod.ext
  · funext vertex
    change (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs (.inl vertex)) = _
    rw [_p2mH483, _p2mH482]
    rfl
  · apply Prod.ext
    · funext leg
      change (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs (.inr (.inl leg))) = _
      rw [_p2mH483, _p2mH482]
      rfl
    · funext leg
      change (numberedMatrix bodyEdges legs scale shear).mulVec input (edgeIndex bodyEdges legs (.inr (.inr leg))) = _
      rw [_p2mH483, _p2mH482]
      rfl
open _root_.P2M661a572e renaming h478 → _p2mH478
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h479 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin (bodyEdges + 1)) :
    queueColumn bodyEdges legs modulus queues relabeling (relabeling (vertexIndex bodyEdges legs (.inl vertex))) =
      if vertex ∈ Finset.univ.map queues then 1 else 0 := by
  have hequal : relabeling (vertexIndex bodyEdges legs (.inl vertex)) ∈
      Finset.univ.map (queueEmbedding bodyEdges legs modulus queues relabeling) ↔
      vertex ∈ Finset.univ.map queues := by
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨point, heq⟩
      exact ⟨point, Sum.inl.inj ((vertexIndex bodyEdges legs).injective (relabeling.injective heq))⟩
    · rintro ⟨point, heq⟩
      exact ⟨point, congrArg (fun vertex => relabeling (vertexIndex bodyEdges legs (.inl vertex))) heq⟩
  simp only [queueColumn, hequal]
open _root_.P2M661a572e renaming h479 → _p2mH479
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h480 (bodyEdges legs modulus : ℕ)
    (queues : Fin modulus ↪ Fin (bodyEdges + 1))
    (relabeling : Equiv.Perm (Fin (bodyEdges + (legs + legs) + 1))) (vertex : Fin legs ⊕ Fin legs) :
    queueColumn bodyEdges legs modulus queues relabeling (relabeling (vertexIndex bodyEdges legs (.inr vertex))) = 0 := by
  have hnot : relabeling (vertexIndex bodyEdges legs (.inr vertex)) ∉
      Finset.univ.map (queueEmbedding bodyEdges legs modulus queues relabeling) := by
    intro hmem
    obtain ⟨point, _, heq⟩ := Finset.mem_map.mp hmem
    have h := (vertexIndex bodyEdges legs).injective (relabeling.injective heq)
    cases h
  exact if_neg hnot
open _root_.P2M661a572e renaming h480 → _p2mH480
end
open _root_.P2M661a572e renaming h478 → _p2mH478
open _root_.P2M661a572e renaming h479 → _p2mH479
open _root_.P2M661a572e renaming h480 → _p2mH480
end CurrentAFT.LobsterAffineLoad
open _root_.P2M661a572e renaming h478 → _p2mH478
open _root_.P2M661a572e renaming h479 → _p2mH479
open _root_.P2M661a572e renaming h480 → _p2mH480
end
open _root_.P2M661a572e renaming h480 → _p2mH480
open _root_.P2M661a572e renaming h479 → _p2mH479
open _root_.P2M661a572e renaming h478 → _p2mH478
section
namespace CurrentAFT.NumericalAffineTransport
open AFT ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean
  CurrentAffineData CurrentPublicAffineSample CurrentHiddenSourceTransport CurrentZeroFiber
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
attribute [local instance] _root_.CurrentAFT.NumericalAffineTransport.modulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h485 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    gaussianOutput security layout ((law security weight hpositive).map some) =
      CurrentAffineTransport.gaussianLaw security layout weight hpositive := by
  rw [gaussianOutput, FiniteDist.mix_map]
  rfl
open _root_.P2M661a572e renaming h485 → _p2mH485
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h486 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (PublicResult security)) (numerical : ℝ)
    (himplementation : FiniteDist.TVBound implementation ((law security weight hpositive).map some) numerical) :
    FiniteDist.TVBound (gaussianOutput security layout implementation)
      (CurrentAffineTransport.gaussianLaw security layout weight hpositive) numerical := by
  have h := himplementation.mix (gaussianChannel security layout)
  change FiniteDist.TVBound (gaussianOutput security layout implementation)
    (gaussianOutput security layout ((law security weight hpositive).map some)) numerical at h
  rw [_p2mH485] at h
  exact h
open _root_.P2M661a572e renaming h486 → _p2mH486
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h487 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (PublicResult security)) (numerical analytic : ℝ)
    (himplementation : FiniteDist.TVBound implementation ((law security weight hpositive).map some) numerical)
    (hanalytic : (CurrentAffineTransport.gaussianLaw security layout weight hpositive).totalVariation
      (uniformFiber security) ≤ analytic) :
    (gaussianOutput security layout implementation).totalVariation (uniformFiber security) ≤ analytic + numerical := by
  have h := (_p2mH486 security layout weight hpositive implementation numerical himplementation).triangle
    ((_p2mH93 _ _ _).mpr hanalytic)
  exact ((_p2mH93 _ _ _).mp h).trans_eq (add_comm numerical analytic)
open _root_.P2M661a572e renaming h487 → _p2mH487
end
open _root_.P2M661a572e renaming h485 → _p2mH485
open _root_.P2M661a572e renaming h486 → _p2mH486
open _root_.P2M661a572e renaming h487 → _p2mH487
end CurrentAFT.NumericalAffineTransport
open _root_.P2M661a572e renaming h485 → _p2mH485
open _root_.P2M661a572e renaming h486 → _p2mH486
open _root_.P2M661a572e renaming h487 → _p2mH487
end
open _root_.P2M661a572e renaming h485 → _p2mH485
open _root_.P2M661a572e renaming h487 → _p2mH487
open _root_.P2M661a572e renaming h486 → _p2mH486
section
namespace CurrentAFT.NumericalPublicCompletion
open AFT ActualPublicCharge CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h497 {Core Charts Edge : Type*} [Fintype Core] [Fintype Charts] [Fintype Edge]
    (coreLaw : FiniteDist Core) (charts : Core → FiniteDist Charts) (edge : FiniteDist Edge) :
    coreLaw.mix (fun core => ((charts core).prod edge).map
      (fun pair => ((core, pair.1), pair.2))) = (FiniteDist.joint coreLaw charts).prod edge := by
  ext output
  rcases output with ⟨⟨core, chart⟩, closing⟩
  simp only [FiniteDist.mix_weight, FiniteDist.map_weight, FiniteDist.prod_weight,
    Fintype.sum_prod_type, Prod.mk.injEq, FiniteDist.joint_weight]
  simp only [ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero, mul_ite, mul_zero]
  exact (mul_assoc _ _ _).symm
open _root_.P2M661a572e renaming h497 → _p2mH497
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h500 (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (Option (CachedCore security))) (error : ℝ)
    (hcore : FiniteDist.TVBound (implementation.map (Option.map (coreEquiv security)))
      ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).map some) error) :
    FiniteDist.TVBound implementation (targetCore security weight hpositive) error := by
  have h := hcore.map (Option.map (coreEquiv security).symm)
  rw [FiniteDist.map_map] at h
  have hid : (fun result : Option (CachedCore security) =>
      Option.map (coreEquiv security).symm (Option.map (coreEquiv security) result)) = id := by
    funext result
    cases result <;> simp
  have hmap : implementation.map id = implementation := by
    ext point
    exact FiniteDist.map_equiv_weight implementation (Equiv.refl _) point
  rw [hid, hmap] at h
  simpa only [targetCore, FiniteDist.map_map, Option.map_some] using h
open _root_.P2M661a572e renaming h500 → _p2mH500
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h501 (security : ℕ) (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security)) :
    (targetCore security weight hpositive).mix (targetKernel security) =
      (CurrentPublicAffineSample.law security weight hpositive).map some := by
  rw [targetCore, FiniteDist.mix_map, FiniteDist.mix_map]
  change (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).mix
    (fun core => ((CurrentPublicAffineSample.chartsLaw security core).prod (DiffuseProfiles.edgeLaw security)).map
      (fun pair => some ((core, pair.1), pair.2))) = _
  have h := _p2mH497 (positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive)
    (CurrentPublicAffineSample.chartsLaw security) (DiffuseProfiles.edgeLaw security)
  have hm := congrArg (fun law => law.map some) h
  try dsimp only at hm
  rw [FiniteDist.map_mix] at hm
  simp only [FiniteDist.map_map] at hm
  exact hm
open _root_.P2M661a572e renaming h501 → _p2mH501
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h498 (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (input : Option (CachedCore security)) :
    FiniteDist.TVBound (kernel security precisionBits drawBits edgeBits input) (targetKernel security input)
      (errorBound security precisionBits drawBits edgeBits/2) := by
  rw [_p2mH93, FiniteDist.totalVariation_eq_half_l1]
  exact div_le_div_of_nonneg_right (_p2mH450 security precisionBits drawBits edgeBits hprecision input) (by norm_num)
open _root_.P2M661a572e renaming h498 → _p2mH498
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h499 (security precisionBits drawBits edgeBits : ℕ) (hprecision : 1 ≤ precisionBits)
    (weight : Core security → ℝ)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (implementation : FiniteDist (Option (CachedCore security))) (coreError : ℝ)
    (hcore : FiniteDist.TVBound implementation (targetCore security weight hpositive) coreError) :
    FiniteDist.TVBound (implementation.mix (kernel security precisionBits drawBits edgeBits))
      ((CurrentPublicAffineSample.law security weight hpositive).map some)
      (coreError+errorBound security precisionBits drawBits edgeBits/2) := by
  have hc := hcore.mix (kernel security precisionBits drawBits edgeBits)
  have hh := _p2mH68 (targetCore security weight hpositive)
    (_p2mH498 security precisionBits drawBits edgeBits hprecision)
  rw [_p2mH501] at hh
  exact hc.triangle hh
open _root_.P2M661a572e renaming h499 → _p2mH499
end
open _root_.P2M661a572e renaming h497 → _p2mH497
open _root_.P2M661a572e renaming h498 → _p2mH498
open _root_.P2M661a572e renaming h499 → _p2mH499
open _root_.P2M661a572e renaming h500 → _p2mH500
open _root_.P2M661a572e renaming h501 → _p2mH501
end CurrentAFT.NumericalPublicCompletion
open _root_.P2M661a572e renaming h497 → _p2mH497
open _root_.P2M661a572e renaming h498 → _p2mH498
open _root_.P2M661a572e renaming h499 → _p2mH499
open _root_.P2M661a572e renaming h500 → _p2mH500
open _root_.P2M661a572e renaming h501 → _p2mH501
end
open _root_.P2M661a572e renaming h499 → _p2mH499
open _root_.P2M661a572e renaming h500 → _p2mH500
open _root_.P2M661a572e renaming h497 → _p2mH497
open _root_.P2M661a572e renaming h498 → _p2mH498
open _root_.P2M661a572e renaming h501 → _p2mH501
section
namespace CurrentAFT.BinaryPublicRejection
open AFT CurrentCoreProposal ActualPublicCharge CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize Parameters.dimension
  CurrentPreparedCoreProposal.draw BinaryPublicRejection.draw RationalWeightProgram.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h197 (security bits : ℕ) :
    CurrentCoreProposalLaw.tapeLaw security bits = FiniteDist.uniform (Tapes security bits) := by
  simp only [CurrentCoreProposalLaw.tapeLaw, CurrentCoreProposalLaw.controlTapeLaw,
    CurrentCoreProposalLaw.legTapeLaw, CurrentPublicSeedDraw.tapeLaw,
    ← _p2mH95, _p2mH80]
open _root_.P2M661a572e renaming h197 → _p2mH197
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h191 (security weightBits coinBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    ∀ input, 0 ≤ coin security weightBits coinBits order table input ∧ coin security weightBits coinBits order table input ≤ 1 :=
  _p2mH225 _ _ _
open _root_.P2M661a572e renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h192 (security weightBits coinBits order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) (input : Option (Core security)) :
    RationalAcceptanceCoin.probability coinBits (max (coreScore security weightBits order table input) 0/2) =
      coin security weightBits coinBits order table input := by
  cases input with
  | none => norm_num [coreScore, coin, ClippedRejectionCoin.optionCoin, RationalAcceptanceCoin.probability,
      RationalAcceptanceCoin.count, RationalAcceptanceCoin.clipped]
  | some core =>
    simp only [coreScore, coin, ClippedRejectionCoin.optionCoin, ClippedRejectionCoin.probability,
      ClippedRejectionCoin.raw, decide_eq_true_eq]
open _root_.P2M661a572e renaming h192 → _p2mH192
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h194 (security tableBits drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    (law security tableBits drawBits weightBits coinBits order attempts table).map (decodeResult security) =
      (((CurrentPreparedCoreProposal.law security tableBits drawBits).map MaterializedCore.core).map some).cappedRejection
        (coin security weightBits coinBits order table) (_p2mH191 security weightBits coinBits order table)
        (CanonicalMoments.pointLaw none) attempts := by
  rw [law, FiniteDist.map_map]
  simp only [_p2mH196]
  rw [RationalRejectionProgram.positiveDraw, _p2mH144]
  have hp : (FiniteDist.uniform (Tapes security drawBits)).map
      (fun word => some (CurrentPreparedCoreProposal.draw security tableBits drawBits word).value.core) =
      ((CurrentPreparedCoreProposal.law security tableBits drawBits).map MaterializedCore.core).map some := by
    simp only [CurrentPreparedCoreProposal.law, _p2mH197, FiniteDist.map_map]
  simp only [hp, _p2mH192, Nat.cast_ofNat]
open _root_.P2M661a572e renaming h194 → _p2mH194
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h193 (security drawBits weightBits coinBits order attempts : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(coreWeight security weightBits order table core : ℝ)-weight core| ≤ weightError)
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound
      ((law security (CurrentProposalPrecision.tableBits security drawBits) drawBits weightBits coinBits order attempts table).map
        (decodeResult security))
      ((positivePublicCoreLaw (proposal security) weight (publicCharge security)
        (lt_of_lt_of_le (by
          have hq : (0 : ℝ) < Parameters.modulus security := Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos
          positivity) hmass)).map some)
      ((attempts : ℝ)*(CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security drawBits) drawBits/2+
        (1/(2 : ℝ)^coinBits+weightError/2)) + Real.exp (-(attempts : ℝ)/(8*(Parameters.modulus security : ℝ)))) := by
  rw [_p2mH194]
  have hp : FiniteDist.TVBound
      ((CurrentPreparedCoreProposal.law security (CurrentProposalPrecision.tableBits security drawBits) drawBits).map MaterializedCore.core)
      (proposal security) (CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security drawBits) drawBits/2) := by
    rw [_p2mH93, FiniteDist.totalVariation_eq_half_l1]
    exact div_le_div_of_nonneg_right (_p2mH439 security drawBits) (by norm_num)
  exact _p2mH503 (proposal security) _ weight (publicCharge security)
    (coin security weightBits coinBits order table) (_p2mH191 security weightBits coinBits order table)
    (Parameters.modulus security) _ _ (Nat.cast_pos.mpr (Parameters.modulus_spec security).2.pos) hmass hp
    (_p2mH226 coinBits (fun core => decide (publicCharge security core))
      (coreWeight security weightBits order table) weight (publicCharge security) weightError he
      (fun _ => by simp only [decide_eq_true_eq]) hweight) attempts
open _root_.P2M661a572e renaming h193 → _p2mH193
end
open _root_.P2M661a572e renaming h191 → _p2mH191
open _root_.P2M661a572e renaming h192 → _p2mH192
open _root_.P2M661a572e renaming h193 → _p2mH193
open _root_.P2M661a572e renaming h194 → _p2mH194
open _root_.P2M661a572e renaming h197 → _p2mH197
end CurrentAFT.BinaryPublicRejection
open _root_.P2M661a572e renaming h191 → _p2mH191
open _root_.P2M661a572e renaming h192 → _p2mH192
open _root_.P2M661a572e renaming h193 → _p2mH193
open _root_.P2M661a572e renaming h194 → _p2mH194
open _root_.P2M661a572e renaming h197 → _p2mH197
end
open _root_.P2M661a572e renaming h194 → _p2mH194
open _root_.P2M661a572e renaming h191 → _p2mH191
open _root_.P2M661a572e renaming h197 → _p2mH197
open _root_.P2M661a572e renaming h192 → _p2mH192
open _root_.P2M661a572e renaming h193 → _p2mH193
section
namespace CurrentAFT.BinaryRejectionCap
open AFT BinaryArithmetic
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PublicParameterProgram.modulus multiplyCounter
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h201 (security : ℕ) :
    Real.exp (-((current security).count : ℝ)/(8*(Parameters.modulus security : ℝ))) = Real.exp (-(security : ℝ)) := by
  rw [current_value]
  congr 1
  push_cast
  have hq : (Parameters.modulus security : ℝ) ≠ 0 := (Nat.cast_ne_zero.mpr (Parameters.modulus_spec security).2.ne_zero)
  field_simp
open _root_.P2M661a572e renaming h201 → _p2mH201
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h200 : Negligible (fun security =>
    Real.exp (-((current security).count : ℝ)/(8*(Parameters.modulus security : ℝ)))) := by
  have h := _p2mH152 1 0 1 1 (by norm_num) (by norm_num) (by norm_num)
  simpa only [_p2mH201, pow_zero, mul_one, one_mul, Real.rpow_one, neg_mul, neg_neg] using h
open _root_.P2M661a572e renaming h200 → _p2mH200
end CurrentAFT.BinaryRejectionCap
open _root_.P2M661a572e renaming h200 → _p2mH200
open _root_.P2M661a572e renaming h201 → _p2mH201
end
open _root_.P2M661a572e renaming h200 → _p2mH200
open _root_.P2M661a572e renaming h201 → _p2mH201
section
namespace CurrentAFT.CalibrationPrecisionRates
open AFT CalibrationTableNorm CalibrationMatrixApproximation CalibrationMatrixRates
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h218 (constant : ℝ) (degree : ℕ) (ratio : ℝ)
    (hc : 0 ≤ constant) (hr : 0 < ratio) (hr1 : ratio < 1) :
    Negligible (fun security => constant * (Parameters.base security : ℝ)^degree * ratio^security) := by
  have hmain := (_p2mH0 (constant * 3^degree) ratio
    (by positivity) hr hr1 (fun security => security) (by filter_upwards [] with security; rfl)).mul_polynomial degree
  apply hmain.of_eventually_le
  filter_upwards [eventually_ge_atTop 1] with security hsecurity
  have hb : (Parameters.base security : ℝ) ≤ 3 * security := by
    exact_mod_cast (show Parameters.base security ≤ 3 * security by unfold Parameters.base; omega)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ Parameters.base security by positivity) hb degree
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (pow_nonneg hr.le security)
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hm
open _root_.P2M661a572e renaming h218 → _p2mH218
end
open _root_.P2M661a572e renaming h218 → _p2mH218
end CurrentAFT.CalibrationPrecisionRates
open _root_.P2M661a572e renaming h218 → _p2mH218
end
open _root_.P2M661a572e renaming h218 → _p2mH218
section
namespace CurrentAFT.NumericalWeightRates
open AFT CalibrationTableNorm CalibrationMatrixApproximation CalibrationMatrixRates
  CalibrationPrecisionRates CalibratedWeightApproximation NumericalWeightEvaluation
open Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h502 {error : ℕ → ℝ} (h : Negligible error) (constant : ℝ) :
    Negligible (fun security => constant * error security) := by
  apply (h.mul_polynomial 1).of_eventually_le
  filter_upwards [eventually_ge_atTop ⌈|constant|⌉₊] with security hs
  have hc : |constant| ≤ (security : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hs)
  rw [abs_mul, abs_mul, pow_one, abs_of_nonneg (show (0 : ℝ) ≤ security by positivity)]
  exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
open _root_.P2M661a572e renaming h502 → _p2mH502
end
open _root_.P2M661a572e renaming h502 → _p2mH502
end CurrentAFT.NumericalWeightRates
open _root_.P2M661a572e renaming h502 → _p2mH502
end
open _root_.P2M661a572e renaming h502 → _p2mH502
namespace CurrentAFT.NumericalWeightEvaluation
end CurrentAFT.NumericalWeightEvaluation
namespace CurrentAFT.NumericalWeightEvaluation.localError
end CurrentAFT.NumericalWeightEvaluation.localError
namespace CurrentAFT.NumericalWeightRates
end CurrentAFT.NumericalWeightRates
section
namespace CurrentAFT.NumericalProposalRates
open AFT Filter NumericalWeightRates Polynomial
open scoped Polynomial Topology
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.dimension Parameters.bodySize
  CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h492 {error : ℕ → ℝ} (h : Negligible error) (polynomial : Polynomial ℕ) :
    Negligible (fun security => ((polynomial.eval security : ℕ) : ℝ)*error security) := by
  induction polynomial using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, Nat.cast_add, add_mul] using hp.add hq
  | monomial power coefficient =>
    simpa only [Polynomial.eval_monomial, Nat.cast_mul, Nat.cast_pow, mul_assoc] using
      _p2mH502 (h.mul_polynomial power) (coefficient : ℝ)
open _root_.P2M661a572e renaming h492 → _p2mH492
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h491 : Negligible (fun security => 1/(2 : ℝ)^security) := by
  simpa only [pow_zero, mul_one, one_mul, div_pow, one_pow] using
    _p2mH218 1 0 (1/2) (by norm_num) (by norm_num) (by norm_num)
open _root_.P2M661a572e renaming h491 → _p2mH491
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h488 {error factor : ℕ → ℝ} (h : Negligible error)
    (polynomial : Polynomial ℕ) (hfactor : ∀ security, |factor security| ≤ ((polynomial.eval security : ℕ) : ℝ)) :
    Negligible (fun security => factor security*error security) := by
  apply (_p2mH492 h polynomial).of_eventually_le
  filter_upwards [] with security
  rw [abs_mul, abs_mul]
  rw [abs_of_nonneg (Nat.cast_nonneg (polynomial.eval security) : (0 : ℝ) ≤ ((polynomial.eval security : ℕ) : ℝ))]
  exact mul_le_mul_of_nonneg_right (hfactor security) (abs_nonneg _)
open _root_.P2M661a572e renaming h488 → _p2mH488
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h495 (security bits : ℕ) :
    0 ≤ CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security bits) bits := by
  unfold CurrentCoreProposalRates.error CurrentCoreProposalRates.controlError CurrentCoreProposalRates.ticketError
  positivity
open _root_.P2M661a572e renaming h495 → _p2mH495
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h493 (security bits : ℕ) :
    CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security bits) bits ≤
      ((proposalPolynomial.eval security : ℕ) : ℝ)*(1/(2 : ℝ)^bits) := by
  let size := ((CurrentProposalResources.countPolynomial.eval security : ℕ) : ℝ)
  have hs := CurrentProposalResources.count_bounds security
  have hv := CurrentProposalDimensions.current_values security
  have hc : ((CurrentProposalDimensions.current security).controls : ℝ) ≤ size := by dsimp only [size]; exact_mod_cast hs.1
  have hl : (Parameters.legCount security : ℝ) ≤ size := by rw [← hv.2.1]; dsimp only [size]; exact_mod_cast hs.2.1
  have hq : (Parameters.modulus security : ℝ) ≤ size := by rw [← hv.1]; dsimp only [size]; exact_mod_cast hs.2.2.1
  have hb : ((CurrentProposalDimensions.current security).body : ℝ) ≤ size := by dsimp only [size]; exact_mod_cast hs.2.2.2.1
  have hd : ((CurrentProposalDimensions.current security).dimension : ℝ) ≤ size := by dsimp only [size]; exact_mod_cast hs.2.2.2.2
  have hd' : (Parameters.dimension security : ℝ) ≤ size := by rw [← hv.2.2.2.1]; exact hd
  have hp : 1/(2 : ℝ)^CurrentProposalPrecision.tableBits security bits ≤ 1/(2 : ℝ)^bits := by
    apply one_div_le_one_div_of_le (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    exact Nat.le_add_right _ _
  have hsize : 0 ≤ size := Nat.cast_nonneg _
  have ht : 0 ≤ 1/(2 : ℝ)^bits := by positivity
  have hctrl : CurrentCoreProposalRates.controlError security (CurrentProposalPrecision.tableBits security bits) bits ≤
      (2+size*(64*(security+2)*size+(64*(security+2)*size*size+2)))*(1/(2 : ℝ)^bits) := by
    unfold CurrentCoreProposalRates.controlError CurrentCoreProposalRates.ticketError
    calc
      _ ≤ 2*(1/(2 : ℝ)^bits)+size*(64*(security+2)*size+(64*(security+2)*size*size+2))*(1/(2 : ℝ)^bits) := by
        simp only [Parameters.base]
        push_cast
        gcongr
      _ = _ := by ring
  unfold CurrentCoreProposalRates.error CurrentCoreProposalRates.ticketError
  have hcn : 0 ≤ CurrentCoreProposalRates.controlError security (CurrentProposalPrecision.tableBits security bits) bits := by
    unfold CurrentCoreProposalRates.controlError CurrentCoreProposalRates.ticketError
    positivity
  calc
    _ ≤ size*((2+size*(64*(security+2)*size+(64*(security+2)*size*size+2)))*(1/(2 : ℝ)^bits))+
        size*(5*(1/(2 : ℝ)^bits)+1/(2 : ℝ)^bits)+size*(1/(2 : ℝ)^bits)+
        2*size^2*(1/(2 : ℝ)^bits)+2*size^2*(1/(2 : ℝ)^bits) := by
      gcongr
    _ = _ := by
      simp only [proposalPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_ofNat, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      dsimp only [size]
      ring
open _root_.P2M661a572e renaming h493 → _p2mH493
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h494 : Negligible (fun security =>
    CurrentCoreProposalRates.error security (CurrentProposalPrecision.tableBits security security) security) := by
  apply (_p2mH492 _p2mH491 proposalPolynomial).of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (_p2mH495 security security), abs_of_nonneg (by positivity)]
  exact _p2mH493 security security
open _root_.P2M661a572e renaming h494 → _p2mH494
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h489 (security : ℕ) :
    CurrentPublicCompletion.errorBound security security security security ≤
      ((completionPolynomial.eval security : ℕ) : ℝ)*(1/(2 : ℝ)^security) := by
  have hs := (CurrentProposalResources.count_bounds security).2.1
  rw [(CurrentProposalDimensions.current_values security).2.1] at hs
  have hl : (Parameters.legCount security : ℝ) ≤ ((CurrentProposalResources.countPolynomial.eval security : ℕ) : ℝ) := by exact_mod_cast hs
  unfold CurrentPublicCompletion.errorBound
  calc
    _ ≤ ((CurrentProposalResources.countPolynomial.eval security : ℕ) : ℝ)*
        (1/(2 : ℝ)^security+4*(1/(2 : ℝ)^security))+1/(2 : ℝ)^security := by gcongr
    _ = _ := by
      simp only [completionPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      ring
open _root_.P2M661a572e renaming h489 → _p2mH489
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h490 : Negligible (fun security =>
    CurrentPublicCompletion.errorBound security security security security) := by
  apply (_p2mH492 _p2mH491 completionPolynomial).of_eventually_le
  filter_upwards [] with security
  rw [abs_of_nonneg (by unfold CurrentPublicCompletion.errorBound; positivity), abs_of_nonneg (by positivity)]
  exact _p2mH489 security
open _root_.P2M661a572e renaming h490 → _p2mH490
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h496 {error : ℕ → ℝ} (h : Negligible error) :
    Negligible (fun security => ((BinaryRejectionCap.current security).count : ℝ)*error security) := by
  exact _p2mH488 h BinaryRejectionCap.countPolynomial (fun security => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast BinaryRejectionCap.count_bound security)
open _root_.P2M661a572e renaming h496 → _p2mH496
end
open _root_.P2M661a572e renaming h488 → _p2mH488
open _root_.P2M661a572e renaming h489 → _p2mH489
open _root_.P2M661a572e renaming h490 → _p2mH490
open _root_.P2M661a572e renaming h491 → _p2mH491
open _root_.P2M661a572e renaming h492 → _p2mH492
open _root_.P2M661a572e renaming h493 → _p2mH493
open _root_.P2M661a572e renaming h494 → _p2mH494
open _root_.P2M661a572e renaming h495 → _p2mH495
open _root_.P2M661a572e renaming h496 → _p2mH496
end CurrentAFT.NumericalProposalRates
open _root_.P2M661a572e renaming h488 → _p2mH488
open _root_.P2M661a572e renaming h489 → _p2mH489
open _root_.P2M661a572e renaming h490 → _p2mH490
open _root_.P2M661a572e renaming h491 → _p2mH491
open _root_.P2M661a572e renaming h492 → _p2mH492
open _root_.P2M661a572e renaming h493 → _p2mH493
open _root_.P2M661a572e renaming h494 → _p2mH494
open _root_.P2M661a572e renaming h495 → _p2mH495
open _root_.P2M661a572e renaming h496 → _p2mH496
end
open _root_.P2M661a572e renaming h495 → _p2mH495
open _root_.P2M661a572e renaming h491 → _p2mH491
open _root_.P2M661a572e renaming h496 → _p2mH496
open _root_.P2M661a572e renaming h493 → _p2mH493
open _root_.P2M661a572e renaming h492 → _p2mH492
open _root_.P2M661a572e renaming h489 → _p2mH489
open _root_.P2M661a572e renaming h490 → _p2mH490
open _root_.P2M661a572e renaming h488 → _p2mH488
open _root_.P2M661a572e renaming h494 → _p2mH494
section
namespace CurrentAFT.CappedPublicRejection
open AFT BinaryArithmetic RationalNumerics RationalRejectionProgram CurrentCoreProposal
open ActualPublicCharge
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryPublicRejection.draw BinaryRejectionCap.current BinaryProposalPrecision.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h220 (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) (word : Tapes security) :
    (current security order table word).value =
      (BinaryPublicRejection.draw security (CurrentProposalPrecision.tableBits security security)
        security security security order (BinaryRejectionCap.current security).count table word).value := by
  simp only [current, _p2mH190]
open _root_.P2M661a572e renaming h220 → CurrentAFT.CappedPublicRejection.current_value
open _root_.P2M661a572e renaming h220 → _p2mH220
noncomputable section
open scoped Classical
open Polynomial
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h222 (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    law security order table = BinaryPublicRejection.law security (CurrentProposalPrecision.tableBits security security)
      security security security order (BinaryRejectionCap.current security).count table := by
  simp only [law, _p2mH220, BinaryPublicRejection.law]
open _root_.P2M661a572e renaming h222 → _p2mH222
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h221 {weightError : ℕ → ℝ} (h : Negligible weightError) :
    Negligible (fun security => error security (weightError security)) := by
  have hp := _p2mH502 _p2mH494 (1/2)
  have hw := _p2mH502 h (1/2)
  have hr := _p2mH496 (hp.add (_p2mH491.add hw))
  have ht : Negligible (fun security => Real.exp (-(security : ℝ))) := by
    simpa only [_p2mH201] using _p2mH200
  convert hr.add ht using 1
  funext security
  unfold error
  ring
open _root_.P2M661a572e renaming h221 → _p2mH221
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h219 (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(BinaryPublicRejection.coreWeight security security order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound ((law security order table).map (BinaryPublicRejection.decodeResult security))
      ((positivePublicCoreLaw (proposal security) weight (publicCharge security) hpositive).map some)
      (error security weightError) := by
  rw [_p2mH222]
  have h := _p2mH193 security security security security order
    (BinaryRejectionCap.current security).count table weight weightError he hweight hmass
  simpa only [error, _p2mH201] using h
open _root_.P2M661a572e renaming h219 → _p2mH219
end
open _root_.P2M661a572e renaming h219 → _p2mH219
open _root_.P2M661a572e renaming h221 → _p2mH221
open _root_.P2M661a572e renaming h222 → _p2mH222
end CurrentAFT.CappedPublicRejection
open _root_.P2M661a572e renaming h219 → _p2mH219
open _root_.P2M661a572e renaming h220 → CurrentAFT.CappedPublicRejection.current_value
open _root_.P2M661a572e renaming h220 → _p2mH220
open _root_.P2M661a572e renaming h221 → _p2mH221
open _root_.P2M661a572e renaming h222 → _p2mH222
end
open _root_.P2M661a572e renaming h219 → _p2mH219
open _root_.P2M661a572e renaming h222 → _p2mH222
open _root_.P2M661a572e renaming h220 → CurrentAFT.CappedPublicRejection.current_value
open _root_.P2M661a572e renaming h220 → _p2mH220
open _root_.P2M661a572e renaming h221 → _p2mH221
section
namespace CurrentAFT.CurrentAffineEmissionBridge
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open ActualPublicCharge ActualCycleMeanMGF ConditionalHistogramMean CurrentAffineGeometry CurrentAffineLoad
  LobsterCoordinates LobsterMixerMatrix AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h234 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ) :
    rounding security ((CurrentAffineGeometry.matrix security layout core scale shear).mulVec input) =
      linearLoad security layout core scale shear input := by
  unfold rounding
  rw [_p2mH240, _p2mH164]
  rfl
open _root_.P2M661a572e renaming h234 → _p2mH234
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h236 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear intercept : Fin (Parameters.legCount security) → ℤ) (closure : ℤ)
    (hcharge : publicCharge security core) :
    rounding security (CurrentAffineGeometry.offset security layout core intercept closure hcharge) =
      load security layout core scale shear intercept closure 0 := by
  simpa only [Matrix.mulVec_zero, zero_add] using _p2mH238 security layout core scale shear intercept closure hcharge 0
open _root_.P2M661a572e renaming h236 → _p2mH236
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h235 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (column : Fin (Parameters.dimension security)) :
    rounding security (fun row => CurrentAffineGeometry.matrix security layout core scale shear row column) =
      linearLoad security layout core scale shear (Pi.single column 1) := by
  have h := _p2mH234 security layout core scale shear (Pi.single column 1)
  have he : (CurrentAffineGeometry.matrix security layout core scale shear).mulVec (Pi.single column 1) =
      fun row => CurrentAffineGeometry.matrix security layout core scale shear row column := by
    funext row
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rwa [he] at h
open _root_.P2M661a572e renaming h235 → _p2mH235
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h233 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) :
    totalCharge (injectionColumn (edgeCount security) (Parameters.modulus security)) = (Parameters.modulus security : ℤ) := by
  exact totalCharge_injectionColumn _ _ (AffineRealization.queue_modulus_le
    (bodyEdges security) (Parameters.legCount security) (Parameters.modulus security) (queues security layout))
open _root_.P2M661a572e renaming h233 → _p2mH233
set_option maxRecDepth 8192
 theorem _root_.P2M661a572e.h232 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security)
    (modulus : List Bool) (hmodulus : AFT.BinaryArithmetic.value modulus = Parameters.modulus security)
    (injection bitLoad : Vector IntegerBits (edgeCount security + 1))
    (hinjection : ∀ vertex, (injection.get vertex).decode = injectionColumn _ (Parameters.modulus security) vertex)
    (target : Fin (Parameters.dimension security) → ℤ)
    (hload : ∀ vertex, (bitLoad.get vertex).decode = rounding security target (dimensionEquiv security vertex)) :
    packSource security
      ((fun edge => ((binaryRoundingInverse (edgeCount security) modulus injection bitLoad).edges.get edge).decode),
        (binaryRoundingInverse (edgeCount security) modulus injection bitLoad).charge.decode) = target := by
  let decodedInjection := injection.map IntegerBits.decode
  let decodedLoad := bitLoad.map IntegerBits.decode
  have hi : decodedInjection.get = injectionColumn (edgeCount security) (Parameters.modulus security) := by
    funext vertex
    simpa only [decodedInjection, Vector.get_map] using hinjection vertex
  have hm : totalCharge decodedInjection.get = (Parameters.modulus security : ℤ) := by
    rw [hi]
    exact _p2mH233 security layout
  have hl : decodedLoad.get = roundingLoad (edgeCount security) decodedInjection.get (splitSource security target) := by
    funext vertex
    rw [hi]
    simpa only [decodedLoad, Vector.get_map, rounding, Equiv.symm_apply_apply] using hload vertex
  have hd : (Parameters.modulus security : ℤ) ∣ totalCharge decodedLoad.get := by
    exact (rounding_image_lattice _ _ _ hm _).mp ⟨splitSource security target, hl.symm⟩
  have hbitdiv : (AFT.BinaryArithmetic.value modulus : ℤ) ∣ ∑ vertex, (bitLoad.get vertex).decode := by
    simpa only [hmodulus, decodedLoad, totalCharge, Vector.get_map] using hd
  have hb := _p2mH31 (edgeCount security) modulus injection bitLoad
    (by rw [hmodulus]; exact (Parameters.modulus_spec security).2.pos) hbitdiv
  have hq : (Parameters.modulus security : ℤ) ≠ 0 := by exact_mod_cast (Parameters.modulus_spec security).2.ne_zero
  have he : ((roundingInverseProgram (edgeCount security) (Parameters.modulus security) decodedInjection decodedLoad).value.1.get,
      (roundingInverseProgram (edgeCount security) (Parameters.modulus security) decodedInjection decodedLoad).value.2) =
        splitSource security target := by
    apply roundingLoad_injective (edgeCount security) (Parameters.modulus security) hq decodedInjection.get hm
    rw [_p2mH154 _ _ _ _ hm hd, hl]
  rw [hmodulus] at hb
  have hresult : ((fun edge => ((binaryRoundingInverse (edgeCount security) modulus injection bitLoad).edges.get edge).decode),
      (binaryRoundingInverse (edgeCount security) modulus injection bitLoad).charge.decode) = splitSource security target := by
    apply (Prod.ext (funext hb.2) hb.1).trans he
  rw [hresult, _p2mH242]
open _root_.P2M661a572e renaming h232 → _p2mH232
end
open _root_.P2M661a572e renaming h232 → _p2mH232
open _root_.P2M661a572e renaming h233 → _p2mH233
open _root_.P2M661a572e renaming h234 → _p2mH234
open _root_.P2M661a572e renaming h235 → _p2mH235
open _root_.P2M661a572e renaming h236 → _p2mH236
end CurrentAFT.CurrentAffineEmissionBridge
open _root_.P2M661a572e renaming h232 → _p2mH232
open _root_.P2M661a572e renaming h233 → _p2mH233
open _root_.P2M661a572e renaming h234 → _p2mH234
open _root_.P2M661a572e renaming h235 → _p2mH235
open _root_.P2M661a572e renaming h236 → _p2mH236
end
open _root_.P2M661a572e renaming h232 → _p2mH232
open _root_.P2M661a572e renaming h233 → _p2mH233
open _root_.P2M661a572e renaming h234 → _p2mH234
open _root_.P2M661a572e renaming h235 → _p2mH235
open _root_.P2M661a572e renaming h236 → _p2mH236
section
namespace CurrentAFT.CurrentEmissionRootOrder
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentProposalDimensions CurrentProposalResources CurrentCoreProposal
open ActualCycleMeanMGF ConditionalHistogramMean ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount
  CurrentCoreProposal.draw addCounter subtractCounter lessCounter
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h316 (count front : ℕ) (hprefix : front ≤ count) (index : Fin count) :
    (rotate count front hprefix index).value.val = if index.val < front then count - front + index.val else index.val - front := by
  by_cases hi : index.val < front
  · have hs : (lessCounter index.val front).value = true := (lessCounter_value _ _).mpr hi
    simp only [rotate, dif_pos hs, Fin.val_mk, addCounter_value, subtractCounter_value, if_pos hi]
  · have hs : ¬(lessCounter index.val front).value = true := by simpa only [lessCounter_value] using hi
    simp only [rotate, dif_neg hs, Fin.val_mk, subtractCounter_value, if_neg hi]
open _root_.P2M661a572e renaming h316 → _p2mH316
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h315 (security : ℕ) (index : Fin (current security).body) :
    CurrentProposalDimensions.bodyEquiv security
      (rotate (current security).body (current security).legs (legs_le_body security) index).value =
    CurrentLayoutDraw.canonicalLayout security (rootToRole security ((rootNumbering security).symm index)) := by
  obtain ⟨leg | (center | queue), rfl⟩ := (rootNumbering security).surjective index
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals apply Fin.ext
  · have hi : leg.val < (current security).legs := by simpa only [(current_values security).2.1] using leg.isLt
    have hcount := root_count security
    change (rotate _ _ _ (rootNumbering security (.inl leg))).value.val = _
    rw [_p2mH316]
    have hv : (rootNumbering security (.inl leg)).val = leg.val := rfl
    rw [hv, if_pos hi]
    change (current security).body - (current security).legs + leg.val =
      BackgroundPopulationBounds.freeCount security + (Parameters.modulus security + leg.val)
    rw [(current_values security).2.1]
    unfold BackgroundPopulationBounds.freeCount centerCount at *
    omega
  · change (rotate _ _ _ (rootNumbering security (.inr (.inl center)))).value.val = _
    rw [_p2mH316]
    have hv : (rootNumbering security (.inr (.inl center))).val = Parameters.legCount security + center.val := rfl
    rw [hv]
    have hn : ¬Parameters.legCount security + center.val < (current security).legs := by
      rw [(current_values security).2.1]; omega
    rw [if_neg hn]
    change Parameters.legCount security + center.val - (current security).legs = center.val
    rw [(current_values security).2.1]
    omega
  · change (rotate _ _ _ (rootNumbering security (.inr (.inr queue)))).value.val = _
    rw [_p2mH316]
    have hv : (rootNumbering security (.inr (.inr queue))).val = Parameters.legCount security + (centerCount security + queue.val) := rfl
    rw [hv]
    have hn : ¬Parameters.legCount security + (centerCount security + queue.val) < (current security).legs := by
      rw [(current_values security).2.1]; omega
    rw [if_neg hn]
    change Parameters.legCount security + (centerCount security + queue.val) - (current security).legs =
      BackgroundPopulationBounds.freeCount security + queue.val
    rw [(current_values security).2.1]
    unfold BackgroundPopulationBounds.freeCount centerCount
    omega
open _root_.P2M661a572e renaming h315 → _p2mH315
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h314 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security)
    (index : Fin (current security).body) :
    (positions security layout data).value.get index =
      data.body.inverse.get (layout.forward.get (rotate (current security).body (current security).legs (legs_le_body security) index).value) := by
  simp only [positions, storeData_get, readVector_value]
open _root_.P2M661a572e renaming h314 → _p2mH314
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h562 {State Target : Type*} (equiv : State ≃ Target) (permutation : Equiv.Perm State) (state : State) :
    (equiv.permCongr permutation).symm (equiv state) = equiv (permutation.symm state) := by
  apply (equiv.permCongr permutation).injective
  simp only [Equiv.apply_symm_apply, Equiv.permCongr_apply, Equiv.symm_apply_apply]
open _root_.P2M661a572e renaming h562 → _p2mH562
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h313 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (data : MaterializedCore security)
    (index : Fin (current security).body) :
    CurrentProposalDimensions.bodyEquiv security ((positions security layout data).value.get index) =
      data.core.bodyPermutation.symm (layout.layout (rootToRole security ((rootNumbering security).symm index))) := by
  rw [_p2mH314]
  change CurrentProposalDimensions.bodyEquiv security
      (data.body.toEquiv.symm (layout.toEquiv (rotate _ _ _ index).value)) =
    ((CurrentProposalDimensions.bodyEquiv security).permCongr data.body.toEquiv).symm
      (((CurrentProposalDimensions.bodyEquiv security).permCongr layout.toEquiv)
        (CurrentLayoutDraw.canonicalLayout security (rootToRole security ((rootNumbering security).symm index))))
  rw [← _p2mH315 security index, Equiv.permCongr_apply, Equiv.symm_apply_apply, _p2mH562]
open _root_.P2M661a572e renaming h313 → _p2mH313
end CurrentAFT.CurrentEmissionRootOrder
open _root_.P2M661a572e renaming h313 → _p2mH313
open _root_.P2M661a572e renaming h314 → _p2mH314
open _root_.P2M661a572e renaming h315 → _p2mH315
open _root_.P2M661a572e renaming h316 → _p2mH316
open _root_.P2M661a572e renaming h562 → _p2mH562
end
open _root_.P2M661a572e renaming h314 → _p2mH314
open _root_.P2M661a572e renaming h315 → _p2mH315
open _root_.P2M661a572e renaming h313 → _p2mH313
open _root_.P2M661a572e renaming h316 → _p2mH316
section
namespace CurrentAFT.CurrentEmissionMetadata
open AFT AFT.BinaryArithmetic CurrentProposalDimensions CurrentProposalResources
open ActualBlockFock
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current Parameters.bodySize Parameters.legCount Parameters.dimension
  subtractCounter
attribute [local irreducible] CurrentEmissionMetadata.current
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h312 (security : ℕ)
    (point : Sigma (blockSlotsProgram (CurrentProposalDimensions.current security).legs (current security).rest)) :
    vertexEquiv security (physicalVertexNumberingProgram _ _ _ (current_counts security).2.2.2.1 point) =
      CurrentPhysicalNumbering.numbering security (pointEquiv security point) := by
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    apply Fin.ext
    change _ = (CurrentPhysicalNumbering.numbering security ⟨.inl (legEquiv security leg), slot⟩).val
    rw [_p2mH436]
    change slot.val + 3 * leg.val = slot.val + 3 * leg.val
    rfl
  · change Fin 1 at slot
    have hs : slot = 0 := Subsingleton.elim _ _
    subst slot
    obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    · apply Fin.ext
      change _ = (CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, _p2mH435]
      have hv := congrArg Fin.val he
      change center.val = body.val at hv
      change (CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) = Parameters.legCount security * 3 + center.val
      rw [(CurrentProposalDimensions.current_values security).2.1]
      omega
    · apply Fin.ext
      change _ = (CurrentPhysicalNumbering.numbering security
        (match finSumFinEquiv.symm (restEquiv security body) with
          | .inl center => ⟨.inr (.inl center), (0 : Fin 1)⟩
          | .inr queue => ⟨.inr (.inr queue), (0 : Fin 1)⟩)).val
      rw [← he, Equiv.symm_apply_apply, _p2mH437]
      have hv := congrArg Fin.val he
      change centerCount security + queue.val = body.val at hv
      change (CurrentProposalDimensions.current security).legs * 3 + (0 + 1 * body.val) =
        Parameters.legCount security * 3 + (centerCount security + queue.val)
      rw [(CurrentProposalDimensions.current_values security).2.1]
      omega
open _root_.P2M661a572e renaming h312 → _p2mH312
end CurrentAFT.CurrentEmissionMetadata
open _root_.P2M661a572e renaming h312 → _p2mH312
end
open _root_.P2M661a572e renaming h312 → _p2mH312
section
namespace CurrentAFT.CurrentBinaryIncidence
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h560 (condition : Prop) [Decidable condition] (first second : IntegerBits) :
    (if condition then first else second).decode = if condition then first.decode else second.decode := by
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h560 → _p2mH560
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h265 (bodyEdges column root : ℕ) :
    (pathEntry bodyEdges column root).value.decode = if column < bodyEdges then
      (if root = column then 1 else 0) - (if root = column + 1 then 1 else 0) else 0 := by
  have hi : (lessCounter column bodyEdges).value = true ↔ column < bodyEdges := lessCounter_value _ _
  have hp : (equalCounter root column).value = true ↔ root = column := equalCounter_value _ _
  have hn : (equalCounter root (addCounter column 1).count).value = true ↔ root = column + 1 := by
    rw [equalCounter_value, addCounter_value]
  simp only [pathEntry, _p2mH560, IntegerBits.subtract_value, IntegerBits.one_value, IntegerBits.zero_value, hi, hp, hn]
open _root_.P2M661a572e renaming h265 → _p2mH265
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h264 {legs : ℕ} (bodyEdges column : ℕ) (scale shear : Vector IntegerBits legs) (leg : Fin legs) :
    let first := (if column = bodyEdges + leg.val then (scale.get leg).decode else 0) +
      (if column = bodyEdges + leg.val + legs then (shear.get leg).decode else 0)
    let second := if column = bodyEdges + leg.val + legs then (1 : ℤ) else 0
    ((legEntries bodyEdges column scale shear leg).value.1.decode,
      ((legEntries bodyEdges column scale shear leg).value.2.1.decode,
        (legEntries bodyEdges column scale shear leg).value.2.2.decode)) = (first, (-first - second, second)) := by
  have hf : (equalCounter column (addCounter bodyEdges leg.val).count).value = true ↔ column = bodyEdges + leg.val := by
    rw [equalCounter_value, addCounter_value]
  have hs : (equalCounter column (addCounter (addCounter bodyEdges leg.val).count legs).count).value = true ↔
      column = bodyEdges + leg.val + legs := by
    rw [equalCounter_value, addCounter_value, addCounter_value]
  simp only [legEntries, _p2mH560, IntegerBits.add_value, IntegerBits.subtract_value, IntegerBits.negate_value, readVector_value, hf, hs, IntegerBits.zero_value, IntegerBits.one_value]
open _root_.P2M661a572e renaming h264 → _p2mH264
end CurrentAFT.CurrentBinaryIncidence
open _root_.P2M661a572e renaming h264 → _p2mH264
open _root_.P2M661a572e renaming h265 → _p2mH265
open _root_.P2M661a572e renaming h560 → _p2mH560
end
open _root_.P2M661a572e renaming h265 → _p2mH265
open _root_.P2M661a572e renaming h264 → _p2mH264
section
namespace CurrentAFT.CurrentPathImpulse
open AFT
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h429 (count column : ℕ) (vertex : Fin (count + 1)) :
    pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex =
      if column < count then (if vertex.val = column then 1 else 0) -
        (if vertex.val = column + 1 then 1 else 0) else 0 := by
  induction count generalizing column with
  | zero => simp only [pathLoad, Pi.zero_apply, Nat.not_lt_zero, if_false]
  | succ count ih =>
    cases column with
    | zero =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = 0 then (1 : ℤ) else 0) = 0 := by
          funext edge
          simp [Fin.tail]
        rw [pathLoad, Fin.cons_succ, ht, pathLoad_zero]
        have he : rest.val + 1 = 1 ↔ rest = 0 := by
          constructor
          · intro h; apply Fin.ext; change rest.val = 0; omega
          · rintro rfl; rfl
        change (0 - if rest = 0 then (1 : ℤ) else 0) =
          if 0 < count + 1 then (if rest.val + 1 = 0 then 1 else 0) -
            (if rest.val + 1 = 1 then 1 else 0) else 0
        simp only [Nat.zero_lt_succ, if_true, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, he]
    | succ column =>
      refine Fin.cases ?_ (fun rest => ?_) vertex
      · simp [pathLoad]
      · have ht : Fin.tail (fun edge : Fin (count + 1) => if edge.val = column + 1 then (1 : ℤ) else 0) =
            (fun edge : Fin count => if edge.val = column then 1 else 0) := by
          funext edge
          simp [Fin.tail]
        rw [pathLoad, Fin.cons_succ, ht, ih]
        have hf : ((0 : Fin (count + 1)).val = column + 1) = False := by simp
        have hp : rest.succ.val = column + 1 ↔ rest.val = column := by simp
        have hn : rest.succ.val = column + 1 + 1 ↔ rest.val = column + 1 := by simp
        simp only [hf, if_false, ite_self, Nat.add_lt_add_iff_right, hp, hn]
        exact sub_zero _
open _root_.P2M661a572e renaming h429 → _p2mH429
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h428 (count column : ℕ) (vertex : Fin (count + 1)) :
    (CurrentBinaryIncidence.pathEntry count column vertex.val).value.decode =
      pathLoad count (fun edge => if edge.val = column then (1 : ℤ) else 0) vertex := by
  rw [_p2mH265, _p2mH429]
open _root_.P2M661a572e renaming h428 → _p2mH428
end CurrentAFT.CurrentPathImpulse
open _root_.P2M661a572e renaming h428 → _p2mH428
open _root_.P2M661a572e renaming h429 → _p2mH429
end
open _root_.P2M661a572e renaming h428 → _p2mH428
open _root_.P2M661a572e renaming h429 → _p2mH429
namespace CurrentAFT.CurrentPathImpulse
end CurrentAFT.CurrentPathImpulse
section
namespace CurrentAFT.CurrentBinaryLoadColumns
open AFT AFT.BinaryArithmetic AFT.RationalRejectionProgram
open CurrentEmissionMetadata
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h268 (security : ℕ) (roots : Roots security) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (rootRead security roots point).value = roots.get
      ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1) := by
  simp only [rootRead, readVector_value, _p2mH30]
open _root_.P2M661a572e renaming h268 → _p2mH268
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h266 (security column : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (point : Point security) :
    (entry security column scale shear roots point).value.decode =
      loadEntry security column (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots point := by
  rcases point with ⟨leg | body, slot⟩
  · have hv := _p2mH264 (current security).bodyEdges column scale shear leg
    have hfirst := congrArg Prod.fst hv
    have hcompanion := congrArg (fun value => value.2.1) hv
    have hsecond := congrArg (fun value => value.2.2) hv
    try dsimp only at hfirst hcompanion hsecond
    have hp := _p2mH428 (current security).bodyEdges column
      ((rootRead security roots (.inl leg)).value.cast (current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    change Fin 3 at slot
    fin_cases slot <;> simp only [entry, loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ', IntegerBits.add_value,
      hfirst, hcompanion, hsecond, primaryEntry, secondEntry]
    change (CurrentBinaryIncidence.pathEntry (current security).bodyEdges column (rootRead security roots (.inl leg)).value.val).value.decode + _ = _
    rw [hp]
    simp only [_p2mH268, pathValue]
  · have hp := _p2mH428 (current security).bodyEdges column
      ((rootRead security roots (.inr body)).value.cast (current_counts security).1.symm)
    simp only [Fin.val_cast] at hp
    have hf : (lessCounter body.val (current security).centers).value = false ↔ (current security).centers ≤ body.val := by
      rw [Bool.eq_false_iff]
      exact (not_congr (lessCounter_value _ _)).trans not_lt
    have hc : ((! (lessCounter body.val (current security).centers).value) &&
        (equalCounter column (current security).edges).value) = true ↔
        (current security).centers ≤ body.val ∧ column = (current security).edges := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', hf, equalCounter_value]
    simp only [entry, loadEntry, IntegerBits.add_value]
    rw [hp]
    simp only [_p2mH268, pathValue]
    congr 1
    by_cases h : ((! (lessCounter body.val (current security).centers).value) &&
      (equalCounter column (current security).edges).value) = true
    · rw [if_pos h, if_pos (hc.mp h), IntegerBits.one_value]
    · rw [if_neg h, if_neg (fun hh => h (hc.mpr hh)), IntegerBits.zero_value]
open _root_.P2M661a572e renaming h266 → _p2mH266
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h267 (security : ℕ) (scale shear : Vector IntegerBits (Legs security)) (roots : Roots security)
    (column row : Fin ((current security).edges + 1)) :
    (((matrix security scale shear roots).value.get column).get row).decode =
      loadEntry security column.val (fun leg => (scale.get leg).decode) (fun leg => (shear.get leg).decode) roots
        ((physicalVertexNumberingProgram (Legs security) (current security).rest (current security).edges
          (current_counts security).2.2.2.1).symm row) := by
  simp only [matrix, storeData_get, _p2mH266, _p2mH26]
open _root_.P2M661a572e renaming h267 → _p2mH267
end CurrentAFT.CurrentBinaryLoadColumns
open _root_.P2M661a572e renaming h266 → _p2mH266
open _root_.P2M661a572e renaming h267 → _p2mH267
open _root_.P2M661a572e renaming h268 → _p2mH268
end
open _root_.P2M661a572e renaming h267 → _p2mH267
open _root_.P2M661a572e renaming h268 → _p2mH268
open _root_.P2M661a572e renaming h266 → _p2mH266
section
namespace CurrentAFT.CurrentBinaryChartData
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h255 (security : ℕ) (charts : Charts security)
    (field : CurrentAffineLegCarry.PublicChart security → ZMod (Parameters.modulus security))
    (leg : Fin (CurrentProposalDimensions.current security).legs) :
    ((fieldArray security charts field).value.get leg).decode = (field (charts.get (legEquiv security leg))).val := by
  simp only [fieldArray, storeData_get, _p2mH459, readVector_value]
open _root_.P2M661a572e renaming h255 → _p2mH255
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h256 (security : ℕ) (core : MaterializedCore security)
    (leg : Fin (CurrentProposalDimensions.current security).legs) :
    ((shiftArray security core).value.get leg).decode = ActualPublicCharge.legShift security core.core (legEquiv security leg) := by
  simp only [shiftArray, storeData_get, _p2mH457, readVector_value,
    core.inputs_correct, ActualPublicCharge.legShift, MaterializedCore.core, decode]
open _root_.P2M661a572e renaming h256 → _p2mH256
end CurrentAFT.CurrentBinaryChartData
open _root_.P2M661a572e renaming h255 → _p2mH255
open _root_.P2M661a572e renaming h256 → _p2mH256
end
open _root_.P2M661a572e renaming h256 → _p2mH256
open _root_.P2M661a572e renaming h255 → _p2mH255
section
namespace CurrentAFT.CurrentBinaryBaselines
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentEmissionMetadata
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h253 (security : ℕ) (body : Fin (current security).rest) (center : Fin (ActualBlockFock.centerCount security))
    (he : finSumFinEquiv (.inl center) = restEquiv security body)
    (index : Fin (CurrentProposalDimensions.current security).controls) (hi : index.val = body.val) :
    CurrentProposalDimensions.controlsEquiv security index = (UniformTaggedOutput.centerSplit security).symm center := by
  apply (UniformTaggedOutput.centerSplit security).injective
  apply Fin.ext
  have hv := congrArg Fin.val he
  change center.val = body.val at hv
  have hc : (UniformTaggedOutput.centerSplit security (CurrentProposalDimensions.controlsEquiv security index)).val = index.val := by
    simp only [UniformTaggedOutput.centerSplit, CurrentProposalDimensions.controlsEquiv, Equiv.trans_apply,
      finCongr_apply, Equiv.apply_symm_apply, Fin.val_cast]
  simpa only [Equiv.apply_symm_apply, hc, hi] using hv.symm
open _root_.P2M661a572e renaming h253 → _p2mH253
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h254 (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (read security core point).value.decode = ActualPublicCharge.centerAt security layout core.core (layout (role security point)) := by
  rcases point with leg | body
  · simp only [read, _p2mH459, readVector_value, role,
      ActualPublicCharge.centerAt, Equiv.symm_apply_apply, MaterializedCore.core, decode, CurrentEmissionMetadata.legEquiv]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val = body.val at hv
      have hb : body.val < (current security).centers := by
        rw [(current_values security).2.2.2, ← hv]
        exact center.isLt
      have hs := (lessCounter_value _ _).mpr hb
      simp only [read, dif_pos hs, _p2mH459, readVector_value,
        role, ← he, Equiv.symm_apply_apply, ActualPublicCharge.centerAt]
      have ha := _p2mH253 security body center he ⟨body.val, by rw [controls_count]; exact hb⟩ rfl
      simp only [MaterializedCore.core, decode]
      rw [← ha, Equiv.symm_apply_apply]
    · have hv := congrArg Fin.val he
      change ActualBlockFock.centerCount security + queue.val = body.val at hv
      have hb : ¬body.val < (current security).centers := by
        rw [(current_values security).2.2.2]; omega
      have hs : ¬(lessCounter body.val (current security).centers).value = true := fun hs => hb ((lessCounter_value _ _).mp hs)
      simp only [read, dif_neg hs, _p2mH459, readVector_value,
        role, ← he, Equiv.symm_apply_apply, ActualPublicCharge.centerAt, MaterializedCore.core, decode]
      have ha : (subtractCounter body.val (current security).centers).count =
          ((CurrentProposalDimensions.queueEquiv security).symm queue).val := by
        change (subtractCounter body.val (current security).centers).count = queue.val
        rw [subtractCounter_value, (current_values security).2.2.2]
        omega
      have hi (h : (subtractCounter body.val (current security).centers).count < (CurrentProposalDimensions.current security).colors) :
          (⟨(subtractCounter body.val (current security).centers).count, h⟩ : Fin (CurrentProposalDimensions.current security).colors) =
            (CurrentProposalDimensions.queueEquiv security).symm queue := Fin.ext ha
      rw [hi]
open _root_.P2M661a572e renaming h254 → _p2mH254
end CurrentAFT.CurrentBinaryBaselines
open _root_.P2M661a572e renaming h253 → _p2mH253
open _root_.P2M661a572e renaming h254 → _p2mH254
end
open _root_.P2M661a572e renaming h254 → _p2mH254
open _root_.P2M661a572e renaming h253 → _p2mH253
section
namespace CurrentAFT.CurrentBinaryOffsetLoad
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h286 (bodyEdges : ℕ) (root : Fin (bodyEdges + 1)) (scalar : IntegerBits) :
    (closure bodyEdges root.val scalar).value.decode = AffineBaseline.closure bodyEdges scalar.decode root := by
  have hl : (equalCounter root.val bodyEdges).value = true ↔ root = Fin.last bodyEdges := by
    rw [equalCounter_value, Fin.ext_iff]
    rfl
  have hf : (equalCounter root.val 0).value = true ↔ root = 0 := by
    rw [equalCounter_value, Fin.ext_iff]
    rfl
  unfold closure AffineBaseline.closure
  try dsimp only
  rw [IntegerBits.subtract_value]
  have he (test : Bool) : (if test then scalar else IntegerBits.zero).decode = if test then scalar.decode else 0 := by
    cases test <;> rfl
  rw [he, he]
  simp only [hl, hf]
open _root_.P2M661a572e renaming h286 → _p2mH286
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h287 (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (modulus : IntegerBits) (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits)
    (point : Point security) :
    (entry security core modulus shift intercept roots scalar point).value.decode =
      physicalLoad security core layout modulus.decode (fun leg => (shift.get leg).decode)
        (fun leg => (intercept.get leg).decode) roots scalar.decode point := by
  rcases point with ⟨leg | body, slot⟩
  · have hc := _p2mH286 (current security).bodyEdges
      ((rootRead security roots (.inl leg)).value.cast (current_counts security).1.symm) scalar
    simp only [Fin.val_cast, _p2mH268] at hc
    change Fin 3 at slot
    fin_cases slot <;> simp only [entry, physicalLoad, Matrix.cons_val_zero', Matrix.cons_val_succ',
      IntegerBits.add_value, IntegerBits.subtract_value, IntegerBits.one_value, readVector_value,
      _p2mH254 security core layout, hc, _p2mH268]
  · have hc := _p2mH286 (current security).bodyEdges
      ((rootRead security roots (.inr body)).value.cast (current_counts security).1.symm) scalar
    simp only [Fin.val_cast, _p2mH268] at hc
    simp only [entry, physicalLoad, IntegerBits.add_value,
      _p2mH254 security core layout, hc, _p2mH268]
open _root_.P2M661a572e renaming h287 → _p2mH287
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h288 (security : ℕ) (core : MaterializedCore security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (modulus : IntegerBits) (shift intercept : Vector IntegerBits (Legs security)) (roots : Roots security) (scalar : IntegerBits)
    (row : Fin ((current security).edges + 1)) :
    ((load security core modulus shift intercept roots scalar).value.get row).decode =
      physicalLoad security core layout modulus.decode (fun leg => (shift.get leg).decode)
        (fun leg => (intercept.get leg).decode) roots scalar.decode
        ((physicalVertexNumberingProgram (Legs security) (current security).rest (current security).edges
          (current_counts security).2.2.2.1).symm row) := by
  simp only [load, storeData_get, _p2mH287 security core layout, _p2mH26]
open _root_.P2M661a572e renaming h288 → _p2mH288
end CurrentAFT.CurrentBinaryOffsetLoad
open _root_.P2M661a572e renaming h286 → _p2mH286
open _root_.P2M661a572e renaming h287 → _p2mH287
open _root_.P2M661a572e renaming h288 → _p2mH288
end
open _root_.P2M661a572e renaming h287 → _p2mH287
open _root_.P2M661a572e renaming h286 → _p2mH286
open _root_.P2M661a572e renaming h288 → _p2mH288
section
namespace CurrentAFT.CurrentBinaryAffinePrimitives
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h251 (security : ℕ) (row : Fin (Size security)) :
    ((injection security).value.get row).decode = injectionColumn (current security).edges (Parameters.modulus security) row := by
  have h : (lessCounter row.val (CurrentProposalDimensions.current security).colors).value = true ↔ row.val < Parameters.modulus security := by
    rw [lessCounter_value, (CurrentProposalDimensions.current_values security).1]
  simp only [injection, storeData_get, injectionColumn]
  by_cases ht : (lessCounter row.val (CurrentProposalDimensions.current security).colors).value = true
  · rw [if_pos ht, if_pos (h.mp ht), IntegerBits.one_value]
  · rw [if_neg ht, if_neg (fun hh => ht (h.mpr hh)), IntegerBits.zero_value]
open _root_.P2M661a572e renaming h251 → _p2mH251
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h250 (security : ℕ) (core : MaterializedCore security) (row : Fin (Size security)) :
    vertexEquiv security ((endpointPermutation security core).value.get row) =
      core.core.endpointPermutation (vertexEquiv security row) := by
  simp only [endpointPermutation, storeData_get, readVector_value, MaterializedCore.core, decode,
    Equiv.permCongr_apply]
  apply Fin.ext
  change (core.endpoints.forward.get (row.cast (current_counts security).2.1)).val =
    (core.endpoints.forward.get ((CurrentProposalDimensions.endpointEquiv security).symm (vertexEquiv security row))).val
  have hi : row.cast (current_counts security).2.1 =
      (CurrentProposalDimensions.endpointEquiv security).symm (vertexEquiv security row) := by
    apply Fin.ext
    rfl
  rw [hi]
open _root_.P2M661a572e renaming h250 → _p2mH250
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h252 (security : ℕ) (data : Vector IntegerBits (Size security))
    (permutation : Vector (Fin (Size security)) (Size security)) (row : Fin (Size security)) :
    (permuteLoad security data permutation).value.get row = data.get (permutation.get row) := by
  simp only [permuteLoad, storeData_get, readVector_value]
open _root_.P2M661a572e renaming h252 → _p2mH252
end CurrentAFT.CurrentBinaryAffinePrimitives
open _root_.P2M661a572e renaming h250 → _p2mH250
open _root_.P2M661a572e renaming h251 → _p2mH251
open _root_.P2M661a572e renaming h252 → _p2mH252
end
open _root_.P2M661a572e renaming h250 → _p2mH250
open _root_.P2M661a572e renaming h251 → _p2mH251
open _root_.P2M661a572e renaming h252 → _p2mH252
section
namespace CurrentAFT.CurrentBinaryAffineGuard
open AFT BinaryArithmetic RationalRejectionProgram CurrentCoreProposal CurrentBinaryChartData
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.legCount Parameters.dimension Parameters.bodySize
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h249 (security : ℕ) (charts : Charts security) (leg : Fin (Parameters.legCount security)) :
    (scale security charts leg).value = true ↔ (charts.get leg).2.2.1 ≠ 0 := by
  have he : (equalCounter (charts.get leg).2.2.1.val 0).value = true ↔ (charts.get leg).2.2.1 = 0 := by
    rw [equalCounter_value, ZMod.val_eq_zero]
  simp only [scale, readVector_value, Bool.not_eq_true', Bool.eq_false_iff]
  exact not_congr he
open _root_.P2M661a572e renaming h249 → _p2mH249
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h248 (security : ℕ) (core : MaterializedCore security) (charts : Charts security) :
    (current security core charts).value = true ↔ CurrentAffineData.Valid security core.core charts.get := by
  simp only [current, Bool.and_eq_true, _p2mH169,
    BinaryProposalGuard.allFin_value, _p2mH249, CurrentAffineData.Valid]
open _root_.P2M661a572e renaming h248 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2M661a572e renaming h248 → _p2mH248
end CurrentAFT.CurrentBinaryAffineGuard
open _root_.P2M661a572e renaming h248 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2M661a572e renaming h248 → _p2mH248
open _root_.P2M661a572e renaming h249 → _p2mH249
end
open _root_.P2M661a572e renaming h249 → _p2mH249
open _root_.P2M661a572e renaming h248 → CurrentAFT.CurrentBinaryAffineGuard.current_value
open _root_.P2M661a572e renaming h248 → _p2mH248
section
namespace CurrentAFT.CurrentMaterializedCompletion
open AFT GaussianSource BinaryArithmetic RationalRejectionProgram
open CurrentCoreProposal CurrentAffineData
set_option maxHeartbeats 800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentChartsDraw.drawStored CurrentEdgeDrawProgram.draw
  CappedPublicRejection.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h419 (security : ℕ) (input : Option (MaterializedCore security)) (precision bits edgeBits : ℕ)
    (word : CurrentPublicCompletion.Tapes security bits edgeBits) :
    Option.map Result.sample (complete security input precision bits edgeBits word).value =
      (CurrentPublicCompletion.complete security (Option.map MaterializedCore.cached input) precision bits edgeBits word).value := by
  cases input with
  | none => rfl
  | some core => rfl
open _root_.P2M661a572e renaming h419 → _p2mH419
noncomputable section
open scoped Classical
open Polynomial
end
end CurrentAFT.CurrentMaterializedCompletion
open _root_.P2M661a572e renaming h419 → _p2mH419
end
open _root_.P2M661a572e renaming h419 → _p2mH419
section
namespace CurrentAFT.CurrentBinaryAffineEmitter
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentCoreProposal
open CurrentBinaryAffinePrimitives CurrentBinaryLoadColumns
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h246 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security)
    (h : ¬CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (emit security layout (some sample)).columns = (fallback security).columns ∧
      (emit security layout (some sample)).offset = (fallback security).offset := by
  have ht : ¬(CurrentBinaryAffineGuard.current security sample.core sample.charts).value = true :=
    fun ht => h ((_p2mH248 security sample.core sample.charts).mp ht)
  simp only [emit, if_neg ht, and_self]
open _root_.P2M661a572e renaming h246 → _p2mH246
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h247 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security)
    (h : CurrentAffineData.Valid security sample.core.core sample.charts.get) :
    (emit security layout (some sample)).columns = (assembled security layout sample).columns ∧
      (emit security layout (some sample)).offset = (assembled security layout sample).offset := by
  have ht := (_p2mH248 security sample.core sample.charts).mpr h
  simp only [emit, if_pos ht, and_self]
open _root_.P2M661a572e renaming h247 → _p2mH247
end
open _root_.P2M661a572e renaming h246 → _p2mH246
open _root_.P2M661a572e renaming h247 → _p2mH247
end CurrentAFT.CurrentBinaryAffineEmitter
open _root_.P2M661a572e renaming h246 → _p2mH246
open _root_.P2M661a572e renaming h247 → _p2mH247
end
open _root_.P2M661a572e renaming h246 → _p2mH246
open _root_.P2M661a572e renaming h247 → _p2mH247
section
namespace CurrentAFT.CurrentBinaryFallbackSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata CurrentBinaryAffineEmitter
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
private theorem _root_.P2M661a572e.h559 (test : Prop) [Decidable test] : (if test then IntegerBits.one else IntegerBits.zero).decode = if test then 1 else 0 := by
  split_ifs <;> rfl
open _root_.P2M661a572e renaming h559 → _p2mH559
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h261 (security : ℕ) (column : Fin (CurrentBinaryAffinePrimitives.Size security)) :
    CurrentBinaryAffineEmitter.decodeCoordinate security (fallbackColumn security column).value = Pi.single (vertexEquiv security column) 1 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (CurrentAffineGeometry.coordinateNumbering security).surjective row
  · have he : (equalCounter edge.val column.val).value = true ↔
        CurrentAffineGeometry.coordinateNumbering security (.inl edge) = vertexEquiv security column := by
      rw [equalCounter_value, Fin.ext_iff]
      change edge.val = column.val ↔ edge.val = column.val
      rfl
    simp only [CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inl,
      fallbackColumn, storeData_get, Fin.val_cast, _p2mH559, Pi.single_apply, he]
  · cases point
    have he : (equalCounter column.val (current security).edges).value = true ↔
        CurrentAffineGeometry.coordinateNumbering security (.inr ()) = vertexEquiv security column := by
      rw [equalCounter_value, Fin.ext_iff]
      change column.val = (current security).edges ↔ CurrentAffineGeometry.edgeCount security = column.val
      rw [(current_values security).2.1]
      exact eq_comm
    simp only [CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply, Sum.elim_inr,
      fallbackColumn, _p2mH559, Pi.single_apply, he]
open _root_.P2M661a572e renaming h261 → _p2mH261
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h262 (security : ℕ) : CurrentBinaryAffineEmitter.matrix security (fallback security) = 1 := by
  funext row column
  change CurrentBinaryAffineEmitter.decodeCoordinate security ((storeData _ (fallbackColumn security)).value.get ((vertexEquiv security).symm column)) row = _
  rw [storeData_get, _p2mH261, Equiv.apply_symm_apply]
  simp [Pi.single_apply, Matrix.one_apply]
open _root_.P2M661a572e renaming h262 → _p2mH262
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h263 (security : ℕ) : CurrentBinaryAffineEmitter.offset security (fallback security) = 0 := by
  funext row
  obtain ⟨edge | point, rfl⟩ := (CurrentAffineGeometry.coordinateNumbering security).surjective row
  · simp only [offset, fallback, CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply,
      Sum.elim_inl, storeData_get, IntegerBits.zero_value, Pi.zero_apply]
  · cases point
    simp only [offset, fallback, CurrentBinaryAffineEmitter.decodeCoordinate, CurrentAffineLoad.packSource, Equiv.symm_apply_apply,
      Sum.elim_inr, IntegerBits.zero_value, Pi.zero_apply]
open _root_.P2M661a572e renaming h263 → _p2mH263
end CurrentAFT.CurrentBinaryFallbackSemantic
open _root_.P2M661a572e renaming h261 → _p2mH261
open _root_.P2M661a572e renaming h262 → _p2mH262
open _root_.P2M661a572e renaming h263 → _p2mH263
open _root_.P2M661a572e renaming h559 → _p2mH559
end
open _root_.P2M661a572e renaming h263 → _p2mH263
open _root_.P2M661a572e renaming h262 → _p2mH262
open _root_.P2M661a572e renaming h261 → _p2mH261
section
namespace CurrentAFT.CurrentLinearPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates LobsterMixerMatrix PublicCharge
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h417 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ)
    (vertex : AssemblyIndex security) :
    linearLoad security layout core scale shear input
        (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      LobsterIncidence.load (placement security core) (attachments security layout)
        ((sourceEdges security input).1, (primary security scale shear input, (sourceEdges security input).2.2))
        (Sum.map (CurrentAffineGeometry.bodyEquiv security) id vertex) +
      (splitSource security input).2 * AffineRealization.queueColumn (bodyEdges security) (Parameters.legCount security)
        (Parameters.modulus security) (queues security layout) (relabeling security layout core)
        (relabeling security layout core (naturalNumbering security vertex)) := by
  have hi : (dimensionEquiv security).symm
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      relabeling security layout core (naturalNumbering security vertex) := by
    apply (dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, _p2mH237]
  unfold linearLoad
  rw [hi]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, _p2mH481,
    Equiv.symm_apply_apply]
  rw [_p2mH478]
  simp only [naturalNumbering, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.sumCongr_apply]
  rfl
open _root_.P2M661a572e renaming h417 → _p2mH417
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h418 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (scale shear : Fin (Parameters.legCount security) → ℤ) (input : Fin (Parameters.dimension security) → ℤ)
    (point : Sigma (Slots security)) :
    linearLoad security layout core scale shear input
      (core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security point)) =
      physical security layout core scale shear input point := by
  have hp : CurrentPhysicalNumbering.numbering security point =
      endpointFlatten security layout (toAssembly security layout point) := by
    change PublicCoefficientOutput.flatten security point =
      PublicCoefficientOutput.flatten security (toPhysical security layout (toAssembly security layout point))
    rw [toPhysical_toAssembly]
  rw [hp, _p2mH417]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [toAssembly, Fin.cases, Fin.induction, Fin.induction.go, naturalNumbering, _p2mH480,
        _p2mH479, LobsterIncidence.load, attachmentIncrement,
        attachments, attachmentPosition, queues, queuePosition, physical, path, placement]
  · simp [toAssembly, naturalNumbering, _p2mH479,
      LobsterIncidence.load, attachmentIncrement, attachments, attachmentPosition,
      queues, queuePosition, physical, path, placement]
  · simp [toAssembly, naturalNumbering, _p2mH479,
      LobsterIncidence.load, attachmentIncrement, attachments, attachmentPosition,
      queues, queuePosition, physical, path, placement]
open _root_.P2M661a572e renaming h418 → _p2mH418
end
open _root_.P2M661a572e renaming h417 → _p2mH417
open _root_.P2M661a572e renaming h418 → _p2mH418
end CurrentAFT.CurrentLinearPhysicalLoad
open _root_.P2M661a572e renaming h417 → _p2mH417
open _root_.P2M661a572e renaming h418 → _p2mH418
end
open _root_.P2M661a572e renaming h418 → _p2mH418
open _root_.P2M661a572e renaming h417 → _p2mH417
section
namespace CurrentAFT.CurrentBinaryLoadSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata
open CurrentCoreProposal (MaterializedCore)
open
  CurrentLinearPhysicalLoad CurrentAffineGeometry CurrentAffineLoad
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h277 (security : ℕ) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    (blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1 =
      CurrentEmissionRootOrder.rootNumbering security (blockEquiv security point) := by
  rcases point with leg | body
  · apply Fin.ext
    rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    all_goals
      apply Fin.ext
      simp only [blockEquiv, Equiv.sumCongr_apply, Sum.map_inr, Equiv.trans_apply,
        ← he, Equiv.symm_apply_apply]
    · change (Legs security)+body.val=Parameters.legCount security+center.val
      have hv := congrArg Fin.val he
      change center.val=body.val at hv
      rw [show Legs security=Parameters.legCount security from (CurrentProposalDimensions.current_values security).2.1, hv]
    · change (Legs security)+body.val=Parameters.legCount security+(centerCount security+queue.val)
      have hv := congrArg Fin.val he
      change centerCount security+queue.val=body.val at hv
      rw [show Legs security=Parameters.legCount security from (CurrentProposalDimensions.current_values security).2.1, hv]
open _root_.P2M661a572e renaming h277 → _p2mH277
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h270 (security : ℕ) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    CurrentEmissionRootOrder.rootToRole security (blockEquiv security point) = CurrentBinaryBaselines.role security point := by
  rcases point with leg | body
  · rfl
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    all_goals simp only [blockEquiv, CurrentBinaryBaselines.role, Equiv.sumCongr_apply, Sum.map_inr,
      Equiv.trans_apply, ← he, Equiv.symm_apply_apply]; rfl
open _root_.P2M661a572e renaming h270 → _p2mH270
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h278 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    ((CurrentEmissionRootOrder.positions security layout core).value.get
      ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)).val =
      (core.core.bodyPermutation.symm (layout.layout (CurrentBinaryBaselines.role security point))).val := by
  have h := _p2mH313 security layout core
    ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)
  rw [_p2mH277, Equiv.symm_apply_apply, _p2mH270] at h
  have hv := congrArg (fun vertex : BodyIndex security => vertex.val) h
  simpa only [CurrentProposalDimensions.bodyEquiv, finCongr_apply, Fin.val_cast, _p2mH277] using hv
open _root_.P2M661a572e renaming h278 → _p2mH278
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h269 (security : ℕ) (column : Fin ((current security).edges+1)) (index : Fin (Parameters.dimension security)) :
    (basisInput security column) index = if index.val=column.val then 1 else 0 := by
  simp only [basisInput, Pi.single_apply, Fin.ext_iff]
  rfl
open _root_.P2M661a572e renaming h269 → _p2mH269
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h271 (security : ℕ) (column : Fin ((current security).edges+1)) :
    (sourceEdges security (basisInput security column)).1 =
      fun edge => if edge.val=column.val then 1 else 0 := by
  funext edge
  change (basisInput security column)
    (coordinateNumbering security (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inl edge)))) = _
  rw [_p2mH269]
  rfl
open _root_.P2M661a572e renaming h271 → _p2mH271
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h272 (security : ℕ) (column : Fin ((current security).edges+1)) (leg : Fin (Parameters.legCount security)) :
    (sourceEdges security (basisInput security column)).2.1 leg =
      if bodyEdges security+leg.val=column.val then 1 else 0 := by
  change (basisInput security column)
    (coordinateNumbering security (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inl leg))))) = _
  rw [_p2mH269]
  rfl
open _root_.P2M661a572e renaming h272 → _p2mH272
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h279 (security : ℕ) (column : Fin ((current security).edges+1)) (leg : Fin (Parameters.legCount security)) :
    (sourceEdges security (basisInput security column)).2.2 leg =
      if bodyEdges security+(Parameters.legCount security+leg.val)=column.val then 1 else 0 := by
  change (basisInput security column)
    (coordinateNumbering security (.inl (LobsterCoordinates.edgeIndex (bodyEdges security) (Parameters.legCount security) (.inr (.inr leg))))) = _
  rw [_p2mH269]
  rfl
open _root_.P2M661a572e renaming h279 → _p2mH279
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h276 (security : ℕ) (column : Fin ((current security).edges+1)) :
    (splitSource security (basisInput security column)).2 =
      if column.val=(current security).edges then 1 else 0 := by
  change (basisInput security column) (coordinateNumbering security (.inr ())) = _
  rw [_p2mH269]
  change (if edgeCount security=column.val then (1 : ℤ) else 0)=_
  simp only [(current_values security).2.1, eq_comm]
open _root_.P2M661a572e renaming h276 → _p2mH276
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h275 (security : ℕ) (column : Fin ((current security).edges+1))
    (scale shear : Fin (Legs security) → ℤ) (leg : Fin (Legs security)) :
    primary security (fun i => scale ((CurrentEmissionMetadata.legEquiv security).symm i))
      (fun i => shear ((CurrentEmissionMetadata.legEquiv security).symm i))
      (basisInput security column) (CurrentEmissionMetadata.legEquiv security leg) =
      primaryEntry security column.val scale shear leg := by
  rw [primary, _p2mH272, _p2mH279]
  simp only [Equiv.symm_apply_apply]
  have hleg : (CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  unfold primaryEntry
  simp only [(current_values security).1, show Legs security=Parameters.legCount security from
    (CurrentProposalDimensions.current_values security).2.1]
  simp only [bodyEdges, add_comm (Parameters.legCount security) leg.val, ← add_assoc,
    eq_comm, mul_ite, mul_one, mul_zero]
open _root_.P2M661a572e renaming h275 → _p2mH275
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h280 (security : ℕ) (column : Fin ((current security).edges+1)) (leg : Fin (Legs security)) :
    (sourceEdges security (basisInput security column)).2.2 (CurrentEmissionMetadata.legEquiv security leg) =
      secondEntry security column.val leg := by
  rw [_p2mH279]
  unfold secondEntry
  simp only [(current_values security).1, show Legs security=Parameters.legCount security from
    (CurrentProposalDimensions.current_values security).2.1]
  have hleg : (CurrentEmissionMetadata.legEquiv security leg).val=leg.val := rfl
  rw [hleg]
  simp only [bodyEdges, add_comm (Parameters.legCount security) leg.val, ← add_assoc, eq_comm]
open _root_.P2M661a572e renaming h280 → _p2mH280
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h274 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (column : Fin ((current security).edges+1)) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    pathValue security column.val (CurrentEmissionRootOrder.positions security layout core).value point =
      path security core.core (basisInput security column)
        (layout.layout (CurrentBinaryBaselines.role security point)) := by
  unfold path pathValue
  rw [_p2mH271, _p2mH429, _p2mH429]
  simp only [Fin.val_cast]
  simp only [_p2mH278, (current_values security).1]
  rfl
open _root_.P2M661a572e renaming h274 → _p2mH274
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h273 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (column : Fin ((current security).edges+1)) (scale shear : Fin (Legs security) → ℤ) (point : Point security) :
    loadEntry security column.val scale shear (CurrentEmissionRootOrder.positions security layout core).value point =
      CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
        (fun leg => scale ((CurrentEmissionMetadata.legEquiv security).symm leg))
        (fun leg => shear ((CurrentEmissionMetadata.legEquiv security).symm leg))
        (basisInput security column)
        (core.core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security (pointEquiv security point))) := by
  rw [_p2mH418]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [pointEquiv, Equiv.coe_fn_mk, physical, loadEntry, Matrix.cons_val_zero', Matrix.cons_val_succ',
      _p2mH275, _p2mH280, _p2mH274, CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    · have hv := congrArg Fin.val he
      change center.val=body.val at hv
      have hn : ¬(current security).centers ≤ body.val := by
        rw [(current_values security).2.2.2, ← hv]
        exact Nat.not_le.mpr center.isLt
      simp only [pointEquiv, Equiv.coe_fn_mk, loadEntry, physical, ← he, Equiv.symm_apply_apply, _p2mH274,
        CurrentBinaryBaselines.role, hn, false_and, if_false, add_zero]
    · have hv := congrArg Fin.val he
      change centerCount security+queue.val=body.val at hv
      have hy : (current security).centers ≤ body.val := by
        rw [(current_values security).2.2.2, ← hv]
        omega
      simp only [pointEquiv, Equiv.coe_fn_mk, loadEntry, physical, ← he, Equiv.symm_apply_apply, _p2mH274,
        CurrentBinaryBaselines.role, hy, true_and, _p2mH276]
open _root_.P2M661a572e renaming h273 → _p2mH273
end
open _root_.P2M661a572e renaming h269 → _p2mH269
open _root_.P2M661a572e renaming h270 → _p2mH270
open _root_.P2M661a572e renaming h271 → _p2mH271
open _root_.P2M661a572e renaming h272 → _p2mH272
open _root_.P2M661a572e renaming h273 → _p2mH273
open _root_.P2M661a572e renaming h274 → _p2mH274
open _root_.P2M661a572e renaming h275 → _p2mH275
open _root_.P2M661a572e renaming h276 → _p2mH276
open _root_.P2M661a572e renaming h277 → _p2mH277
open _root_.P2M661a572e renaming h278 → _p2mH278
open _root_.P2M661a572e renaming h279 → _p2mH279
open _root_.P2M661a572e renaming h280 → _p2mH280
end CurrentAFT.CurrentBinaryLoadSemantic
open _root_.P2M661a572e renaming h269 → _p2mH269
open _root_.P2M661a572e renaming h270 → _p2mH270
open _root_.P2M661a572e renaming h271 → _p2mH271
open _root_.P2M661a572e renaming h272 → _p2mH272
open _root_.P2M661a572e renaming h273 → _p2mH273
open _root_.P2M661a572e renaming h274 → _p2mH274
open _root_.P2M661a572e renaming h275 → _p2mH275
open _root_.P2M661a572e renaming h276 → _p2mH276
open _root_.P2M661a572e renaming h277 → _p2mH277
open _root_.P2M661a572e renaming h278 → _p2mH278
open _root_.P2M661a572e renaming h279 → _p2mH279
open _root_.P2M661a572e renaming h280 → _p2mH280
end
open _root_.P2M661a572e renaming h277 → _p2mH277
open _root_.P2M661a572e renaming h275 → _p2mH275
open _root_.P2M661a572e renaming h270 → _p2mH270
open _root_.P2M661a572e renaming h276 → _p2mH276
open _root_.P2M661a572e renaming h280 → _p2mH280
open _root_.P2M661a572e renaming h278 → _p2mH278
open _root_.P2M661a572e renaming h274 → _p2mH274
open _root_.P2M661a572e renaming h273 → _p2mH273
open _root_.P2M661a572e renaming h271 → _p2mH271
open _root_.P2M661a572e renaming h269 → _p2mH269
open _root_.P2M661a572e renaming h279 → _p2mH279
open _root_.P2M661a572e renaming h272 → _p2mH272
namespace CurrentAFT.CurrentBinaryAffineEmitter
end CurrentAFT.CurrentBinaryAffineEmitter
namespace CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
end CurrentAFT.CurrentBinaryAffineEmitter.decodeCoordinate
namespace CurrentAFT.CurrentBinaryAffineEmitter.fallback
end CurrentAFT.CurrentBinaryAffineEmitter.fallback
namespace CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn
end CurrentAFT.CurrentBinaryAffineEmitter.fallbackColumn
namespace CurrentAFT.CurrentBinaryAffineEmitter.offset
end CurrentAFT.CurrentBinaryAffineEmitter.offset
namespace CurrentAFT.CurrentBinaryFallbackSemantic
end CurrentAFT.CurrentBinaryFallbackSemantic
section
namespace CurrentAFT.CurrentBinaryMatrixSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h283 (security : ℕ)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (count : ℕ) (hc : count = CurrentAffineGeometry.edgeCount security)
    (modulus : List Bool) (hm : value modulus = Parameters.modulus security)
    (injection load : Vector IntegerBits (count + 1))
    (hi : ∀ vertex, (injection.get vertex).decode = if vertex.val < Parameters.modulus security then 1 else 0)
    (target : Fin (Parameters.dimension security) → ℤ)
    (hl : ∀ vertex, (load.get vertex).decode = CurrentAffineLoad.rounding security target
      (CurrentAffineGeometry.dimensionEquiv security (vertex.cast (congrArg (fun n => n + 1) hc)))) :
    CurrentAffineLoad.packSource security
      ((fun edge => ((binaryRoundingInverse count modulus injection load).edges.get (edge.cast hc.symm)).decode),
        (binaryRoundingInverse count modulus injection load).charge.decode) = target := by
  subst count
  apply _p2mH232 security layout modulus hm injection load
    (fun vertex => hi vertex) target
  intro vertex
  simpa only [id_eq,Fin.cast_refl] using hl vertex
open _root_.P2M661a572e renaming h283 → _p2mH283
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h285 (security : ℕ) (vertex : Fin (Size security)) :
    CurrentAffineGeometry.dimensionEquiv security
      (vertex.cast (congrArg (fun n => n + 1) (current_values security).2.1)) = vertexEquiv security vertex := by
  apply Fin.ext
  rfl
open _root_.P2M661a572e renaming h285 → _p2mH285
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h284 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (core : MaterializedCore security) (scale shear : Vector IntegerBits (Legs security))
    (column row : Fin (Size security)) :
    ((binaryPermutedColumn (current security).edges
      (CurrentBinaryLoadColumns.matrix security scale shear (CurrentEmissionRootOrder.positions security layout core).value).value
      (endpointPermutation security core).value column).value.get row).decode =
    CurrentAffineEmissionBridge.linearLoad security layout.layout core.core
      (fun leg => (scale.get ((legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((legEquiv security).symm leg)).decode)
      (CurrentBinaryLoadSemantic.basisInput security column) (vertexEquiv security row) := by
  rw [_p2mH25, _p2mH267, _p2mH273]
  have hp := _p2mH312 security ((physicalVertexNumberingProgram (Legs security) (current security).rest
    (current security).edges (current_counts security).2.2.2.1).symm ((endpointPermutation security core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, _p2mH250, Equiv.symm_apply_apply]
open _root_.P2M661a572e renaming h284 → _p2mH284
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h282 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (core : MaterializedCore security) (scale shear : Vector IntegerBits (Legs security))
    (column : Fin (Size security)) :
    CurrentBinaryAffineEmitter.decodeCoordinate security
      (binaryAffineColumn (current security).edges
        (canonicalCounter (PublicParameterProgram.modulus security).count).digits
        (injection security).value
        (CurrentBinaryLoadColumns.matrix security scale shear (CurrentEmissionRootOrder.positions security layout core).value).value
        (endpointPermutation security core).value column).value =
    fun row => CurrentAffineGeometry.matrix security layout.layout core.core
      (fun leg => (scale.get ((legEquiv security).symm leg)).decode)
      (fun leg => (shear.get ((legEquiv security).symm leg)).decode) row (vertexEquiv security column) := by
  unfold CurrentBinaryAffineEmitter.decodeCoordinate binaryAffineColumn
  apply _p2mH283 security layout.layout (current security).edges (current_values security).2.1
  · rw [canonicalCounter_value, PublicParameterProgram.modulus_value]
  · intro vertex
    exact _p2mH251 security vertex
  · intro vertex
    rw [_p2mH284, _p2mH285]
    exact congrFun (_p2mH235 security layout.layout core.core _ _
      (vertexEquiv security column)).symm (vertexEquiv security vertex)
open _root_.P2M661a572e renaming h282 → _p2mH282
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h281 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) :
    CurrentBinaryAffineEmitter.matrix security (CurrentBinaryAffineEmitter.assembled security layout sample) =
      CurrentAffineGeometry.matrix security layout.layout sample.core.core
        (CurrentAffineData.scales security sample.charts.get) (CurrentAffineData.shears security sample.charts.get) := by
  funext row column
  simp only [CurrentBinaryAffineEmitter.matrix, CurrentBinaryAffineEmitter.assembled, storeData_get, _p2mH282,
    Equiv.apply_symm_apply]
  congr 1 <;> funext leg <;>
    simp only [_p2mH255, Equiv.apply_symm_apply,
      CurrentAffineData.scales, CurrentAffineData.shears]
open _root_.P2M661a572e renaming h281 → _p2mH281
end
open _root_.P2M661a572e renaming h281 → _p2mH281
open _root_.P2M661a572e renaming h282 → _p2mH282
open _root_.P2M661a572e renaming h283 → _p2mH283
open _root_.P2M661a572e renaming h284 → _p2mH284
open _root_.P2M661a572e renaming h285 → _p2mH285
end CurrentAFT.CurrentBinaryMatrixSemantic
open _root_.P2M661a572e renaming h281 → _p2mH281
open _root_.P2M661a572e renaming h282 → _p2mH282
open _root_.P2M661a572e renaming h283 → _p2mH283
open _root_.P2M661a572e renaming h284 → _p2mH284
open _root_.P2M661a572e renaming h285 → _p2mH285
end
open _root_.P2M661a572e renaming h284 → _p2mH284
open _root_.P2M661a572e renaming h281 → _p2mH281
open _root_.P2M661a572e renaming h282 → _p2mH282
open _root_.P2M661a572e renaming h285 → _p2mH285
open _root_.P2M661a572e renaming h283 → _p2mH283
section
namespace CurrentAFT.CurrentOffsetPhysicalLoad
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentAffineGeometry CurrentAffineLoad CurrentAffineEmissionBridge PublicEndpointPlacement
  LobsterCoordinates AffineBaseline
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h426 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (scalar : ℤ) (hcharge : publicCharge security core)
    (vertex : AssemblyIndex security) :
    rounding security (CurrentAffineGeometry.offset security layout core intercept scalar hcharge)
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      AffineBaseline.offset (Parameters.modulus security) (centers security layout core)
        (legShift security core) intercept (placement security core) scalar
        (Sum.map (CurrentAffineGeometry.bodyEquiv security) id vertex) := by
  have hi : (dimensionEquiv security).symm
      (core.endpointPermutation.symm (endpointFlatten security layout vertex)) =
      relabeling security layout core (naturalNumbering security vertex) := by
    apply (dimensionEquiv security).injective
    rw [Equiv.apply_symm_apply, _p2mH237]
  rw [_p2mH236 security layout core 0 0 intercept scalar hcharge]
  unfold CurrentAffineLoad.load
  rw [show splitSource security (0 : Fin (Parameters.dimension security) → ℤ) = 0 from rfl]
  simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, map_zero, ZeroMemClass.coe_zero,
    zero_smul, zero_add, numberedOffset, hi, Equiv.symm_apply_apply, naturalNumbering,
    Equiv.trans_apply, Equiv.sumCongr_apply]
  rfl
open _root_.P2M661a572e renaming h426 → _p2mH426
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h427 (security : ℕ) (layout : RoleIndex security ≃ BodyIndex security) (core : Core security)
    (intercept : Fin (Parameters.legCount security) → ℤ) (scalar : ℤ) (hcharge : publicCharge security core)
    (point : Sigma (Slots security)) :
    rounding security (CurrentAffineGeometry.offset security layout core intercept scalar hcharge)
      (core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security point)) =
      physical security layout core intercept scalar point := by
  have hp : CurrentPhysicalNumbering.numbering security point =
      endpointFlatten security layout (toAssembly security layout point) := by
    change PublicCoefficientOutput.flatten security point =
      PublicCoefficientOutput.flatten security (toPhysical security layout (toAssembly security layout point))
    rw [toPhysical_toAssembly]
  rw [hp, _p2mH426]
  rcases point with ⟨leg | (center | queue), slot⟩
  · change Fin 3 at slot
    fin_cases slot <;>
      simp [toAssembly, Fin.cases, Fin.induction, Fin.induction.go, AffineBaseline.offset,
        baseline, centers, placement, physical, rootLoad]
  · simp [toAssembly, AffineBaseline.offset, baseline, centers, placement, physical, rootLoad]
  · simp [toAssembly, AffineBaseline.offset, baseline, centers, placement, physical, rootLoad]
open _root_.P2M661a572e renaming h427 → _p2mH427
end
open _root_.P2M661a572e renaming h426 → _p2mH426
open _root_.P2M661a572e renaming h427 → _p2mH427
end CurrentAFT.CurrentOffsetPhysicalLoad
open _root_.P2M661a572e renaming h426 → _p2mH426
open _root_.P2M661a572e renaming h427 → _p2mH427
end
open _root_.P2M661a572e renaming h427 → _p2mH427
open _root_.P2M661a572e renaming h426 → _p2mH426
section
namespace CurrentAFT.CurrentBinaryOffsetSemantic
open AFT ActualBlockFock ActualCycleMeanMGF ConditionalHistogramMean ActualPublicCharge
  CurrentBinaryLoadColumns CurrentEmissionMetadata CurrentBinaryLoadSemantic
  CurrentAffineGeometry CurrentAffineLoad
open CurrentCoreProposal (MaterializedCore)
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentEmissionMetadata.current CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h289 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (scalar : ℤ) (point : Fin (Legs security) ⊕ Fin (current security).rest) :
    AffineBaseline.closure (current security).bodyEdges scalar
      (((CurrentEmissionRootOrder.positions security layout core).value.get
        ((blockNumbering (Legs security) (current security).rest point).cast (current_counts security).2.2.1)).cast
          (current_counts security).1.symm) =
    AffineBaseline.closure (bodyEdges security) scalar
      (CurrentAffineGeometry.bodyEquiv security
        (core.core.bodyPermutation.symm (layout.layout (CurrentBinaryBaselines.role security point)))) := by
  simp only [AffineBaseline.closure, Fin.ext_iff, Fin.val_cast, Fin.val_last, Fin.val_zero,
    _p2mH278, (current_values security).1]
  rfl
open _root_.P2M661a572e renaming h289 → _p2mH289
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h290 (security : ℕ) (layout : CurrentLayoutDraw.Cache security) (core : MaterializedCore security)
    (intercept : Fin (Legs security) → ℤ) (scalar : ℤ) (hcharge : publicCharge security core.core)
    (point : Point security) :
    CurrentBinaryOffsetLoad.physicalLoad security core layout.layout (Parameters.modulus security)
      (fun leg => legShift security core.core (CurrentEmissionMetadata.legEquiv security leg)) intercept
      (CurrentEmissionRootOrder.positions security layout core).value scalar point =
      rounding security
        (CurrentAffineGeometry.offset security layout.layout core.core
          (fun leg => intercept ((CurrentEmissionMetadata.legEquiv security).symm leg)) scalar hcharge)
        (core.core.endpointPermutation.symm (CurrentPhysicalNumbering.numbering security (pointEquiv security point))) := by
  rw [_p2mH427]
  rcases point with ⟨leg | body, slot⟩
  · change Fin 3 at slot
    fin_cases slot <;> simp only [pointEquiv, Equiv.coe_fn_mk, CurrentOffsetPhysicalLoad.physical,
      CurrentBinaryOffsetLoad.physicalLoad, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Equiv.symm_apply_apply, _p2mH289, CurrentOffsetPhysicalLoad.rootLoad, CurrentBinaryBaselines.role]
  · obtain ⟨center | queue, he⟩ := finSumFinEquiv.surjective (restEquiv security body)
    all_goals simp only [pointEquiv, Equiv.coe_fn_mk, CurrentOffsetPhysicalLoad.physical,
      CurrentBinaryOffsetLoad.physicalLoad, ← he, Equiv.symm_apply_apply, _p2mH289,
      CurrentOffsetPhysicalLoad.rootLoad, CurrentBinaryBaselines.role]
open _root_.P2M661a572e renaming h290 → _p2mH290
end
open _root_.P2M661a572e renaming h289 → _p2mH289
open _root_.P2M661a572e renaming h290 → _p2mH290
end CurrentAFT.CurrentBinaryOffsetSemantic
open _root_.P2M661a572e renaming h289 → _p2mH289
open _root_.P2M661a572e renaming h290 → _p2mH290
end
open _root_.P2M661a572e renaming h290 → _p2mH290
open _root_.P2M661a572e renaming h289 → _p2mH289
namespace CurrentAFT.CurrentAffineData
end CurrentAFT.CurrentAffineData
namespace CurrentAFT.CurrentAffineData.shears
end CurrentAFT.CurrentAffineData.shears
namespace CurrentAFT.CurrentBinaryAffineEmitter.assembled
end CurrentAFT.CurrentBinaryAffineEmitter.assembled
namespace CurrentAFT.CurrentBinaryAffineEmitter.matrix
end CurrentAFT.CurrentBinaryAffineEmitter.matrix
namespace CurrentAFT.CurrentBinaryMatrixSemantic
end CurrentAFT.CurrentBinaryMatrixSemantic
namespace CurrentAFT.CurrentBinaryOffsetSemantic
end CurrentAFT.CurrentBinaryOffsetSemantic
namespace CurrentAFT.CurrentEmissionMetadata
end CurrentAFT.CurrentEmissionMetadata
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv
end CurrentAFT.CurrentEmissionMetadata.pointEquiv
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_1
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_3
namespace CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
end CurrentAFT.CurrentEmissionMetadata.pointEquiv.match_5
section
namespace CurrentAFT.CurrentBinaryEmitterSemantic
open AFT BinaryArithmetic RationalRejectionProgram CurrentEmissionMetadata
open CurrentBinaryLoadColumns CurrentBinaryAffinePrimitives
open CurrentCoreProposal (MaterializedCore)
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
noncomputable section
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h260 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) (hcharge : ActualPublicCharge.publicCharge security sample.core.core)
    (row : Fin (Size security)) :
    ((permuteLoad security
      (CurrentBinaryOffsetLoad.load security sample.core
        ⟨false, (canonicalCounter (PublicParameterProgram.modulus security).count).digits⟩
        (CurrentBinaryChartData.shiftArray security sample.core).value
        (CurrentBinaryChartData.fieldArray security sample.charts (fun chart => chart.2.1)).value
        (CurrentEmissionRootOrder.positions security layout sample.core).value
        (CurrentPublicShiftProgram.encode sample.edge.val).value).value
      (endpointPermutation security sample.core).value).value.get row).decode =
    CurrentAffineLoad.rounding security
      (CurrentAffineGeometry.offset security layout.layout sample.core.core
        (CurrentAffineData.intercepts security sample.charts.get) sample.edge.val hcharge) (vertexEquiv security row) := by
  rw [_p2mH252, _p2mH288 security sample.core layout.layout]
  have hmod : (⟨false, (canonicalCounter (PublicParameterProgram.modulus security).count).digits⟩ : IntegerBits).decode = Parameters.modulus security := by
    simp only [IntegerBits.decode, signedValue, canonicalCounter_value, PublicParameterProgram.modulus_value, Bool.false_eq_true, if_false]
  rw [hmod, _p2mH459]
  simp only [_p2mH256]
  rw [_p2mH290 security layout sample.core _ _ hcharge]
  have hp := _p2mH312 security ((physicalVertexNumberingProgram (Legs security) (current security).rest
    (current security).edges (current_counts security).2.2.2.1).symm ((endpointPermutation security sample.core).value.get row))
  rw [Equiv.apply_symm_apply] at hp
  rw [← hp, _p2mH250, Equiv.symm_apply_apply]
  congr 2
  funext leg
  simp only [_p2mH255, Equiv.apply_symm_apply, CurrentAffineData.intercepts]
open _root_.P2M661a572e renaming h260 → _p2mH260
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h257 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (sample : CurrentMaterializedCompletion.Result security) (hcharge : ActualPublicCharge.publicCharge security sample.core.core) :
    CurrentBinaryAffineEmitter.offset security (CurrentBinaryAffineEmitter.assembled security layout sample) =
      CurrentAffineGeometry.offset security layout.layout sample.core.core
        (CurrentAffineData.intercepts security sample.charts.get) sample.edge.val hcharge := by
  unfold CurrentBinaryAffineEmitter.offset CurrentBinaryAffineEmitter.assembled CurrentBinaryAffineEmitter.decodeCoordinate
  apply _p2mH283 security layout.layout (current security).edges (current_values security).2.1
  · rw [canonicalCounter_value, PublicParameterProgram.modulus_value]
  · intro vertex
    exact _p2mH251 security vertex
  · intro vertex
    rw [_p2mH260 security layout sample hcharge, _p2mH285]
open _root_.P2M661a572e renaming h257 → _p2mH257
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h258 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) :
    CurrentBinaryAffineEmitter.matrix security (CurrentBinaryAffineEmitter.emit security layout input) =
      (NumericalAffineTransport.realizeResult security layout.layout (input.map CurrentMaterializedCompletion.Result.sample)).matrix := by
  cases input with
  | none => exact _p2mH262 security
  | some sample =>
    by_cases h : CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (_p2mH247 security layout sample h).1
      change (fun row column => CurrentBinaryAffineEmitter.decodeCoordinate security
        ((CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (_p2mH281 security layout sample).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_pos h, CurrentAffineData.assembled])
    · have he := (_p2mH246 security layout sample h).1
      change (fun row column => CurrentBinaryAffineEmitter.decodeCoordinate security
        ((CurrentBinaryAffineEmitter.emit security layout (some sample)).columns.get ((vertexEquiv security).symm column)) row) = _
      rw [he]
      exact (_p2mH262 security).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_neg h, CurrentAffineData.fallback])
open _root_.P2M661a572e renaming h258 → _p2mH258
 set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h259 (security : ℕ) (layout : CurrentLayoutDraw.Cache security)
    (input : Option (CurrentMaterializedCompletion.Result security)) :
    CurrentBinaryAffineEmitter.offset security (CurrentBinaryAffineEmitter.emit security layout input) =
      (NumericalAffineTransport.realizeResult security layout.layout (input.map CurrentMaterializedCompletion.Result.sample)).offset := by
  cases input with
  | none => exact _p2mH263 security
  | some sample =>
    by_cases h : CurrentAffineData.Valid security sample.core.core sample.charts.get
    · have he := (_p2mH247 security layout sample h).2
      change CurrentBinaryAffineEmitter.decodeCoordinate security (CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = _
      rw [he]
      exact (_p2mH257 security layout sample h.1).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_pos h, CurrentAffineData.assembled])
    · have he := (_p2mH246 security layout sample h).2
      change CurrentBinaryAffineEmitter.decodeCoordinate security (CurrentBinaryAffineEmitter.emit security layout (some sample)).offset = _
      rw [he]
      exact (_p2mH263 security).trans (by
        simp only [NumericalAffineTransport.realizeResult, Option.map_some, CurrentPublicAffineSample.realize,
          CurrentMaterializedCompletion.Result.sample, CurrentAffineData.assemble, dif_neg h, CurrentAffineData.fallback])
open _root_.P2M661a572e renaming h259 → _p2mH259
end
open _root_.P2M661a572e renaming h257 → _p2mH257
open _root_.P2M661a572e renaming h258 → _p2mH258
open _root_.P2M661a572e renaming h259 → _p2mH259
open _root_.P2M661a572e renaming h260 → _p2mH260
end CurrentAFT.CurrentBinaryEmitterSemantic
open _root_.P2M661a572e renaming h257 → _p2mH257
open _root_.P2M661a572e renaming h258 → _p2mH258
open _root_.P2M661a572e renaming h259 → _p2mH259
open _root_.P2M661a572e renaming h260 → _p2mH260
end
open _root_.P2M661a572e renaming h258 → _p2mH258
open _root_.P2M661a572e renaming h257 → _p2mH257
open _root_.P2M661a572e renaming h259 → _p2mH259
open _root_.P2M661a572e renaming h260 → _p2mH260
section
namespace CurrentAFT.CurrentMaterializedCompletion
open AFT ActualPublicCharge CurrentCoreProposal CurrentPublicCompletion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CappedPublicRejection.current CurrentMaterializedCompletion.current
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h420 (security bits edgeBits : ℕ) :
    CurrentPublicCompletion.tapeLaw security bits edgeBits = FiniteDist.uniform (CurrentPublicCompletion.Tapes security bits edgeBits) := by
  simp only [CurrentPublicCompletion.tapeLaw, CurrentChartsDraw.tapeLaw, CurrentFlagJointDraw.tapeLaw,
    ← _p2mH95, _p2mH80]
open _root_.P2M661a572e renaming h420 → _p2mH420
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h422 {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (program : First → Second → Output) :
    (first.prod second).map (fun pair => program pair.1 pair.2) =
      first.mix (fun input => second.map (program input)) := by
  ext output
  simp only [FiniteDist.map_weight, FiniteDist.prod_weight, FiniteDist.mix_weight, Fintype.sum_prod_type,
    Finset.mul_sum, mul_ite, mul_zero]
open _root_.P2M661a572e renaming h422 → _p2mH422
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h423 (security order : ℕ)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order) :
    publicLaw security order table =
      ((CappedPublicRejection.law security order table).map (Option.map MaterializedCore.cached)).mix
        (CurrentPublicCompletion.kernel security security security security) := by
  rw [publicLaw, _p2mH95]
  unfold CurrentMaterializedCompletion.current
  change ((FiniteDist.uniform (CappedPublicRejection.Tapes security)).prod
    (FiniteDist.uniform (CurrentPublicCompletion.Tapes security security security))).map
      (fun pair => Option.map Result.sample (complete security
        (CappedPublicRejection.current security order table pair.1).value security security security pair.2).value) = _
  simp only [_p2mH419]
  rw [_p2mH422 (FiniteDist.uniform (CappedPublicRejection.Tapes security))
    (FiniteDist.uniform (CurrentPublicCompletion.Tapes security security security))
    (fun first second => (CurrentPublicCompletion.complete security
      (Option.map MaterializedCore.cached (CappedPublicRejection.current security order table first).value)
      security security security second).value)]
  simp only [CappedPublicRejection.law, FiniteDist.mix_map, CurrentPublicCompletion.kernel, _p2mH420]
open _root_.P2M661a572e renaming h423 → _p2mH423
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h425 {weightError : ℕ → ℝ} (he : Negligible weightError) :
    Negligible (fun security => totalError security (weightError security)) := by
  have hc := _p2mH221 he
  have hp := _p2mH502 _p2mH490 (1/2)
  convert hc.add hp using 1
  funext security
  unfold totalError
  ring
open _root_.P2M661a572e renaming h425 → _p2mH425
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h424 (security order : ℕ) (hsecurity : 1 ≤ security)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(BinaryPublicRejection.coreWeight security security order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security)) :
    FiniteDist.TVBound (publicLaw security order table)
      ((CurrentPublicAffineSample.law security weight hpositive).map some) (totalError security weightError) := by
  have hc := _p2mH219 security order table weight weightError he hweight hpositive hmass
  have hforget : ((CappedPublicRejection.law security order table).map (Option.map MaterializedCore.cached)).map
      (Option.map (CurrentPublicCompletion.coreEquiv security)) =
      (CappedPublicRejection.law security order table).map (BinaryPublicRejection.decodeResult security) := by
    rw [FiniteDist.map_map]
    congr 1
    funext input
    cases input <;> rfl
  have hl := _p2mH500 security weight hpositive
    ((CappedPublicRejection.law security order table).map (Option.map MaterializedCore.cached))
    (CappedPublicRejection.error security weightError) (by rw [hforget]; exact hc)
  rw [_p2mH423]
  exact _p2mH499 security security security security hsecurity weight hpositive
    _ _ hl
open _root_.P2M661a572e renaming h424 → _p2mH424
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h421 (security order : ℕ) (hsecurity : 1 ≤ security)
    (layout : ConditionalHistogramMean.RoleIndex security ≃ ActualCycleMeanMGF.BodyIndex security)
    (table : BinaryWeightCoordinates.Table (BinaryWeightLocal.colors security) order)
    (weight : Core security → ℝ) (weightError analytic : ℝ) (he : 0 ≤ weightError)
    (hweight : ∀ core, |(BinaryPublicRejection.coreWeight security security order table core : ℝ)-weight core| ≤ weightError)
    (hpositive : 0 < publicCoreMass (proposal security) weight (publicCharge security))
    (hmass : 1/(4*(Parameters.modulus security : ℝ)) ≤ publicCoreMass (proposal security) weight (publicCharge security))
    (hanalytic : (CurrentAffineTransport.gaussianLaw security layout weight hpositive).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ analytic) :
    (NumericalAffineTransport.gaussianOutput security layout (publicLaw security order table)).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ analytic+totalError security weightError :=
  _p2mH487 security layout weight hpositive (publicLaw security order table)
    (totalError security weightError) analytic (_p2mH424 security order hsecurity table weight weightError he hweight hpositive hmass) hanalytic
open _root_.P2M661a572e renaming h421 → _p2mH421
end
open _root_.P2M661a572e renaming h420 → _p2mH420
open _root_.P2M661a572e renaming h421 → _p2mH421
open _root_.P2M661a572e renaming h422 → _p2mH422
open _root_.P2M661a572e renaming h423 → _p2mH423
open _root_.P2M661a572e renaming h424 → _p2mH424
open _root_.P2M661a572e renaming h425 → _p2mH425
end CurrentAFT.CurrentMaterializedCompletion
open _root_.P2M661a572e renaming h420 → _p2mH420
open _root_.P2M661a572e renaming h421 → _p2mH421
open _root_.P2M661a572e renaming h422 → _p2mH422
open _root_.P2M661a572e renaming h423 → _p2mH423
open _root_.P2M661a572e renaming h424 → _p2mH424
open _root_.P2M661a572e renaming h425 → _p2mH425
end
open _root_.P2M661a572e renaming h422 → _p2mH422
open _root_.P2M661a572e renaming h424 → _p2mH424
open _root_.P2M661a572e renaming h420 → _p2mH420
open _root_.P2M661a572e renaming h423 → _p2mH423
open _root_.P2M661a572e renaming h421 → _p2mH421
open _root_.P2M661a572e renaming h425 → _p2mH425
section
namespace CurrentAFT.PublicBitTapes
open AFT CurrentCoreProposal
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h522 {State : Type*} [Fintype State] [Nonempty State] (encoding : Encoding State) :
    (FiniteDist.uniform (Fin encoding.bits → Fin 2)).map encoding.equiv = FiniteDist.uniform State :=
  FiniteDist.uniform_map_equiv encoding.equiv
open _root_.P2M661a572e renaming h522 → _p2mH522
end
open _root_.P2M661a572e renaming h522 → _p2mH522
end CurrentAFT.PublicBitTapes
open _root_.P2M661a572e renaming h522 → _p2mH522
end
open _root_.P2M661a572e renaming h522 → _p2mH522
namespace CurrentAFT.CurrentAffineData.assembled
end CurrentAFT.CurrentAffineData.assembled
namespace CurrentAFT.CurrentAffineData.intercepts
end CurrentAFT.CurrentAffineData.intercepts
namespace CurrentAFT.CurrentBinaryEmitterSemantic
end CurrentAFT.CurrentBinaryEmitterSemantic
namespace CurrentAFT.CurrentMaterializedCompletion
end CurrentAFT.CurrentMaterializedCompletion
namespace CurrentAFT.CurrentMaterializedCompletion.Result
end CurrentAFT.CurrentMaterializedCompletion.Result
namespace CurrentAFT.CurrentMaterializedCompletion.Result.sample
end CurrentAFT.CurrentMaterializedCompletion.Result.sample
namespace CurrentAFT.CurrentPublicAffineSample
end CurrentAFT.CurrentPublicAffineSample
namespace CurrentAFT.CurrentPublicAffineSample.realize
end CurrentAFT.CurrentPublicAffineSample.realize
namespace CurrentAFT.NumericalAffineTransport
end CurrentAFT.NumericalAffineTransport
namespace CurrentAFT.NumericalAffineTransport.realizeResult
end CurrentAFT.NumericalAffineTransport.realizeResult
namespace CurrentAFT.NumericalAffineTransport.realizeResult.match_1
end CurrentAFT.NumericalAffineTransport.realizeResult.match_1
namespace CurrentAFT.PublicBitResources
end CurrentAFT.PublicBitResources
section
namespace CurrentAFT.PublicAffinePipeline
open AFT BinaryArithmetic RationalRejectionProgram
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw
noncomputable section
open scoped Classical
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h512 (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    CurrentBinaryAffineEmitter.matrix security (addWork security extra data) =
      CurrentBinaryAffineEmitter.matrix security data := rfl
open _root_.P2M661a572e renaming h512 → _p2mH512
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h513 (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    CurrentBinaryAffineEmitter.offset security (addWork security extra data) =
      CurrentBinaryAffineEmitter.offset security data := rfl
open _root_.P2M661a572e renaming h513 → _p2mH513
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h517 (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentBinaryAffineEmitter.matrix security (forLayout security order producer layout word) =
      (NumericalAffineTransport.realizeResult security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample)).matrix :=
  _p2mH258 security layout _
open _root_.P2M661a572e renaming h517 → _p2mH517
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h518 (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    CurrentBinaryAffineEmitter.offset security (forLayout security order producer layout word) =
      (NumericalAffineTransport.realizeResult security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample)).offset :=
  _p2mH259 security layout _
open _root_.P2M661a572e renaming h518 → _p2mH518
end
open _root_.P2M661a572e renaming h512 → _p2mH512
open _root_.P2M661a572e renaming h513 → _p2mH513
open _root_.P2M661a572e renaming h517 → _p2mH517
open _root_.P2M661a572e renaming h518 → _p2mH518
end CurrentAFT.PublicAffinePipeline
open _root_.P2M661a572e renaming h512 → _p2mH512
open _root_.P2M661a572e renaming h513 → _p2mH513
open _root_.P2M661a572e renaming h517 → _p2mH517
open _root_.P2M661a572e renaming h518 → _p2mH518
end
open _root_.P2M661a572e renaming h513 → _p2mH513
open _root_.P2M661a572e renaming h518 → _p2mH518
open _root_.P2M661a572e renaming h512 → _p2mH512
open _root_.P2M661a572e renaming h517 → _p2mH517
section
namespace CurrentAFT.PublicAffinePipeline
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] CurrentProposalDimensions.current CurrentEmissionMetadata.current
  Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentBinaryAffineEmitter.emit CurrentMaterializedCompletion.current CurrentLayoutDraw.draw
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h511 (security extra : ℕ) (data : CurrentBinaryAffineEmitter.Data security) :
    gaussianChannel security (addWork security extra data) = gaussianChannel security data := by
  simp only [gaussianChannel, _p2mH512, _p2mH513]
open _root_.P2M661a572e renaming h511 → _p2mH511
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h516 (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) (word : CurrentMaterializedCompletion.Tapes security) :
    gaussianChannel security (forLayout security order producer layout word) =
      NumericalAffineTransport.gaussianChannel security layout.layout
        ((CurrentMaterializedCompletion.current security order (producer layout).value word).value.map
          CurrentMaterializedCompletion.Result.sample) := by
  unfold gaussianChannel
  rw [_p2mH517, _p2mH518]
  rfl
open _root_.P2M661a572e renaming h516 → _p2mH516
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h515 (security order : ℕ) (producer : Producer security order)
    (layout : CurrentLayoutDraw.Cache security) :
    fixedGaussian security order producer layout =
      NumericalAffineTransport.gaussianOutput security layout.layout
        (CurrentMaterializedCompletion.publicLaw security order (producer layout).value) := by
  simp only [fixedGaussian, _p2mH516, NumericalAffineTransport.gaussianOutput,
    CurrentMaterializedCompletion.publicLaw, FiniteDist.mix_map]
open _root_.P2M661a572e renaming h515 → _p2mH515
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h514 (security order : ℕ) (producer : Producer security order) :
    fairGaussian security order producer = runGaussian security order producer := by
  unfold fairGaussian fairBitRun runGaussian
  rw [← FiniteDist.mix_map _ (PublicBitTapes.current security).equiv
    (fun word => gaussianChannel security (run security order producer word)), _p2mH522]
open _root_.P2M661a572e renaming h514 → _p2mH514
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h520 {First Second Output : Type*} [Fintype First] [Fintype Second] [Fintype Output]
    (first : FiniteDist First) (second : FiniteDist Second) (channel : First × Second → FiniteDist Output) :
    (first.prod second).mix channel = first.mix (fun a => second.mix (fun b => channel (a,b))) := by
  ext output
  simp only [FiniteDist.mix_weight, FiniteDist.prod_weight, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
open _root_.P2M661a572e renaming h520 → _p2mH520
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h521 (security order : ℕ) (producer : Producer security order) :
    runGaussian security order producer =
      (FiniteDist.uniform (CurrentLayoutDraw.Tape security security)).mix
        (fun word => fixedGaussian security order producer (CurrentLayoutDraw.draw security security word).value) := by
  rw [runGaussian, _p2mH95, _p2mH520]
  simp only [run, _p2mH511, fixedGaussian]
open _root_.P2M661a572e renaming h521 → _p2mH521
set_option maxRecDepth 8192
theorem _root_.P2M661a572e.h519 (security order : ℕ) (producer : Producer security order) (error : ℝ)
    (hfixed : ∀ layout, (fixedGaussian security order producer layout).totalVariation
      (CurrentZeroFiber.uniformFiber security) ≤ error) :
    (fairGaussian security order producer).totalVariation (CurrentZeroFiber.uniformFiber security) ≤ error := by
  rw [_p2mH514, _p2mH521]
  have h := _p2mH68 (FiniteDist.uniform (CurrentLayoutDraw.Tape security security))
    (first := fun word => fixedGaussian security order producer (CurrentLayoutDraw.draw security security word).value)
    (second := fun _ => CurrentZeroFiber.uniformFiber security)
    (fun word => (_p2mH93 _ _ _).mpr (hfixed _))
  rw [FiniteDist.mix_const] at h
  exact (_p2mH93 _ _ _).mp h
open _root_.P2M661a572e renaming h519 → _p2mH519
end
open _root_.P2M661a572e renaming h511 → _p2mH511
open _root_.P2M661a572e renaming h514 → _p2mH514
open _root_.P2M661a572e renaming h515 → _p2mH515
open _root_.P2M661a572e renaming h516 → _p2mH516
open _root_.P2M661a572e renaming h519 → _p2mH519
open _root_.P2M661a572e renaming h520 → _p2mH520
open _root_.P2M661a572e renaming h521 → _p2mH521
end CurrentAFT.PublicAffinePipeline
open _root_.P2M661a572e renaming h511 → _p2mH511
open _root_.P2M661a572e renaming h514 → _p2mH514
open _root_.P2M661a572e renaming h515 → _p2mH515
open _root_.P2M661a572e renaming h516 → _p2mH516
open _root_.P2M661a572e renaming h519 → _p2mH519
open _root_.P2M661a572e renaming h520 → _p2mH520
open _root_.P2M661a572e renaming h521 → _p2mH521
end
open _root_.P2M661a572e renaming h519 → _p2mH519
open _root_.P2M661a572e renaming h511 → _p2mH511
open _root_.P2M661a572e renaming h520 → _p2mH520
open _root_.P2M661a572e renaming h514 → _p2mH514
open _root_.P2M661a572e renaming h516 → _p2mH516
open _root_.P2M661a572e renaming h515 → _p2mH515
open _root_.P2M661a572e renaming h521 → _p2mH521
namespace CurrentAFT.ActualCalibratedPublic
end CurrentAFT.ActualCalibratedPublic
namespace CurrentAFT.ActualCalibratedPublic.weight
end CurrentAFT.ActualCalibratedPublic.weight
namespace CurrentAFT.CurrentAffineTransport
end CurrentAFT.CurrentAffineTransport
namespace CurrentAFT.CurrentAffineTransport.gaussianLaw
end CurrentAFT.CurrentAffineTransport.gaussianLaw
namespace CurrentAFT.NumericalGaussianAccuracy
end CurrentAFT.NumericalGaussianAccuracy
section
namespace CurrentAFT.PublicAffinePipeline
open AFT ActualPublicCharge ActualCompleteStability ActualGaussianAccuracy ActualCalibrationRates
open Filter
open scoped Classical Topology
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  CurrentProposalDimensions.current
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.PublicAffinePipeline.__p2m_proof_661a572e2b79379039c5 (accuracyOrder : ℕ)
    (producer : ∀ security, Producer security (Parameters.calibrationOrder accuracyOrder))
    (weightError : ℕ → ℝ) (hnonneg : ∀ security, 0 ≤ weightError security) (hnegligible : Negligible weightError)
    (hweight : ∀ᶠ security : ℕ in atTop,
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (_p2mH159 accuracyOrder) ≤ security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : Core security),
        |(BinaryPublicRejection.coreWeight security security (Parameters.calibrationOrder accuracyOrder)
          (producer security layout).value core : ℝ)-
          ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH159 accuracyOrder) hsecurity layout.layout core| ≤ weightError security) :
    ∃ cutoff : ℕ, ∀ security ≥ cutoff,
      (fairGaussian security (Parameters.calibrationOrder accuracyOrder) (producer security)).totalVariation
        (CurrentZeroFiber.uniformFiber security) ≤ (security : ℝ)^(-(accuracyOrder : ℝ)) := by
  have herror := _p2mH425 hnegligible
  obtain ⟨analyticCutoff, ha⟩ := NumericalGaussianAccuracy.gaussian_with_numerics accuracyOrder
    (fun security => CurrentMaterializedCompletion.totalError security (weightError security)) herror
  have hall : ∀ᶠ security : ℕ in atTop,
      analyticCutoff ≤ security ∧ 1 ≤ security ∧
      ∀ hsecurity : threshold (Parameters.calibrationOrder accuracyOrder)
        (_p2mH159 accuracyOrder) ≤ security,
      ∀ (layout : CurrentLayoutDraw.Cache security) (core : Core security),
        |(BinaryPublicRejection.coreWeight security security (Parameters.calibrationOrder accuracyOrder)
          (producer security layout).value core : ℝ)-
          ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
            (_p2mH159 accuracyOrder) hsecurity layout.layout core| ≤ weightError security := by
    filter_upwards [eventually_ge_atTop analyticCutoff, eventually_ge_atTop 1, hweight] with security hc hs hw
    exact ⟨hc,hs,hw⟩
  obtain ⟨cutoff, hcutoff⟩ := eventually_atTop.mp hall
  refine ⟨cutoff, fun security hs => ?_⟩
  obtain ⟨hc, hsec, hw⟩ := hcutoff security hs
  obtain ⟨hsecurity, hbound⟩ := ha security hc
  apply _p2mH519
  intro layout
  obtain ⟨hpositive, hmass, htotal⟩ := hbound layout.layout
  rw [_p2mH515]
  have hlower : 1/(4*(Parameters.modulus security : ℝ)) ≤ 1/(2*(Parameters.modulus security : ℝ)) := by
    have hq : (0 : ℝ)<Parameters.modulus security := by exact_mod_cast (Parameters.modulus_spec security).2.pos
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h := _p2mH421 security (Parameters.calibrationOrder accuracyOrder) hsec
    layout.layout (producer security layout).value
    (ActualCalibratedPublic.weight security (Parameters.calibrationOrder accuracyOrder)
      (_p2mH159 accuracyOrder) hsecurity layout.layout)
    (weightError security) _ (hnonneg security) (hw hsecurity layout) hpositive (hlower.trans hmass) le_rfl
  exact h.trans htotal
end
end CurrentAFT.PublicAffinePipeline
end
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.PublicAffinePipeline.__p2m_proof_661a572e2b79379039c5) := @_root_.CurrentAFT.PublicAffinePipeline.__p2m_proof_661a572e2b79379039c5
