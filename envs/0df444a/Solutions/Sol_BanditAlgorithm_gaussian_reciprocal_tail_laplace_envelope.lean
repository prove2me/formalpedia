-- Prove2me | solution 1 for BanditAlgorithm.gaussian_reciprocal_tail_laplace_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T01:09:37.678357+00:00
-- url     : https://prove2.me/submissions/20843471-d1f5-4094-a5e7-918379640793

import Theorems.Thm_BanditAlgorithm_standardGaussian_mills_lower_bound
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private noncomputable def Qlap (u : ℝ) : ℝ :=
  (gaussianReal 0 1).real (Set.Ioi u)

private theorem Qlap_compl (u : ℝ) :
    Qlap u + Qlap (-u) = 1 := by
  let P : Measure ℝ := gaussianReal 0 1
  have hmap : P.map (fun x ↦ -x) = P := by
    dsimp [P]
    simpa using
      (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have happ := congrArg (fun M : Measure ℝ ↦ M.real (Set.Ioi (-u))) hmap
  change (P.map (fun x ↦ -x)).real (Set.Ioi (-u)) =
    P.real (Set.Ioi (-u)) at happ
  rw [MeasureTheory.map_measureReal_apply (by fun_prop) measurableSet_Ioi] at happ
  have hpre :
      (fun x : ℝ ↦ -x) ⁻¹' Set.Ioi (-u) = Set.Iio u := by
    ext x
    change (-u < -x) ↔ x < u
    constructor <;> intro h <;> linarith
  have hsym : Qlap (-u) = P.real (Set.Iio u) := by
    simpa [Qlap, P, hpre] using happ.symm
  have hzero : P.real (Set.Iic u \ Set.Iio u) = 0 := by
    letI : NullSingletonClass P := by
      dsimp [P]
      exact noAtoms_gaussianReal (by norm_num)
    have hdiff : Set.Iic u \ Set.Iio u = {u} := by
      ext x
      simp
    rw [hdiff, Measure.real, measure_singleton]
    simp
  have hioic : P.real (Set.Iio u) = P.real (Set.Iic u) :=
    MeasureTheory.measureReal_eq_measureReal_of_null_diff Set.Iio_subset_Iic_self hzero
  have hcompl :=
    MeasureTheory.measureReal_add_measureReal_compl
      (μ := P) (s := Set.Ioi u) measurableSet_Ioi
  rw [show (Set.Ioi u)ᶜ = Set.Iic u by ext x; simp] at hcompl
  rw [hsym, hioic]
  simpa [Qlap, P] using hcompl

private theorem Qlap_zero : Qlap 0 = 1 / 2 := by
  have h := Qlap_compl 0
  norm_num at h ⊢
  linarith

private theorem Qlap_antitone : Antitone Qlap := by
  intro a b hab
  unfold Qlap
  exact MeasureTheory.measureReal_mono (Set.Ioi_subset_Ioi hab)

private theorem Qlap_pos (u : ℝ) : 0 < Qlap u := by
  by_cases hu : 0 ≤ u
  · obtain ⟨c, hc, hmills⟩ := standardGaussian_mills_lower_bound
    have h := hmills u hu
    have hleft : 0 < c / (u + 1) * Real.exp (-u ^ 2 / 2) := by
      positivity
    exact hleft.trans_le h
  · have hle : Qlap 0 ≤ Qlap u :=
      Qlap_antitone (le_of_not_ge hu)
    exact Qlap_zero ▸ (by norm_num : (0 : ℝ) < 1 / 2) |>.trans_le hle

private theorem Qlap_upper (u : ℝ) (hu : 0 ≤ u) :
    Qlap u ≤ Real.exp (-u ^ 2 / 2) := by
  have hsub :
      HasSubgaussianMGF id 1 (gaussianReal 0 1) := by
    constructor
    · exact fun t ↦ integrable_exp_mul_gaussianReal t
    · intro t
      rw [mgf_id_gaussianReal]
      norm_num
  apply (MeasureTheory.measureReal_mono
    (show Set.Ioi u ⊆ {x : ℝ | u ≤ id x} by
      intro x hx
      change u < x at hx
      exact hx.le)).trans
  simpa using hsub.measure_ge_le hu

private theorem reciprocal_bad_lap
    (c : ℝ) (hc : 0 < c)
    (hmills : ∀ u : ℝ, 0 ≤ u →
      c / (u + 1) * Real.exp (-u ^ 2 / 2) ≤ Qlap u)
    (u : ℝ) (hu : 0 ≤ u) :
    1 / Qlap u - 1 ≤
      (u + 1) / c * Real.exp (u ^ 2 / 2) := by
  have hq := Qlap_pos u
  have hbpos :
      0 < c / (u + 1) * Real.exp (-u ^ 2 / 2) := by positivity
  have hinv :
      1 / Qlap u ≤
        1 / (c / (u + 1) * Real.exp (-u ^ 2 / 2)) :=
    one_div_le_one_div_of_le hbpos (hmills u hu)
  have heq :
      1 / (c / (u + 1) * Real.exp (-u ^ 2 / 2)) =
        (u + 1) / c * Real.exp (u ^ 2 / 2) := by
    rw [show -u ^ 2 / 2 = -(u ^ 2 / 2) by ring, Real.exp_neg]
    field_simp
  rw [heq] at hinv
  linarith

private theorem reciprocal_good_lap (u : ℝ) (hu : u < 0) :
    1 / Qlap u - 1 ≤
      2 * Real.exp (-(-u) ^ 2 / 2) := by
  have hq := Qlap_pos u
  have hqhalf : 1 / 2 ≤ Qlap u := by
    have := Qlap_antitone (show u ≤ 0 by linarith)
    simpa [Qlap_zero] using this
  have hcomp : 1 - Qlap u = Qlap (-u) := by
    linarith [Qlap_compl u]
  have hratio :
      1 / Qlap u - 1 = (1 - Qlap u) / Qlap u := by
    field_simp
  rw [hratio, hcomp]
  have hqnonneg : 0 ≤ Qlap (-u) := (Qlap_pos (-u)).le
  calc
    Qlap (-u) / Qlap u ≤ Qlap (-u) / (1 / 2) := by
      exact div_le_div_of_nonneg_left hqnonneg (by norm_num) hqhalf
    _ = 2 * Qlap (-u) := by ring
    _ ≤ 2 * Real.exp (-(-u) ^ 2 / 2) := by
      gcongr
      exact Qlap_upper (-u) (by linarith)

private noncomputable def Jlap (u : ℝ) : ENNReal :=
  ∫⁻ l : ℝ in Set.Ioi 0,
    ENNReal.ofReal (l * Real.exp (l * u - l ^ 2 / 2))

private theorem interval_lower_lap
    (u p q A : ℝ) (hpq : p ≤ q) (hp : 0 ≤ p)
    (hpoint : ∀ l ∈ Set.Ioc p q,
      A * l ≤ l * Real.exp (l * u - l ^ 2 / 2))
    (hA : 0 ≤ A) :
    ENNReal.ofReal (A * (q ^ 2 - p ^ 2) / 2) ≤ Jlap u := by
  have hcont : Continuous
      (fun l : ℝ ↦ l * Real.exp (l * u - l ^ 2 / 2)) := by fun_prop
  have hint : IntegrableOn
      (fun l : ℝ ↦ l * Real.exp (l * u - l ^ 2 / 2))
      (Set.Ioc p q) :=
    hcont.integrableOn_Ioc
  have hbase : IntegrableOn (fun l : ℝ ↦ A * l) (Set.Ioc p q) :=
    (continuous_const.mul continuous_id).integrableOn_Ioc
  have hmono :
      (∫ l : ℝ in Set.Ioc p q, A * l) ≤
        ∫ l : ℝ in Set.Ioc p q,
          l * Real.exp (l * u - l ^ 2 / 2) := by
    apply integral_mono_ae hbase hint
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
    exact hpoint l hl
  have hcalc :
      (∫ l : ℝ in Set.Ioc p q, A * l) =
        A * (q ^ 2 - p ^ 2) / 2 := by
    change (∫ l : ℝ, A * l ∂(volume.restrict (Set.Ioc p q))) =
      A * (q ^ 2 - p ^ 2) / 2
    rw [integral_const_mul]
    have hid : (∫ l : ℝ in Set.Ioc p q, l) =
        (q ^ 2 - p ^ 2) / 2 := by
      rw [← intervalIntegral.integral_of_le hpq, integral_id]
    rw [hid]
    ring
  rw [← hcalc]
  calc
    ENNReal.ofReal (∫ l : ℝ in Set.Ioc p q, A * l) ≤
        ENNReal.ofReal (∫ l : ℝ in Set.Ioc p q,
          l * Real.exp (l * u - l ^ 2 / 2)) :=
      ENNReal.ofReal_le_ofReal hmono
    _ = ∫⁻ l : ℝ in Set.Ioc p q,
          ENNReal.ofReal (l * Real.exp (l * u - l ^ 2 / 2)) := by
      apply ofReal_integral_eq_lintegral_ofReal hint
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with l hl
      exact mul_nonneg (le_trans hp hl.1.le) (Real.exp_nonneg _)
    _ ≤ Jlap u := by
      exact lintegral_mono_set (fun l hl ↦ lt_of_le_of_lt hp hl.1)

private theorem exp_sq_decay_lap (v : ℝ) (hv : 0 ≤ v) :
    Real.exp (-v ^ 2 / 2) ≤ 8 / (v + 1) ^ 2 := by
  by_cases hv1 : v ≤ 1
  · have he : Real.exp (-v ^ 2 / 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg v])
    have hs : (v + 1) ^ 2 ≤ 4 := by nlinarith
    have hp : 0 < (v + 1) ^ 2 := by positivity
    calc
      Real.exp (-v ^ 2 / 2) ≤ 1 := he
      _ ≤ 8 / (v + 1) ^ 2 := by
        rw [le_div_iff₀ hp]
        linarith
  · have hv1' : 1 ≤ v := le_of_not_ge hv1
    have hs : (v + 1) ^ 2 ≤ 4 * v ^ 2 := by nlinarith
    have hy : 0 ≤ v ^ 2 / 2 := by positivity
    have hm := Real.mul_exp_neg_le_exp_neg_one (v ^ 2 / 2)
    have hve : v ^ 2 * Real.exp (-v ^ 2 / 2) ≤ 2 := by
      calc
        v ^ 2 * Real.exp (-v ^ 2 / 2) =
            2 * ((v ^ 2 / 2) * Real.exp (-(v ^ 2 / 2))) := by ring
        _ ≤ 2 * Real.exp (-1) := by gcongr
        _ ≤ 2 := by
          exact mul_le_of_le_one_right (by norm_num)
            (Real.exp_le_one_iff.mpr (by norm_num))
    have hp : 0 < (v + 1) ^ 2 := by positivity
    rw [le_div_iff₀ hp]
    calc
      Real.exp (-v ^ 2 / 2) * (v + 1) ^ 2 ≤
          Real.exp (-v ^ 2 / 2) * (4 * v ^ 2) := by
        gcongr
      _ = 4 * (v ^ 2 * Real.exp (-v ^ 2 / 2)) := by ring
      _ ≤ 8 := by linarith

theorem check_laplace_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ENNReal.ofReal (1 / Qlap u - 1) ≤ ENNReal.ofReal C * Jlap u := by
  obtain ⟨c, hc, hmills⟩ := standardGaussian_mills_lower_bound
  let C : ℝ := 4 * Real.exp 1 / c + 32 * Real.exp 2
  have hC : 0 < C := by positivity
  refine ⟨C, hC, ?_⟩
  intro u
  by_cases hu : 0 ≤ u
  · by_cases hu1 : 1 ≤ u
    · have hJ :
          ENNReal.ofReal
              (Real.exp (u ^ 2 / 2 - 1 / 2) *
                ((u + 1) ^ 2 - u ^ 2) / 2) ≤
            Jlap u := by
        apply interval_lower_lap u u (u + 1)
          (Real.exp (u ^ 2 / 2 - 1 / 2)) (by linarith) hu
        · intro l hl
          have hlu : u ≤ l := hl.1.le
          have hlu1 : l ≤ u + 1 := hl.2
          have hexp :
              Real.exp (u ^ 2 / 2 - 1 / 2) ≤
                Real.exp (l * u - l ^ 2 / 2) := by
            apply Real.exp_le_exp.mpr
            nlinarith [sq_nonneg (l - u)]
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hexp (hu.trans hlu))
        · positivity
      have hratio := reciprocal_bad_lap c hc hmills u hu
      have hreal :
          1 / Qlap u - 1 ≤
            (4 * Real.exp 1 / c) *
              (Real.exp (u ^ 2 / 2 - 1 / 2) *
                ((u + 1) ^ 2 - u ^ 2) / 2) := by
        calc
          1 / Qlap u - 1 ≤ (u + 1) / c * Real.exp (u ^ 2 / 2) := hratio
          _ ≤ (4 * Real.exp 1 / c) *
              (Real.exp (u ^ 2 / 2 - 1 / 2) *
                ((u + 1) ^ 2 - u ^ 2) / 2) := by
            have he :
                Real.exp (u ^ 2 / 2) ≤
                  Real.exp 1 * Real.exp (u ^ 2 / 2 - 1 / 2) := by
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              linarith
            have hpoly : u + 1 ≤
                4 * (((u + 1) ^ 2 - u ^ 2) / 2) := by
              nlinarith [sq_nonneg u]
            calc
              (u + 1) / c * Real.exp (u ^ 2 / 2) ≤
                  (u + 1) / c *
                    (Real.exp 1 * Real.exp (u ^ 2 / 2 - 1 / 2)) := by
                gcongr
              _ ≤ (4 * Real.exp 1 / c) *
                    (Real.exp (u ^ 2 / 2 - 1 / 2) *
                      ((u + 1) ^ 2 - u ^ 2) / 2) := by
                have hc0 : 0 ≤ 1 / c := by positivity
                have he0 : 0 < Real.exp 1 := Real.exp_pos 1
                have heu0 : 0 < Real.exp (u ^ 2 / 2 - 1 / 2) :=
                  Real.exp_pos _
                calc
                  (u + 1) / c *
                      (Real.exp 1 * Real.exp (u ^ 2 / 2 - 1 / 2)) =
                    (1 / c * Real.exp 1 *
                      Real.exp (u ^ 2 / 2 - 1 / 2)) * (u + 1) := by ring
                  _ ≤ (1 / c * Real.exp 1 *
                      Real.exp (u ^ 2 / 2 - 1 / 2)) *
                      (4 * (((u + 1) ^ 2 - u ^ 2) / 2)) := by
                    exact mul_le_mul_of_nonneg_left hpoly (by positivity)
                  _ = _ := by ring
      calc
        ENNReal.ofReal (1 / Qlap u - 1) ≤
            ENNReal.ofReal ((4 * Real.exp 1 / c) *
              (Real.exp (u ^ 2 / 2 - 1 / 2) *
                ((u + 1) ^ 2 - u ^ 2) / 2)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (4 * Real.exp 1 / c) *
            ENNReal.ofReal
              (Real.exp (u ^ 2 / 2 - 1 / 2) *
                ((u + 1) ^ 2 - u ^ 2) / 2) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (4 * Real.exp 1 / c) * Jlap u := by gcongr
        _ ≤ ENNReal.ofReal C * Jlap u := by
          gcongr
          dsimp [C]
          exact le_add_of_nonneg_right (by positivity)
    · have hu1' : u < 1 := lt_of_not_ge hu1
      have hJ :
          ENNReal.ofReal (Real.exp (-1 / 2) / 2) ≤ Jlap u := by
        have := interval_lower_lap u 0 1 (Real.exp (-1 / 2))
          (by norm_num) (by norm_num) (by
            intro l hl
            have hl0 : 0 ≤ l := hl.1.le
            have hl1 : l ≤ 1 := hl.2
            have hexp :
                Real.exp (-1 / 2) ≤ Real.exp (l * u - l ^ 2 / 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith
            simpa [mul_comm] using
              (mul_le_mul_of_nonneg_left hexp hl0)) (by positivity)
        norm_num at this ⊢
        simpa [div_eq_mul_inv, mul_assoc] using this
      have hratio := reciprocal_bad_lap c hc hmills u hu
      have hreal :
          1 / Qlap u - 1 ≤
            (4 * Real.exp 1 / c) * (Real.exp (-1 / 2) / 2) := by
        calc
          1 / Qlap u - 1 ≤ (u + 1) / c * Real.exp (u ^ 2 / 2) := hratio
          _ ≤ (4 * Real.exp 1 / c) * (Real.exp (-1 / 2) / 2) := by
            have he : Real.exp (u ^ 2 / 2) ≤ Real.exp (1 / 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith
            have hc' : 0 < c := hc
            calc
              (u + 1) / c * Real.exp (u ^ 2 / 2) ≤
                  2 / c * Real.exp (1 / 2) := by gcongr <;> linarith
              _ = (4 * Real.exp 1 / c) *
                    (Real.exp (-1 / 2) / 2) := by
                have heq : Real.exp (1 / 2) =
                    Real.exp 1 * Real.exp (-1 / 2) := by
                  rw [← Real.exp_add]
                  norm_num
                rw [heq]
                ring
      calc
        ENNReal.ofReal (1 / Qlap u - 1) ≤
            ENNReal.ofReal ((4 * Real.exp 1 / c) *
              (Real.exp (-1 / 2) / 2)) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (4 * Real.exp 1 / c) *
            ENNReal.ofReal (Real.exp (-1 / 2) / 2) := by
          rw [ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (4 * Real.exp 1 / c) * Jlap u := by gcongr
        _ ≤ ENNReal.ofReal C * Jlap u := by
          gcongr
          dsimp [C]
          exact le_add_of_nonneg_right (by positivity)
  · have hu' : u < 0 := lt_of_not_ge hu
    let v := -u
    have hv : 0 ≤ v := by dsimp [v]; linarith
    let b := 1 / (v + 1)
    have hb : 0 < b := by dsimp [b]; positivity
    have hJ :
        ENNReal.ofReal (Real.exp (-3 / 2) * b ^ 2 / 2) ≤ Jlap u := by
      have := interval_lower_lap u 0 b (Real.exp (-3 / 2))
        hb.le (by norm_num) (by
          intro l hl
          have hl0 : 0 ≤ l := hl.1.le
          have hlb : l ≤ b := hl.2
          have hlv : l * v ≤ 1 := by
            have hvp : 0 < v + 1 := by positivity
            have hmul : l * (v + 1) ≤ 1 := by
              apply (le_div_iff₀ hvp).mp
              simpa [b] using hlb
            nlinarith
          have hlone : l ≤ 1 := by
            calc l ≤ b := hlb
                 _ ≤ 1 := by
                  apply (div_le_iff₀ (show (0 : ℝ) < v + 1 by positivity)).mpr
                  try dsimp only [b]
                  nlinarith
          have hexp :
              Real.exp (-3 / 2) ≤ Real.exp (l * u - l ^ 2 / 2) := by
            apply Real.exp_le_exp.mpr
            dsimp [v] at hlv
            nlinarith [sq_nonneg l]
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left hexp hl0)) (by positivity)
      norm_num at this ⊢
      simpa using this
    have hratio := reciprocal_good_lap u hu'
    have hdecay := exp_sq_decay_lap v hv
    have hreal :
        1 / Qlap u - 1 ≤
          (32 * Real.exp 2) * (Real.exp (-3 / 2) * b ^ 2 / 2) := by
      calc
        1 / Qlap u - 1 ≤ 2 * Real.exp (-(-u) ^ 2 / 2) := hratio
        _ = 2 * Real.exp (-v ^ 2 / 2) := by rfl
        _ ≤ 16 / (v + 1) ^ 2 := by
          exact (mul_le_mul_of_nonneg_left hdecay
            (show (0 : ℝ) ≤ 2 by norm_num)).trans_eq (by ring)
        _ ≤ (32 * Real.exp 2) *
            (Real.exp (-3 / 2) * b ^ 2 / 2) := by
          have he : 1 ≤ Real.exp 2 * Real.exp (-3 / 2) := by
            rw [← Real.exp_add]
            exact Real.one_le_exp (by norm_num)
          have hb2 : 16 / (v + 1) ^ 2 = 16 * b ^ 2 := by
            dsimp [b]
            rw [one_div_pow]
            ring
          rw [hb2]
          have hb20 : 0 ≤ b ^ 2 := sq_nonneg b
          calc
            16 * b ^ 2 ≤
                16 * (Real.exp 2 * Real.exp (-3 / 2)) * b ^ 2 := by
              have h16 : (0 : ℝ) ≤ 16 := by norm_num
              have hfactor :
                  16 ≤ 16 * (Real.exp 2 * Real.exp (-3 / 2)) :=
                by simpa using mul_le_mul_of_nonneg_left he h16
              exact mul_le_mul_of_nonneg_right hfactor hb20
            _ = _ := by ring
    calc
      ENNReal.ofReal (1 / Qlap u - 1) ≤
          ENNReal.ofReal ((32 * Real.exp 2) *
            (Real.exp (-3 / 2) * b ^ 2 / 2)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (32 * Real.exp 2) *
          ENNReal.ofReal (Real.exp (-3 / 2) * b ^ 2 / 2) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (32 * Real.exp 2) * Jlap u := by gcongr
      _ ≤ ENNReal.ofReal C * Jlap u := by
        gcongr
        dsimp [C]
        exact le_add_of_nonneg_left (by positivity)

theorem gaussian_reciprocal_tail_laplace_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ENNReal.ofReal
          (1 / (gaussianReal 0 1).real (Set.Ioi u) - 1) ≤
        ENNReal.ofReal C *
          (∫⁻ l : ℝ in Set.Ioi 0,
            ENNReal.ofReal
              (l * Real.exp (l * u - l ^ 2 / 2))) := by
  simpa [Qlap, Jlap] using check_laplace_envelope

end BanditAlgorithm

open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ,
      ENNReal.ofReal
          (1 / (gaussianReal 0 1).real (Set.Ioi u) - 1) ≤
        ENNReal.ofReal C *
          (∫⁻ l : ℝ in Set.Ioi 0,
            ENNReal.ofReal
              (l * Real.exp (l * u - l ^ 2 / 2))) :=
  gaussian_reciprocal_tail_laplace_envelope
