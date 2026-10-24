-- Prove2me | solution 1 for Cohen2019.Robust.thm1_binary_case_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T06:35:06.156275+00:00
-- url     : https://prove2.me/submissions/1d909fed-2a3a-4170-819c-a4e80b27df66

import Mathlib
import Definitions.Def_Cohen2019_Robust_Model
import Theorems.Thm_Cohen2019_Robust_certified_radius

set_option autoImplicit false

open MeasureTheory ProbabilityTheory in
theorem co87_phi_strictMono : StrictMono Cohen2019.Robust.Phi := by
  intro a b hab
  unfold Cohen2019.Robust.Phi
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hpos : (gaussianReal 0 1) (Set.Ioc a b) ≠ 0 := by
    intro h
    have h2 := gaussianReal_absolutelyContinuous' (0 : ℝ) hv h
    rw [Real.volume_Ioc, ENNReal.ofReal_eq_zero] at h2
    linarith
  have hm := (cdf (gaussianReal 0 1)).measure_Ioc a b
  rw [measure_cdf] at hm
  rw [hm] at hpos
  have : ¬ (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ 0) := by
    intro hle; exact hpos (ENNReal.ofReal_eq_zero.mpr hle)
  linarith

open MeasureTheory ProbabilityTheory in
theorem co87_phi_continuous : Continuous Cohen2019.Robust.Phi := by
  have hfun : Cohen2019.Robust.Phi = fun t => cdf (gaussianReal 0 1) t := rfl
  rw [hfun, continuous_iff_continuousAt]
  intro a
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [(monotone_cdf (gaussianReal 0 1)).continuousAt_iff_leftLim_eq_rightLim,
    StieltjesFunction.rightLim_eq]
  have hs := (cdf (gaussianReal 0 1)).measure_singleton a
  rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
  have hle := (monotone_cdf (gaussianReal 0 1)).leftLim_le (le_refl a)
  linarith

open MeasureTheory ProbabilityTheory Filter in
theorem co87_phi_inv {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.Phi (Cohen2019.Robust.PhiInvReal q) = q := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot (gaussianReal 0 1)).eventually
    (Iio_mem_nhds hq0)).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop (gaussianReal 0 1)).eventually
    (Ioi_mem_nhds hq1)).exists
  have hmem : q ∈ Set.Icc (Cohen2019.Robust.Phi a) (Cohen2019.Robust.Phi b) :=
    ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ a b co87_phi_continuous hmem
  have hS : {s : ℝ | q ≤ Cohen2019.Robust.Phi s} = Set.Ici t := by
    ext s
    simp only [Set.mem_Ici]
    rw [← ht]
    exact co87_phi_strictMono.le_iff_le
  unfold Cohen2019.Robust.PhiInvReal
  rw [hS, csInf_Ici, ht]

open MeasureTheory ProbabilityTheory in
theorem co87_phi_def (t : ℝ) :
    (gaussianReal 0 1).real (Set.Iic t) = Cohen2019.Robust.Phi t := by
  rw [Cohen2019.Robust.Phi, cdf_eq_real]

open MeasureTheory ProbabilityTheory in
theorem co87_phi_neg (t : ℝ) : Cohen2019.Robust.Phi (-t) = 1 - Cohen2019.Robust.Phi t := by
  have h := gaussianReal_map_neg (μ := (0:ℝ)) (v := 1)
  rw [neg_zero] at h
  rw [← co87_phi_def, ← co87_phi_def]
  have h1 : (gaussianReal 0 1).real (Set.Iic (-t)) = (gaussianReal 0 1).real (Set.Ici t) := by
    conv_lhs => rw [← h]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext y
    simp
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [h1, ← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic]

theorem co87_phiInv_one_sub {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Cohen2019.Robust.PhiInvReal (1 - q) = - Cohen2019.Robust.PhiInvReal q := by
  apply co87_phi_strictMono.injective
  rw [co87_phi_inv (by linarith) (by linarith), co87_phi_neg, co87_phi_inv hq0 hq1]

/-! ### Product Gaussian density (copied from our accepted sibling bd7edd52) -/

section dens

open MeasureTheory ProbabilityTheory

variable {N : ℕ}

noncomputable def co87_gw (y : Fin N → ℝ) : ℝ := Real.exp (-(∑ i, y i ^ 2) / 2)

open MeasureTheory ProbabilityTheory Cohen2019.Robust

theorem solution {d : ℕ} {Y : Type*}
    (f : EuclideanSpace ℝ (Fin d) → PMF Y) (hf : ∀ c : Y, Measurable fun z => f z c)
    (σ : ℝ) (hσ : 0 < σ) (x : EuclideanSpace ℝ (Fin d)) (cA cB : Y) (hAB : cA ≠ cB)
    (hY : ∀ c : Y, c = cA ∨ c = cB) (pA : ℝ) (hpA0 : 1 / 2 < pA) (hpA1 : pA ≤ 1)
    (hA : pA ≤ classProb f σ x cA) :
    ∀ δ : EuclideanSpace ℝ (Fin d), ((‖δ‖ : ℝ) : EReal) < ((σ : ℝ) : EReal) * PhiInv pA →
      IsSmoothedPrediction f σ (x + δ) cA := by
  classical
  -- the two class probabilities sum to one
  have hsum1 : ∀ z, (f z cA).toReal + (f z cB).toReal = 1 := by
    intro z
    have h := (f z).tsum_coe
    have hsupp : ∀ c ∉ ({cA, cB} : Finset Y), (f z) c = 0 := by
      intro c hc
      exfalso; apply hc
      rcases hY c with rfl | rfl <;> simp
    rw [tsum_eq_sum hsupp, Finset.sum_pair hAB] at h
    rw [← ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _), h]
    simp
  have hmeas : ∀ c : Y, Measurable fun u : EuclideanSpace ℝ (Fin d) =>
      (f (x + σ • u) c).toReal := fun c =>
    ENNReal.measurable_toReal.comp ((hf c).comp (by fun_prop))
  have hbd : ∀ c : Y, ∀ u, (f u c).toReal ≤ 1 := fun c u => by
    have := PMF.coe_le_one (f u) c
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have hint : ∀ c : Y, Integrable (fun u : EuclideanSpace ℝ (Fin d) => (f (x + σ • u) c).toReal)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := fun c =>
    Integrable.of_bound (hmeas c).aestronglyMeasurable 1
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs, abs_le]; constructor
        · linarith [ENNReal.toReal_nonneg (a := f (x + σ • u) c)]
        · exact hbd c _)
  have hcp : classProb f σ x cA + classProb f σ x cB = 1 := by
    simp only [classProb, RandomGradFree.Shared.smoothing]
    rw [← integral_add (hint cA) (hint cB)]
    simp [hsum1]
  set pB := 1 - pA with hpB
  have hB : ∀ c : Y, c ≠ cA → classProb f σ x c ≤ pB := by
    intro c hc
    rcases hY c with rfl | rfl
    · exact absurd rfl hc
    · linarith
  have hcr := certified_radius f hf σ hσ x cA pA pB (by linarith) hpA1 (by linarith)
    (by linarith) hA (by linarith) hB
  -- the binary radius σ Φ⁻¹(pA) equals the certified radius (σ/2)(Φ⁻¹(pA) − Φ⁻¹(1 − pA))
  have hrad : ((σ : ℝ) : EReal) * PhiInv pA = certRadius σ pA pB := by
    unfold certRadius PhiInv
    rcases hpA1.lt_or_eq with hlt | heq
    · have h0 : ¬ pA ≤ 0 := by linarith
      have h1 : ¬ 1 ≤ pA := by linarith
      have h0' : ¬ pB ≤ 0 := by rw [hpB]; linarith
      have h1' : ¬ 1 ≤ pB := by rw [hpB]; linarith
      rw [if_neg h0, if_neg h1, if_neg h0', if_neg h1', hpB,
        co87_phiInv_one_sub (by linarith) hlt]
      rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul]
      congr 1; ring
    · subst heq
      have hB0 : pB = 0 := by rw [hpB]; ring
      rw [hB0]
      simp only [le_refl, if_true, show ¬ (1 : ℝ) ≤ 0 by norm_num, if_false]
      rw [EReal.top_sub_bot, EReal.coe_mul_top_of_pos hσ,
        EReal.coe_mul_top_of_pos (by linarith : (0 : ℝ) < σ / 2)]
  intro δ hδ
  exact hcr δ (hrad ▸ hδ)
