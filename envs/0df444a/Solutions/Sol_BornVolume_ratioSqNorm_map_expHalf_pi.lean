-- Prove2me | solution 1 for BornVolume.ratioSqNorm_map_expHalf_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:55:33.223845+00:00
-- url     : https://prove2.me/submissions/d5ac566f-0b9e-4fcd-8e50-9718bcf8c363

module
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Matrix.Block
public import Definitions.Def_BornVolumeLean_Volume_MomentMarginalUniform
public import Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
public import Definitions.Def_BornVolumeLean_Volume_MomentRatioUniformN
public import Theorems.Thm_BornVolume_lintegral_radial_moment
public import Theorems.Thm_BornVolume_psiFDerivN_det
public import Theorems.Thm_BornVolume_hasFDerivAt_PsiN
public import Theorems.Thm_BornVolume_measurableSet_domainN
public import Theorems.Thm_BornVolume_measurableSet_posQuadrant
public import Theorems.Thm_BornVolume_PsiN_sum
public import Theorems.Thm_BornVolume_injOn_PsiN
public import Theorems.Thm_BornVolume_image_PsiN
public import Theorems.Thm_BornVolume_measurable_dExp
public import Theorems.Thm_BornVolume_expHalf_eq_withDensity_dExp
public import Theorems.Thm_MeasureTheory_pi_withDensity


set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Real Set
open scoped ENNReal
open BornVolume
variable {M : ℕ}
namespace BornVolume
theorem _root_.solution :
    Measure.map ratioN (Measure.pi (fun _ : Fin (M + 1) => expHalf))
      = (Nat.factorial M : ℝ≥0∞) • volume.restrict openSimplexFree := by
  have hsum_meas : Measurable (fun s : Fin (M + 1) → ℝ => ∑ i, s i) :=
    Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)
  have hratio_meas : Measurable (ratioN (M := M)) :=
    measurable_pi_iff.mpr (fun k => (measurable_pi_apply _).div hsum_meas)
  have hprod_meas : Measurable (fun x : Fin (M + 1) → ℝ => ∏ i, dExp (x i)) :=
    Finset.measurable_prod _ fun i _ => measurable_dExp.comp (measurable_pi_apply i)
  -- σ-finite of `expHalf` (probability measure) for the pi-withDensity bridge.
  have hsf : SigmaFinite ((volume : Measure ℝ).withDensity dExp) := by
    rw [← expHalf_eq_withDensity_dExp]; infer_instance
  -- `pi expHalf = volume.withDensity (∏ dExp)` (`pi_withDensity` and `volume_pi`).
  have hpiexp : (Measure.pi (fun _ : Fin (M + 1) => expHalf))
      = (volume : Measure (Fin (M + 1) → ℝ)).withDensity (fun x => ∏ i, dExp (x i)) := by
    simp_rw [expHalf_eq_withDensity_dExp]
    rw [MeasureTheory.pi_withDensity (fun _ : Fin (M + 1) => volume) (fun _ => dExp)
      (fun _ => measurable_dExp), volume_pi]
  refine Measure.ext_of_lintegral _ (fun g hg => ?_)
  -- Step 1-3: push through `ratioN`, expose the joint density.
  rw [lintegral_map hg hratio_meas, hpiexp]
  rw [lintegral_withDensity_eq_lintegral_mul (f := fun x => ∏ i, dExp (x i)) _ hprod_meas
    (show Measurable (fun s : Fin (M + 1) → ℝ => g (ratioN s)) from hg.comp hratio_meas)]
  -- Fold the `Pi.mul` form into a single `fun s => _ * _` (so `set F` matches).
  show (∫⁻ s, (fun s => (∏ i, dExp (s i)) * g (ratioN s)) s ∂volume) = _
  -- The post-density integrand.
  set F : (Fin (M + 1) → ℝ) → ℝ≥0∞ :=
    fun s => (∏ i, dExp (s i)) * g (ratioN s) with hF
  -- Step 4: F is supported on the positive quadrant.
  have hFsupp : F = (posQuadrant (M := M)).indicator F := by
    classical
    funext s
    rw [Set.indicator_apply]
    by_cases hs : s ∈ posQuadrant
    · rw [if_pos hs]
    · rw [if_neg hs, hF]
      simp only [posQuadrant, Set.mem_ofPred_eq, not_forall, not_lt] at hs
      obtain ⟨i, hi⟩ := hs
      refine mul_eq_zero.mpr (Or.inl ?_)
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [dExp, if_neg (not_lt.mpr hi), ENNReal.ofReal_zero]
  -- Pointwise integrand after the substitution, on `domainN`.
  have hcongr : ∀ y ∈ domainN (M := M),
      ENNReal.ofReal |(psiFDerivN y).det| * F (PsiN y)
        = ENNReal.ofReal ((1 / 2) ^ (M + 1) * (y (Fin.last M)) ^ M
            * Real.exp (-(y (Fin.last M)) / 2)) * g (fun k => y (Fin.castSucc k)) := by
    intro y hy
    obtain ⟨ht, hsum, hS⟩ := hy
    -- |det| = S^M (S = y last > 0).
    rw [psiFDerivN_det, abs_of_nonneg (pow_nonneg hS.le M)]
    -- all coordinates of `PsiN y` are positive.
    have hposPsi : ∀ i, 0 < PsiN y i := by
      intro i
      induction i using Fin.lastCases with
      | last => simp only [PsiN, Fin.lastCases_last]; exact mul_pos (by linarith) hS
      | cast k => simp only [PsiN, Fin.lastCases_castSucc]; exact mul_pos (ht k) hS
    -- ratioN (PsiN y) = y ∘ castSucc.
    have hratioPsi : ratioN (PsiN y) = fun k => y (Fin.castSucc k) := by
      funext k; rw [ratioN, PsiN_sum]
      simp only [PsiN, Fin.lastCases_castSucc]
      rw [mul_div_assoc, div_self (ne_of_gt hS), mul_one]
    -- density product collapse: ∏ dExp(PsiN y) = ofReal ((1/2)^(M+1) exp(-S/2)).
    have hprodPsi : (∏ i, dExp (PsiN y i))
        = ENNReal.ofReal ((1 / 2) ^ (M + 1) * Real.exp (-(y (Fin.last M)) / 2)) := by
      have hpos : ∀ i, dExp (PsiN y i) = ENNReal.ofReal ((1 / 2) * Real.exp (-(PsiN y i) / 2)) :=
        fun i => by rw [dExp, if_pos (hposPsi i)]
      simp_rw [hpos]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← Real.exp_sum]
      congr 2
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_neg_distrib, PsiN_sum]
    show ENNReal.ofReal (y (Fin.last M) ^ M) * ((∏ i, dExp (PsiN y i)) * g (ratioN (PsiN y))) = _
    rw [hprodPsi, hratioPsi, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    ring
  -- Step 5: change of variables; Step 4 restricts to posQuadrant = PsiN '' domainN.
  rw [hFsupp, lintegral_indicator measurableSet_posQuadrant, ← image_PsiN,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_domainN
      (fun y _ => (hasFDerivAt_PsiN y).hasFDerivWithinAt) injOn_PsiN F,
    setLIntegral_congr_fun measurableSet_domainN hcongr]
  -- Reindex `domainN` as a preimage of `Ioi 0 ×ˢ openSimplexFree` under the
  -- measure-preserving `piFinSuccAbove (last M)`, then Tonelli + radial collapse.
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (M + 1) => ℝ) (Fin.last M) with he_def
  have he : ∀ y, e y = (y (Fin.last M), fun k => y (Fin.castSucc k)) := by
    intro y; simp [he_def, MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]
  have hdom : domainN (M := M) = e ⁻¹' (Set.Ioi 0 ×ˢ openSimplexFree) := by
    ext y
    simp only [domainN, openSimplexFree, Set.mem_preimage, he, Set.mem_prod, Set.mem_Ioi,
      Set.mem_ofPred_eq]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h3, h1, h2⟩, fun ⟨h3, h1, h2⟩ => ⟨h1, h2, h3⟩⟩
  -- Volume MP for `e`.
  have hmp : MeasurePreserving e (volume : Measure (Fin (M + 1) → ℝ))
      (volume.prod (volume : Measure (Fin M → ℝ))) := by
    have h := measurePreserving_piFinSuccAbove (fun _ : Fin (M + 1) => (volume : Measure ℝ))
      (Fin.last M)
    rwa [show (Measure.pi (fun _ : Fin (M + 1) => (volume : Measure ℝ)))
          = (volume : Measure (Fin (M + 1) → ℝ)) from volume_pi,
      show (Measure.pi (fun _ : Fin M => (volume : Measure ℝ)))
          = (volume : Measure (Fin M → ℝ)) from volume_pi] at h
  -- Express the integrand as `F' ∘ e` with `F' (S,t) = ofReal(...S^M...) · g t`.
  set F' : ℝ × (Fin M → ℝ) → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((1 / 2) ^ (M + 1) * p.1 ^ M * Real.exp (-p.1 / 2)) * g p.2 with hF'
  rw [hdom,
    show (fun x : Fin (M + 1) → ℝ =>
        ENNReal.ofReal ((1 / 2) ^ (M + 1) * x (Fin.last M) ^ M * Real.exp (-x (Fin.last M) / 2))
          * g (fun k => x (Fin.castSucc k)))
      = fun x => F' (e x) from by funext x; rw [hF', he],
    hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding F']
  -- `setLIntegral_prod` (Tonelli): outer over `Ioi 0`, inner over `openSimplexFree`.
  rw [setLIntegral_prod _ (by refine Measurable.aemeasurable ?_; rw [hF']; fun_prop)]
  -- Inner integral pulls out the `S`-factor; outer is the radial moment (`lintegral_radial_moment`).
  simp only [hF']
  -- RHS: M! • vol.restrict → (M! : ℝ≥0∞) * ∫⁻_{simplex} g.
  rw [lintegral_smul_measure]
  -- Inner integral: pull the (constant-in-`y`) radial factor out of `∫⁻_{simplex}`.
  have hinner : ∀ S : ℝ,
      (∫⁻ y in openSimplexFree, ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2))
          * g y)
        = ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2))
            * ∫⁻ y in openSimplexFree, g y := by
    intro S; rw [lintegral_const_mul _ hg]
  simp_rw [hinner]
  -- Outer: ∫⁻_{S>0} ofReal((1/2)^{M+1} S^M e^{-S/2}) dS · (∫⁻ g) = M! · (∫⁻ g).
  rw [lintegral_mul_const _ (by fun_prop)]
  -- The radial factor evaluates to `M!`.
  have hradial : (∫⁻ S in Set.Ioi (0 : ℝ),
        ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2)))
      = (Nat.factorial M : ℝ≥0∞) := by
    -- Factor out the constant `(1/2)^{M+1}`, apply `lintegral_radial_moment`, then `(1/2)^{M+1}·2^{M+1} = 1`.
    have hfac : ∀ S : ℝ, ENNReal.ofReal ((1 / 2) ^ (M + 1) * S ^ M * Real.exp (-S / 2))
        = ENNReal.ofReal ((1 / 2) ^ (M + 1)) * ENNReal.ofReal (S ^ M * Real.exp (-S / 2)) := by
      intro S
      rw [mul_assoc, ENNReal.ofReal_mul (by positivity)]
    simp_rw [hfac]
    rw [lintegral_const_mul _ (by fun_prop), lintegral_radial_moment,
      ← ENNReal.ofReal_mul (by positivity)]
    rw [show (1 / 2 : ℝ) ^ (M + 1) * (2 ^ (M + 1) * (Nat.factorial M : ℝ))
          = (Nat.factorial M : ℝ) from by
        rw [show (1 / 2 : ℝ) ^ (M + 1) = (2 ^ (M + 1))⁻¹ by rw [one_div, inv_pow]]
        field_simp,
      ENNReal.ofReal_natCast]
  rw [hradial, smul_eq_mul]
end BornVolume
