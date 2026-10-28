-- Prove2me | solution 1 for FiniteEnergyPlane.rescale_isFiniteEnergyCurve
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T18:09:46.630135+00:00
-- url     : https://prove2.me/submissions/fb375759-96da-4501-a73b-5fa32160cf80

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn
import Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_add_smul
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Domain rescaling and `ℝ`-translation of finite-energy curves. -/
theorem rescale_isFiniteEnergyCurve_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J)
    (U : Set ℂ) (hU : IsOpen U) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (z₀ : ℂ) (s : ℝ)
    (hs : 0 < s) (c : ℝ) (hc : 0 < c) :
    IsFiniteEnergyCurve H J {w | z₀ + s • w ∈ U} (fun w => c • u (z₀ + s • w)) ∧
      (∀ w, z₀ + s • w ∈ U →
        aCoord H (c • u (z₀ + s • w)) = aCoord H (u (z₀ + s • w)) + Real.log c / 2) ∧
      (∀ w, z₀ + s • w ∈ U →
        gradNorm H (fun w => c • u (z₀ + s • w)) w = s * gradNorm H u (z₀ + s • w)) ∧
      ∀ A ⊆ U, MeasurableSet A →
        energy H {w | z₀ + s • w ∈ A} (fun w => c • u (z₀ + s • w)) = energy H A u ∧
          dlambdaEnergy H {w | z₀ + s • w ∈ A} (fun w => c • u (z₀ + s • w)) =
            dlambdaEnergy H A u := by
  obtain ⟨-, hprojs, haCs, -, hJs⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨husm, hune, huhol, hufin⟩ := hu
  set κ : ℝ := Real.log c / 2 with hκ
  -- scaling identities in the symplectization
  have hsc : ∀ y : V n, y ≠ 0 → scaleToS H (c • y) = scaleToS H y / c ∧ 0 < scaleToS H y := by
    intro y hy
    obtain ⟨r, ⟨hr0, hr1⟩, hru⟩ := hH.2.1 y hy
    have e1 : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := ⟨r, hr0, hr1⟩
    have e2 : ∃ r : ℝ, 0 < r ∧ H (r • (c • y)) = 1 :=
      ⟨r / c, div_pos hr0 hc, by rw [smul_smul, div_mul_cancel₀ _ hc.ne']; exact hr1⟩
    have h1 : scaleToS H y = r := by
      unfold scaleToS
      rw [dif_pos e1]
      exact hru _ (Classical.choose_spec e1)
    have h2 : scaleToS H (c • y) = r / c := by
      unfold scaleToS
      rw [dif_pos e2]
      have hs2 := Classical.choose_spec e2
      have := hru (Classical.choose e2 * c) ⟨mul_pos hs2.1 hc, by rw [← smul_smul]; exact hs2.2⟩
      rw [← this, mul_div_cancel_right₀ _ hc.ne']
    rw [h1, h2]
    exact ⟨rfl, hr0⟩
  have hproj : ∀ y : V n, y ≠ 0 → proj H (c • y) = proj H y := by
    intro y hy
    obtain ⟨h1, -⟩ := hsc y hy
    unfold proj
    rw [h1, smul_smul, div_mul_cancel₀ _ hc.ne']
  have haC : ∀ y : V n, y ≠ 0 → aCoord H (c • y) = aCoord H y + κ := by
    intro y hy
    obtain ⟨h1, h2⟩ := hsc y hy
    unfold aCoord
    rw [h1, Real.log_div h2.ne' hc.ne', hκ]
    ring
  -- the affine reparametrization
  set aff : ℂ → ℂ := fun w => z₀ + s • w with haff
  set W : Set ℂ := {w | z₀ + s • w ∈ U} with hW
  have haffc : Continuous aff := by fun_prop
  have hWo : IsOpen W := hU.preimage haffc
  have hDaff : ∀ w, HasFDerivAt aff (s • ContinuousLinearMap.id ℝ ℂ) w := fun w =>
    ((hasFDerivAt_id w).const_smul s).const_add z₀
  have hcomp : ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (F : ℂ → X) (w : ℂ),
      DifferentiableAt ℝ F (aff w) →
      fderiv ℝ (fun w => F (aff w)) w = s • fderiv ℝ F (aff w) := by
    intro X _ _ F w hF
    refine (hF.hasFDerivAt.comp w (hDaff w)).fderiv.trans ?_
    ext x
    simp
  -- coordinates of `u`
  set au : ℂ → ℝ := fun z => aCoord H (u z) with hau
  set pu : ℂ → V n := fun z => proj H (u z) with hpu
  have hau_s : ContDiffOn ℝ ∞ au U := haCs.comp husm (fun z hz => hune z hz)
  have hpu_s : ContDiffOn ℝ ∞ pu U := hprojs.comp husm (fun z hz => hune z hz)
  have hau_d : ∀ z ∈ U, DifferentiableAt ℝ au z := fun z hz =>
    (hau_s.differentiableOn (by simp) z hz).differentiableAt (hU.mem_nhds hz)
  have hpu_d : ∀ z ∈ U, DifferentiableAt ℝ pu z := fun z hz =>
    (hpu_s.differentiableOn (by simp) z hz).differentiableAt (hU.mem_nhds hz)
  set v : ℂ → V n := fun w => c • u (z₀ + s • w) with hv
  -- local agreement of the coordinates of `v` with those of `u ∘ aff`
  have hav : ∀ w ∈ W, (fun w => aCoord H (v w)) =ᶠ[𝓝 w] fun w => au (aff w) + κ := by
    intro w hw
    filter_upwards [hWo.mem_nhds hw] with w' hw'
    exact haC _ (hune _ hw')
  have hpv : ∀ w ∈ W, (fun w => proj H (v w)) =ᶠ[𝓝 w] fun w => pu (aff w) := by
    intro w hw
    filter_upwards [hWo.mem_nhds hw] with w' hw'
    exact hproj _ (hune _ hw')
  have hDa : ∀ w ∈ W, fderiv ℝ (fun w => aCoord H (v w)) w = s • fderiv ℝ au (aff w) := by
    intro w hw
    rw [(hav w hw).fderiv_eq, fderiv_add_const, hcomp au w (hau_d _ hw)]
  have hDp : ∀ w ∈ W, fderiv ℝ (fun w => proj H (v w)) w = s • fderiv ℝ pu (aff w) := by
    intro w hw
    rw [(hpv w hw).fderiv_eq, hcomp pu w (hpu_d _ hw)]
  have hgrad : ∀ w ∈ W, gradNorm H v w = s * gradNorm H u (aff w) := by
    intro w hw
    unfold gradNorm
    rw [hDa w hw, hDp w hw, norm_smul, norm_smul, Real.norm_of_nonneg hs.le]
    ring
  -- linearity of the forms
  have hj0 : ∀ (t : ℝ) (x : V n), j0 (t • x) = t • j0 x := by
    intro t x
    funext k
    simp only [j0, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  have hlv : ∀ (x y : V n) (t : ℝ), liouville x (t • y) = t * liouville x y := by
    intro x y t
    simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hom : ∀ (x y : V n) (t : ℝ), omega0 (t • x) (t • y) = t ^ 2 * omega0 x y := by
    intro x y t
    simp only [omega0, hj0, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  -- the densities
  have hdens : ∀ φ : ℝ → ℝ, ∀ w ∈ W,
      energyDensity H φ v w = s ^ 2 * energyDensity H (fun r => φ (r + κ)) u (aff w) := by
    intro φ w hw
    have h1 : aCoord H (v w) = au (aff w) + κ := (hav w hw).self_of_nhds
    have h2 : proj H (v w) = pu (aff w) := (hpv w hw).self_of_nhds
    unfold energyDensity ds dt
    simp only
    rw [hDa w hw, hDp w hw, h1, h2]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hlv, hom,
      deriv_comp_add_const]
    ring
  have hdl : ∀ w ∈ W, dlambdaDensity H v w = s ^ 2 * dlambdaDensity H u (aff w) := by
    intro w hw
    unfold dlambdaDensity ds dt
    rw [hDp w hw]
    simp only [ContinuousLinearMap.smul_apply, hom]
    rfl
  -- change of variables
  have hme : MeasurableEmbedding aff :=
    ((Homeomorph.smulOfNeZero s hs.ne').trans (Homeomorph.addLeft z₀)).measurableEmbedding
  have hmap : Measure.map aff volume = ENNReal.ofReal (|s ^ 2|⁻¹) • (volume : Measure ℂ) := by
    have e1 : aff = (fun y => z₀ + y) ∘ (fun w : ℂ => s • w) := rfl
    have h1 := Measure.map_addHaar_smul (volume : Measure ℂ) hs.ne'
    rw [Complex.finrank_real_complex] at h1
    rw [e1, ← Measure.map_map (by fun_prop) (by fun_prop), h1, Measure.map_smul,
      Measure.IsAddLeftInvariant.map_add_left_eq_self, abs_inv]
  have hcv : ∀ (F : ℂ → ℝ≥0∞) (A : Set ℂ), MeasurableSet A →
      ∫⁻ w in {w | z₀ + s • w ∈ A}, ENNReal.ofReal (s ^ 2) * F (aff w) = ∫⁻ y in A, F y := by
    intro F A hA
    have key : ∫⁻ y in A, ENNReal.ofReal (s ^ 2) * F y ∂(Measure.map aff volume) =
        ∫⁻ w in {w | z₀ + s • w ∈ A}, ENNReal.ofReal (s ^ 2) * F (aff w) := by
      rw [hme.restrict_map, hme.lintegral_map]
      rfl
    rw [← key, hmap, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul
      (inv_nonneg.2 (abs_nonneg _)), abs_of_nonneg (sq_nonneg s),
      inv_mul_cancel₀ (pow_ne_zero 2 hs.ne'), ENNReal.ofReal_one, one_mul]
  have hE : ∀ A ⊆ U, MeasurableSet A →
      energy H {w | z₀ + s • w ∈ A} v = energy H A u ∧
        dlambdaEnergy H {w | z₀ + s • w ∈ A} v = dlambdaEnergy H A u := by
    intro A hAU hA
    have hpreA : MeasurableSet {w | z₀ + s • w ∈ A} := hA.preimage haffc.measurable
    have hsubW : {w | z₀ + s • w ∈ A} ⊆ W := fun w hw => hAU hw
    have hφ : ∀ φ : ℝ → ℝ, ∫⁻ w in {w | z₀ + s • w ∈ A}, ENNReal.ofReal (energyDensity H φ v w) =
        ∫⁻ y in A, ENNReal.ofReal (energyDensity H (fun r => φ (r + κ)) u y) := by
      intro φ
      rw [← hcv _ A hA]
      refine setLIntegral_congr_fun hpreA fun w hw => ?_
      rw [hdens φ w (hsubW hw), ENNReal.ofReal_mul (sq_nonneg s)]
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · refine iSup₂_le fun φ hφa => ?_
      rw [hφ φ]
      have hadm : Admissible (fun r => φ (r + κ)) :=
        ⟨hφa.1.comp (by fun_prop : ContDiff ℝ ∞ fun r : ℝ => r + κ),
          fun a b hab => hφa.2.1 (by linarith), fun r => hφa.2.2 _⟩
      exact le_iSup₂ (f := fun (ψ : ℝ → ℝ) (_ : Admissible ψ) =>
        ∫⁻ y in A, ENNReal.ofReal (energyDensity H ψ u y)) _ hadm
    · refine iSup₂_le fun ψ hψa => ?_
      have hadm : Admissible (fun r => ψ (r - κ)) :=
        ⟨hψa.1.comp (by fun_prop : ContDiff ℝ ∞ fun r : ℝ => r - κ),
          fun a b hab => hψa.2.1 (by linarith), fun r => hψa.2.2 _⟩
      have := le_iSup₂ (f := fun (φ : ℝ → ℝ) (_ : Admissible φ) =>
        ∫⁻ w in {w | z₀ + s • w ∈ A}, ENNReal.ofReal (energyDensity H φ v w)) _ hadm
      rw [hφ] at this
      have e : (fun r => ψ (r + κ - κ)) = ψ := funext fun r => by rw [add_sub_cancel_right]
      rw [e] at this
      exact this
    · unfold dlambdaEnergy
      rw [← hcv _ A hA]
      refine setLIntegral_congr_fun hpreA fun w hw => ?_
      rw [hdl w (hsubW hw), ENNReal.ofReal_mul (sq_nonneg s)]
  -- the curve itself
  obtain ⟨hfhol, hfder⟩ := isJHolomorphicOn_comp_add_smul (Jtilde H J) U u huhol z₀ s
  have hvsm : ContDiffOn ℝ ∞ v W := by
    have ha : ContDiff ℝ ∞ (fun w : ℂ => z₀ + s • w) := by fun_prop
    exact ContDiffOn.const_smul c (husm.comp ha.contDiffOn fun w hw => hw)
  refine ⟨⟨hvsm, fun w hw => smul_ne_zero hc.ne' (hune _ hw), fun w hw => ?_, ?_⟩,
    fun w hw => haC _ (hune _ hw), hgrad, hE⟩
  · obtain ⟨hd, hdb⟩ := hfhol w hw
    have hvd : HasFDerivAt v (c • fderiv ℝ (fun w => u (z₀ + s • w)) w) w :=
      hd.hasFDerivAt.const_smul c
    refine ⟨hvd.differentiableAt, ?_⟩
    unfold JHolomorphic.dbarJ at hdb ⊢
    rw [hvd.fderiv]
    simp only [ContinuousLinearMap.smul_apply]
    rw [hJs _ (hune _ hw) c hc, map_smul, ← smul_add, hdb, smul_zero]
  · rw [(hE U subset_rfl hU.measurableSet).1]
    exact hufin

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J U u) (z₀ : ℂ) (s : ℝ) (hs : 0 < s) (c : ℝ)
    (hc : 0 < c) :
    IsFiniteEnergyCurve H J {w | z₀ + s • w ∈ U} (fun w => c • u (z₀ + s • w)) ∧
      (∀ w, z₀ + s • w ∈ U →
        aCoord H (c • u (z₀ + s • w)) = aCoord H (u (z₀ + s • w)) + Real.log c / 2) ∧
      (∀ w, z₀ + s • w ∈ U →
        gradNorm H (fun w => c • u (z₀ + s • w)) w = s * gradNorm H u (z₀ + s • w)) ∧
      ∀ A ⊆ U, MeasurableSet A →
        energy H {w | z₀ + s • w ∈ A} (fun w => c • u (z₀ + s • w)) = energy H A u ∧
          dlambdaEnergy H {w | z₀ + s • w ∈ A} (fun w => c • u (z₀ + s • w)) =
            dlambdaEnergy H A u :=
  rescale_isFiniteEnergyCurve_aux H hH J hJ U hU u hu z₀ s hs c hc
