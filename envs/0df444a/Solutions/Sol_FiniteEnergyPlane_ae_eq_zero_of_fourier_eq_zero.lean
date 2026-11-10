-- Prove2me | solution 1 for FiniteEnergyPlane.ae_eq_zero_of_fourier_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-09T22:25:00.008594+00:00
-- url     : https://prove2.me/submissions/5f1ee8a2-bdd0-46ff-9bf0-48c2c880b31b

import Mathlib



/-!
# Tg-Inj layer 2 (local, NOT published): vanishing Fourier coefficients on `[0, 1)`

`ae_eq_zero_of_fourier_eq_zero`: an integrable `H : ℝ → ℂ` on `[0, 1)` all of whose Fourier
coefficients `∫₀¹ e^{2πikt} H(t) dt` vanish is `0` a.e. on `[0, 1)`.
-/

namespace FiniteEnergyPlane.TgInj

open MeasureTheory Filter Topology Set
open scoped ContDiff Real

noncomputable section

instance fact_zero_lt_one_real : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩

/-- `F ↦ ∫₀¹ F(t) H(t) dt` on `C(AddCircle 1, ℂ)`. -/
def pairL (H : ℝ → ℂ) (hH : IntegrableOn H (Ico 0 1)) : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun F => ∫ t in Ico (0 : ℝ) 1, F (t : AddCircle (1 : ℝ)) * H t
      map_add' := fun F G => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hH.bdd_mul (F.continuous.comp
          (AddCircle.continuous_mk' 1)).aestronglyMeasurable
          (Eventually.of_forall fun t => F.norm_coe_le_norm _))
          (hH.bdd_mul (G.continuous.comp (AddCircle.continuous_mk' 1)).aestronglyMeasurable
          (Eventually.of_forall fun t => G.norm_coe_le_norm _))
      map_smul' := fun c F => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul c _ }
    (∫ t in Ico (0 : ℝ) 1, ‖H t‖) (fun F => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [mul_comm, ← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
        (hH.norm.const_mul _) (Eventually.of_forall fun t => ?_)
      show ‖F (t : AddCircle (1 : ℝ)) * H t‖ ≤ ‖F‖ * ‖H t‖
      rw [norm_mul]
      gcongr
      exact F.norm_coe_le_norm _)

lemma pairL_apply (H : ℝ → ℂ) (hH : IntegrableOn H (Ico 0 1)) (F : C(AddCircle (1 : ℝ), ℂ)) :
    pairL H hH F = ∫ t in Ico (0 : ℝ) 1, F (t : AddCircle (1 : ℝ)) * H t := rfl

/-- Tg-Inj layer 2. -/
theorem ae_eq_zero_of_fourier_eq_zero (H : ℝ → ℂ) (hH : IntegrableOn H (Ico 0 1))
    (h : ∀ k : ℤ, ∫ t in Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * k * t) * H t = 0) :
    ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), H t = 0 := by
  -- every continuous function on the circle pairs to zero
  have hker : ∀ F : C(AddCircle (1 : ℝ), ℂ), pairL H hH F = 0 := by
    have hle : (Submodule.span ℂ (range (@fourier (1 : ℝ)))) ≤ LinearMap.ker (pairL H hH : C(AddCircle (1 : ℝ), ℂ) →ₗ[ℂ] ℂ) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, pairL_apply]
      rw [← h k]
      refine setIntegral_congr_fun measurableSet_Ico fun t _ => ?_
      simp only [fourier_coe_apply, Complex.ofReal_one, div_one]
    have hcl := Submodule.topologicalClosure_minimal _ hle (pairL H hH).isClosed_ker
    rw [span_fourier_closure_eq_top] at hcl
    exact fun F => hcl Submodule.mem_top
  have hU := (isOpen_Ioo (a := (0 : ℝ)) (b := 1)).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume) ((hH.mono_set Ioo_subset_Ico_self).locallyIntegrableOn) (f := H)
    fun g hg hgc hgU => by
      have hg0 : g 0 = 0 := image_eq_zero_of_notMem_tsupport fun h0 => (hgU h0).1.false
      have hg1 : g 1 = 0 := image_eq_zero_of_notMem_tsupport fun h1 => (hgU h1).2.false
      let F : C(AddCircle (1 : ℝ), ℂ) :=
        ⟨AddCircle.liftIco 1 0 (fun t => (g t : ℂ)), AddCircle.liftIco_zero_continuous
          (by simp [hg0, hg1]) (Complex.continuous_ofReal.comp hg.continuous).continuousOn⟩
      have hF := hker F
      rw [pairL_apply] at hF
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ico (0 : ℝ) 1) fun t ht => by
        rw [image_eq_zero_of_notMem_tsupport fun h' => ht (Ioo_subset_Ico_self (hgU h')),
          zero_smul]]
      rw [← hF]
      refine setIntegral_congr_fun measurableSet_Ico fun t ht => ?_
      simp only [F, ContinuousMap.coe_mk, AddCircle.liftIco_zero_coe_apply ht, Complex.real_smul]
  have hnull : volume ({0} : Set ℝ) = 0 := Real.volume_singleton
  rw [ae_restrict_iff' measurableSet_Ico]
  have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    rw [ae_iff]; simpa using hnull
  filter_upwards [hU, h0] with t ht ht0 htI
  exact ht ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), htI.2⟩

end

end FiniteEnergyPlane.TgInj

open FiniteEnergyPlane

open MeasureTheory Filter Topology Set
open scoped ContDiff Real

theorem solution (H : ℝ → ℂ) (hH : IntegrableOn H (Ico 0 1))
    (h : ∀ k : ℤ, ∫ t in Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * k * t) * H t = 0) :
    ∀ᵐ t ∂(volume.restrict (Ico (0 : ℝ) 1)), H t = 0 :=
  FiniteEnergyPlane.TgInj.ae_eq_zero_of_fourier_eq_zero H hH h
