-- Prove2me | solution 1 for ConnesGreen.canonical_source_pairing_mellin
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T04:51:33.259154+00:00
-- url     : https://prove2.me/submissions/d11c7bbc-10b1-4b63-a2b5-d49a187341c0

import Definitions.Def_ConnesGreen_RG0_original_actors
import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative Set
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
theorem sourceLift_inner (t : ℝ) (f : WindowL2 t) (h : Physical t) :
    ⟪sourceLift t f, h⟫_ℂ = (2 : ℂ) * ⟪f, (h : Ambient t) 1⟫_ℂ := by
  rw [sourceLift, Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  simp [sourceLoad, PiLp.inner_apply, Fin.sum_univ_two, inner_smul_left,
    map_ofNat]

theorem continuous_window_memLp (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    MemLp f 2 (windowMeasure t) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc

theorem windowL2_inner (t : ℝ) (f g : ℝ → ℂ)
    (hf : MemLp f 2 (windowMeasure t)) (hg : MemLp g 2 (windowMeasure t)) :
    ⟪windowL2 t f, windowL2 t g⟫_ℂ =
      ∫ x, star (f x) * g x ∂windowMeasure t := by
  simp only [windowL2, dif_pos hf, dif_pos hg, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, RCLike.inner_apply, mul_comm]











theorem reflected_ordinate_source (z : ℂ) (x : ℝ) :
    star (realExpMode (problemOneFreq (-I * (mirror z - 1 / 2))) x) =
      Complex.exp ((z - 1 / 2) * x) := by
  have hf : problemOneFreq (-I * (mirror z - 1 / 2)) = star (z - 1 / 2) := by
    simp [problemOneFreq, mirror, mul_neg, neg_mul, ← mul_assoc]
    ring
  rw [hf]
  change (starRingEnd ℂ) (Complex.exp ((x : ℂ) * star (z - 1 / 2))) = _
  rw [← Complex.exp_conj]
  congr 1
  change star ((x : ℂ) * star (z - 1 / 2)) = (z - 1 / 2) * x
  simp [mul_comm]

theorem solution (t : ℝ) (ht : 0 < t) (g : ℝ → ℂ) (hg : SupportedTest t g) (ρ : CriticalZeros) :
    ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (problemOneL g)⟫_ℂ = mellinHat g ρ.1 := by
  have hi := sourceLift_inner t (windowL2 t (actualGreenSource ρ)) (sourceEmbed t (problemOneL g))
  change ⟪sourceEmbed t (actualGreenSource ρ), sourceEmbed t (problemOneL g)⟫_ℂ = _ at hi
  rw [ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht g hg] at hi
  have he : (energyVector t g) 1 = (1 / 2 : ℂ) • windowL2 t g := by simp [energyVector]
  rw [he, inner_smul_right] at hi
  have hm : (2 : ℂ) * ((1 / 2 : ℂ) * ⟪windowL2 t (actualGreenSource ρ), windowL2 t g⟫_ℂ) = ⟪windowL2 t (actualGreenSource ρ), windowL2 t g⟫_ℂ := by ring
  rw [hm] at hi
  have hc : Continuous (actualGreenSource ρ) := by
    unfold actualGreenSource realExpMode
    fun_prop
  rw [windowL2_inner t _ _ (continuous_window_memLp t _ hc) (continuous_window_memLp t g hg.1.1.continuous)] at hi
  rw [hi]
  unfold windowMeasure
  have heq : (fun x : ℝ => star (actualGreenSource ρ x) * g x) = fun x => g x * Complex.exp ((ρ.1 - 1 / 2) * x) := by
    funext x
    rw [actualGreenSource, actualGreenOrdinate, reflected_ordinate_source]
    ring
  rw [heq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have h0 : g x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(hg.2 h).1.le, (hg.2 h).2.le⟩)
  simp [h0]
