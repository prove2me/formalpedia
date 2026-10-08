-- Prove2me | solution 2 for ConnesGreen.actual_physical_test_norm
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T22:53:16.574543+00:00
-- url     : https://prove2.me/submissions/fd4af2e6-921f-4aa7-a36d-78163d465ec6

import Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
import Definitions.Def_ConnesGreen_RG0_source_constructors
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical Topology
noncomputable section

namespace ConnesGreen
/-- All continuous native sources and columns are valid L2 inputs on a finite
window, so the total extension used in the model is never invoked there. -/
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
end ConnesGreen
namespace ConnesGreen
open Filter WeilDefect WeilDefect.ConnesNative
theorem windowL2_norm_sq (t : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    ‖windowL2 t f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂windowMeasure t := by
  rw [@norm_sq_eq_re_inner ℂ]
  change (⟪windowL2 t f, windowL2 t f⟫_ℂ).re = _
  rw [windowL2_inner t f f (continuous_window_memLp t f hf) (continuous_window_memLp t f hf)]
  have he : (∫ x, star (f x) * f x ∂windowMeasure t) =
      ((∫ x, ‖f x‖ ^ 2 ∂windowMeasure t : ℝ) : ℂ) := by
    trans ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂windowMeasure t
    · apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simpa [RCLike.star_def] using Complex.conj_mul' (f x))
    · exact integral_complex_ofReal
  rw [he]
  rfl

def physicalTestEnergy (g : ℝ → ℂ) : ℝ :=
  (∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) + (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2)

theorem physicalTestEnergy_nonnegative (g : ℝ → ℂ) : 0 ≤ physicalTestEnergy g := by
  unfold physicalTestEnergy
  exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
    (mul_nonneg (by norm_num) (integral_nonneg (fun _ => sq_nonneg _)))

/-- The physical source norm is exactly the original test's global Dirichlet
energy. In particular it is independent of any window containing its support. -/
theorem sourceEmbed_L_norm_sq_exact (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖sourceEmbed t (problemOneL g)‖ ^ 2 = physicalTestEnergy g := by
  have hn : ‖sourceEmbed t (problemOneL g)‖ = ‖energyVector t g‖ := by
    change ‖(sourceEmbed t (problemOneL g) : Ambient t)‖ = _
    rw [ConnesGreen.RG0Integration.sourceEmbed_L_energyVector t ht g hg]
  rw [hn]
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  change ‖windowL2 t (iteratedDeriv 1 g)‖ ^ 2 +
    ‖(1 / 2 : ℂ) • windowL2 t g‖ ^ 2 = _
  have hc : ‖(1 / 2 : ℂ)‖ ^ 2 = (1 / 4 : ℝ) := by norm_num
  rw [norm_smul, mul_pow, hc,
    windowL2_norm_sq t (iteratedDeriv 1 g) (hg.1.1.continuous_iteratedDeriv 1 (by simp)),
    windowL2_norm_sq t g hg.1.1.continuous]
  have hs : tsupport g ⊆ Set.Icc (-t) t :=
    hg.2.trans Set.Ioo_subset_Icc_self
  have hd : tsupport (iteratedDeriv 1 g) ⊆ tsupport g := by
    rw [iteratedDeriv_one]
    exact tsupport_deriv_subset
  have hi : (∫ x, ‖g x‖ ^ 2 ∂windowMeasure t) = ∫ x : ℝ, ‖g x‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
    simp [h0]
  have hid : (∫ x, ‖iteratedDeriv 1 g x‖ ^ 2 ∂windowMeasure t) =
      ∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have h0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs (hd h)))
    simp [h0]
  rw [hi, hid]
  rfl

end ConnesGreen

open ConnesGreen ConnesRZFrontier WeilDefect WeilDefect.ConnesNative
theorem solution (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    ‖sourceEmbed t (problemOneL g)‖ ^ 2 =
      (∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
      (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2) :=
  sourceEmbed_L_norm_sq_exact t ht g hg
