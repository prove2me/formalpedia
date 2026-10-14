-- Prove2me | solution 1 for DbarRegularity.integral_integral_mul_sub_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T16:54:10.874489+00:00
-- url     : https://prove2.me/submissions/b1afa864-ba8b-42ed-aa34-bd2ac2a81a96

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For `K, g ∈ L²(ℝ^d)` and `f ∈ L¹(ℝ^d)`:
`∫ (∫ K(x - y) f(y) dy) g(x) dx = ∫ (∫ K(x - y) g(x) dx) f(y) dy`. -/
theorem integral_integral_mul_sub_mul_comm {d : ℕ} {K f g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) (hf : Integrable f volume) (hg : MemLp g 2 volume) :
    ∫ x, (∫ y, K (x - y) * f y) * g x = ∫ y, (∫ x, K (x - y) * g x) * f y := by
  have hFm : AEStronglyMeasurable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin d) =>
      K (x - y) * f y * g x) (volume.prod volume) :=
    ((hK.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub volume volume)).mul
      (hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)).mul
      (hg.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hinner : ∀ y, ∫⁻ x, ‖K (x - y) * g x‖ₑ ≤ eLpNorm K 2 volume * eLpNorm g 2 volume := by
    intro y
    have hKy : MemLp (fun x => K (x - y)) 2 volume :=
      hK.comp_measurePreserving (measurePreserving_sub_right volume y)
    have h := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hg.1 hKy.1
    have he : eLpNorm (fun x => K (x - y)) 2 volume = eLpNorm K 2 volume :=
      eLpNorm_comp_measurePreserving hK.1 (measurePreserving_sub_right volume y)
    rw [eLpNorm_one_eq_lintegral_enorm, he] at h
    simpa [smul_eq_mul] using h
  have hF : Integrable (Function.uncurry fun x y : EuclideanSpace ℝ (Fin d) =>
      K (x - y) * f y * g x) (volume.prod volume) := by
    refine ⟨hFm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hFm.enorm]
    calc ∫⁻ y, ∫⁻ x, ‖Function.uncurry (fun x y : EuclideanSpace ℝ (Fin d) =>
            K (x - y) * f y * g x) (x, y)‖ₑ
        = ∫⁻ y, ‖f y‖ₑ * ∫⁻ x, ‖K (x - y) * g x‖ₑ := by
          refine lintegral_congr fun y => ?_
          rw [← lintegral_const_mul' _ _ enorm_ne_top]
          refine lintegral_congr fun x => ?_
          simp only [Function.uncurry_apply_pair, enorm_mul]; ring
      _ ≤ ∫⁻ y, ‖f y‖ₑ * (eLpNorm K 2 volume * eLpNorm g 2 volume) :=
          lintegral_mono fun y => by gcongr; exact hinner y
      _ = (∫⁻ y, ‖f y‖ₑ) * (eLpNorm K 2 volume * eLpNorm g 2 volume) :=
          lintegral_mul_const' _ _ (ENNReal.mul_ne_top hK.2.ne hg.2.ne)
      _ < ⊤ := ENNReal.mul_lt_top hf.2 (ENNReal.mul_lt_top hK.2 hg.2)
  calc ∫ x, (∫ y, K (x - y) * f y) * g x = ∫ x, ∫ y, K (x - y) * f y * g x :=
        integral_congr_ae (ae_of_all _ fun x => (integral_mul_const _ _).symm)
    _ = ∫ y, ∫ x, K (x - y) * f y * g x := integral_integral_swap hF
    _ = ∫ y, (∫ x, K (x - y) * g x) * f y := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        dsimp only
        rw [← integral_mul_const]
        congr 1; funext x; ring

end DbarRegularity

open DbarRegularity

open MeasureTheory
open scoped ENNReal

theorem solution {d : ℕ} {K f g : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) (hf : Integrable f volume) (hg : MemLp g 2 volume) :
    ∫ x, (∫ y, K (x - y) * f y) * g x = ∫ y, (∫ x, K (x - y) * g x) * f y :=
  integral_integral_mul_sub_mul_comm hK hf hg
