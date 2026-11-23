-- Prove2me | solution 1 for DedekindZeta.ConeRadialReduction.exists_isMellinPair_radialTheta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:58:05.08281+00:00
-- url     : https://prove2.me/submissions/c14e2827-f43d-4c04-84cc-33925830f930

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_MellinPrinciple
import Definitions.Def_DedekindZeta_GammaIntegral
import Definitions.Def_DedekindZeta_ConeRadialReduction
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_orbitThetaFrac
import Theorems.Thm_DedekindZeta_ConeRadialReduction_continuousOn_orbitTheta
import Theorems.Thm_DedekindZeta_ConeRadialReduction_exists_decay_radialTheta
import Theorems.Thm_DedekindZeta_ConeRadialReduction_radialTheta_inversion

set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory Module
open scoped Real ENNReal nonZeroDivisors
open DedekindZeta DedekindZeta.ConeRadialReduction
variable (K : Type*) [Field K] [NumberField K]
variable {K}
namespace DedekindZeta.ConeRadialReduction
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) :
    ∃ c α : ℝ,
      MellinPrinciple.IsMellinPair (radialTheta K 𝔞) (radialThetaDual K 𝔞)
        (surfaceVolume K) (surfaceVolume K) ((Theta.covolume K 𝔞 : ℂ)⁻¹) 1 c α := by
  obtain ⟨c, α, hc, hα, hf, hg⟩ := exists_decay_radialTheta (K := K) 𝔞
  refine ⟨c, α, ?_⟩
  refine
    { hf_cont := ?_
      hg_cont := ?_
      hk := one_pos
      hc := hc
      hα := hα
      hC := ?_
      hf_decay := hf
      hg_decay := hg
      hfe := ?_ }
  · -- continuity of `radialTheta K 𝔞 = orbitTheta K 𝔞 + V` on `Ioi 0`
    -- (`orbitTheta` is only continuous on `Ioi 0`; see `continuousOn_orbitTheta`).
    exact (continuousOn_orbitTheta K 𝔞).add continuousOn_const
  · -- continuity of `radialThetaDual K 𝔞 = orbitThetaFrac K (dualIdeal K 𝔞) + V`
    --  on `Ioi 0` (`continuousOn_orbitThetaFrac`).
    exact (continuousOn_orbitThetaFrac K (Theta.dualIdeal K 𝔞)).add continuousOn_const
  · -- `(covolume K 𝔞)⁻¹ ≠ 0`: reduces to `covolume K 𝔞 ≠ 0`, i.e.
    -- `(absNorm 𝔞 : ℝ) ≠ 0` (`Ideal.absNorm_eq_zero_iff`, `𝔞 ≠ 0`) and
    -- `√|discr K| ≠ 0` (`NumberField.discr_ne_zero`).
    have hcov : Theta.covolume K 𝔞 ≠ 0 := by
      rw [Theta.covolume]
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr hne
      · exact (Real.sqrt_pos_of_pos
          (abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K)))).ne'
    exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hcov)
  · -- inversion law `f(1/y) = C · y^k · g(y)`
    intro y hy
    exact radialTheta_inversion (K := K) 𝔞 hne y hy
end DedekindZeta.ConeRadialReduction
