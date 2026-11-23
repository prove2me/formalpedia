-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.periodisation_eq_tsum_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:17:51.702843+00:00
-- url     : https://prove2.me/submissions/9cb35de7-6c3f-49b3-a2c8-692ae7cdf2dc

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_periodisationTorus_mk
import Theorems.Thm_DedekindZeta_PoissonSummation_continuous_periodisationTorus
import Theorems.Thm_DedekindZeta_PoissonSummation_integral_fundamentalDomain_periodisation
import Theorems.Thm_DedekindZeta_PoissonSummation_summable_periodisation_fourier
import Theorems.Thm_DedekindZeta_PoissonSummation_continuous_torusEquiv_symm
import Theorems.Thm_DedekindZeta_PoissonSummation_fourierChar_inner_eq_prod_fourier
import Theorems.Thm_DedekindZeta_PoissonSummation_hasSum_fourier_product_of_summable
import Theorems.Thm_DedekindZeta_PoissonSummation_integral_eq_covolume_inv_smul_integral_fundamentalDomain

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open UnitAddTorus ComplexConjugate
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_1176
attribute [local instance] DedekindZeta.PoissonSummation._p2m_local_instance_c635516111_1182
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
set_option maxHeartbeats 1000000
namespace DedekindZeta.PoissonSummation
theorem _root_.solution (x : V) :
    periodisation L f x
      = ∑' w : dualLattice L,
          𝐞 (⟪x, (w : V)⟫) •
            ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V)) := by
  classical
  -- A ℤ-basis of `L` provides the torus iso `torusEquiv` and the dual-lattice
  -- bijection `dualLatticeEquiv`.
  set d := Module.finrank ℤ L with hd
  let b : Basis (Fin d) ℤ L := Module.finBasis ℤ L
  -- The periodisation transported to the product torus `(AddCircle 1)^d`.
  set Fp : (Fin d → AddCircle (1 : ℝ)) → ℂ :=
    fun θ => periodisationTorus L f ((torusEquiv L b).symm θ) with hFp
  have hcont : Continuous Fp :=
    (continuous_periodisationTorus L f).comp (continuous_torusEquiv_symm L b)
  -- A fundamental domain of `L`, in the `↥L.toAddSubgroup` form expected by the
  -- Fourier-coefficient and measure-transport lemmas.
  set D : Set V := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) with hDdef
  have hDmeas : MeasurableSet D :=
    ZSpan.fundamentalDomain_measurableSet (b.ofZLatticeBasis ℝ L)
  have hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D := by
    have h := ZSpan.isAddFundamentalDomain' (b.ofZLatticeBasis ℝ L) (volume)
    rwa [b.ofZLatticeBasis_span ℝ] at h
  -- Coefficient identity: the product Fourier coefficient of `Fp` at the
  -- multi-index `dualLatticeEquiv L b w` equals `(vol L)⁻¹ · 𝓕 f w`.
  have hcoeff : ∀ w : dualLattice L,
      fourierCoeffProd Fp (dualLatticeEquiv L b w)
        = (ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V) := by
    intro w
    have hgcont : Continuous
        (fun θ : Fin d → AddCircle (1 : ℝ) =>
          (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i) (θ i))) • Fp θ) := by
      refine Continuous.smul (continuous_finsetProd
        (f := fun (i : Fin d) (θ : Fin d → AddCircle (1 : ℝ)) =>
          (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i) (θ i)))
        Finset.univ ?_) hcont
      intro i _
      exact Complex.continuous_conj.comp
        ((fourier (dualLatticeEquiv L b w i)).continuous.comp (continuous_apply i))
    have hgint : Integrable
        (fun θ : Fin d → AddCircle (1 : ℝ) =>
          (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i) (θ i))) • Fp θ) :=
      hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    -- Transport the product-torus integral to a fundamental-domain integral.
    have step1 : fourierCoeffProd Fp (dualLatticeEquiv L b w)
        = (ZLattice.covolume L)⁻¹ •
            ∫ x' in D,
              (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
                  ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
                • Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) :=
      integral_eq_covolume_inv_smul_integral_fundamentalDomain L b hD hgint
    -- Identify the fundamental-domain integral with `𝓕 f w`.
    have hbody : ∀ x' : V,
        (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
            ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
              • Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup))
          = 𝐞 (-⟪x', (w : V)⟫) • periodisation L f x' := by
      intro x'
      have hFval : Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup))
          = periodisation L f x' := by
        change periodisationTorus L f
            ((torusEquiv L b).symm (torusEquiv L b (x' : V ⧸ L.toAddSubgroup)))
            = periodisation L f x'
        rw [(torusEquiv L b).symm_apply_apply, periodisationTorus_mk]
      have hchar : (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
            ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
          = ((𝐞 (-⟪x', (w : V)⟫) : Circle) : ℂ) := by
        rw [← map_prod (starRingEnd ℂ),
          ← fourierChar_inner_eq_prod_fourier L b w x',
          AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
      rw [hFval, hchar, Circle.smul_def]
    have hII : (∫ x' in D,
          (∏ i, (starRingEnd ℂ) (fourier (dualLatticeEquiv L b w i)
              ((torusEquiv L b (x' : V ⧸ L.toAddSubgroup)) i)))
                • Fp (torusEquiv L b (x' : V ⧸ L.toAddSubgroup)))
        = 𝓕 (f : V → ℂ) (w : V) := by
      rw [← integral_fundamentalDomain_periodisation L f hD w]
      exact setIntegral_congr_fun hDmeas (fun x' _ => hbody x')
    rw [step1, hII, Complex.real_smul, Complex.ofReal_inv]
  -- Summability of the product Fourier coefficients (no character, modulus 1).
  have hs0 := summable_periodisation_fourier L f 0
  simp only [inner_zero_left, AddChar.map_zero_eq_one, one_smul] at hs0
  have hsumw : Summable (fun w : dualLattice L =>
      fourierCoeffProd Fp (dualLatticeEquiv L b w)) :=
    hs0.congr (fun w => (hcoeff w).symm)
  have hsum : Summable (fun n : Fin d → ℤ => fourierCoeffProd Fp n) :=
    (dualLatticeEquiv L b).summable_iff.mp hsumw
  -- Apply product-torus inversion at `θ = torusEquiv L b ↑x`.
  set θ := torusEquiv L b (x : V ⧸ L.toAddSubgroup) with hθ
  have hHS := hasSum_fourier_product_of_summable hcont hsum θ
  have hFpθ : Fp θ = periodisation L f x := by
    change periodisationTorus L f ((torusEquiv L b).symm θ) = periodisation L f x
    rw [hθ, (torusEquiv L b).symm_apply_apply, periodisationTorus_mk]
  rw [hFpθ] at hHS
  -- Re-index `∑_{n∈ℤ^d}` back to `∑_{w∈L*}` via `dualLatticeEquiv`.
  have hHS2 : HasSum (fun w : dualLattice L =>
      (∏ i, fourier (dualLatticeEquiv L b w i) (θ i))
        • fourierCoeffProd Fp (dualLatticeEquiv L b w))
      (periodisation L f x) :=
    (dualLatticeEquiv L b).hasSum_iff.mpr hHS
  have htarget : (fun w : dualLattice L =>
        (∏ i, fourier (dualLatticeEquiv L b w i) (θ i))
          • fourierCoeffProd Fp (dualLatticeEquiv L b w))
      = (fun w : dualLattice L =>
        𝐞 (⟪x, (w : V)⟫) •
          ((ZLattice.covolume L : ℂ)⁻¹ * 𝓕 (f : V → ℂ) (w : V))) := by
    funext w
    rw [hcoeff w,
      show (∏ i, fourier (dualLatticeEquiv L b w i) (θ i))
            = ((𝐞 (⟪x, (w : V)⟫) : Circle) : ℂ) from
        (fourierChar_inner_eq_prod_fourier L b w x).symm,
      Circle.smul_def]
  rw [htarget] at hHS2
  exact hHS2.tsum_eq.symm
end DedekindZeta.PoissonSummation
