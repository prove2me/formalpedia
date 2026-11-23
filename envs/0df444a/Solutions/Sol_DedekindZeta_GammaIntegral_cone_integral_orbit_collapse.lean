-- Prove2me | solution 1 for DedekindZeta.GammaIntegral.cone_integral_orbit_collapse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:44:48.804656+00:00
-- url     : https://prove2.me/submissions/3b36fc5c-ab2d-4062-9eb0-15b3291674bf

import Mathlib
import Definitions.Def_DedekindZeta_Statements
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_GammaIntegral
import Theorems.Thm_DedekindZeta_GammaIntegral_mellin_mixedGaussian_mul_eq
import Theorems.Thm_DedekindZeta_GammaIntegral_integrable_mixedGaussian_mul_norm_cpow
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
import Theorems.Thm_DedekindZeta_isFundamentalDomain_fundamentalCone
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open MeasureTheory
open scoped Real ENNReal
open DedekindZeta DedekindZeta.GammaIntegral
open DedekindZeta DedekindZeta.Theta
open NumberField.Units NumberField.Units.dirichletUnitTheorem
attribute [local instance] DedekindZeta.coneMulAction DedekindZeta.coneMeasurableConstSMul
  DedekindZeta.coneCountable DedekindZeta.coneSMulInvariantMeasure
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped nonZeroDivisors
open scoped Pointwise
variable {K}
namespace DedekindZeta.GammaIntegral
theorem _root_.solution (s : ℂ) (hs : 1 < s.re)
    {a₀ : RingOfIntegers K} (ha₀ : a₀ ≠ 0) :
    ∑' u : (RingOfIntegers K)ˣ,
          ∫ x, (mixedEmbedding.fundamentalCone K).indicator
              (fun x => (mixedGaussian K
                  (x * mixedEmbedding K
                    (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
                * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K)
      = (Units.torsionOrder K : ℂ) * I K s *
          (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) := by
  classical
  -- The shift `σ a₀` and the whole-space integrand `F y = g(y·σ a₀)·|N y|^s`.
  set c₀ : mixedEmbedding.mixedSpace K :=
    mixedEmbedding K ((a₀ : RingOfIntegers K) : K) with hc₀
  set F : mixedEmbedding.mixedSpace K → ℂ :=
    fun y => (mixedGaussian K (y * c₀) : ℂ) * (mixedEmbedding.norm y : ℂ) ^ s with hF
  -- Whole-space integrability and Mellin value of `F`.
  have hint : Integrable F (mixedMulHaar K) := by
    rw [hF, hc₀]; exact integrable_mixedGaussian_mul_norm_cpow s hs ha₀
  have hV : ∫ x, F x ∂(mixedMulHaar K)
      = (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) * I K s := by
    rw [hF, hc₀]; exact mellin_mixedGaussian_mul_eq s ha₀
  -- The cone integrals along the free-complement action.
  let A : Multiplicative (Fin (rank K) → ℤ) → ℂ :=
    fun g => ∫ x in mixedEmbedding.fundamentalCone K, F (g • x) ∂(mixedMulHaar K)
  -- `HasSum A (∫ F)` from the cone fundamental domain.
  have hFD := isFundamentalDomain_fundamentalCone (K := K)
  have hAeq : (fun g : Multiplicative (Fin (rank K) → ℤ) =>
        ∫ x, F x ∂((mixedMulHaar K).restrict (g • mixedEmbedding.fundamentalCone K))) = A := by
    funext g
    show ∫ x in g • mixedEmbedding.fundamentalCone K, F x ∂(mixedMulHaar K)
        = ∫ x in mixedEmbedding.fundamentalCone K, F (g • x) ∂(mixedMulHaar K)
    rw [← (measurePreserving_smul g (mixedMulHaar K)).setIntegral_image_emb
          (measurableEmbedding_const_smul g) F (mixedEmbedding.fundamentalCone K),
      Set.image_smul]
  have hHS : HasSum A (∫ x, F x ∂(mixedMulHaar K)) := by
    have hms := hFD.sum_restrict
    have hintsum : Integrable F
        (Measure.sum (fun g : Multiplicative (Fin (rank K) → ℤ) => (mixedMulHaar K).restrict
          (g • mixedEmbedding.fundamentalCone K))) := by rw [hms]; exact hint
    have h0 := hasSum_integral_measure hintsum
    rw [hms] at h0
    rwa [hAeq] at h0
  have hsummableA : Summable A := hHS.summable
  have htsumA : ∑' g, A g = ∫ x, F x ∂(mixedMulHaar K) := hHS.tsum_eq
  -- Per-unit integrand collapses to `F (u • x)`.
  have hF_smul : ∀ (u : (RingOfIntegers K)ˣ) (x : mixedEmbedding.mixedSpace K),
      F (u • x) = (mixedGaussian K
          (x * mixedEmbedding K (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
        * (mixedEmbedding.norm x : ℂ) ^ s := by
    intro u x
    have harg : (u • x) * c₀ = x * mixedEmbedding K
        (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K) := by
      rw [hc₀, unitSMul_smul,
        show (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)
            = ((u : RingOfIntegers K) : K) * ((a₀ : RingOfIntegers K) : K) by push_cast; ring,
        map_mul]
      ring
    have hnorm : mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := norm_unit_smul u x
    simp only [hF]
    rw [harg, hnorm]
  -- The reindexing of the unit group by `torsion × free` (Dirichlet).
  let f₀ : torsion K × (Fin (rank K) → ℤ) → (RingOfIntegers K)ˣ :=
    fun p => (p.1 : (RingOfIntegers K)ˣ) * ∏ i, fundSystem K i ^ (p.2 i)
  have hf₀app : ∀ p, f₀ p
      = (p.1 : (RingOfIntegers K)ˣ) * ∏ i, fundSystem K i ^ (p.2 i) := fun _ => rfl
  have hbij : Function.Bijective f₀ := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · exact (exist_unique_eq_mul_prod K (f₀ p)).unique (hf₀app p) (by rw [h])
    · obtain ⟨p, hp, -⟩ := exist_unique_eq_mul_prod K x
      exact ⟨p, (hf₀app p).trans hp.symm⟩
  let ev : (torsion K × (Fin (rank K) → ℤ)) ≃ (RingOfIntegers K)ˣ :=
    Equiv.ofBijective f₀ hbij
  -- The free-part summand, indexed additively.
  let Ã : (Fin (rank K) → ℤ) → ℂ := fun e => A (Multiplicative.ofAdd e)
  -- Each unit-coset cone integral collapses to a free-part cone integral.
  have hBev : ∀ p : torsion K × (Fin (rank K) → ℤ),
      (∫ x in mixedEmbedding.fundamentalCone K, F ((ev p) • x) ∂(mixedMulHaar K)) = Ã p.2 := by
    rintro ⟨ζ, e⟩
    have hcu : (coneUnitHom (K := K) (Multiplicative.ofAdd e) : (RingOfIntegers K)ˣ)
        = ∏ i, fundSystem K i ^ (e i) := by simp [coneUnitHom]
    have hev : ev (ζ, e)
        = (ζ : (RingOfIntegers K)ˣ) * coneUnitHom (K := K) (Multiplicative.ofAdd e) := by
      show f₀ (ζ, e) = _
      show (ζ : (RingOfIntegers K)ˣ) * ∏ i, fundSystem K i ^ (e i)
          = (ζ : (RingOfIntegers K)ˣ) * coneUnitHom (K := K) (Multiplicative.ofAdd e)
      rw [hcu]
    have hcomm : ∀ y : mixedEmbedding.mixedSpace K,
        (ev (ζ, e)) • y
          = (coneUnitHom (K := K) (Multiplicative.ofAdd e)) • ((ζ : (RingOfIntegers K)ˣ) • y) := by
      intro y
      rw [hev, mul_smul]
      simp only [unitSMul_smul]
      ring
    have himg : (fun y : mixedEmbedding.mixedSpace K => (ζ : (RingOfIntegers K)ˣ) • y) ''
          mixedEmbedding.fundamentalCone K = mixedEmbedding.fundamentalCone K := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact fundamentalCone.torsion_smul_mem_of_mem hz ζ.2
      · intro hy
        exact ⟨(ζ : (RingOfIntegers K)ˣ)⁻¹ • y,
          fundamentalCone.torsion_smul_mem_of_mem hy ((torsion K).inv_mem ζ.2),
          by simp only [smul_smul, mul_inv_cancel, one_smul]⟩
    let ψ : mixedEmbedding.mixedSpace K ≃ᵐ mixedEmbedding.mixedSpace K :=
      { toFun := fun y => (ζ : (RingOfIntegers K)ˣ) • y
        invFun := fun y => (ζ : (RingOfIntegers K)ˣ)⁻¹ • y
        left_inv := fun y => by simp only [smul_smul, inv_mul_cancel, one_smul]
        right_inv := fun y => by simp only [smul_smul, mul_inv_cancel, one_smul]
        measurable_toFun := measurable_unitSMul _
        measurable_invFun := measurable_unitSMul _ }
    have hmp : MeasurePreserving (fun y : mixedEmbedding.mixedSpace K =>
        (ζ : (RingOfIntegers K)ˣ) • y) (mixedMulHaar K) (mixedMulHaar K) :=
      measurePreserving_unitSMul (ζ : (RingOfIntegers K)ˣ)
    calc ∫ x in mixedEmbedding.fundamentalCone K, F ((ev (ζ, e)) • x) ∂(mixedMulHaar K)
        = ∫ x in mixedEmbedding.fundamentalCone K,
            F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • ((ζ : (RingOfIntegers K)ˣ) • x))
              ∂(mixedMulHaar K) := by
          refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
          simp only [hcomm]
      _ = ∫ y in (fun y => (ζ : (RingOfIntegers K)ˣ) • y) ''
              mixedEmbedding.fundamentalCone K,
            F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • y) ∂(mixedMulHaar K) :=
          (hmp.setIntegral_image_emb ψ.measurableEmbedding
            (fun y => F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • y))
            (mixedEmbedding.fundamentalCone K)).symm
      _ = ∫ y in mixedEmbedding.fundamentalCone K,
            F ((coneUnitHom (K := K) (Multiplicative.ofAdd e)) • y) ∂(mixedMulHaar K) := by
          rw [himg]
      _ = Ã e := rfl
  -- Summability transported to the additive free part.
  have hsummableÃ : Summable Ã :=
    (Equiv.summable_iff (Multiplicative.ofAdd)).mpr hsummableA
  have htsumÃ : ∑' e, Ã e = ∫ x, F x ∂(mixedMulHaar K) :=
    (Equiv.tsum_eq (Multiplicative.ofAdd) A).trans htsumA
  letI : Fintype (torsion K) := Fintype.ofFinite (torsion K)
  -- Summability of the torsion-indexed family `(ζ, e) ↦ Ã e`.
  have hSumProd : Summable (fun p : torsion K × (Fin (rank K) → ℤ) => Ã p.2) := by
    have hsplit : (fun p : torsion K × (Fin (rank K) → ℤ) => Ã p.2)
        = fun p => ∑ ζ ∈ (Finset.univ : Finset (torsion K)),
            (fun q : torsion K × (Fin (rank K) → ℤ) => if q.1 = ζ then Ã q.2 else 0) p := by
      funext p
      simp
    rw [hsplit]
    apply summable_sum
    intro ζ _
    have hi : Function.Injective
        (fun e : (Fin (rank K) → ℤ) => ((ζ, e) : torsion K × (Fin (rank K) → ℤ))) := by
      intro a b h; simpa using h
    refine (Function.Injective.summable_iff hi ?_).mp ?_
    · intro q hq
      by_cases heq : q.1 = ζ
      · exact absurd ⟨q.2, by simp [← heq]⟩ hq
      · simp [heq]
    · have hcomp : ((fun q : torsion K × (Fin (rank K) → ℤ) =>
            if q.1 = ζ then Ã q.2 else 0) ∘ fun e => ((ζ, e) : torsion K × (Fin (rank K) → ℤ)))
          = Ã := by funext e; simp
      rw [hcomp]; exact hsummableÃ
  -- Reduce each unit term to a cone integral, then assemble.
  have hterm : ∀ u : (RingOfIntegers K)ˣ,
      (∫ x, (mixedEmbedding.fundamentalCone K).indicator
          (fun x => (mixedGaussian K
              (x * mixedEmbedding K
                (((u : RingOfIntegers K) * a₀ : RingOfIntegers K) : K)) : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ s) x ∂(mixedMulHaar K))
        = ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K) := by
    intro u
    rw [integral_indicator (measurableSet_fundamentalCone K)]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact (hF_smul u x).symm
  have hstep2 : (∑' u : (RingOfIntegers K)ˣ,
        ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K))
      = ∑' p : torsion K × (Fin (rank K) → ℤ), Ã p.2 := by
    rw [← Equiv.tsum_eq ev
        (fun u => ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K))]
    exact tsum_congr (fun p => hBev p)
  rw [tsum_congr hterm]
  calc ∑' u : (RingOfIntegers K)ˣ,
          ∫ x in mixedEmbedding.fundamentalCone K, F (u • x) ∂(mixedMulHaar K)
      = ∑' p : torsion K × (Fin (rank K) → ℤ), Ã p.2 := hstep2
    _ = ∑' (ζ : torsion K), ∑' (c : (Fin (rank K) → ℤ)), Ã (ζ, c).2 := hSumProd.tsum_prod
    _ = ∑' (_ : torsion K), ∫ x, F x ∂(mixedMulHaar K) :=
        tsum_congr (fun ζ => by simpa using htsumÃ)
    _ = (Fintype.card (torsion K) : ℂ) * ∫ x, F x ∂(mixedMulHaar K) := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Units.torsionOrder K : ℂ) * I K s
          * (Ideal.absNorm (Ideal.span {a₀}) : ℂ) ^ (-s) := by
        rw [hV, show (Units.torsionOrder K : ℂ) = (Fintype.card (torsion K) : ℂ) from by simp only [Units.torsionOrder, Nat.card_eq_fintype_card]]; ring
end DedekindZeta.GammaIntegral
