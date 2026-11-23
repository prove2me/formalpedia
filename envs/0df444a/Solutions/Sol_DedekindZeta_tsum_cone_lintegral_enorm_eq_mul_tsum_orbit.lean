-- Prove2me | solution 1 for DedekindZeta.tsum_cone_lintegral_enorm_eq_mul_tsum_orbit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:25:26.469575+00:00
-- url     : https://prove2.me/submissions/e2968f7c-0a0b-45e1-ba73-b3fd92f4bc01

import Mathlib
import Definitions.Def_DedekindZeta_Theta
import Definitions.Def_DedekindZeta_Statements
import Theorems.Thm_DedekindZeta_coneUnitHom_mem_torsion_iff
import Theorems.Thm_DedekindZeta_lintegral_enorm_mixedGaussian_mul_norm_cpow_eq
import Theorems.Thm_DedekindZeta_tsum_unit_lintegral_enorm_cone_eq_lintegral_whole
import Theorems.Thm_DedekindZeta_Theta_gaussVSchwartz_apply
import Theorems.Thm_DedekindZeta_Theta_mixedGaussianSchwartz_apply
attribute [local simp] DedekindZeta.Theta.gaussVSchwartz_apply
attribute [local simp] DedekindZeta.Theta.mixedGaussianSchwartz_apply



set_option autoImplicit true
open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors
open DedekindZeta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
open scoped NNReal ENNReal
namespace DedekindZeta
theorem _root_.solution
    (I : FractionalIdeal (𝓞 K)⁰ K) (t : ℂ) :
    (∑' a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0},
        ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K))
      = (∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
              * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K))
        * ∑' o : Quotient (MulAction.orbitRel
              (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
              {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
            ENNReal.ofReal
              (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re)) := by
  classical
  -- The cone-action group and the index set of nonzero elements of `I`.
  -- `coneFracSMul I` is a global instance, so the `MulAction` is available.
  -- Abbreviations are written out in full to keep instance resolution happy.
  -- `coneUnitHom` is injective: if `coneUnitHom a = coneUnitHom b` then
  -- `coneUnitHom (a*b⁻¹) = 1 ∈ torsion K`, so `a*b⁻¹ = 1` by
  -- `coneUnitHom_mem_torsion_iff`.
  have hcuh_inj : Function.Injective (coneUnitHom (K := K)) := by
    intro a b hab
    have h1 : coneUnitHom (K := K) (a * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : (coneUnitHom (K := K) (a * b⁻¹) : (𝓞 K)ˣ) ∈ NumberField.Units.torsion K := by
      rw [h1]; exact one_mem _
    have h3 := (coneUnitHom_mem_torsion_iff (K := K) (a * b⁻¹)).mp h2
    rwa [mul_inv_eq_one] at h3
  -- The cone action on `S`, unfolded, multiplies by `coneUnitHom g` in `K`.
  have hsmul : ∀ (g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      (a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
      (g • a).1 = ((coneUnitHom (K := K) g : 𝓞 K) : K) * a.1 := fun _ _ => rfl
  -- Freeness: `g • a = g' • a` with `a ≠ 0` forces `g = g'`.
  have hfree : ∀ {g g' : Multiplicative (Fin (NumberField.Units.rank K) → ℤ)}
      {a : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}},
      g • a = g' • a → g = g' := by
    intro g g' a h
    have hval : ((coneUnitHom (K := K) g : 𝓞 K) : K) * a.1
        = ((coneUnitHom (K := K) g' : 𝓞 K) : K) * a.1 := by
      rw [← hsmul, ← hsmul, h]
    have hk : ((coneUnitHom (K := K) g : 𝓞 K) : K)
        = ((coneUnitHom (K := K) g' : 𝓞 K) : K) := mul_right_cancel₀ a.2.2 hval
    apply hcuh_inj
    apply Units.ext
    exact_mod_cast hk
  -- The free-orbit reindexing equivalence `Σ (o : Ω), G ≃ S`.
  let F : (Σ _o : Quotient (MulAction.orbitRel
        (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
        {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}),
        Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      → {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} :=
    fun p => p.2 • Quotient.out p.1
  have hFsurj : Function.Surjective F := by
    intro a
    set o₀ := Quotient.mk (MulAction.orbitRel
      (Multiplicative (Fin (NumberField.Units.rank K) → ℤ))
      {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0}) a with ho₀
    have hrel : MulAction.orbitRel _ _ (Quotient.out o₀) a :=
      Quotient.exact (Quotient.out_eq o₀)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨c, hc⟩ := hrel
    refine ⟨⟨o₀, c⁻¹⟩, ?_⟩
    show c⁻¹ • Quotient.out o₀ = a
    rw [← hc, inv_smul_smul]
  have hFinj : Function.Injective F := by
    rintro ⟨o, g⟩ ⟨o', g'⟩ h
    have h' : g • Quotient.out o = g' • Quotient.out o' := h
    have hmem : Quotient.out o ∈ MulAction.orbit _ (Quotient.out o') :=
      MulAction.mem_orbit_iff.mpr ⟨g⁻¹ * g', by rw [mul_smul, ← h', inv_smul_smul]⟩
    have hoo : o = o' := by
      have hsound := Quotient.sound (MulAction.orbitRel_apply.mpr hmem)
      rwa [Quotient.out_eq, Quotient.out_eq] at hsound
    subst hoo
    have hgg : g = g' := hfree h'
    subst hgg
    rfl
  let E := Equiv.ofBijective F ⟨hFinj, hFsurj⟩
  -- Package the per-element cone-lintegral as `P`.
  set P : {a : K // a ∈ (I : Submodule (𝓞 K) K) ∧ a ≠ 0} → ℝ≥0∞ :=
    fun a => ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
        (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K a.1) : ℂ)
          * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K) with hP
  -- For each orbit `o`, the per-element sum over the orbit collapses (helper -4)
  -- to the whole-space lintegral, which (helper -2) is `ofReal (N^{-Re t}) * M`.
  have step : ∀ o, (∑' g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        P (E ⟨o, g⟩))
      = ENNReal.ofReal
          (mixedEmbedding.norm (mixedEmbedding K (Quotient.out o).1) ^ (-t.re))
        * ∫⁻ x, ‖(Theta.mixedGaussian K x : ℂ)
            * (mixedEmbedding.norm x : ℂ) ^ t‖ₑ ∂(mixedMulHaar K) := by
    intro o
    have hPeq : ∀ g : Multiplicative (Fin (NumberField.Units.rank K) → ℤ),
        P (E ⟨o, g⟩)
        = ∫⁻ x, ‖(mixedEmbedding.fundamentalCone K).indicator
            (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K (Quotient.out o).1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) x‖ₑ ∂(mixedMulHaar K) := by
      intro g
      have harg : ∀ y, y * mixedEmbedding K (E ⟨o, g⟩).1
          = (coneUnitHom (K := K) g • y) * mixedEmbedding K (Quotient.out o).1 := by
        intro y
        show y * mixedEmbedding K (((coneUnitHom (K := K) g : 𝓞 K) : K) * (Quotient.out o).1)
            = _
        rw [map_mul, NumberField.mixedEmbedding.unitSMul_smul]
        ring
      have hfun : (fun y => (Theta.mixedGaussian K (y * mixedEmbedding K (E ⟨o, g⟩).1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t)
          = (fun y => (Theta.mixedGaussian K
                ((coneUnitHom (K := K) g • y) * mixedEmbedding K (Quotient.out o).1) : ℂ)
              * (mixedEmbedding.norm y : ℂ) ^ t) := by
        funext y; rw [harg y]
      rw [hP]
      simp only [hfun]
    rw [tsum_congr hPeq,
      tsum_unit_lintegral_enorm_cone_eq_lintegral_whole K (Quotient.out o).1 t,
      lintegral_enorm_mixedGaussian_mul_norm_cpow_eq K (Quotient.out o).2.2 t]
  -- Reindex `∑' a : S` over the free orbits, then collapse each orbit and pull `M`.
  rw [← Equiv.tsum_eq E P, ENNReal.tsum_sigma', tsum_congr step,
    ENNReal.tsum_mul_right, mul_comm]
end DedekindZeta
