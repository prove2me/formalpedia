-- Prove2me | solution 1 for DedekindZeta.PoissonSummation.integral_fundamentalDomain_periodisation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:04:01.250475+00:00
-- url     : https://prove2.me/submissions/49b0eb09-8e35-4a57-af82-b5dff8dae9ee

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Theorems.Thm_DedekindZeta_PoissonSummation_mem_dualLattice

set_option autoImplicit true
open MeasureTheory Module
open scoped FourierTransform RealInnerProductSpace
open DedekindZeta DedekindZeta.PoissonSummation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
  (f : SchwartzMap V ℂ)
namespace DedekindZeta.PoissonSummation
theorem _root_.solution
    {D : Set V} (hD : IsAddFundamentalDomain (↥L.toAddSubgroup) D)
    (w : dualLattice L) :
    (∫ x in D, 𝐞 (-⟪x, (w : V)⟫) • periodisation L f x)
      = 𝓕 (f : V → ℂ) (w : V) := by
  classical
  haveI : Countable (↥L.toAddSubgroup) :=
    Countable.of_equiv (↥L)
      (Equiv.subtypeEquivRight (fun a => Submodule.mem_toAddSubgroup L)).symm
  have hf_int : Integrable (f : V → ℂ) := f.integrable
  have hg_int : Integrable (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) :=
    (Real.fourierIntegral_convergent_iff (w : V)).mpr hf_int
  have hchar : ∀ (γ : ↥L.toAddSubgroup) (x : V),
      𝐞 (-⟪(γ : V) + x, (w : V)⟫) = 𝐞 (-⟪x, (w : V)⟫) := by
    intro γ x
    have hmem : (γ : V) ∈ L := by
      have := γ.2; rwa [Submodule.mem_toAddSubgroup] at this
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (mem_dualLattice.mp w.2 (γ : V) hmem)
    have hn' : ⟪(w : V), (γ : V)⟫ = (n : ℝ) := by rw [← hn]; simp
    have hgw : ⟪(γ : V), (w : V)⟫ = (n : ℝ) := by rw [real_inner_comm]; exact hn'
    have hsplit : -⟪(γ : V) + x, (w : V)⟫ = -(n : ℝ) + -⟪x, (w : V)⟫ := by
      rw [inner_add_left, hgw]; ring
    have hen : (𝐞 (-(n : ℝ)) : Circle) = 1 := by
      rw [show (-(n : ℝ)) = (((-n : ℤ)) : ℝ) by push_cast; ring, Real.fourierChar_apply']
      exact Circle.exp_two_pi_mul_int (-n)
    rw [hsplit, AddChar.map_add_eq_mul, hen, one_mul]
  have hbody : ∀ (γ : ↥L.toAddSubgroup) (x : V),
      (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) (γ +ᵥ x)
        = 𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x) := by
    intro γ x; simp only [AddSubgroup.vadd_def, vadd_eq_add]; rw [hchar γ x]
  have hmeas : ∀ γ : ↥L.toAddSubgroup,
      AEStronglyMeasurable
        (fun x => 𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)) (volume.restrict D) := by
    intro γ
    refine Continuous.aestronglyMeasurable ?_
    have hinner : Continuous fun x : V => ⟪x, (w : V)⟫ := continuous_id.inner continuous_const
    exact (Real.continuous_fourierChar.comp hinner.neg).smul
      (f.continuous.comp (continuous_const.add continuous_id))
  have hnorm : ∀ (γ : ↥L.toAddSubgroup) (x : V),
      ‖𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)‖ₑ = ‖(f : V → ℂ) ((γ : V) + x)‖ₑ := by
    intro γ x; rw [enorm_eq_nnnorm, enorm_eq_nnnorm]; congr 1
    exact Subtype.ext (Circle.norm_smul _ _)
  have hfin : (∑' γ : ↥L.toAddSubgroup,
      ∫⁻ x in D, ‖𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume) ≠ (⊤ : ENNReal) := by
    have hcongr : (∑' γ : ↥L.toAddSubgroup,
          ∫⁻ x in D, ‖𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume)
        = ∑' γ : ↥L.toAddSubgroup, ∫⁻ x in D, ‖(f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume :=
      tsum_congr (fun γ => lintegral_congr (fun x => hnorm γ x))
    have h1 : (∑' γ : ↥L.toAddSubgroup, ∫⁻ x in D, ‖(f : V → ℂ) ((γ : V) + x)‖ₑ ∂volume)
        = ∫⁻ x, ‖(f : V → ℂ) x‖ₑ ∂volume := by
      rw [hD.lintegral_eq_tsum'' (fun v => ‖(f : V → ℂ) v‖ₑ)]
      simp only [AddSubgroup.vadd_def, vadd_eq_add]
    rw [hcongr, h1]; exact hf_int.hasFiniteIntegral.ne
  have hpt : ∀ x : V,
      (∑' γ : ↥L.toAddSubgroup, 𝐞 (-⟪x, (w : V)⟫) • (f : V → ℂ) ((γ : V) + x))
        = 𝐞 (-⟪x, (w : V)⟫) • periodisation L f x := by
    intro x
    rw [tsum_const_smul' (𝐞 (-⟪x, (w : V)⟫))]
    congr 1
    rw [periodisation_apply]
    rw [← (Equiv.subtypeEquivRight (fun a => Submodule.mem_toAddSubgroup L)).tsum_eq
          (fun v : ↥L => (f : V → ℂ) (x + (v : V)))]
    exact tsum_congr (fun γ => by rw [add_comm]; rfl)
  have e1 : 𝓕 (f : V → ℂ) (w : V)
      = ∑' γ : ↥L.toAddSubgroup, ∫ x in D,
          (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) (γ +ᵥ x) :=
    (Real.fourier_eq _ _).trans
      (hD.integral_eq_tsum'' (fun v => 𝐞 (-⟪v, (w : V)⟫) • (f : V → ℂ) v) hg_int)
  rw [e1]; symm; simp_rw [hbody]; rw [← integral_tsum hmeas hfin]; simp_rw [hpt]
end DedekindZeta.PoissonSummation
