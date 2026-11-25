-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.sumsq_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:32:22.541751+00:00
-- url     : https://prove2.me/submissions/372a1ad5-595a-42f7-b65e-13f282cacc5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerConv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerSum
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_bound
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Fk_continuous
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_conv_integral
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_gvec_continuous
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_gvec_inner
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_gvec_norm
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_kF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {μS ν : Measure G} (hS : IsHaarSub S μS) [SFinite ν] {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (hWc : Continuous W) (hW1 : ∫⁻ x, ‖W x‖ₑ ∂ν < ⊤) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S)
    (hfin : μS Ω < ⊤) :
    ((∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2 : ℝ) : ℂ) =
      ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
  have hS' := hS
  obtain ⟨-, -, hSmul, hSinv, hSig, -, -, -, -, -, -⟩ := hS'
  haveI : SigmaFinite μS := hSig
  haveI : IsFiniteMeasure (μS.restrict Ω) := isFiniteMeasure_restrict.mpr hfin.ne
  have hleft : ∀ (μ : Measure G) (f : G → PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH)),
      Integrable f μ → ∀ c, ⟪∫ x, f x ∂μ, c⟫_ℂ = ∫ x, ⟪f x, c⟫_ℂ ∂μ := by
    intro μ f hf c
    rw [← inner_conj_symm, ← integral_inner hf, ← integral_conj]
    simp_rw [inner_conj_symm]
  set g := gvec σ w W with hg
  have hgc : Continuous g := gvec_continuous hσ w hWc
  have hWn : ∀ s ∈ S, ∀ x, ‖W (s * x)‖ = ‖W x‖ := by
    intro s hs x
    rw [hWeq s hs x]
    have h := hτu s hs (W x) (W x)
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖τ s (W x)‖ ^ 2 = ‖W x‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'
  have hgn : ∀ s ∈ Ω, ∀ z, ‖g (s⁻¹ * z)‖ = ‖W z‖ := by
    intro s hs z
    rw [hg, gvec_norm hσ hw]
    exact hWn s⁻¹ (hSinv s (hΩS hs)) z
  have hgint : ∀ z, Integrable (fun s => g (s⁻¹ * z)) (μS.restrict Ω) := by
    intro z
    refine Integrable.mono' (integrable_const ‖W z‖) ?_ ?_
    · exact (hgc.comp (continuous_inv.mul continuous_const)).aestronglyMeasurable
    · exact (ae_restrict_iff' hΩm).mpr (Filter.Eventually.of_forall fun s hs => (hgn s hs z).le)
  set F : G → PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
    fun z => ∫ s in Ω, g (s⁻¹ * z) ∂μS with hF
  have hWi : Integrable W ν := ⟨hWc.aestronglyMeasurable, hW1⟩
  have hWint : Integrable (fun z => ‖W z‖) ν := hWi.norm
  have hFint : Integrable F ν := by
    refine Integrable.mono' (hWint.const_mul (μS.real Ω)) ?_ ?_
    · have hsm : StronglyMeasurable (Function.uncurry fun (z s : G) => g (s⁻¹ * z)) := by
        apply Continuous.stronglyMeasurable
        exact hgc.comp ((continuous_snd.inv).mul continuous_fst)
      exact (hsm.integral_prod_right (ν := μS.restrict Ω)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      have h1 := norm_integral_le_of_norm_le_const (μ := μS.restrict Ω) (f := fun s => g (s⁻¹ * z))
        (C := ‖W z‖) ((ae_restrict_iff' hΩm).mpr (Filter.Eventually.of_forall fun s hs => (hgn s hs z).le))
      calc ‖F z‖ ≤ ‖W z‖ * (μS.restrict Ω).real Set.univ := h1
        _ = μS.real Ω * ‖W z‖ := by
          simp only [Measure.real, Measure.restrict_apply_univ]
          ring
  have hY : ∀ i, (∫ z, F z ∂ν).ofLp i = yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i) := by
    intro i
    have h1 := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (Module.finrank ℂ V) => HH) i).integral_comp_comm hFint
    simp only [PiLp.proj_apply] at h1
    rw [← h1]
    unfold yv
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have h2 := (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin (Module.finrank ℂ V) => HH) i).integral_comp_comm
      (hgint z)
    simp only [PiLp.proj_apply] at h2
    simp only [hF]
    rw [← h2]
    simp [hg, gvec]
  have hr : (∑ i, ‖yv μS ν σ w W Ω (stdOrthonormalBasis ℂ V i)‖ ^ 2) = ‖∫ z, F z ∂ν‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [hY]
  rw [hr]
  push_cast
  refine (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∫ z, F z ∂ν)).symm.trans ?_
  calc ⟪∫ z, F z ∂ν, ∫ z, F z ∂ν⟫_ℂ = ∫ z, ⟪F z, ∫ z', F z' ∂ν⟫_ℂ ∂ν := hleft ν F hFint _
    _ = ∫ z, ∫ z', ⟪F z, F z'⟫_ℂ ∂ν ∂ν := by
        congr 1
        funext z
        exact (integral_inner hFint _).symm
    _ = ∫ z, ∫ z', ∫ q, (cnt μS Ω q).toReal • Fk σ w W z z' q ∂μS ∂ν ∂ν := by
        congr 1
        funext z
        congr 1
        funext z'
        have hae : ∀ᵐ p ∂((μS.restrict Ω).prod (μS.restrict Ω)), p ∈ Ω ×ˢ Ω := by
          rw [Measure.prod_restrict]
          exact ae_restrict_mem (hΩm.prod hΩm)
        have hint : Integrable (fun p : G × G => Fk σ w W z z' (p.1 * p.2⁻¹))
            ((μS.restrict Ω).prod (μS.restrict Ω)) := by
          refine Integrable.mono' (integrable_const (‖W z‖ * ‖W z'‖)) ?_ ?_
          · exact (Fk_continuous hσ w hWc (a := fun _ => z) (b := fun _ => z')
              (c := fun p : G × G => p.1 * p.2⁻¹) continuous_const continuous_const
              (continuous_fst.mul continuous_snd.inv)).aestronglyMeasurable
          · exact hae.mono fun p hp =>
              Fk_bound hσ hw hWeq hτu z z' (hSmul _ (hΩS hp.1) _ (hSinv _ (hΩS hp.2)))
        calc ⟪F z, F z'⟫_ℂ = ∫ s in Ω, ⟪g (s⁻¹ * z), F z'⟫_ℂ ∂μS := hleft _ _ (hgint z) _
          _ = ∫ s in Ω, ∫ t in Ω, ⟪g (s⁻¹ * z), g (t⁻¹ * z')⟫_ℂ ∂μS ∂μS := by
              congr 1
              funext s
              exact (integral_inner (hgint z') _).symm
          _ = ∫ s in Ω, ∫ t in Ω, Fk σ w W z z' (s * t⁻¹) ∂μS ∂μS := by
              refine setIntegral_congr_fun hΩm fun s hs => ?_
              congr 1
              funext t
              rw [hg, gvec_inner]
              exact kF hσ w hSinv hWeq hτu z z' (hΩS hs)
          _ = _ := conv_integral hS hΩm hΩS hfin _
              (Fk_continuous hσ w hWc (a := fun _ => z) (b := fun _ => z') (c := fun q => q)
                continuous_const continuous_const continuous_id).stronglyMeasurable hint
end Formalism.L2.S.Pv.EnergyAbs
