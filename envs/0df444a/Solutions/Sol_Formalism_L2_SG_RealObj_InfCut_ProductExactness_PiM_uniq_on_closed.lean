-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM.uniq_on_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:42.11653+00:00
-- url     : https://prove2.me/submissions/16498026-b50e-49be-8e6b-079b275c4811

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_LintegralFinProd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_PiMapMulRight
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_ProductExactness_PiM_exists_pos_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.ProductExactness Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (H : Subgroup G) (hH : IsClosed (H : Set G)) (μ ν : Measure G)
    [SigmaFinite μ] [SigmaFinite ν] (hμc : μ (H : Set G)ᶜ = 0) (hνc : ν (H : Set G)ᶜ = 0)
    (hμi : ∀ h ∈ H, μ.map (fun x => h * x) = μ) (hνi : ∀ h ∈ H, ν.map (fun x => h * x) = ν) (hμ0 : μ ≠ 0)
    (hν0 : ν ≠ 0) : ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ = κ • ν := by
  classical
  have hHm : MeasurableSet (H : Set G) := hH.measurableSet
  have he : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hHm
  have hback : ∀ (m : Measure G), m (H : Set G)ᶜ = 0 →
      (m.comap (Subtype.val : H → G)).map Subtype.val = m := by
    intro m hm
    rw [he.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    convert hm using 2
    ext x
    simp
  have hinv : ∀ (m : Measure G), (∀ h ∈ H, m.map (fun x => h * x) = m) →
      (m.comap (Subtype.val : H → G)).IsMulLeftInvariant := by
    intro m hm
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (measurable_const_mul g) hs, he.comap_apply, he.comap_apply]
    have himg : Subtype.val '' ((fun x : H => g * x) ⁻¹' s) =
        (fun x : G => (g : G) * x) ⁻¹' (Subtype.val '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g * y, hy, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        have hx : x ∈ H := by
          have hx' : x = (g : G)⁻¹ * (y : G) := by rw [hxy, inv_mul_cancel_left]
          rw [hx']
          exact H.mul_mem (H.inv_mem g.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        have hgy : g * (⟨x, hx⟩ : H) = y := Subtype.ext (by rw [Subgroup.coe_mul]; exact hxy.symm)
        rw [hgy]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (g : G)) (he.measurableSet_image.2 hs),
      hm g g.2]
  have hsf : ∀ (m : Measure G) [SigmaFinite m], m (H : Set G)ᶜ = 0 →
      SigmaFinite (m.comap (Subtype.val : H → G)) := by
    intro m _ hm
    refine SigmaFinite.of_map _ he.measurable.aemeasurable ?_
    rw [hback m hm]
    infer_instance
  have hne : ∀ (m : Measure G), m (H : Set G)ᶜ = 0 → m ≠ 0 → m.comap (Subtype.val : H → G) ≠ 0 := by
    intro m hm h0 h
    apply h0
    rw [← hback m hm, h, Measure.map_zero]
  haveI := hsf μ hμc
  haveI := hsf ν hνc
  haveI := hinv μ hμi
  haveI := hinv ν hνi
  obtain ⟨t, -, htν0, htνi⟩ := exists_pos_fin (ν.comap (Subtype.val : H → G)) (hne ν hνc hν0)
  obtain ⟨t', -, htμ0, htμi⟩ := exists_pos_fin (μ.comap (Subtype.val : H → G)) (hne μ hμc hμ0)
  haveI : BorelSpace H := Subtype.borelSpace _
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : MeasurableMul₂ H := ContinuousMul.measurableMul₂
  haveI : MeasurableInv H := ContinuousInv.measurableInv
  have key := measure_eq_div_smul (μ.comap (Subtype.val : H → G)) (ν.comap (Subtype.val : H → G)) htν0 htνi
  set κ := μ.comap (Subtype.val : H → G) t / ν.comap (Subtype.val : H → G) t with hκ
  have hval := congrArg (fun m : Measure H => m t') key
  simp only [Measure.smul_apply, smul_eq_mul] at hval
  refine ⟨κ, ?_, ?_, ?_⟩
  · intro h0
    rw [h0, zero_mul] at hval
    exact htμ0 hval
  · intro hi
    rw [hi] at hval
    by_cases h : ν.comap (Subtype.val : H → G) t' = 0
    · rw [h, mul_zero] at hval
      exact htμ0 hval
    · rw [ENNReal.top_mul h] at hval
      exact htμi hval
  · conv_lhs => rw [← hback μ hμc, key]
    rw [Measure.map_smul, hback ν hνc]
end Formalism.L2.SG.RealObj.InfCut.ProductExactness.PiM
