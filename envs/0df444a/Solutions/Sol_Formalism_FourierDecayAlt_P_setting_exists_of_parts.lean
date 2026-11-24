-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.setting_exists_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:49:25.127751+00:00
-- url     : https://prove2.me/submissions/c3a0c6cf-ab72-40bf-a7b2-872764b7d341

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_haar_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleExists := by
  intro hG hW hN hS hχ hI hZ
  have hE : RealPlaceDataExists := by
    intro k r Wp Wq _ _ _ _ z z' p1 p2 hk hz hz' hT hT' hrep hrep' hu hu' hcn hcn'
    obtain ⟨μG, hμG⟩ := hG k r
    obtain ⟨μW, hμW⟩ := hW k r z hz hT
    obtain ⟨μN, hμN⟩ := hN k r
    obtain ⟨μW', hμW'⟩ := hW k r z' hz' hT'
    obtain ⟨μsec, hsec⟩ := hS k r z z' hk hz hz' hT hT'
    obtain ⟨χ, hχ1, hχ2, hχ3⟩ := hχ
    have md : IsMeasData k r z z' μsec μG μW μN μW' := ⟨hk, hz, hz', hT, hT', hμG, hμW, hμN, hμW', hsec⟩
    obtain ⟨c, ⟨hc0, hcF⟩, -⟩ := hI k r z z' μsec μG μW μN μW' md
    exact ⟨⟨z, z', p1, p2, c • μG, μW, μN, μW', μsec, χ, hk, hz, hz', hT, hT', hrep, hrep', hu, hu', hcn, hcn',
      SettingConstruction.haar_smul hμG c hc0, hμW, hμN, hμW', hsec, hχ1, hχ2, hχ3⟩, rfl, rfl, rfl, rfl, hcF⟩
  refine ⟨hE, ?_⟩
  intro k r hk
  obtain ⟨hzm, hzT⟩ := hZ k r
  have hrep : IsCRepOn (UWset k r (bvec (wI k r (Fin.last k)))) (fun _ : Mat k r => (1 : ℂ →L[ℂ] ℂ)) := by
    refine ⟨rfl, fun a _ b _ => ?_⟩
    ext; simp
  have hT : 0 < Tz k r (bvec (wI k r (Fin.last k))) := by rw [hzT]; norm_num
  obtain ⟨D, -, -, -, -, hD⟩ := hE k r ℂ ℂ _ _ (fun _ => 1) (fun _ => 1) hk hzm hzm hT hT hrep hrep
    (fun _ _ v => by simp) (fun _ _ v => by simp) continuousOn_const continuousOn_const
  exact ⟨D, hD⟩
end Formalism.FourierDecayAlt.P
