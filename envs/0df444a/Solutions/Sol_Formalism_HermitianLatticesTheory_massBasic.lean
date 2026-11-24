-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.massBasic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:25.225481+00:00
-- url     : https://prove2.me/submissions/01e623bd-2879-4a1a-ba72-a5e7d138441a

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic_sum_cast
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic_mass_eq
import Theorems.Thm_Formalism_HermitianLatticesTheory_massBasic_self_mem_genus
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_ThetaLiftIndependence_classRepsDefinite
import Theorems.Thm_Formalism_ThetaLiftIndependence_latLiftIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : MassBasic := by
  intro K V _ _ _ _ _ _ _ _ h hh hpos L hL
  obtain ⟨hex, hwt, -⟩ := Formalism.ThetaLiftIndependence.classRepsDefinite K V h hh hpos L hL
  refine ⟨hex, fun s hs => ?_, ?_⟩
  · rw [massBasic_mass_eq h L hex]
    have e := Formalism.ThetaLiftIndependence.latLiftIndep K V h L (fun _ => 1) (fun _ => 1)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _ hex.choose_spec hs
    rw [← massBasic_sum_cast, ← massBasic_sum_cast] at e
    exact_mod_cast e
  · rw [massBasic_mass_eq h L hex]
    obtain ⟨hmem, huniq⟩ := hex.choose_spec
    obtain ⟨N, ⟨hN, -⟩, -⟩ := huniq L (massBasic_self_mem_genus h L hL)
    apply Finset.sum_pos
    · intro M hM
      obtain ⟨n, hn, hnw⟩ := hwt M (hmem M hM)
      have hc : Nat.card (Formalism.ThetaLiftIndependence.autL h M) = n := by
        simp only [Formalism.ThetaLiftIndependence.latWt] at hnw
        exact_mod_cast inv_inj.mp hnw
      rw [hc]
      exact inv_pos.mpr (by exact_mod_cast hn)
    · exact ⟨N, hN⟩
end Formalism.HermitianLatticesTheory
