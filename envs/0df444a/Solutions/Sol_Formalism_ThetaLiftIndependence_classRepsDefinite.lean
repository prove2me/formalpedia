-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.classRepsDefinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:34:20.976844+00:00
-- url     : https://prove2.me/submissions/d2bb1168-5381-42c9-a6f6-4df4070c9f07

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_ClassRepsDefinite
import Theorems.Thm_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_exists_reps
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_autFinite
import Theorems.Thm_Formalism_HermitianLatticesTheory_final_classSetFinite
import Theorems.Thm_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_latWt_gmap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ThetaLiftIndependence
open Formalism.HermitianLatticesTheory LatticeLiftIndependence DefiniteClassRepresentatives
namespace Formalism.ThetaLiftIndependence
theorem _root_.solution : ClassRepsDefinite := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos L hL
  classical

  have hcard : ∀ M ∈ genus h L, 0 < Nat.card (autL h M) := by
    intro M hM
    have hfin : Set.Finite (autL h M) := final_autFinite K V h hsymm hpos M hM.1
    have : Finite (autL h M) := hfin.to_subtype
    have : Nonempty (autL h M) := ⟨⟨1, (isom h).one_mem, gmap_one M⟩⟩
    exact Nat.card_pos
  obtain ⟨s₀, h₁, h₂⟩ := final_classSetFinite K V h hsymm hpos L hL
  obtain ⟨s, hs⟩ := exists_reps h L s₀ h₁ h₂
  refine ⟨⟨s, hs⟩, fun M hM => ⟨Nat.card (autL h M), hcard M hM, rfl⟩, ?_⟩
  refine ⟨∏ N ∈ s, Nat.card (autL h N), Finset.prod_pos fun N hN => hcard N (hs.1 N hN), ?_⟩
  intro M hM
  obtain ⟨N, ⟨hN, g, hg, e⟩, -⟩ := hs.2 M hM
  refine ⟨((∏ N' ∈ s.erase N, Nat.card (autL h N') : ℕ) : ℤ), ?_⟩
  rw [← e, latWt_gmap h hg N, ← Finset.mul_prod_erase s _ hN]
  have hne : ((Nat.card (autL h N) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (hcard N (hs.1 N hN)).ne'
  unfold latWt
  push_cast
  field_simp
end Formalism.ThetaLiftIndependence
