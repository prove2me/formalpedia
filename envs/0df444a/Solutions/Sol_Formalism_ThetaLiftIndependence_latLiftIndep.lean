-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.latLiftIndep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:47:30.63278+00:00
-- url     : https://prove2.me/submissions/456c5932-1f57-48a8-a9bf-6e9a19cfb227

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_LatLiftIndep
import Theorems.Thm_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_latWt_gmap
import Theorems.Thm_Formalism_ThetaLiftIndependence_LatticeLiftIndependence_reps_inv

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
open Formalism.HermitianLatticesTheory LatticeLiftIndependence
namespace Formalism.ThetaLiftIndependence
theorem _root_.solution : LatLiftIndep := by
  intro K V _ _ _ _ _ _ _ h L f Θ hf hΘ s s' hs hs'
  classical
  have ex : ∀ {t t' : Finset (Submodule (NumberField.RingOfIntegers K) V)},
      IsClassReps h L t → IsClassReps h L t' → ∀ N ∈ t,
        ∃ N', N' ∈ t' ∧ ∃ g ∈ isom h, gmap g N' = N :=
    fun ht ht' N hN => (ht'.2 N (ht.1 N hN)).exists
  let i : ∀ N ∈ s, Submodule (NumberField.RingOfIntegers K) V :=
    fun N hN => Classical.choose (ex hs hs' N hN)
  let j : ∀ N ∈ s', Submodule (NumberField.RingOfIntegers K) V :=
    fun N hN => Classical.choose (ex hs' hs N hN)
  have hi : ∀ N (hN : N ∈ s), i N hN ∈ s' ∧ ∃ g ∈ isom h, gmap g (i N hN) = N :=
    fun N hN => Classical.choose_spec (ex hs hs' N hN)
  have hj : ∀ N (hN : N ∈ s'), j N hN ∈ s ∧ ∃ g ∈ isom h, gmap g (j N hN) = N :=
    fun N hN => Classical.choose_spec (ex hs' hs N hN)
  unfold latLift
  refine Finset.sum_bij' i j (fun N hN => (hi N hN).1) (fun N hN => (hj N hN).1) ?_ ?_ ?_
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hi N hN
    obtain ⟨-, g', hg', e'⟩ := hj (i N hN) (hi N hN).1
    exact reps_inv h L hs hN (hj _ (hi N hN).1).1 hg hg' e e'
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hj N hN
    obtain ⟨-, g', hg', e'⟩ := hi (j N hN) (hj N hN).1
    exact reps_inv h L hs' hN (hi _ (hj N hN).1).1 hg hg' e e'
  · intro N hN
    obtain ⟨-, g, hg, e⟩ := hi N hN
    conv_lhs => rw [← e]
    rw [latWt_gmap h hg, hf g hg, hΘ g hg]
end Formalism.ThetaLiftIndependence
