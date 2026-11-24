-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.heisHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:23:08.154418+00:00
-- url     : https://prove2.me/submissions/1fa9ef46-b54b-4955-a6c7-ffbd5408f2b7

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_heisMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_coord_heis
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_continuous_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_isClosed_Hset
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_heisT
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5__Heis_eq_adc2ccc881fd
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B2x5_map__Heis_fdf4803780e5
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_lmulM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_rmulF
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_shear
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_herm_im_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x5_measurable_herm_im_right

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution : HeisHaar := by
  intro k r'
  have hcl : @IsClosed (Mt k (1 + r')) _ (Hset k r') := isClosed_Hset k r'
  have hmeasU : @MeasurableSet (Mt k (1 + r')) _ (Hset k r')ᶜ := hcl.measurableSet.compl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [μHeis_eq]
    exact (Measure.map_apply (measurable_heisT k r') hmeasU).trans
      (measure_mono_null (fun x hx => hx (Set.mem_range.mpr ⟨x, rfl⟩)) measure_empty)
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    refine map_μHeis k r' (measurable_lmulM _)
      (shear k r' (measurePreserving_add_left volume x.1) ((measurable_herm_im_left k r' x.1).const_sub x.2)) ?_
    intro y
    show heis0 k r' x * heis0 k r' y = heis0 k r' (x.1 + y.1, y.2 + (x.2 - (herm (Hpk k r') y.1 x.1).im))
    rw [heisMul]
    congr 2
    ring
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    refine map_μHeis k r' (measurable_rmulF _)
      (shear k r' (measurePreserving_add_left volume x.1) ((measurable_herm_im_right k r' x.1).const_sub x.2)) ?_
    intro y
    show heis0 k r' y * heis0 k r' x = heis0 k r' (x.1 + y.1, y.2 + (x.2 - (herm (Hpk k r') x.1 y.1).im))
    rw [heisMul]
    congr 2 <;> first | ring | abel
  · intro K hK
    have hK' : IsCompact (coord k r' '' (K : Set (Mat k (1 + r')))) := hK.image (continuous_coord k r')
    rw [μHeis_eq, Measure.map_apply (measurable_heisT k r') hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) hK'.measure_lt_top
    intro x hx
    exact ⟨heisT k r' x, hx, coord_heis k r' x⟩
  · rw [μHeis_eq]
    intro h
    rw [Measure.map_eq_zero_iff (measurable_heisT k r').aemeasurable] at h
    first
    | exact NeZero.ne _ h
    | exact (IsOpenPosMeasure.open_pos (μ := (volume : Measure (HPar k r'))) Set.univ isOpen_univ
        Set.univ_nonempty) (by rw [h]; rfl)
end Formalism.FourierDecayAlt.P.B2x5
