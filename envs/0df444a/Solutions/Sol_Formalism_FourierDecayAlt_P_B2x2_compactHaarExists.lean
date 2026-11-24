-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.compactHaarExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:20.975807+00:00
-- url     : https://prove2.me/submissions/4bed7d08-9933-4ead-845e-a26f5f240d45

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_rmulF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_compl_null
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_haar_right_of_compact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x2
namespace Formalism.FourierDecayAlt.P.B2x2
theorem _root_.solution : CompactHaarExists := by
  intro k r U hU hc
  let S : Subgroup (Mat k r)ˣ :=
    { carrier := {u | (u : Mat k r) ∈ U}
      mul_mem' := fun {a b} ha hb => hU.mul_mem _ ha _ hb
      one_mem' := hU.one_mem
      inv_mem' := fun {a} ha => by
        show ((a⁻¹ : (Mat k r)ˣ) : Mat k r) ∈ U
        rw [Matrix.coe_units_inv]; exact hU.inv_mem _ ha }
  have hcS : IsCompact (S : Set (Mat k r)ˣ) := by
    have hK : IsCompact (U ×ˢ (MulOpposite.op '' U)) := hc.prod (hc.image MulOpposite.continuous_op)
    have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage hK
    have e : (S : Set (Mat k r)ˣ) = (Units.embedProduct (Mat k r)) ⁻¹' (U ×ˢ (MulOpposite.op '' U)) := by
      ext u
      constructor
      · intro hu
        exact ⟨hu, ⟨_, S.inv_mem hu, rfl⟩⟩
      · intro hu
        exact hu.1
    rw [e]; exact h
  have : CompactSpace S := isCompact_iff_compactSpace.mp hcS
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩
  let μ0 : Measure S := Measure.haar
  let j : S → Mt k r := fun s => ((s : (Mat k r)ˣ) : Mat k r)
  have hj0 : Continuous (fun s : S => ((s : (Mat k r)ˣ) : Mat k r)) := Units.continuous_val.comp continuous_subtype_val
  have hj : Continuous j := hj0
  have hjm : Measurable j := hj.measurable
  have lift : ∀ a ∈ U, ∃ s : S, j s = a := by
    intro a ha
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det a).2 (hU.unit a ha)
    exact ⟨⟨u, by show (u : Mat k r) ∈ U; rw [hu]; exact ha⟩, hu⟩
  refine ⟨μ0.map j, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · refine map_compl_null U hU.closed μ0 j hjm ?_
    have : {x : S | j x ∉ U} = ∅ := by
      ext s
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact s.2
    rw [this, measure_empty]
  · intro a ha
    obtain ⟨s, rfl⟩ := lift a ha
    rw [Measure.map_map (lmulM_cont _).measurable hjm]
    have : (lmulM (j s) ∘ j : S → Mt k r) = j ∘ (fun x => s * x) := by
      funext x; rfl
    rw [this, ← Measure.map_map hjm (measurable_const_mul s), map_mul_left_eq_self]
  · intro a ha
    obtain ⟨s, rfl⟩ := lift a ha
    rw [Measure.map_map (rmulF_cont _).measurable hjm]
    have : (rmulF (j s) ∘ j : S → Mt k r) = j ∘ (fun x => x * s) := by
      funext x; rfl
    rw [this, ← Measure.map_map hjm (measurable_mul_const s), haar_right_of_compact]
  · intro K hK
    rw [Measure.map_apply hjm hK.isClosed.measurableSet]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ _)) isCompact_univ.measure_lt_top
  · exact map_ne_zero μ0 j hjm (NeZero.ne μ0)
end Formalism.FourierDecayAlt.P.B2x2
