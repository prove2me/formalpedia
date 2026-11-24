-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x2.levHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:22.012977+00:00
-- url     : https://prove2.me/submissions/a0d77b18-473b-437f-835b-9c16991cb0c4

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_rmulF_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_blk_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_blk_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_levM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_lev_closed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_compl_null
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_map_ne_zero

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
theorem _root_.solution : LevHaar := by
  intro k r' U μ hU hμ
  have hright : ∀ u ∈ U, ιLev k 1 r' u * ιLev k 1 r' u⁻¹ = 1 := by
    intro u hu
    rw [← lev_mul, Matrix.mul_nonsing_inv u (hU.unit u hu), lev_one]
  have hinv : ∀ u ∈ U, (ιLev k 1 r' u)⁻¹ = ιLev k 1 r' u⁻¹ := fun u hu =>
    Matrix.inv_eq_right_inv (hright u hu)
  have hmeas : Measurable (levM k r') := (levM_cont k r').measurable
  refine ⟨⟨⟨1, hU.one_mem, lev_one k r'⟩, ?_, ?_, ?_, lev_closed k r' U hU.closed⟩, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact ⟨a * b, hU.mul_mem a ha b hb, lev_mul k r' a b⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, hU.inv_mem a ha, (hinv a ha).symm⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact Matrix.isUnit_det_of_right_inverse (hright a ha)
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · refine map_compl_null (ιLev k 1 r' '' U) (lev_closed k r' U hU.closed) μ (levM k r') hmeas
        (measure_mono_null ?_ hμ.conc)
      intro x hx hxU
      exact hx ⟨x, hxU, rfl⟩
    · rintro _ ⟨u, hu, rfl⟩
      rw [Measure.map_map (lmulM_cont _).measurable hmeas]
      have e : lmulM (ιLev k 1 r' u) ∘ levM k r' = levM k r' ∘ lmulM u := by
        funext x
        show ιLev k 1 r' u * ιLev k 1 r' (Matrix.of x) = ιLev k 1 r' (u * Matrix.of x)
        rw [lev_mul]
      rw [e, ← Measure.map_map hmeas (lmulM_cont u).measurable, hμ.left u hu]
    · rintro _ ⟨u, hu, rfl⟩
      rw [Measure.map_map (rmulF_cont _).measurable hmeas]
      have e : rmulF (ιLev k 1 r' u) ∘ levM k r' = levM k r' ∘ rmulF u := by
        funext x
        show ιLev k 1 r' (Matrix.of x) * ιLev k 1 r' u = ιLev k 1 r' (Matrix.of x * u)
        rw [lev_mul]
      rw [e, ← Measure.map_map hmeas (rmulF_cont u).measurable, hμ.right u hu]
    · intro K hK
      rw [Measure.map_apply hmeas hK.isClosed.measurableSet]
      calc μ (levM k r' ⁻¹' K) ≤ μ (blk k r' '' K) :=
            measure_mono (fun x hx => ⟨levM k r' x, hx, blk_lev k r' x⟩)
        _ < ∞ := hμ.finite_compact _ (hK.image (blk_cont k r'))
    · exact Formalism.FourierDecayAlt.P.B2x2.map_ne_zero μ (levM k r') hmeas hμ.ne_zero
end Formalism.FourierDecayAlt.P.B2x2
