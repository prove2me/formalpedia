-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.covolumeIndex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.750838+00:00
-- url     : https://prove2.me/submissions/7782ff36-ca3b-44cf-8524-524c2d05bc4d

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_lattice_of_index
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_map_zsub_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x5_finrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x5
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
open scoped Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.CovolumeIndex := by
  intro E _ _ _ B L c hB hc hBL hn
  have hinj : Function.Injective (emb E).toAddMonoidHom := (mixedEmbedding E).injective
  have hidx : ((zsub E B).map (emb E)).toAddSubgroup.relIndex (L.map (emb E)).toAddSubgroup
      = idx E (zsub E B) L := by
    unfold idx
    rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hle : (zsub E B).map (emb E) ≤ L.map (emb E) := Submodule.map_mono hBL
  rw [map_zsub_eq E B hB] at hidx hle
  have key := lattice_of_index (volume : Measure (mixedEmbedding.mixedSpace E))
    (mixedEmbedding.idealLattice E (Units.mk0 B hB)) (L.map (emb E)) hle (by rw [hidx]; exact hn)
    c hc
  refine ⟨key.1, key.2.1, ?_⟩
  have h1 : InfinitePlace.nrComplexPlaces E = deg E := by
    have h5 := IsTotallyComplex.finrank E
    have := finrank_eq E
    omega
  have h3 := key.2.2
  rw [hidx, mixedEmbedding.covolume_idealLattice, mixedEmbedding.finrank, finrank_eq E, h1] at h3
  unfold frameLat
  rw [h3]
  simp [mul_assoc]
end Formalism.FourierDecayAlt.P
