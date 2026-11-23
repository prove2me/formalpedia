-- Prove2me | solution 1 for Formalism.HF.P.nrRealPlaces_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:44.083249+00:00
-- url     : https://prove2.me/submissions/99a9ab68-73d5-48f3-9810-47675daa3cf4

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution {E : Type} [Field E] [NumberField E] (x : E) (c : ℤ) (hc : c < 0)
    (hx : x ^ 2 = (c : E)) : nrRealPlaces E = 0 := by
  haveI : IsEmpty {w : InfinitePlace E // w.IsReal} := ⟨fun ⟨w, hw⟩ => by
    have h1 := congrArg (embedding_of_isReal hw) hx
    rw [map_pow, map_intCast] at h1
    have h2 : (0 : ℝ) ≤ (embedding_of_isReal hw x) ^ 2 := sq_nonneg _
    rw [h1] at h2
    have h3 : (c : ℝ) < 0 := by exact_mod_cast hc
    linarith⟩
  simp [nrRealPlaces]
end Formalism.HF.P
