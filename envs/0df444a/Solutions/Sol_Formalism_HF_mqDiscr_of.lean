-- Prove2me | solution 1 for Formalism.HF.mqDiscr_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:39:26.154825+00:00
-- url     : https://prove2.me/submissions/2bdf92bc-ea9e-42d2-b075-74382e33fc7d

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_MQDiscr
import Theorems.Thm_Formalism_HF_P_not_isSquare_prod
import Theorems.Thm_Formalism_HF_P_nrRealPlaces_zero
import Theorems.Thm_Formalism_HF_P_natAbs_discr
import Theorems.Thm_Formalism_Q3_mqKummer


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
open Formalism Formalism.HF
namespace Formalism.HF
theorem _root_.solution (hQ : QuadDiscr) : MQDiscr := by
  intro k q hk hq hinj E _ _ α hMQ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hnat := P.natAbs_discr hQ m q hq hinj E α hMQ
  have hfin : Module.finrank ℚ E = 2 ^ (m + 1) :=
    (mqKummer (m + 1) E _ α hMQ (P.not_isSquare_prod q (fun i => (hq i).1) hinj)).1
  have hr : InfinitePlace.nrRealPlaces E = 0 :=
    P.nrRealPlaces_zero (α 0) (-(q 0 : ℤ)) (by have := (hq 0).1.pos; omega) (hMQ.1 0)
  have hc : InfinitePlace.nrComplexPlaces E = 2 ^ m := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank (K := E)
    rw [hr, hfin, pow_succ] at this
    linarith
  have hs : (discr E).sign = (-1) ^ (2 ^ m) := by rw [sign_discr, hc]
  rw [← Int.sign_mul_natAbs (discr E), hs, hnat]
  simp
end Formalism.HF
