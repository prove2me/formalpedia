-- Prove2me | solution 1 for Formalism.REAL.prod_ofFn_update_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:35:57.737361+00:00
-- url     : https://prove2.me/submissions/f221eddf-fa44-4bdc-b669-d9a8e94bede0

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_prod_ofFn_update_eq_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] {t : ℕ} (F : Fin t → A) (k : Fin t) (p : Prop)
    [Decidable p] (x : A) :
    (List.ofFn (Function.update F k (if p then x else 0))).prod =
      if p then (List.ofFn (Function.update F k x)).prod else 0 := by
  by_cases hp : p
  · simp only [if_pos hp]
  · simp only [if_neg hp]
    obtain ⟨L, R, h⟩ := prod_ofFn_update_eq_mul F k
    rw [h, mul_zero, zero_mul]
end Formalism.REAL
