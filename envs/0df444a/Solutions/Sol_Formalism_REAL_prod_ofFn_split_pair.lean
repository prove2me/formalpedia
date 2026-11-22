-- Prove2me | solution 1 for Formalism.REAL.prod_ofFn_split_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:09:52.944125+00:00
-- url     : https://prove2.me/submissions/99234a1d-f220-443f-ade1-d087917a0d11

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd

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
theorem _root_.solution {M : Type*} [Monoid M] {t : ℕ} (f : Fin t → M) (i : ℕ) (hi : i + 1 < t) :
    (List.ofFn f).prod = ((List.ofFn f).take i).prod * (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have h0 : i < (List.ofFn f).length := by simp; omega
  have h1 : i + 1 < (List.ofFn f).length := by simp; omega
  conv_lhs => rw [← List.take_append_drop i (List.ofFn f)]
  rw [List.prod_append, List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1,
    show i + 2 = i + 1 + 1 from rfl]
  simp only [List.prod_cons, List.getElem_ofFn, mul_assoc]
end Formalism.REAL
