-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.orderedTermProduct_neg_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:52.047878+00:00
-- url     : https://prove2.me/submissions/3adb1c52-a65d-4f6b-9f12-8e466084fd76

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_term_neg_transpose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) :
    orderedTermProduct (fun a b => -E b a) arg σ τ = (-1) ^ n * orderedTermProduct E (fun k => -arg k) τ σ := by
  simp only [orderedTermProduct]
  have h : (fun k : Fin n => Tm (fun a b => -E b a) (arg k) (σ k) (τ k)) =
      fun k => -(Tm E (-arg k) (τ k) (σ k)) := funext fun k => term_neg_transpose E (arg k) (σ k) (τ k)
  rw [h, show (List.ofFn fun k => -(Tm E (-arg k) (τ k) (σ k))) =
      (List.ofFn fun k => Tm E (-arg k) (τ k) (σ k)).map Neg.neg by rw [List.map_ofFn]; rfl,
    List.prod_map_neg, List.length_ofFn]
end Formalism.HermitianLatticeCounting.P
