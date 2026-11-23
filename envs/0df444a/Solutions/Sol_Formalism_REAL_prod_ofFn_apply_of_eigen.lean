-- Prove2me | solution 1 for Formalism.REAL.prod_ofFn_apply_of_eigen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:13.351807+00:00
-- url     : https://prove2.me/submissions/90940ea7-a342-46f9-94df-d5cffb78713e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds

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
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V),
      (∀ k, F k v = c k • v) → (List.ofFn F).prod v = (∏ k, c k) • v := by
  intro m
  induction m with
  | zero => intro F c v _; simp
  | succ m ih =>
    intro F c v h
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (fun i => F i.succ) (fun i => c i.succ) v (fun i => h i.succ), map_smul, h 0, smul_smul,
      Fin.prod_univ_succ, mul_comm (c 0)]
end Formalism.REAL
