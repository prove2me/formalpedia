-- Prove2me | solution 1 for Formalism.REAL.prod_ofFn_update_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:13.768409+00:00
-- url     : https://prove2.me/submissions/7a21b931-9357-4a75-8e4e-ab0ebc29c3dc

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet

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
theorem _root_.solution {A : Type*} [Ring A] : ∀ {t : ℕ} (F : Fin t → A) (k : Fin t),
    ∃ L R : A, ∀ x : A, (List.ofFn (Function.update F k x)).prod = L * x * R
  | 0, _, k => k.elim0
  | t + 1, F, k => by
    refine Fin.cases ?_ (fun k' => ?_) k
    · refine ⟨1, (List.ofFn fun i : Fin t => F i.succ).prod, fun x => ?_⟩
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    · obtain ⟨L, R, h⟩ := solution (fun i : Fin t => F i.succ) k'
      refine ⟨F 0 * L, R, fun x => ?_⟩
      have hf : (fun i : Fin t => Function.update F k'.succ x i.succ) =
          Function.update (fun i : Fin t => F i.succ) k' x := by
        funext i; simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, hf, h]
      simp [Function.update_apply, (Fin.succ_ne_zero k').symm, mul_assoc]
end Formalism.REAL
