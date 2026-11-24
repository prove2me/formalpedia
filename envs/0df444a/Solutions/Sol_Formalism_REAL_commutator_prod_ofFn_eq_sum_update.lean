-- Prove2me | solution 1 for Formalism.REAL.commutator_prod_ofFn_eq_sum_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:12.407773+00:00
-- url     : https://prove2.me/submissions/d7924ec6-1faa-48ae-bfa6-48ff45b2b42c

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
theorem _root_.solution {A : Type*} [Ring A] (X : A) : ∀ {t : ℕ} (F : Fin t → A),
    X * (List.ofFn F).prod - (List.ofFn F).prod * X =
      ∑ k, (List.ofFn (Function.update F k (X * F k - F k * X))).prod
  | 0, F => by simp
  | t + 1, F => by
    have ih := solution X (fun i : Fin t => F i.succ)
    rw [Fin.sum_univ_succ]
    have h0 : (List.ofFn (Function.update F 0 (X * F 0 - F 0 * X))).prod =
        (X * F 0 - F 0 * X) * (List.ofFn fun i : Fin t => F i.succ).prod := by
      simp [List.ofFn_succ, Function.update_apply, Fin.succ_ne_zero]
    have hs : ∀ k : Fin t, (List.ofFn (Function.update F k.succ (X * F k.succ - F k.succ * X))).prod =
        F 0 * (List.ofFn (Function.update (fun i : Fin t => F i.succ) k
          (X * F k.succ - F k.succ * X))).prod := by
      intro k
      have hf : (fun i : Fin t => Function.update F k.succ (X * F k.succ - F k.succ * X) i.succ) =
          Function.update (fun i : Fin t => F i.succ) k (X * F k.succ - F k.succ * X) := by
        funext i; simp [Function.update_apply, Fin.succ_inj]
      rw [List.ofFn_succ, List.prod_cons, hf]
      simp [Function.update_apply, (Fin.succ_ne_zero k).symm]
    rw [h0, Finset.sum_congr rfl (fun k _ => hs k), ← Finset.mul_sum, ← ih, List.ofFn_succ,
      List.prod_cons]
    noncomm_ring
end Formalism.REAL
