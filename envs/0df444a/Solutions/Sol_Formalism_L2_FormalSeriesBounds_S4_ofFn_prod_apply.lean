-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.S4.ofFn_prod_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:57:06.758082+00:00
-- url     : https://prove2.me/submissions/a0e2443f-b1e8-4234-95fe-5a1b84a28e8c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4
variable {R : Type*} [CommRing R]
namespace Formalism.L2.FormalSeriesBounds.S4
theorem _root_.solution {F : Type*} [AddCommGroup F] [Module R F] (g : F) :
    ∀ {m : ℕ} (E : Fin m → Module.End R F) (s : Fin m → R), (∀ i, E i g = s i • g) →
      (List.ofFn E).prod g = (∏ i, s i) • g := by
  intro m
  induction m with
  | zero =>
    intro E s _
    simp
  | succ m ih =>
    intro E s hE
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (fun i => E i.succ) (fun i => s i.succ) (fun i => hE i.succ), map_smul, hE 0, smul_smul,
      Fin.prod_univ_succ]
    congr 1
    ring
end Formalism.L2.FormalSeriesBounds.S4
