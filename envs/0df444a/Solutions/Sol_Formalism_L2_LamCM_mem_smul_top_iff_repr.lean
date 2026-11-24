-- Prove2me | solution 1 for Formalism.L2.LamCM.mem_smul_top_iff_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:13:30.134684+00:00
-- url     : https://prove2.me/submissions/a5fbff88-a0f6-4350-bcd8-3db13b636fca

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open Polynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution {R M ι : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    (b : Module.Basis ι R M) (J : Ideal R) (x : M) :
    x ∈ J • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ J := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on (p := fun x => b.repr x i ∈ J) hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · simp only [map_add, Finsupp.add_apply]
      exact J.add_mem hx hy
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top
end Formalism.L2.LamCM
