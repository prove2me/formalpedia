-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_smul_top_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:25.920567+00:00
-- url     : https://prove2.me/submissions/12655066-0591-4058-a644-ab86f013f03b

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module
variable {O : Type} [CommRing O] [IsDedekindDomain O]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type} [CommRing R] (I : Ideal R) (n : ℕ) (x : Fin n → R) :
    x ∈ I • (⊤ : Submodule R (Fin n → R)) ↔ ∀ i, x i ∈ I := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ I) hx (fun r hr z _ i => ?_)
      (fun a b ha hb i => ?_)
    · exact I.mul_mem_right _ hr
    · exact I.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (hx i) trivial
end Formalism.HermitianLatticeCounting.P
