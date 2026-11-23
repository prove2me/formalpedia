-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sum_fin_succ_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:11:53.34169+00:00
-- url     : https://prove2.me/submissions/75ec1e9f-897d-44d0-8cf3-ece6c2c53913

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι M : Type} [Fintype ι] [AddCommMonoid M] (q : ℕ) (F : (Fin (q + 1) → ι) → M) :
    ∑ σ, F σ = ∑ τ : Fin q → ι, ∑ i : ι, F (Fin.cons i τ) := by
  rw [← (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (q + 1) => ι)) (fun p => F (Fin.cons p.1 p.2)) F
    (fun _ => rfl)), Fintype.sum_prod_type_right]
end Formalism.HermitianLatticeCounting.P
