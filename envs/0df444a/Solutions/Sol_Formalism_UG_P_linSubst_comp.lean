-- Prove2me | solution 1 for Formalism.UG.P.linSubst_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:56.730491+00:00
-- url     : https://prove2.me/submissions/8a69bb17-2007-4560-b430-6c2403b6432a

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Actions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix MvPolynomial
namespace Formalism.UG.P
theorem _root_.solution (O : Type) [CommRing O] (n : Type) [Fintype n] [DecidableEq n]
    (M N : Matrix n n O) :
    (Formalism.UG.linSubst O n M).comp (Formalism.UG.linSubst O n N) = Formalism.UG.linSubst O n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [Formalism.UG.linSubst, AlgHom.comp_apply, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp only [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
end Formalism.UG.P
