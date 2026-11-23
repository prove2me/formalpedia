-- Prove2me | solution 1 for Formalism.DegreeFormula.PFlagDeg.prod_perm_rev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:55.775337+00:00
-- url     : https://prove2.me/submissions/0558f3c4-20cf-45ad-851d-73863e8fb1e6

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_FlagDeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open Formalism Formalism.DegreeFormula
open Formalism.DegreeFormula.PFlagDeg
namespace Formalism.DegreeFormula.PFlagDeg
theorem _root_.solution {M : Type*} [CommMonoid M] {N : ℕ} (s : Equiv.Perm (Fin N)) (g : ℕ → M) :
    ∏ i : Fin N, g (N - 1 - ((s i : Fin N) : ℕ)) = ∏ i : Fin N, g (i : ℕ) := by
  rw [Equiv.prod_comp s (fun j : Fin N => g (N - 1 - (j : ℕ)))]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  congr 1
  omega
end Formalism.DegreeFormula.PFlagDeg
