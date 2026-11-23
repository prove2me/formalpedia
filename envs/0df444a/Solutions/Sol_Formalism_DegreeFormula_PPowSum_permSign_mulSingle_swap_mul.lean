-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.permSign_mulSingle_swap_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:40.405337+00:00
-- url     : https://prove2.me/submissions/024d68dd-d6cf-42a6-8c91-4444f3b64377

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (a b : Fin N)
    (hab : a ≠ b) (σ : ι → Equiv.Perm (Fin N)) :
    sgnP (Pi.mulSingle τ (Equiv.swap a b) * σ) = -sgnP σ := by
  unfold sgnP
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  have h1 : ∏ t ∈ Finset.univ.erase τ,
      ((Equiv.Perm.sign ((Pi.mulSingle τ (Equiv.swap a b) * σ : ι → Equiv.Perm (Fin N)) t) : ℤ) : ℝ) =
      ∏ t ∈ Finset.univ.erase τ, ((Equiv.Perm.sign (σ t) : ℤ) : ℝ) := by
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase ht), one_mul]
  rw [h1, Pi.mul_apply, Pi.mulSingle_eq_same, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab]
  simp only [Units.val_mul, Units.val_neg, Units.val_one, Int.cast_mul, Int.cast_neg, Int.cast_one]
  ring
end Formalism.DegreeFormula.PPowSum
