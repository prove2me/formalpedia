-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.rem_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:40.682852+00:00
-- url     : https://prove2.me/submissions/17891815-d1eb-4a14-b411-835a60998516

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_permExp_apply
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_mulSingle_mul_apply

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
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (σ : ι → Equiv.Perm (Fin N)) (τ : ι)
    (k : ℕ) (j j' : Fin N) (hj : (j' : ℕ) = j + k) (hne : j ≠ j') :
    permExp (Pi.mulSingle τ (Equiv.swap j j') * σ) - Finsupp.single (τ, (σ τ).symm j') k =
      permExp σ - Finsupp.single (τ, (σ τ).symm j) k := by
  have hne' : (j : ℕ) ≠ j' := fun h => hne (Fin.ext h)
  ext ⟨t, i⟩
  simp only [Finsupp.coe_tsub, Pi.sub_apply, permExp_apply, mulSingle_mul_apply, Finsupp.single_apply,
    Prod.mk.injEq, Equiv.symm_apply_eq, Equiv.swap_apply_def]
  by_cases ht : t = τ
  · subst ht
    by_cases h1 : σ t i = j
    · simp [h1, hne, Ne.symm hne] <;> omega
    · by_cases h2 : σ t i = j'
      · simp [h2, hne, Ne.symm hne] <;> omega
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp [ht, Ne.symm ht]
end Formalism.DegreeFormula.PPowSum
