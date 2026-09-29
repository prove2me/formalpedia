-- Prove2me | solution 1 for BraidsLinksMCG.fadellNeuwirth_range_eq_ker
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T19:54:12.248117+00:00
-- url     : https://prove2.me/submissions/8d0f7379-3ea5-47f5-ad55-502e58d454b6

import Theorems.Thm_BraidsLinksMCG_fadellNeuwirth_ker_le_range
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace ExactSol

variable (n : ℕ)

/-- Forgetting the last point of `(1, …, n, z)` gives the base configuration,
whatever `z` is: the composite of the two Fadell--Neuwirth maps is constant. -/
lemma forget_incl_const (z : PuncturedPlane n) :
    configForget n (configIncl n z) = baseOrdered n := by
  apply Subtype.ext
  funext i
  show Fin.snoc (α := fun _ => ℂ) (fun k : Fin n => ((k : ℕ) + 1 : ℂ)) z.1 i.castSucc
    = ((i : ℕ) + 1 : ℂ)
  rw [Fin.snoc_castSucc]

theorem range_le_ker :
    (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range ≤
      (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker := by
  rintro x ⟨y, rfl⟩
  rw [MonoidHom.mem_ker]
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (FundamentalGroup.toPath y)
  have hy : FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _) = y :=
    congrArg FundamentalGroup.fromPath hQ
  rw [← hy]
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  have hpath :
      ((((Q.map (configIncl n).continuous).cast (configIncl_base n).symm
          (configIncl_base n).symm).map (configForget n).continuous).cast
          (configForget_base n).symm (configForget_base n).symm)
        = Path.refl (baseOrdered n) := by
    refine DFunLike.ext _ _ fun t => ?_
    exact forget_incl_const n (Q t)
  show FundamentalGroup.fromPath
      (⟦(((Q.map (configIncl n).continuous).cast (configIncl_base n).symm
        (configIncl_base n).symm).map (configForget n).continuous).cast
        (configForget_base n).symm (configForget_base n).symm⟧
      : Path.Homotopic.Quotient _ _) = 1
  rw [hpath]
  rfl

end ExactSol


theorem _root_.solution (n : ℕ) :
    (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range =
      (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker :=
  le_antisymm (ExactSol.range_le_ker n) (BraidsLinksMCG.fadellNeuwirth_ker_le_range n)

#print axioms solution
