-- Prove2me | solution 1 for BalanceSpecification.isClosed_wordCylinder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:01.245641+00:00
-- url     : https://prove2.me/submissions/cedd1862-8b55-40d1-8e73-d83d92140695

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Forbidden

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A]
namespace BalanceSpecification
theorem _root_.solution (w : Word A) (k : ℤ) : IsClosed (wordCylinder w k) := by
  rw [wordCylinder_eq_iInter]
  apply isClosed_iInter
  intro i
  change IsClosed ((fun x : Configuration A => x (k + (i.val : ℤ))) ⁻¹'
    ({w[i.val]} : Set A))
  exact (isClosed_discrete _).preimage (continuous_apply _)
end BalanceSpecification
