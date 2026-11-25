-- Prove2me | solution 1 for BayesianPersuasion.Examples.indifferent_tieRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:15.609969+00:00
-- url     : https://prove2.me/submissions/ab71e37e-47ca-4baa-b249-4f14363af26f

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples

set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17
namespace BayesianPersuasion.Examples
theorem _root_.solution : SenderPreferred judge prosecutor indifferent 1 := by
  constructor
  · intro b; fin_cases b <;> norm_num [expected, indifferent, bernoulli, judge, Fin.sum_univ_two]
  · intro b _; fin_cases b <;>
      norm_num [expected, indifferent, bernoulli, prosecutor, Fin.sum_univ_two]
end BayesianPersuasion.Examples
