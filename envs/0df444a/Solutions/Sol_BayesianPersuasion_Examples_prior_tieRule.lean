-- Prove2me | solution 1 for BayesianPersuasion.Examples.prior_tieRule
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:07.095985+00:00
-- url     : https://prove2.me/submissions/18d72515-d746-4ea3-9478-bca31c3a7d2e

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
theorem _root_.solution : SenderPreferred judge prosecutor prior 0 := by
  constructor
  · intro b; fin_cases b <;> norm_num [expected, prior, bernoulli, judge, Fin.sum_univ_two]
  · intro b hb
    fin_cases b
    · exact le_rfl
    · have h := hb 0
      norm_num [expected, prior, bernoulli, judge, Fin.sum_univ_two] at h
end BayesianPersuasion.Examples
