-- Prove2me | solution 1 for BayesianPersuasion.Examples.prosecutor_split_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:10:25.771362+00:00
-- url     : https://prove2.me/submissions/b548e009-3f08-416f-bc6c-89f6757c94ea

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
public import Theorems.Thm_BayesianPersuasion_Examples_innocent_payoff
public import Theorems.Thm_BayesianPersuasion_Examples_indifferent_payoff

set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17
namespace BayesianPersuasion.Examples
theorem _root_.solution : splitValue judge prosecutor weights beliefs = 3 / 5 := by
  simp [splitValue, Fin.sum_univ_two, beliefs, innocent_payoff, indifferent_payoff, weights, bernoulli]
end BayesianPersuasion.Examples
