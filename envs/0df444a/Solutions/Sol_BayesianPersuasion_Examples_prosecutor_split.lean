-- Prove2me | solution 1 for BayesianPersuasion.Examples.prosecutor_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:08:21.077727+00:00
-- url     : https://prove2.me/submissions/0e532a78-649d-4cc5-98a7-2e99c721af1f

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
theorem _root_.solution : BayesPlausible prior weights beliefs := by
  intro ω
  fin_cases ω <;> norm_num [Fin.sum_univ_two, weights, beliefs, prior, innocent, indifferent, bernoulli]
end BayesianPersuasion.Examples
