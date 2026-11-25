-- Prove2me | solution 1 for BayesianPersuasion.Examples.prior_fullSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:52.763692+00:00
-- url     : https://prove2.me/submissions/157adb6a-5d7f-4ec1-9cb7-3ebb049a1849

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
theorem _root_.solution : FullSupport prior := by
  intro ω; fin_cases ω <;> norm_num [prior, bernoulli]
end BayesianPersuasion.Examples
