-- Prove2me | solution 1 for BayesianPersuasion.Examples.judge_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:52.130228+00:00
-- url     : https://prove2.me/submissions/5839968e-2ea4-4373-916b-d48c6280fa41

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
theorem _root_.solution (ω : Fin 2) : Continuous (fun a => judge a ω) :=
  continuous_of_discreteTopology
end BayesianPersuasion.Examples
