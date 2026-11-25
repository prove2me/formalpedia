-- Prove2me | solution 1 for BayesianPersuasion.Examples.prosecutor_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:48.832164+00:00
-- url     : https://prove2.me/submissions/eed1fffd-1d12-4bf0-a4af-43d05ece3eaf

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
theorem _root_.solution (ω : Fin 2) : Continuous (fun a => prosecutor a ω) :=
  continuous_of_discreteTopology
end BayesianPersuasion.Examples
