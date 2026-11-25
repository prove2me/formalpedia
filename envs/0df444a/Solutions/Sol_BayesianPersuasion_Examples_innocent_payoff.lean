-- Prove2me | solution 1 for BayesianPersuasion.Examples.innocent_payoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:09:11.447872+00:00
-- url     : https://prove2.me/submissions/f407ebe9-0fec-4a84-9b59-1fc2990dd9d0

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
public import Theorems.Thm_BayesianPersuasion_Examples_judge_continuous
public import Theorems.Thm_BayesianPersuasion_Examples_prosecutor_continuous
public import Theorems.Thm_BayesianPersuasion_Examples_innocent_tieRule
public import Theorems.Thm_BayesianPersuasion_Proof_senderPayoff_eq


set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17
namespace BayesianPersuasion.Examples
theorem _root_.solution : senderPayoff judge prosecutor innocent = 0 := by
  rw [Proof.senderPayoff_eq judge prosecutor judge_continuous prosecutor_continuous innocent innocent_tieRule]
  norm_num [expected, prosecutor, innocent, bernoulli, Fin.sum_univ_two]
end BayesianPersuasion.Examples
