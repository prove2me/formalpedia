-- Prove2me | solution 1 for BayesianPersuasion.Examples.prosecutor_strict_gain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:11:26.396442+00:00
-- url     : https://prove2.me/submissions/cde8d11d-7dd0-473a-afdf-b63e81ac4550

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
public import Theorems.Thm_BayesianPersuasion_Examples_prior_fullSupport
public import Theorems.Thm_BayesianPersuasion_Examples_prior_payoff
public import Theorems.Thm_BayesianPersuasion_Examples_prosecutor_split
public import Theorems.Thm_BayesianPersuasion_Examples_prosecutor_split_value
public import Theorems.Thm_BayesianPersuasion_Proof_splitting_payoff


set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17
namespace BayesianPersuasion.Examples
theorem _root_.solution :
    ∃ π : Signal (Fin 2) 2,
      signalValue judge prosecutor prior π = 3 / 5 ∧
      senderPayoff judge prosecutor prior < signalValue judge prosecutor prior π := by
  let π := splittingSignal prior prior_fullSupport weights beliefs prosecutor_split
  have hπ : signalValue judge prosecutor prior π = 3 / 5 :=
    (Proof.splitting_payoff prior prior_fullSupport weights beliefs prosecutor_split
      (senderPayoff judge prosecutor)).trans prosecutor_split_value
  exact ⟨π, hπ, by rw [prior_payoff, hπ]; norm_num⟩
end BayesianPersuasion.Examples
