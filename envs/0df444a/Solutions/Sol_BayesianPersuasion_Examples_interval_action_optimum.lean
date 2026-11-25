-- Prove2me | solution 1 for BayesianPersuasion.Examples.interval_action_optimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:15:01.46528+00:00
-- url     : https://prove2.me/submissions/4100f02c-f233-430a-bc88-7ad1b768d6fc

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
public import Theorems.Thm_BayesianPersuasion_Examples_prior_fullSupport
public import Theorems.Thm_BayesianPersuasion_Proof_optimal_signal


set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17
namespace BayesianPersuasion.Examples
theorem _root_.solution :
    ∃ (n : ℕ) (_ : n ≤ 4) (π : Signal (Fin 2) n),
      signalValue quadraticReceiver linearSender prior π =
        concavification quadraticReceiver linearSender prior.val ∧
      ∀ (m : ℕ) (σ : Signal (Fin 2) m),
        signalValue quadraticReceiver linearSender prior σ ≤
          signalValue quadraticReceiver linearSender prior π := by
  have hu : ∀ ω, Continuous (fun a => quadraticReceiver a ω) := by
    intro ω; unfold quadraticReceiver; fun_prop
  have hv : ∀ ω, Continuous (fun a => linearSender a ω) := by
    intro ω; exact continuous_subtype_val
  simpa using Proof.optimal_signal quadraticReceiver linearSender hu hv prior prior_fullSupport
end BayesianPersuasion.Examples
