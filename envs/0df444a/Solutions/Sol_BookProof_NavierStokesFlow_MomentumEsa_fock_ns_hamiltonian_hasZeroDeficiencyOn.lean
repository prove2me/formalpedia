-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:46.273037+00:00
-- url     : https://prove2.me/submissions/c716ecbb-6fa1-435e-85c0-c98b691566d4

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_hasZeroDeficiencyOn_of_esa_core
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fock_ns_hamiltonian_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k)
    (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config)
    (Hc : lpFiniteModes Config →ₗ[ℂ] lpFiniteModes Config)
    (hHc : ∀ x : lpFiniteModes Config, ((Hc x : lpFiniteModes Config) : L2I Config)
      = H (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)) x))
    (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (fockSymbol n)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (fockSymbol n),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (fockSymbol n) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2)
    (hcomm : ∀ x : maxDom (fockSymbol n),
      |commForm H (diagMax (fockSymbol n)) x| ≤ cst * quadForm (diagMax (fockSymbol n)) x) :
    HasZeroDeficiencyOn (lpFiniteModes Config) Hc :=
  hasZeroDeficiencyOn_of_esa_core H Hc hHc
      (fock_ns_hamiltonian_essentiallySelfAdjointOn_core n hn H a b cst hH hcst hrel hcomm)
