-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:27:05.022419+00:00
-- url     : https://prove2.me/submissions/b13ab024-9193-4df2-bc3c-741b67097067

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.fock_ns_hamiltonian_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fockSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ → ℝ) (hn : ∀ k, 0 ≤ n k)
    (H : maxDom (fockSymbol n) →ₗ[ℂ] L2I Config) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (fockSymbol n)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (fockSymbol n),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (fockSymbol n) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2)
    (hcomm : ∀ x : maxDom (fockSymbol n),
      |commForm H (diagMax (fockSymbol n)) x| ≤ cst * quadForm (diagMax (fockSymbol n)) x) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom (fockSymbol n)))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds _ (fockSymbol_nonneg n hn)
      H a b cst hH hcst hrel hcomm
