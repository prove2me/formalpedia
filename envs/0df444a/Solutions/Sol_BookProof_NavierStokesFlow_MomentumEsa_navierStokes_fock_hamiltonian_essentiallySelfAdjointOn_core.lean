-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:53:48.306792+00:00
-- url     : https://prove2.me/submissions/6837a06c-6560-4eb2-8ae2-a958f22564ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_fock_ns_hamiltonian_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesGaugeY
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumEsa





open LpNat BookProof.FarisLavine IkebeKato FarisLavineLift DiagonalEsa
open BookProof.NavierStokesGaugeY

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ)
    (p q : Fin d → ℕ → ℝ)
    (H : maxDom (nsFockSymbol d p q) →ₗ[ℂ] L2I Config) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (nsFockSymbol d p q)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (nsFockSymbol d p q),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (nsFockSymbol d p q) x‖ ^ 2 + b * ‖(x : L2I Config)‖ ^ 2)
    (hcomm : ∀ x : maxDom (nsFockSymbol d p q),
      |commForm H (diagMax (nsFockSymbol d p q)) x|
        ≤ cst * quadForm (diagMax (nsFockSymbol d p q)) x) :
    EssentiallySelfAdjointOn (lpFiniteModes Config)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom (nsFockSymbol d p q)))) :=
  fock_ns_hamiltonian_essentiallySelfAdjointOn_core _ (nsSymbol_nonneg d p q)
      H a b cst hH hcst hrel hcomm
