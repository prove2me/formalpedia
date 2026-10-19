-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:27:02.60484+00:00
-- url     : https://prove2.me/submissions/ee168d10-3ab5-49d7-8856-62858b77ca47

-- Generated from ChapterNavierStokesMomentumEsa.lean — solution of BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumEsa
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumEsa_nsSymbol_nonneg
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
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
theorem solution (d : ℕ) (p q : Fin d → ℕ → ℝ)
    (H : maxDom (nsSymbol d p q) →ₗ[ℂ] L2I ℕ) (a b cst : ℝ)
    (hH : SymmetricOn (maxDom (nsSymbol d p q)) H) (hcst : 0 ≤ cst)
    (hrel : ∀ x : maxDom (nsSymbol d p q),
      ‖H x‖ ^ 2 ≤ a * ‖diagMax (nsSymbol d p q) x‖ ^ 2 + b * ‖(x : L2I ℕ)‖ ^ 2)
    (hcomm : ∀ x : maxDom (nsSymbol d p q),
      |commForm H (diagMax (nsSymbol d p q)) x|
        ≤ cst * quadForm (diagMax (nsSymbol d p q)) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ℕ)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom (nsSymbol d p q)))) :=
  essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds _ (nsSymbol_nonneg d p q)
      H a b cst hH hcst hrel hcomm
