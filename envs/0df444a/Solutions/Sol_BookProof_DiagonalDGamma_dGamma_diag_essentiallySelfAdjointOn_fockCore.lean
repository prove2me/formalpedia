-- Prove2me | solution 1 for BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:15:06.211448+00:00
-- url     : https://prove2.me/submissions/81d0ed6a-5766-48e3-8f48-5b92398dcfb6

-- Generated from ChapterDiagonalDGammaEsa.lean — theorem BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDiagonalDGammaEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.SecondQuantizationCore
open BookProof.DiagonalDGamma

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  {ι : Type*} (e : ι → D₂) (lam : ι → ℝ)
variable {Hs}
variable {E : ι → Hs.carrier} (hE : Orthonormal ℂ E)

set_option maxHeartbeats 1000000 in
theorem solution (lam : ι → ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier))
    (D : Submodule ℂ Hs.carrier) (hcore : IsGraphCore D (diagOp hE lam)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore Hs (diagDomain E) D n))
      (dGammaCoreOp Hs (diagDomain E) (diagOp hE lam) D) :=
  dGamma_diagonal_essentiallySelfAdjointOn_fockCore Hs (diagDomain E) (diagOp hE lam)
      (diagVec hE) lam (diagOp_eig hE lam) (by rw [range_diagVec hE]; exact hdense) D hcore
