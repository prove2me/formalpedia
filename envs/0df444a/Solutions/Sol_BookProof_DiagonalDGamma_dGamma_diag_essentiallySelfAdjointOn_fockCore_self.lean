-- Prove2me | solution 1 for BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:34:12.074526+00:00
-- url     : https://prove2.me/submissions/66cc2473-7ddf-4a50-b2ab-81ab8403cdfb

import Definitions.Def_ChapterDiagonalDGammaEsa

open BookProof.DirectSumEsa
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

theorem solution (lam : ι → ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore Hs (diagDomain E) (diagDomain E) n))
      (dGammaCoreOp Hs (diagDomain E) (diagOp hE lam) (diagDomain E)) := by
  have hdense' : Dense
      (Submodule.span ℂ (Set.range fun i => ((diagVec hE i : Hs.carrier))) : Set Hs.carrier) := by
    rwa [range_diagVec hE]
  refine dGamma_diagonal_essentiallySelfAdjointOn_fockCore Hs (diagDomain E)
    (diagOp hE lam) (diagVec hE) lam (diagOp_eig hE lam) hdense' (diagDomain E) ?_
  intro x ε hε
  exact ⟨x, x.2, by simpa using hε, by simpa using hε⟩
