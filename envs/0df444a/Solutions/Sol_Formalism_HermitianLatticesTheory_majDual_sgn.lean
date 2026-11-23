-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_sgn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:15.518048+00:00
-- url     : https://prove2.me/submissions/9e467324-a425-433b-b267-6486489b949e

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsFrame h b v (X v)) (v : InfinitePlace K) :
    (X v).conjTranspose * gramAt h b v * X v =
      Matrix.diagonal (fun i => ((sgnAt h b X v i : ℝ) : ℂ)) ∧
      ∀ i, sgnAt h b X v i = 1 ∨ sgnAt h b X v i = -1 := by
  obtain ⟨-, ε, hε, hXe⟩ := hX v
  have hs : ∀ i, sgnAt h b X v i = (ε i).re := fun i => by
    simp only [sgnAt, hXe, Matrix.diagonal_apply_eq]
  refine ⟨?_, fun i => ?_⟩
  · rw [hXe]
    congr 1
    funext i
    rw [hs]
    rcases hε i with h1 | h1 <;> simp [h1]
  · rw [hs]
    rcases hε i with h1 | h1 <;> simp [h1]
end Formalism.HermitianLatticesTheory
