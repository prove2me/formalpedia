-- Prove2me | solution 1 for Formalism.L2.SG.RowsOther.rowLoops_of_input
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:00.950248+00:00
-- url     : https://prove2.me/submissions/8e8a40f5-8763-4a02-9cd3-da3a42ec8d36

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
namespace Formalism.L2.SG.RowsOther
theorem _root_.solution (hL : PN.LoopCores) (hSub : PB.SubFamily) (C : ℝ) (hC : 1 ≤ C) :
    ∃ K₀ : ℝ, ∀ (τ Rw I H H₁ : Type) [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁) (k r f : ℕ)
      (A b g v NT Gam : ℝ) (Xi : ℕ → ℝ) (dd : ℝ), 1 ≤ A →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k (2 * r + 2) f b g v NT Gam →
      Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k (2 * r + 2) f b v NT Xi →
      6 * Real.log (3 * A) ≤ (k : ℝ) * f * Real.log k → 0 ≤ dd → X.AbsConv →
      PB.LoopsInput X A C k r f b g v Gam Xi dd →
      X.RowBig (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd ∧
      X.RowNotScalar (Real.exp (-((1 / 3 : ℝ) * k * f * Real.log k))) dd := by
  obtain ⟨h1, h2, h3, h4, h5, hJ, hGR⟩ := hL
  obtain ⟨K₀, hK⟩ := hJ h1 h2 h3 h4 h5 C hC
  refine ⟨K₀, ?_⟩
  intro τ Rw I H H₁ _ _ _ _ _ X k r f A b g v NT Gam Xi dd hA hPar hXi hlog hdd hAbs hIn
  exact hGR hSub τ Rw I H H₁ X _ dd hAbs (hK τ Rw I H H₁ X k r f A b g v NT Gam Xi dd hA hPar hXi hlog hdd hIn)
end Formalism.L2.SG.RowsOther
