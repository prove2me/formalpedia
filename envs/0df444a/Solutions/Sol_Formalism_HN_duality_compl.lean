-- Prove2me | solution 1 for Formalism.HN.duality_compl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:27.55114+00:00
-- url     : https://prove2.me/submissions/7db924f5-97d9-4c91-ad05-b81a7049c092

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_basic
import Theorems.Thm_Formalism_HN_duality_dualZ_quot_le
import Theorems.Thm_Formalism_F_covolAntiSameRank
import Theorems.Thm_Formalism_F_covol_pos
import Theorems.Thm_Formalism_F_degQuot
import Theorems.Thm_Formalism_F_discreteTopology_of_le
import Theorems.Thm_Formalism_F_saturProps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section Dual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
private theorem discreteTopology_of_le_of_discreteTopology {L N : Submodule ℤ E} (h : N ≤ L)
    [DiscreteTopology L] : DiscreteTopology N := by
  exact Formalism.F.discreteTopology_of_le h
end Dual
universe u
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
namespace Formalism.HN
theorem _root_.solution (L S : Submodule ℤ E) [hL : DiscreteTopology L] (hS : S ≤ L) :
    ∃ N : Submodule ℤ E, N ≤ dualZ L ∧ Formalism.F.rk N + Formalism.F.rk S = Formalism.F.rk L ∧
      Formalism.F.deg S - Formalism.F.deg L ≤ Formalism.F.deg N := by
  obtain ⟨hsat, hSS, hrkS⟩ := Formalism.F.saturProps E L S hL hS
  obtain ⟨hQd, hrk, hdeg⟩ :=
    Formalism.F.degQuot E L (Formalism.F.satur L S) hL hsat
  have := hQd
  obtain ⟨-, hr, hd, -⟩ :=
    duality_basic (Formalism.F.quot L (Formalism.F.satur L S))
  have hS'd : DiscreteTopology (Formalism.F.satur L S) :=
    discreteTopology_of_le_of_discreteTopology hsat.1
  have hcov := Formalism.F.covolAntiSameRank E S (Formalism.F.satur L S) hS'd
    hSS hrkS.symm
  have hpos := Formalism.F.covol_pos (Formalism.F.satur L S)
  refine ⟨_, duality_dualZ_quot_le L _ hsat.1, ?_, ?_⟩
  · rw [hr, ← hrkS]
    omega
  · rw [hd]
    have hdS : Formalism.F.deg S ≤
        Formalism.F.deg (Formalism.F.satur L S) := by
      unfold Formalism.F.deg
      exact neg_le_neg (Real.log_le_log hpos hcov)
    linarith
end Formalism.HN
