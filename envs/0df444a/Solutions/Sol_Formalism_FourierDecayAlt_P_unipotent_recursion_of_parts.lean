-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unipotent_recursion_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:46:58.59412+00:00
-- url     : https://prove2.me/submissions/ec8b15b5-6bed-4848-9050-4664afd6e404

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_blk_heis_lev
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_rho_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B2.AssembleNRec := by
  intro hS hLev hCN hHC hHH hConj hConjM hD k r' μ' hμ'
  have hL := hLev k r' (Nset k r') μ' (hCN k r') hμ'
  have h1 : ∀ b ∈ ιLev k 1 r' '' Nset k r', ∀ a ∈ Hset k r', b * a * b⁻¹ ∈ Hset k r' := by
    rintro b ⟨n, hn, rfl⟩ a ⟨x, rfl⟩
    rw [hConj k r' n hn.1 x]
    exact ⟨_, rfl⟩
  have h2 : IsClosed (mulSet (Hset k r') (ιLev k 1 r' '' Nset k r')) := by
    rw [← hD k r']
    exact (hCN k (1 + r')).closed
  have h3 : ∀ a ∈ Hset k r', ∀ b ∈ ιLev k 1 r' '' Nset k r', rho (a * b) = b := by
    rintro a ⟨x, rfl⟩ b ⟨n, _, rfl⟩
    show ιLev k 1 r' (blk (heis0 k r' x * ιLev k 1 r' n)) = ιLev k 1 r' n
    rw [blk_heis_lev]
  have h4 : ∀ b ∈ ιLev k 1 r' '' Nset k r', (μHeis k r').map (conjM b) = μHeis k r' := by
    rintro b ⟨n, hn, rfl⟩
    exact hConjM k r' n hn.1
  have h := hS k (1 + r') (Hset k r') (ιLev k 1 r' '' Nset k r') (μHeis k r') (μ'.map (levM k r')) rho
    (hHC k r').2 hL.1 h1 h2 rho_cont h3 (hHH k r') hL.2 h4
  rw [hD k r']
  exact h.2
end Formalism.FourierDecayAlt.P
