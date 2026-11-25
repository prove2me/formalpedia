-- Prove2me | solution 1 for Formalism.L2.Th1.G.HurwitzJetIntegrality.rep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:37:31.211367+00:00
-- url     : https://prove2.me/submissions/b19b83df-c14f-4c61-9e26-1e14b5fb7075

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_StatementH
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_RamifiedCurveKernels_PairedSquareJets_HurwitzB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.G
open Formalism.DworkPowerSeriesWeights (mfact JetsIntegral)
open HurwitzJetIntegrality
open Formalism.L2.Th1.G.HurwitzJetIntegrality
namespace Formalism.L2.Th1.G.HurwitzJetIntegrality
theorem _root_.solution (B : Type) [Fintype B] {ι : Type} (m : B → ι →₀ ℕ) (k : B) (i : ι) :
    rep B m (k, i) = m k i := by
  classical
  unfold rep
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single k]
  · first
      | exact Finsupp.embDomain_apply_self (blockEmb B ι k) (m k) i
      | exact Finsupp.embDomain_apply_self (f := blockEmb B ι k) (v := m k) (a := i)
      | simp [Finsupp.embDomain_apply, blockEmb]
  · intro k' _ hk'
    rw [Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩
    exact hk' (congrArg Prod.fst hj)
  · intro h
    exact absurd (Finset.mem_univ k) h
end Formalism.L2.Th1.G.HurwitzJetIntegrality
