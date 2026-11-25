-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G9.sum_eq_of_min
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:59:57.603806+00:00
-- url     : https://prove2.me/submissions/8511fa1d-ff87-4dcf-9ad9-fad2b9327992

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G9
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
namespace Formalism.L2.SG.Pf.G9
theorem _root_.solution {n n' : ℕ} (e : Fin n → ℕ) (e' : Fin n' → ℕ)
    (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) : ∑ i, e i = ∑ i, e' i := by
  have h1 : ∀ i, e i ≤ ∑ i, e i + ∑ i, e' i := fun i =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
  have h2 : ∀ i, e' i ≤ ∑ i, e i + ∑ i, e' i := fun i =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
  calc ∑ i, e i = ∑ i, min (e i) (∑ i, e i + ∑ i, e' i) :=
        Finset.sum_congr rfl fun i _ => (min_eq_left (h1 i)).symm
    _ = ∑ i, min (e' i) (∑ i, e i + ∑ i, e' i) := H _
    _ = ∑ i, e' i := Finset.sum_congr rfl fun i _ => min_eq_left (h2 i)
end Formalism.L2.SG.Pf.G9
