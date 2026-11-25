-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFamPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:10.98714+00:00
-- url     : https://prove2.me/submissions/1b9b1966-1206-43e9-94b7-ffa3b2702135

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (k : ℕ) :
    ((dhFam Z m s).map (fun x => 1 / x ^ (k + 1))).sum = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
  unfold dhFam
  rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
  congr 1
  refine Multiset.map_congr rfl fun ρ _ => ?_
  simp [Multiset.map_replicate, Multiset.sum_replicate, div_eq_mul_inv]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
