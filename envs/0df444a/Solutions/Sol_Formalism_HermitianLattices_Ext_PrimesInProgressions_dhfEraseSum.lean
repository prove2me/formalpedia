-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfEraseSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:56:22.656796+00:00
-- url     : https://prove2.me/submissions/851e9059-c1e2-45cc-99d5-8d476e000734

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (Z : Finset ℂ) (m : ℂ → ℕ) (s b : ℂ) (c : Prop) [Decidable c]
    (hb : c → b ∈ dhFam Z m s) (k : ℕ) :
    ((if c then (dhFam Z m s).erase b else dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) - (if c then 1 / b ^ (k + 1) else 0) := by
  have key : ((dhFam Z m s).map (fun x : ℂ => 1 / x ^ (k + 1))).sum =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by
    unfold dhFam
    rw [Multiset.map_bind, Multiset.sum_bind, Finset.sum_eq_multiset_sum]
    congr 1
    apply Multiset.map_congr rfl
    intro ρ _
    rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul]
    ring
  split_ifs with h
  · rw [← key, ← Multiset.sum_map_erase (hb h)]
    ring
  · rw [key, sub_zero]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
