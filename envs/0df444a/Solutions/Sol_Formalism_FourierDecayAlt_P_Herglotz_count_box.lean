-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.count_box
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:00.285873+00:00
-- url     : https://prove2.me/submissions/78499b59-70d4-48b3-917b-5e23c45f731e

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Herglotz
theorem _root_.solution (N : ℕ) (τ : Fin d → ℤ) :
    (((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card) =
      ∏ j, ((N : ℤ) - |τ j|).toNat := by
  have e1 : ((box d N ×ˢ box d N).filter (fun p => p.1 - p.2 = τ)).card
      = ((box d N).filter (fun s => s + τ ∈ box d N)).card := by
    apply Finset.card_nbij' (fun p => p.2) (fun s => (s + τ, s))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hp
      refine ⟨h2, ?_⟩
      convert h1 using 1
      rw [← h3]
      abel
    · intro s hs
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hs ⊢
      exact ⟨⟨hs.2, hs.1⟩, by abel⟩
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hp
      refine Prod.ext ?_ rfl
      simp only
      rw [← hp.2]
      abel
    · intro s _
      rfl
  have e2 : (box d N).filter (fun s => s + τ ∈ box d N)
      = Fintype.piFinset (fun j => (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)) := by
    ext s
    simp [box, Fintype.mem_piFinset, Finset.mem_filter, forall_and]
  rw [e1, e2, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases le_total 0 (τ j) with ht | ht
  · rw [abs_of_nonneg ht]
    have : (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)
        = Finset.Ico 0 ((N : ℤ) - τ j) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [this, Int.card_Ico, sub_zero]
  · rw [abs_of_nonpos ht]
    have : (Finset.Ico (0 : ℤ) N).filter (fun u => u + τ j ∈ Finset.Ico (0 : ℤ) N)
        = Finset.Ico (-τ j) N := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    rw [this, Int.card_Ico]
end Formalism.FourierDecayAlt.P.Herglotz
