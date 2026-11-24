-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Stab.exists_open_normal_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:25.586265+00:00
-- url     : https://prove2.me/submissions/8afef2b2-278c-4c84-bd26-979b48d1bd95

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ExistsOpenNormalOrderOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Stab
namespace Formalism.FrobeniusOrbits.Stab
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (x : G) (hx : IsOfFinOrder x) :
    ∃ N : OpenNormalSubgroup G,
      orderOf (QuotientGroup.mk x : G ⧸ (N.toSubgroup)) = orderOf x := by
  classical
  have hn : 0 < orderOf x := hx.orderOf_pos
  set S : Set G := (fun i : ℕ => x ^ i) '' Set.Ioo 0 (orderOf x) with hSdef
  have hS : IsClosed S := ((Set.finite_Ioo 0 (orderOf x)).image _).isClosed
  have h1 : (1 : G) ∈ Sᶜ := by
    rintro ⟨i, ⟨hi0, hin⟩, hi⟩
    exact pow_ne_one_of_lt_orderOf hi0.ne' hin hi
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS.isOpen_compl h1
  refine ⟨N, le_antisymm ?_ ?_⟩
  · exact Nat.le_of_dvd hn (orderOf_map_dvd (QuotientGroup.mk' N.toSubgroup) x)
  · by_contra hlt
    push_neg at hlt
    have hfo : IsOfFinOrder (QuotientGroup.mk x : G ⧸ N.toSubgroup) := by
      rw [isOfFinOrder_iff_pow_eq_one]
      exact ⟨orderOf x, hn, by rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one]; rfl⟩
    have hj := hfo.orderOf_pos
    have hmem : x ^ orderOf (QuotientGroup.mk x : G ⧸ N.toSubgroup) ∈ N.toSubgroup := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
    exact hN hmem ⟨_, ⟨hj, hlt⟩, rfl⟩
end Formalism.FrobeniusOrbits.Stab
