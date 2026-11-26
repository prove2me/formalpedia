-- Prove2me | solution 1 for C6BipartiteDomination.paper10_fiber_plus_one_le_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:44.046801+00:00
-- url     : https://prove2.me/submissions/f8b5f0a1-bbf6-42a5-a8b4-df5d3316d5c5

import Definitions.Def_C6BipartiteDomination_PaperSection9
import Definitions.Def_C6BipartiteDomination_PaperSection10
import Theorems.Thm_C6BipartiteDomination_paper10_z0_has_S_neighbor
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_paper9_shared_compensation_profile
import Theorems.Thm_C6BipartiteDomination_paper9_shared_external_charge_eq_four


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D Q : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    (hNoIso : HasNoIsolatedVertices G)
    (hQ : ∀ q ∈ Q, IsPaper10SpecialQ G hCan hmax q) {z : V}
    (hz : z ∈ Z0Part G D) :
    (paper10SpecialFiber G hCan hmax Q hQ z).card + 1 ≤ degreeTo G (SPart G D) z := by
  classical
  let F := paper10SpecialFiber G hCan hmax Q hQ z
  by_cases hF : F = ∅
  · obtain ⟨r, hrS, hrAdj⟩ := paper10_z0_has_S_neighbor G hNoIso hz
    have hdeg : r ∈ (SPart G D).filter (fun v => G.Adj z v) :=
      Finset.mem_filter.mpr ⟨hrS, hrAdj⟩
    have hpos : 1 ≤ ((SPart G D).filter (fun v => G.Adj z v)).card := by
      have := Finset.card_pos.mpr ⟨r, hdeg⟩
      omega
    simpa [degreeTo, F, hF] using hpos
  · obtain ⟨q, hqF⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    have hqQ : q ∈ Q := (Finset.mem_filter.mp hqF).1
    have hqSpecial := hQ q hqQ
    let data := Classical.choice hqSpecial
    have hqZopt : paper10SpecialEndpoint G hCan hmax q = some z :=
      (Finset.mem_filter.mp hqF).2
    have hqZ : data.z = z := by
      change (Classical.choice hqSpecial).z = z
      simpa [paper10SpecialEndpoint, hqSpecial] using hqZopt
    have hExtraS : data.w₁ ∈ SPart G D := data.w₁S
    have hzExtra : G.Adj z data.w₁ := by
      rw [← hqZ]
      have := (mem_supportX G D data.w₁ data.z).mp data.zSupport₁
      exact this.2.symm
    have hqNeExtra : q ≠ data.w₁ := by
      intro hEq
      have hnegQ : externalCharge G D q < 0 := by
        rw [hEq]
        exact data.w₁negative
      have hqCharge := paper9_shared_external_charge_eq_four G
        (fun x hx => (mem_supportX G D data.w₁ x).mp hx |>.1)
        (q := q) data.uB data.qShared₁
      omega
    have hExtraNotF : data.w₁ ∉ F := by
      intro hwF
      have hwQ : data.w₁ ∈ Q := (Finset.mem_filter.mp hwF).1
      have hwSpecial := hQ data.w₁ hwQ
      have hNeg := data.w₁negative
      have hwZopt : paper10SpecialEndpoint G hCan hmax data.w₁ = some z :=
        (Finset.mem_filter.mp hwF).2
      let hwData := Classical.choice hwSpecial
      have hX : supportX G D hwData.w₁ ⊆ Z0Part G D := by
        intro x hx
        exact (mem_supportX G D hwData.w₁ x).mp hx |>.1
      have hCharge := paper9_shared_external_charge_eq_four G hX
        (q := data.w₁) hwData.uB hwData.qShared₁
      omega
    have hFiberSub : F ⊆ (SPart G D).filter (fun v => G.Adj z v) := by
      intro r hrF
      have hrQ : r ∈ Q := (Finset.mem_filter.mp hrF).1
      have hrSpecial := hQ r hrQ
      let hrData := Classical.choice hrSpecial
      have hrZopt : paper10SpecialEndpoint G hCan hmax r = some z :=
        (Finset.mem_filter.mp hrF).2
      have hrEq : hrData.z = z := by
        have heq : (Classical.choice hrSpecial).z = z := by
          simpa [paper10SpecialEndpoint, hrSpecial] using hrZopt
        simpa [hrData] using heq
      have hrX : supportX G D hrData.w₁ ⊆ Z0Part G D := by
        intro x hx
        exact (mem_supportX G D hrData.w₁ x).mp hx |>.1
      have hrProfile := paper9_shared_compensation_profile G hrX hrData.uB hrData.qShared₁
      have hrNeU : hrData.z ≠ hrData.u := by
        intro hEq
        have hz0 : hrData.z ∈ Z0Part G D :=
          (mem_supportX G D hrData.w₁ hrData.z).mp hrData.zSupport₁ |>.1
        rw [hEq] at hz0
        exact (Finset.disjoint_left.mp (Z0_disjoint_B G (D := D)) hz0 hrData.uB).elim
      have hrAdjZ : G.Adj z r := by
        have hzIn : z ∈ neighborhoodIn G D r := by
          rw [hrData.qNeighborhood]
          simp [hrEq]
        exact (mem_neighborhoodIn G D r z).mp hzIn |>.2.symm
      exact Finset.mem_filter.mpr ⟨hrProfile.1, hrAdjZ⟩
    have hUnionSub : F ∪ {data.w₁} ⊆ (SPart G D).filter (fun v => G.Adj z v) := by
      intro r hr
      rcases Finset.mem_union.mp hr with hrF | hrExtra
      · exact hFiberSub hrF
      · have hrEq : r = data.w₁ := Finset.mem_singleton.mp hrExtra
        subst r
        exact Finset.mem_filter.mpr ⟨hExtraS, hzExtra⟩
    have hdisj : Disjoint F {data.w₁} := by
      rw [Finset.disjoint_singleton_right]
      exact hExtraNotF
    have hcard := Finset.card_le_card hUnionSub
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    simpa [degreeTo, F] using hcard
end C6BipartiteDomination
