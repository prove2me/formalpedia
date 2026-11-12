-- Prove2me | solution 1 for BFFPyramidal.isSolvable_of_isPyramidal
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T18:51:44.801376+00:00
-- url     : https://prove2.me/submissions/36ae1055-42a2-455e-842c-0dd736c49bd1

import Mathlib
import Definitions.Def_BFFPyramidal_pyramidal

open BFFPyramidal

/-- A subgroup `H ≤ K` whose relative index in `K` is the least prime factor of `|K|`
is normal in `K` with quotient of prime order; hence `K` is solvable as soon as `H` is. -/
private lemma solvable_step {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (hHK : H ≤ K) (hidx : Subgroup.relIndex H K = Nat.minFac (Nat.card K))
    (hH : Group.IsSolvable H) : Group.IsSolvable K := by
  by_cases h1 : Nat.card K = 1
  · have : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
    infer_instance
  · have := hH
    have hidx' : (H.subgroupOf K).index = (Nat.card K).minFac := hidx
    have hnorm : (H.subgroupOf K).Normal :=
      Subgroup.normal_of_index_eq_minFac_card hidx'
    have : Fact (Nat.Prime (Nat.card K).minFac) := ⟨Nat.minFac_prime h1⟩
    have hsub : Group.IsSolvable (H.subgroupOf K) :=
      Group.isSolvable_of_surjective
        (f := (Subgroup.subgroupOfEquivOfLe hHK).symm.toMonoidHom) (MulEquiv.surjective _)
    have hcard : Nat.card (K ⧸ H.subgroupOf K) = (Nat.card K).minFac := hidx'
    have : IsCyclic (K ⧸ H.subgroupOf K) := isCyclic_of_prime_card hcard
    have hq : Group.IsSolvable (K ⧸ H.subgroupOf K) :=
      Group.isSolvable_of_comm
        (fun a b => (IsMulCommutative.is_comm (M := K ⧸ H.subgroupOf K)).comm a b)
    exact (Group.isSolvable_iff_subgroup_quotient (H.subgroupOf K)).mpr ⟨hsub, hq⟩

theorem solution {G : Type*} [Group G] [Finite G] (hG : IsPyramidal G) :
    Group.IsSolvable G := by
  obtain ⟨n, c, h0, hn, hstep⟩ := hG
  have key : ∀ j k : ℕ, k + j = n → Group.IsSolvable (c k) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      have : c k = ⊥ := by
        have : k = n := by omega
        rw [this]; exact hn
      rw [this]
      infer_instance
    | succ j ih =>
      intro k hk
      obtain ⟨hle, hidx⟩ := hstep k (by omega)
      exact solvable_step hle hidx (ih (k + 1) (by omega))
  have htop := key n 0 (by omega)
  rw [h0] at htop
  have := htop
  exact Group.isSolvable_of_surjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom) (MulEquiv.surjective _)
