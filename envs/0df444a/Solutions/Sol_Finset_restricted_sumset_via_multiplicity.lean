-- Prove2me | solution 1 for Finset.restricted_sumset_via_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:44.817735+00:00
-- url     : https://prove2.me/submissions/646dff2a-d45c-45a2-a458-8d7fceaba512

import Mathlib

open scoped Pointwise

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (M : ℕ) :
    (∀ a ∈ A, ∀ b ∈ B,
        M ≤ ((S ×ˢ S ×ˢ S).filter
          (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card) →
    M * (A + B).card ≤ S.card ^ 3 := by
  intro hcover
  -- Build the disjoint sets T_v = { (s₁,s₂,s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }.
  set T : G → Finset (G × G × G) :=
    fun v ↦ (S ×ˢ S ×ˢ S).filter (fun p ↦ p.1 - p.2.1 + p.2.2 = v) with hT_def
  -- Each fiber T_v contributes at least M to the sum over A + B.
  have hMle : ∀ v ∈ A + B, M ≤ (T v).card := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hv
    -- Substitute a + b = v in the multiplicity hypothesis.
    have hM_at := hcover a ha b hb
    -- The triple subset T(a,b) has card ≥ M, and lies inside T v.
    set T_ab : Finset (G × G × G) :=
      (S ×ˢ S ×ˢ S).filter
        (fun p ↦ p.1 - p.2.1 + p.2.2 = a + b) with hTab_def
    have hT_ab_eq : T_ab = T v := by
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h; rw [h, hab]
      · intro h; rw [h, ← hab]
    have : M ≤ T_ab.card := hM_at
    rw [hT_ab_eq] at this
    exact this
  -- The fibers cover disjointly inside S × S × S.
  -- Sum over v ∈ A + B of |T_v| ≤ |S × S × S| = |S|^3.
  have hdisj : ((A + B : Finset G) : Set G).PairwiseDisjoint T := by
    intro v _ w _ hvw
    refine Finset.disjoint_filter.mpr ?_
    intro p _ hpv hpw
    exact hvw (hpv ▸ hpw)
  have hSubset : ∀ v ∈ A + B, T v ⊆ S ×ˢ S ×ˢ S := by
    intro v _ p hp
    exact (Finset.mem_filter.mp hp).1
  -- Σ_v |T_v| = | ⋃_v T_v | ≤ |S × S × S|.
  have hSumCard :
      ∑ v ∈ A + B, (T v).card = ((A + B).biUnion T).card := by
    rw [Finset.card_biUnion]
    intro v hv w hw hvw
    have hpw : ((A + B : Finset G) : Set G).PairwiseDisjoint T := hdisj
    have hv' : v ∈ ((A + B : Finset G) : Set G) := hv
    have hw' : w ∈ ((A + B : Finset G) : Set G) := hw
    exact hpw hv' hw' hvw
  have hSumLeS3 : ∑ v ∈ A + B, (T v).card ≤ (S ×ˢ S ×ˢ S).card := by
    rw [hSumCard]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hpv⟩ := hp
    exact hSubset v hv hpv
  -- Σ_v M ≤ Σ_v |T_v|.
  have hML : M * (A + B).card ≤ ∑ v ∈ A + B, (T v).card := by
    have hsum_le : ∑ _v ∈ A + B, M ≤ ∑ v ∈ A + B, (T v).card :=
      Finset.sum_le_sum (fun v hv ↦ hMle v hv)
    have hconst : ∑ _v ∈ A + B, M = (A + B).card * M := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [hconst, mul_comm] at hsum_le
    exact hsum_le
  -- Combine.
  have hCard_S3 : (S ×ˢ S ×ˢ S).card = S.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product, pow_succ, pow_succ, pow_one]
    ring
  calc M * (A + B).card
      ≤ ∑ v ∈ A + B, (T v).card := hML
    _ ≤ (S ×ˢ S ×ˢ S).card := hSumLeS3
    _ = S.card ^ 3 := hCard_S3
