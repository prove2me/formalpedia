-- Prove2me | solution 1 for ChvatalPolytopes.Separation.union_isDefiningSystem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:29:57.062229+00:00
-- url     : https://prove2.me/submissions/2aaaafc9-3181-44b0-ba36-14e30b4fb73a

import Mathlib
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope



namespace ChvatalPolytopes.Separation

lemma uds_extract {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V1 : Finset V)
    (y : ↥(V1 : Set V) → ℝ) (hy : y ∈ Shared.stablePolytope (G.induce (V1 : Set V))) :
    ∃ w : Finset V → ℝ, (∀ S, 0 ≤ w S) ∧ (∀ S, w S ≠ 0 → S ⊆ V1 ∧ G.IsIndepSet (S : Set V)) ∧
      ∑ S, w S = 1 ∧ ∀ v : ↥(V1 : Set V), y v = ∑ S, w S * (if (v : V) ∈ S then 1 else 0) := by
  unfold Shared.stablePolytope at hy
  suffices hsub : convexHull ℝ (Shared.stableVectors (G.induce (V1 : Set V))) ⊆
      {y : ↥(V1 : Set V) → ℝ | ∃ w : Finset V → ℝ, (∀ S, 0 ≤ w S) ∧
        (∀ S, w S ≠ 0 → S ⊆ V1 ∧ G.IsIndepSet (S : Set V)) ∧
        ∑ S, w S = 1 ∧ ∀ v : ↥(V1 : Set V), y v = ∑ S, w S * (if (v : V) ∈ S then 1 else 0)} from
    hsub hy
  refine convexHull_min ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    refine ⟨fun S => if S = s.map (Function.Embedding.subtype _) then 1 else 0, ?_, ?_, ?_, ?_⟩
    · intro S; dsimp only; split_ifs <;> norm_num
    · intro S hS
      dsimp only at hS
      split_ifs at hS with h
      · subst h
        refine ⟨?_, ?_⟩
        · intro v hv
          rw [Finset.mem_map] at hv
          obtain ⟨a, -, rfl⟩ := hv
          exact a.2
        · intro a ha b hb hne hab
          have ha' : a ∈ s.map (Function.Embedding.subtype _) := ha
          have hb' : b ∈ s.map (Function.Embedding.subtype _) := hb
          rw [Finset.mem_map] at ha' hb'
          obtain ⟨a', ha', rfl⟩ := ha'
          obtain ⟨b', hb', rfl⟩ := hb'
          exact hs ha' hb' (fun h => hne (by rw [h])) hab
      · exact absurd rfl hS
    · simp
    · intro v
      simp only [Shared.incidenceVector]
      rw [Finset.sum_eq_single (s.map (Function.Embedding.subtype _))]
      · simp [Finset.mem_map]
      · intro S _ hS; simp [hS]
      · intro h; exact absurd (Finset.mem_univ _) h
  · rintro y1 ⟨w1, h1, s1, t1, e1⟩ y2 ⟨w2, h2, s2, t2, e2⟩ a b ha hb hab
    refine ⟨fun S => a * w1 S + b * w2 S, ?_, ?_, ?_, ?_⟩
    · intro S; dsimp only; have := h1 S; have := h2 S; positivity
    · intro S hS
      dsimp only at hS
      by_cases hw : w1 S = 0
      · apply s2
        intro h; apply hS; rw [hw, h]; ring
      · exact s1 S hw
    · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, t1, t2]; linarith
    · intro v
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro S _
      ring

lemma uds_uniq {V : Type*} [DecidableEq V] (G : SimpleGraph V) (K S : Finset V)
    (hK : G.IsClique (K : Set V)) (hS : G.IsIndepSet (S : Set V)) :
    ∀ j ∈ S ∩ K, ∀ k ∈ S ∩ K, j = k := by
  intro j hj k hk
  rw [Finset.mem_inter] at hj hk
  by_contra hne
  exact hS (Finset.mem_coe.2 hj.1) (Finset.mem_coe.2 hk.1) hne (hK hj.2 hk.2 hne)

lemma uds_mass_single {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (K : Finset V)
    (hK : G.IsClique (K : Set V)) (w : Finset V → ℝ)
    (hs : ∀ S, w S ≠ 0 → G.IsIndepSet (S : Set V)) (k : V) (hk : k ∈ K) :
    (∑ S, if S ∩ K = {k} then w S else 0) = ∑ S, w S * (if k ∈ S then 1 else 0) := by
  apply Finset.sum_congr rfl
  intro S _
  by_cases hw : w S = 0
  · simp [hw]
  have hu := uds_uniq G K S hK (hs S hw)
  have hiff : S ∩ K = {k} ↔ k ∈ S := by
    constructor
    · intro h
      have : k ∈ S ∩ K := by rw [h]; exact Finset.mem_singleton_self k
      exact (Finset.mem_inter.1 this).1
    · intro h
      have hkS : k ∈ S ∩ K := Finset.mem_inter.2 ⟨h, hk⟩
      rw [Finset.eq_singleton_iff_unique_mem]
      exact ⟨hkS, fun j hj => hu j hj k hkS⟩
  by_cases h : k ∈ S
  · rw [if_pos (hiff.2 h), if_pos h, mul_one]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, mul_zero]

lemma uds_mass_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (K : Finset V)
    (hK : G.IsClique (K : Set V)) (w : Finset V → ℝ)
    (hs : ∀ S, w S ≠ 0 → G.IsIndepSet (S : Set V)) (t : Finset V) (ht : t.Nonempty)
    (hnot : ¬ ∃ k ∈ K, t = {k}) :
    (∑ S, if S ∩ K = t then w S else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro S _
  by_cases hw : w S = 0
  · simp [hw]
  rw [if_neg]
  intro h
  apply hnot
  obtain ⟨k, hk⟩ := ht
  have hu := uds_uniq G K S hK (hs S hw)
  rw [← h] at hk ⊢
  refine ⟨k, (Finset.mem_inter.1 hk).2, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨hk, fun j hj => hu j hj k hk⟩

lemma uds_total {V : Type*} [Fintype V] [DecidableEq V] (K : Finset V) (w : Finset V → ℝ) :
    ∑ t, (∑ S, if S ∩ K = t then w S else 0) = ∑ S, w S := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_eq]
  simp

lemma uds_le_mass {V : Type*} [Fintype V] [DecidableEq V] (K : Finset V) (w : Finset V → ℝ)
    (hw : ∀ S, 0 ≤ w S) (S : Finset V) :
    w S ≤ ∑ S', if S' ∩ K = S ∩ K then w S' else 0 := by
  have := Finset.single_le_sum (f := fun S' => if S' ∩ K = S ∩ K then w S' else 0)
    (fun S' _ => by beta_reduce; split_ifs <;> simp [hw]) (Finset.mem_univ S)
  simpa using this

lemma uds_glue {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V1 V2 : Finset V)
    (hcover : V1 ∪ V2 = Finset.univ)
    (hclique : G.IsClique ((V1 ∩ V2 : Finset V) : Set V))
    (hsep : ∀ u v, u ∈ V1 → u ∉ V2 → v ∈ V2 → v ∉ V1 → ¬ G.Adj u v)
    (x : V → ℝ) (w1 w2 : Finset V → ℝ)
    (hw1 : ∀ S, 0 ≤ w1 S) (hs1 : ∀ S, w1 S ≠ 0 → S ⊆ V1 ∧ G.IsIndepSet (S : Set V))
    (hsum1 : ∑ S, w1 S = 1)
    (hw2 : ∀ S, 0 ≤ w2 S) (hs2 : ∀ S, w2 S ≠ 0 → S ⊆ V2 ∧ G.IsIndepSet (S : Set V))
    (hsum2 : ∑ S, w2 S = 1)
    (hx1 : ∀ v ∈ V1, x v = ∑ S, w1 S * (if v ∈ S then 1 else 0))
    (hx2 : ∀ v ∈ V2, x v = ∑ S, w2 S * (if v ∈ S then 1 else 0)) :
    x ∈ Shared.stablePolytope G := by
  set K := V1 ∩ V2 with hKdef
  set m1 : Finset V → ℝ := fun t => ∑ S, if S ∩ K = t then w1 S else 0 with hm1
  set m2 : Finset V → ℝ := fun t => ∑ S, if S ∩ K = t then w2 S else 0 with hm2
  have hm' : ∀ t, t ≠ ∅ → m1 t = m2 t := by
    intro t ht
    have htne : t.Nonempty := Finset.nonempty_iff_ne_empty.2 ht
    by_cases hex : ∃ k ∈ K, t = {k}
    · obtain ⟨k, hk, rfl⟩ := hex
      have hk1 : k ∈ V1 := (Finset.mem_inter.1 hk).1
      have hk2 : k ∈ V2 := (Finset.mem_inter.1 hk).2
      simp only [hm1, hm2]
      rw [uds_mass_single G K hclique w1 (fun S h => (hs1 S h).2) k hk,
        uds_mass_single G K hclique w2 (fun S h => (hs2 S h).2) k hk, ← hx1 k hk1, ← hx2 k hk2]
    · simp only [hm1, hm2]
      rw [uds_mass_zero G K hclique w1 (fun S h => (hs1 S h).2) t htne hex,
        uds_mass_zero G K hclique w2 (fun S h => (hs2 S h).2) t htne hex]
  have hm : ∀ t, m1 t = m2 t := by
    intro t
    by_cases ht : t = ∅
    · subst ht
      have e1 : ∑ t, m1 t = 1 := by rw [hm1, uds_total, hsum1]
      have e2 : ∑ t, m2 t = 1 := by rw [hm2, uds_total, hsum2]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)] at e1 e2
      have : ∑ t ∈ Finset.univ.erase ∅, m1 t = ∑ t ∈ Finset.univ.erase ∅, m2 t :=
        Finset.sum_congr rfl (fun t ht => hm' t (Finset.ne_of_mem_erase ht))
      linarith
    · exact hm' t ht
  have hle1 : ∀ S, w1 S ≤ m1 (S ∩ K) := fun S => uds_le_mass K w1 hw1 S
  have hle2 : ∀ S, w2 S ≤ m2 (S ∩ K) := fun S => uds_le_mass K w2 hw2 S
  have hm1nn : ∀ t, 0 ≤ m1 t := fun t =>
    Finset.sum_nonneg (fun S _ => by split_ifs <;> simp [hw1])
  let c : Finset V × Finset V → ℝ := fun p =>
    if p.1 ∩ K = p.2 ∩ K then w1 p.1 * w2 p.2 / m1 (p.1 ∩ K) else 0
  have hc0 : ∀ p, 0 ≤ c p := by
    intro p; dsimp only [c]; split_ifs
    · have := hw1 p.1; have := hw2 p.2; have := hm1nn (p.1 ∩ K); positivity
    · exact le_rfl
  have hcne : ∀ p, c p ≠ 0 → w1 p.1 ≠ 0 ∧ w2 p.2 ≠ 0 ∧ p.1 ∩ K = p.2 ∩ K := by
    intro p hp
    dsimp only [c] at hp
    split_ifs at hp with h
    · refine ⟨fun h1 => hp (by rw [h1]; ring), fun h2 => hp (by rw [h2]; ring), h⟩
    · exact absurd rfl hp
  -- sums against functions of the first component
  have hsumS : ∀ g : Finset V → ℝ, ∑ p, c p * g p.1 = ∑ S, w1 S * g S := by
    intro g
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro S _
    have : ∑ T, c (S, T) * g S = (w1 S * g S / m1 (S ∩ K)) * m2 (S ∩ K) := by
      simp only [hm2, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      dsimp only [c]
      by_cases h : S ∩ K = T ∩ K
      · rw [if_pos h, if_pos h.symm]; ring
      · rw [if_neg h, if_neg (Ne.symm h)]; ring
    rw [this, ← hm]
    by_cases h0 : m1 (S ∩ K) = 0
    · have : w1 S = 0 := le_antisymm (h0 ▸ hle1 S) (hw1 S)
      rw [this]; ring
    · field_simp
  have hsumT : ∀ g : Finset V → ℝ, ∑ p, c p * g p.2 = ∑ T, w2 T * g T := by
    intro g
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro T _
    have : ∑ S, c (S, T) * g T = (w2 T * g T / m1 (T ∩ K)) * m1 (T ∩ K) := by
      simp only [hm1]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [c]
      by_cases h : S ∩ K = T ∩ K
      · rw [if_pos h, if_pos h, h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [this]
    by_cases h0 : m1 (T ∩ K) = 0
    · have h2 := hle2 T
      rw [← hm, h0] at h2
      have : w2 T = 0 := le_antisymm h2 (hw2 T)
      rw [this]; ring
    · field_simp
  -- coordinates
  have hcoord : ∀ v, x v = ∑ p, c p * Shared.incidenceVector (p.1 ∪ p.2) v := by
    intro v
    have hv : v ∈ V1 ∨ v ∈ V2 := by
      have : v ∈ V1 ∪ V2 := hcover ▸ Finset.mem_univ v
      exact Finset.mem_union.1 this
    by_cases hv1 : v ∈ V1
    · rw [hx1 v hv1, ← hsumS (fun S => if v ∈ S then 1 else 0)]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : c p = 0
      · simp [hp]
      obtain ⟨h1, h2, h3⟩ := hcne p hp
      congr 1
      simp only [Shared.incidenceVector, Finset.mem_union]
      by_cases hvS : v ∈ p.1
      · simp [hvS]
      · have : v ∉ p.2 := by
          intro hvT
          have hvK : v ∈ p.2 ∩ K :=
            Finset.mem_inter.2 ⟨hvT, Finset.mem_inter.2 ⟨hv1, (hs2 _ h2).1 hvT⟩⟩
          rw [← h3] at hvK
          exact hvS (Finset.mem_inter.1 hvK).1
        simp [hvS, this]
    · have hv2 : v ∈ V2 := hv.resolve_left hv1
      rw [hx2 v hv2, ← hsumT (fun S => if v ∈ S then 1 else 0)]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : c p = 0
      · simp [hp]
      obtain ⟨h1, h2, h3⟩ := hcne p hp
      have : v ∉ p.1 := fun h => hv1 ((hs1 _ h1).1 h)
      simp [Shared.incidenceVector, Finset.mem_union, this]
  -- independence
  have hind : ∀ p, c p ≠ 0 → G.IsIndepSet ((p.1 ∪ p.2 : Finset V) : Set V) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hcne p hp
    obtain ⟨hS1, hSi⟩ := hs1 _ h1
    obtain ⟨hT2, hTi⟩ := hs2 _ h2
    have cross : ∀ a ∈ p.1, ∀ b ∈ p.2, ¬ G.Adj a b := by
      intro a ha b hb hab
      by_cases haV2 : a ∈ V2
      · have : a ∈ p.2 := by
          have : a ∈ p.1 ∩ K := Finset.mem_inter.2 ⟨ha, Finset.mem_inter.2 ⟨hS1 ha, haV2⟩⟩
          rw [h3] at this
          exact (Finset.mem_inter.1 this).1
        exact hTi (Finset.mem_coe.2 this) (Finset.mem_coe.2 hb) hab.ne hab
      by_cases hbV1 : b ∈ V1
      · have : b ∈ p.1 := by
          have : b ∈ p.2 ∩ K := Finset.mem_inter.2 ⟨hb, Finset.mem_inter.2 ⟨hbV1, hT2 hb⟩⟩
          rw [← h3] at this
          exact (Finset.mem_inter.1 this).1
        exact hSi (Finset.mem_coe.2 ha) (Finset.mem_coe.2 this) hab.ne hab
      exact hsep a b (hS1 ha) haV2 (hT2 hb) hbV1 hab
    intro a ha b hb hne hab
    have ha' : a ∈ p.1 ∪ p.2 := ha
    have hb' : b ∈ p.1 ∪ p.2 := hb
    rw [Finset.mem_union] at ha' hb'
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact hSi (Finset.mem_coe.2 ha') (Finset.mem_coe.2 hb') hne hab
    · exact cross a ha' b hb' hab
    · exact cross b hb' a ha' hab.symm
    · exact hTi (Finset.mem_coe.2 ha') (Finset.mem_coe.2 hb') hne hab
  -- total weight
  have hctot : ∑ p, c p = 1 := by
    have := hsumS (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hsum1]
  -- conclude
  have hxeq : x = ∑ p ∈ Finset.univ.filter (fun p => c p ≠ 0),
      c p • Shared.incidenceVector (p.1 ∪ p.2) := by
    funext v
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_filter_of_ne (fun p _ h => left_ne_zero_of_mul h), hcoord v]
  rw [hxeq]
  unfold Shared.stablePolytope
  apply (convex_convexHull ℝ _).sum_mem
  · intro p _; exact hc0 p
  · rw [Finset.sum_filter_ne_zero, hctot]
  · intro p hp
    apply subset_convexHull
    exact ⟨p.1 ∪ p.2, hind p (Finset.mem_filter.1 hp).2, rfl⟩

lemma uds_restrict {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (V₁ : Finset V)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) :
    (fun u : ↥(V₁ : Set V) => Shared.incidenceVector S (u : V)) ∈
      Shared.stablePolytope (G.induce (V₁ : Set V)) := by
  apply subset_convexHull
  refine ⟨Finset.univ.filter (fun u : ↥(V₁ : Set V) => (u : V) ∈ S), ?_, ?_⟩
  · intro a ha b hb hne hab
    have ha' : a ∈ Finset.univ.filter (fun u : ↥(V₁ : Set V) => (u : V) ∈ S) := ha
    have hb' : b ∈ Finset.univ.filter (fun u : ↥(V₁ : Set V) => (u : V) ∈ S) := hb
    rw [Finset.mem_filter] at ha' hb'
    exact hS (Finset.mem_coe.2 ha'.2) (Finset.mem_coe.2 hb'.2)
      (fun h => hne (Subtype.ext h)) hab
  · funext u
    simp [Shared.incidenceVector]

theorem uds_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (V₁ V₂ : Finset V)
    (hcover : V₁ ∪ V₂ = Finset.univ)
    (hclique : G.IsClique ((V₁ ∩ V₂ : Finset V) : Set V))
    (hsep : ∀ u v, u ∈ V₁ → u ∉ V₂ → v ∈ V₂ → v ∉ V₁ → ¬ G.Adj u v)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → ↥(V₁ : Set V) → ℝ) (b₁ : J₁ → ℝ)
    (a₂ : J₂ → ↥(V₂ : Set V) → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : ↥(V₁ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} =
      Shared.stablePolytope (G.induce (V₁ : Set V)))
    (h₂ : {x : ↥(V₂ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₂ i u * x u ≤ b₂ i} =
      Shared.stablePolytope (G.induce (V₂ : Set V))) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ (∀ i, ∑ u : ↥(V₁ : Set V), a₁ i u * x u ≤ b₁ i) ∧
        (∀ i, ∑ u : ↥(V₂ : Set V), a₂ i u * x u ≤ b₂ i)} = Shared.stablePolytope G := by
  ext x
  constructor
  · rintro ⟨hnn, hr1, hr2⟩
    have hy1 : (fun u : ↥(V₁ : Set V) => x u) ∈ Shared.stablePolytope (G.induce (V₁ : Set V)) := by
      rw [← h₁]; exact ⟨fun u => hnn u, hr1⟩
    have hy2 : (fun u : ↥(V₂ : Set V) => x u) ∈ Shared.stablePolytope (G.induce (V₂ : Set V)) := by
      rw [← h₂]; exact ⟨fun u => hnn u, hr2⟩
    obtain ⟨w1, hw1, hs1, hsum1, he1⟩ := uds_extract G V₁ _ hy1
    obtain ⟨w2, hw2, hs2, hsum2, he2⟩ := uds_extract G V₂ _ hy2
    exact uds_glue G V₁ V₂ hcover hclique hsep x w1 w2 hw1 hs1 hsum1 hw2 hs2 hsum2
      (fun v hv => he1 ⟨v, hv⟩) (fun v hv => he2 ⟨v, hv⟩)
  · intro hx
    unfold Shared.stablePolytope at hx
    suffices hsub : convexHull ℝ (Shared.stableVectors G) ⊆
        {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ (∀ i, ∑ u : ↥(V₁ : Set V), a₁ i u * x u ≤ b₁ i) ∧
          (∀ i, ∑ u : ↥(V₂ : Set V), a₂ i u * x u ≤ b₂ i)} from hsub hx
    apply convexHull_min
    · rintro _ ⟨S, hS, rfl⟩
      have r1 := uds_restrict G V₁ S hS
      have r2 := uds_restrict G V₂ S hS
      rw [← h₁] at r1
      rw [← h₂] at r2
      refine ⟨?_, fun i => r1.2 i, fun i => r2.2 i⟩
      intro u
      simp only [Shared.incidenceVector]
      split_ifs <;> norm_num
    · rintro y ⟨hy0, hy1, hy2⟩ z ⟨hz0, hz1, hz2⟩ a b ha hb hab
      refine ⟨?_, ?_, ?_⟩
      · intro u
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have := hy0 u; have := hz0 u; positivity
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
        have e1 : ∑ u : ↥(V₁ : Set V), a₁ i u * (a * y u) = a * ∑ u : ↥(V₁ : Set V), a₁ i u * y u := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
        have e2 : ∑ u : ↥(V₁ : Set V), a₁ i u * (b * z u) = b * ∑ u : ↥(V₁ : Set V), a₁ i u * z u := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_left (hy1 i) ha
        have := mul_le_mul_of_nonneg_left (hz1 i) hb
        have : b₁ i = a * b₁ i + b * b₁ i := by rw [← add_mul, hab, one_mul]
        linarith
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
        have e1 : ∑ u : ↥(V₂ : Set V), a₂ i u * (a * y u) = a * ∑ u : ↥(V₂ : Set V), a₂ i u * y u := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
        have e2 : ∑ u : ↥(V₂ : Set V), a₂ i u * (b * z u) = b * ∑ u : ↥(V₂ : Set V), a₂ i u * z u := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
        rw [e1, e2]
        have := mul_le_mul_of_nonneg_left (hy2 i) ha
        have := mul_le_mul_of_nonneg_left (hz2 i) hb
        have : b₂ i = a * b₂ i + b * b₂ i := by rw [← add_mul, hab, one_mul]
        linarith

end ChvatalPolytopes.Separation

open ChvatalPolytopes.Separation
open ChvatalPolytopes ChvatalPolytopes.Separation

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (V₁ V₂ : Finset V)
    (hcover : V₁ ∪ V₂ = Finset.univ)
    (hclique : G.IsClique ((V₁ ∩ V₂ : Finset V) : Set V))
    (hsep : ∀ u v, u ∈ V₁ → u ∉ V₂ → v ∈ V₂ → v ∉ V₁ → ¬ G.Adj u v)
    {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (a₁ : J₁ → ↥(V₁ : Set V) → ℝ) (b₁ : J₁ → ℝ)
    (a₂ : J₂ → ↥(V₂ : Set V) → ℝ) (b₂ : J₂ → ℝ)
    (h₁ : {x : ↥(V₁ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₁ i u * x u ≤ b₁ i} =
      Shared.stablePolytope (G.induce (V₁ : Set V)))
    (h₂ : {x : ↥(V₂ : Set V) → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ i, ∑ u, a₂ i u * x u ≤ b₂ i} =
      Shared.stablePolytope (G.induce (V₂ : Set V))) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ (∀ i, ∑ u : ↥(V₁ : Set V), a₁ i u * x u ≤ b₁ i) ∧
        (∀ i, ∑ u : ↥(V₂ : Set V), a₂ i u * x u ≤ b₂ i)} = Shared.stablePolytope G := by
  exact uds_core G V₁ V₂ hcover hclique hsep a₁ b₁ a₂ b₂ h₁ h₂
