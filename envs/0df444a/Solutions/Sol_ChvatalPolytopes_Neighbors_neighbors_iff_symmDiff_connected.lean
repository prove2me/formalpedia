-- Prove2me | solution 1 for ChvatalPolytopes.Neighbors.neighbors_iff_symmDiff_connected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:33:57.075614+00:00
-- url     : https://prove2.me/submissions/0616344d-719e-4901-b07f-f88d2e71040a

import Mathlib
import Definitions.Def_ChvatalPolytopes_Neighbors_StablePolytope
import Definitions.Def_ChvatalPolytopes_Neighbors_IsBicoloration
import Definitions.Def_ChvatalPolytopes_Neighbors_AreNeighbors



namespace ChvatalPolytopes.Neighbors

open Classical in
lemma tb_inner_sum {V : Type*} [Fintype V] (T : SimpleGraph V) (x : V → ℝ) (u : V) :
    ∑ v, (if T.Adj u v then x u else 0) = (T.degree u : ℝ) * x u := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  congr 2
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]

open Classical in
lemma tb_double {V : Type*} [Fintype V] (T : SimpleGraph V) (x : V → ℝ) :
    ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0) = 2 * ∑ u, (T.degree u : ℝ) * x u := by
  have h1 : ∀ u v, (if T.Adj u v then x u + x v else 0)
      = (if T.Adj u v then x u else 0) + (if T.Adj v u then x v else 0) := by
    intro u v
    by_cases h : T.Adj u v
    · simp [h, h.symm]
    · have h' : ¬ T.Adj v u := fun h'' => h h''.symm
      simp [h, h']
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v => if T.Adj v u then x v else 0)]
  simp_rw [tb_inner_sum]
  ring

open Classical in
lemma tb_ones {V : Type*} [Fintype V] (T : SimpleGraph V) :
    ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) = 2 * (T.edgeFinset.card : ℝ) := by
  have := tb_double T (fun _ => (1/2 : ℝ))
  have h2 : ∀ u v, (if T.Adj u v then (1/2:ℝ) + 1/2 else 0) = if T.Adj u v then (1:ℝ) else 0 := by
    intro u v; norm_num
  simp only [h2] at this
  rw [this]
  have h3 := T.sum_degrees_eq_twice_card_edges
  have h4 : (∑ u, (T.degree u : ℝ)) = 2 * (T.edgeFinset.card : ℝ) := by exact_mod_cast h3
  rw [← Finset.sum_mul, h4]; ring

lemma tb_indicator_cases {V : Type*} [DecidableEq V] (S : Finset V) (u : V) :
    incidenceVector S u = 1 ∧ u ∈ S ∨ incidenceVector S u = 0 ∧ u ∉ S := by
  unfold incidenceVector; by_cases h : u ∈ S <;> simp [h]

lemma tb_walk {V : Type*} (T : SimpleGraph V) (P : V → Prop)
    (h : ∀ u v, T.Adj u v → (P u ↔ P v)) {a b : V} (p : T.Walk a b) : P a ↔ P b := by
  induction p with
  | nil => rfl
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

theorem tb_core {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) (hT : T.IsTree) (B R : Finset V) (hBR : IsBicoloration T B R) :
    ∃ (c : V → ℕ) (m : ℕ), ∀ x ∈ stableVectors T,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) ↔ x = incidenceVector B ∨ x = incidenceVector R) := by
  classical
  refine ⟨fun u => T.degree u, T.edgeFinset.card, ?_⟩
  rintro x ⟨S, hS, rfl⟩
  set x := incidenceVector S with hx
  have hle : ∀ u v, (if T.Adj u v then x u + x v else 0) ≤ if T.Adj u v then (1:ℝ) else 0 := by
    intro u v
    by_cases h : T.Adj u v
    · simp only [h, if_true]
      rcases tb_indicator_cases S u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
      rcases tb_indicator_cases S v with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;> rw [hx, hu, hv] <;> try norm_num
      exact absurd h (hS hu' hv' (T.ne_of_adj h))
    · simp [h]
  have hsum : ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0)
      ≤ ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) :=
    Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hle u v
  rw [tb_double, tb_ones] at hsum
  refine ⟨by linarith, ?_⟩
  -- equality characterization
  have heq : (∑ u, (T.degree u : ℝ) * x u = (T.edgeFinset.card : ℝ)) ↔
      ∀ u v, T.Adj u v → x u + x v = 1 := by
    constructor
    · intro hE u v huv
      have hE2 : ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0)
          = ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) := by
        rw [tb_double, tb_ones, hE]
      rw [Finset.sum_eq_sum_iff_of_le (fun u _ => Finset.sum_le_sum fun v _ => hle u v)] at hE2
      have := hE2 u (Finset.mem_univ _)
      rw [Finset.sum_eq_sum_iff_of_le (fun v _ => hle u v)] at this
      have := this v (Finset.mem_univ _)
      simpa [huv] using this
    · intro hall
      have hE2 : ∑ u, ∑ v, (if T.Adj u v then x u + x v else 0)
          = ∑ u, ∑ v, (if T.Adj u v then (1:ℝ) else 0) := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        by_cases h : T.Adj u v
        · simp [h, hall u v h]
        · simp [h]
      rw [tb_double, tb_ones] at hE2
      linarith
  have hcast : (∑ u, (((fun u => T.degree u) u : ℕ) : ℝ) * x u) = ∑ u, (T.degree u : ℝ) * x u := rfl
  rw [hcast, heq]
  obtain ⟨hdisj, hunion, hadj⟩ := hBR
  have hR : ∀ u, u ∈ R ↔ u ∉ B := by
    intro u
    constructor
    · intro hu hb; exact Finset.disjoint_left.mp hdisj hb hu
    · intro hb
      have : u ∈ B ∪ R := by rw [hunion]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp this with h | h
      · exact absurd h hb
      · exact h
  have hxval : ∀ u, (x u = 1 ↔ u ∈ S) ∧ (x u = 0 ↔ u ∉ S) := by
    intro u
    rcases tb_indicator_cases S u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;> rw [hx] <;> simp [hu, hu']
  constructor
  · intro hall
    -- P u := (u ∈ S ↔ u ∈ B)
    have hP : ∀ u v, T.Adj u v → ((u ∈ S ↔ u ∈ B) ↔ (v ∈ S ↔ v ∈ B)) := by
      intro u v huv
      have hs := hall u v huv
      have hb := hadj u v huv
      rw [hR, hR] at hb
      rcases tb_indicator_cases S u with ⟨hu, hu'⟩ | ⟨hu, hu'⟩ <;>
      rcases tb_indicator_cases S v with ⟨hv, hv'⟩ | ⟨hv, hv'⟩ <;>
      rw [hx, hu, hv] at hs <;> norm_num at hs <;> tauto
    obtain ⟨v0⟩ := hT.1.nonempty
    have hall' : ∀ u, (u ∈ S ↔ u ∈ B) ↔ (v0 ∈ S ↔ v0 ∈ B) := by
      intro u
      obtain ⟨p⟩ := hT.1.preconnected u v0
      exact tb_walk T _ hP p
    by_cases h0 : (v0 ∈ S ↔ v0 ∈ B)
    · left
      have : S = B := by ext u; exact (hall' u).mpr h0
      rw [hx, this]
    · right
      have : S = R := by
        ext u; rw [hR]; have := (hall' u); tauto
      rw [hx, this]
  · rintro (h | h) u v huv
    · rw [h]; unfold incidenceVector
      have hb := hadj u v huv
      rw [hR, hR] at hb
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    · rw [h]; unfold incidenceVector
      have hb := hadj u v huv
      rcases hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have : u ∉ R := by rw [hR]; simpa using h1
        simp [this, h2]
      · have : v ∉ R := by rw [hR]; simpa using h2
        simp [this, h1]


lemma ct_cases {V : Type*} [DecidableEq V] (S : Finset V) (u : V) :
    incidenceVector S u = 1 ∧ u ∈ S ∨ incidenceVector S u = 0 ∧ u ∉ S := by
  unfold incidenceVector; by_cases h : u ∈ S <;> simp [h]

lemma ct_ind {V : Type*} [DecidableEq V] (Y Z : Finset V) (x : V → ℝ) :
    x = incidenceVector Y ↔ (∀ u ∈ (Y \ Z ∪ Z \ Y), x u = if u ∈ Y \ Z then 1 else 0) ∧
      (∀ u, u ∉ (Y \ Z ∪ Z \ Y) → x u = (fun u => if u ∈ Y ∩ Z then (1:ℝ) else 0) u) := by
  constructor
  · intro h
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [h]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢
    · rw [h]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_inter] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢
  · rintro ⟨h, h'⟩; funext u
    by_cases hu : u ∈ (Y \ Z ∪ Z \ Y)
    · rw [h u hu]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢
    · rw [h' u hu]; simp only [incidenceVector, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_inter] at hu ⊢
      by_cases hy : u ∈ Y <;> by_cases hz : u ∈ Z <;> simp [hy, hz] at hu ⊢

theorem ct_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y Z : Finset V)
    (hY : G.IsIndepSet (Y : Set V)) (hZ : G.IsIndepSet (Z : Set V))
    (T : SimpleGraph (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (hTsub : T ≤ G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V))
    (c' : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) → ℕ) (m : ℕ)
    (hc' : ∀ x ∈ stableVectors T,
      (∑ u, (c' u : ℝ) * x u ≤ (m : ℝ)) ∧
      (∑ u, (c' u : ℝ) * x u = (m : ℝ) ↔
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Y \ Z) ∨
        x = incidenceVector (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Z \ Y))) :
    let c : V → ℤ := fun u =>
      if h : u ∈ (Y \ Z) ∪ (Z \ Y) then (c' ⟨u, by simpa using h⟩ : ℤ)
      else if u ∈ Y ∩ Z then 1 else -1
    ∀ x ∈ stableVectors G,
      (∑ u, (c u : ℝ) * x u ≤ (m : ℝ) + ((Y ∩ Z).card : ℝ)) ∧
      (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ) ↔
        x = incidenceVector Y ∨ x = incidenceVector Z) := by
  intro c
  rintro x ⟨S, hS, rfl⟩
  set x := incidenceVector S with hx
  -- restriction
  set xr : (↑(Y \ Z ∪ Z \ Y) : Set V) → ℝ := fun a => x a.1 with hxr
  have hxr_mem : xr ∈ stableVectors T := by
    refine ⟨Finset.univ.filter fun a : (↑(Y \ Z ∪ Z \ Y) : Set V) => a.1 ∈ S, ?_, ?_⟩
    · intro a ha b hb hab hadj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have := hTsub hadj
      rw [SimpleGraph.comap_adj] at this
      exact hS ha hb (fun h => hab (Subtype.ext h)) this
    · funext a; simp [hxr, hx, incidenceVector]
  obtain ⟨h1, h2⟩ := hc' xr hxr_mem
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun u => u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V))
    (fun u => (c u : ℝ) * x u)
  have hfirst : (∑ i : {u // u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1) = ∑ u, (c' u : ℝ) * xr u := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : a.1 ∈ (Y \ Z ∪ Z \ Y) := by simpa using a.2
    simp only [c, dif_pos ha, hxr]
    norm_num
  -- second sum
  set g : V → ℝ := fun u => if u ∈ Y ∩ Z then 1 else 0 with hg
  have hle2 : ∀ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1 ≤ g i.1 := by
    intro i
    have hi : i.1 ∉ (Y \ Z ∪ Z \ Y) := by simpa using i.2
    simp only [c, dif_neg hi, hg]
    rcases ct_cases S i.1 with ⟨hu, _⟩ | ⟨hu, _⟩ <;> rw [hx, hu] <;>
      by_cases h : i.1 ∈ Y ∩ Z <;> simp [h]
  have hg_sum : (∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, g i.1) = ((Y ∩ Z).card : ℝ) := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun u => u ∉ (Y \ Z ∪ Z \ Y)) (p := fun u => ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V))
      (by intro u; simp)]
    rw [Finset.sum_filter, hg]
    simp only
    rw [← Finset.sum_filter]
    have : (Finset.univ.filter fun u => u ∉ (Y \ Z ∪ Z \ Y) ∧ u ∈ Y ∩ Z) = Y ∩ Z := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_sdiff, Finset.mem_inter]; tauto
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.filter_filter, this]
  have hsecond_le : (∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1) ≤ ((Y ∩ Z).card : ℝ) := by
    rw [← hg_sum]; exact Finset.sum_le_sum fun i _ => hle2 i
  have htot : ∑ u, (c u : ℝ) * x u = (∑ u, (c' u : ℝ) * xr u) +
      ∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1 := by
    rw [← hsplit, ← hfirst]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext a
    simp
  refine ⟨by rw [htot]; linarith, ?_⟩
  -- outside condition
  set O : Prop := ∀ u, u ∉ (Y \ Z ∪ Z \ Y) → x u = g u with hO
  have hsecond_eq : (∑ i : {u // ¬ u ∈ (↑(Y \ Z ∪ Z \ Y) : Set V)}, (c i.1 : ℝ) * x i.1) = ((Y ∩ Z).card : ℝ) ↔ O := by
    rw [← hg_sum, Finset.sum_eq_sum_iff_of_le (fun i _ => hle2 i)]
    constructor
    · intro h u hu
      have := h ⟨u, by simpa using hu⟩ (Finset.mem_univ _)
      simp only [c, dif_neg hu, hg] at this ⊢
      rcases ct_cases S u with ⟨hu', _⟩ | ⟨hu', _⟩ <;> rw [hx, hu'] at this ⊢ <;>
        by_cases h : u ∈ Y ∩ Z <;> simp [h] at this ⊢
    · intro h i _
      have hi : i.1 ∉ (Y \ Z ∪ Z \ Y) := by simpa using i.2
      have := h i.1 hi
      simp only [c, dif_neg hi, hg] at this ⊢
      rw [this]; by_cases h' : i.1 ∈ Y ∩ Z <;> simp [h']
  have hTot_eq : (∑ u, (c u : ℝ) * x u = (m : ℝ) + ((Y ∩ Z).card : ℝ)) ↔
      (∑ u, (c' u : ℝ) * xr u = m) ∧ O := by
    rw [htot, ← hsecond_eq]
    constructor
    · intro h; constructor <;> linarith
    · rintro ⟨h, h'⟩; rw [h, h']
  rw [hTot_eq, h2]
  have hA : ∀ W : Finset V, xr = incidenceVector (Finset.univ.filter fun u : (↑(Y \ Z ∪ Z \ Y) : Set V) => u.1 ∈ W) ↔
      ∀ u ∈ (Y \ Z ∪ Z \ Y), x u = if u ∈ W then 1 else 0 := by
    intro W
    constructor
    · intro h u hu
      have := congrFun h ⟨u, by simpa using hu⟩
      simpa [hxr, incidenceVector] using this
    · intro h; funext a
      have ha : a.1 ∈ (Y \ Z ∪ Z \ Y) := by simpa using a.2
      simp [hxr, incidenceVector, h a.1 ha]
  have hYc := ct_ind Y Z x
  have hZc := ct_ind Z Y x
  rw [Finset.union_comm (Z \ Y), Finset.inter_comm Z Y] at hZc
  rw [hA, hA, hYc, hZc]
  constructor
  · rintro ⟨h | h, h'⟩
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr ⟨h, h'⟩
  · rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact ⟨Or.inl h, h'⟩
    · exact ⟨Or.inr h, h'⟩


lemma mn_onesSet {V : Type*} [DecidableEq V] (S : Finset V) :
    onesSet (incidenceVector S) = (S : Set V) := by
  ext u; simp [onesSet, incidenceVector]

lemma mn_mix {V : Type*} [DecidableEq V] (G : SimpleGraph V) (A B D1 : Finset V)
    (hA : G.IsIndepSet (A : Set V)) (hB : G.IsIndepSet (B : Set V))
    (hcl : ∀ u v, u ∈ A \ B → v ∈ B \ A → G.Adj u v → u ∈ D1 → v ∈ D1) :
    G.IsIndepSet (((A ∩ B) ∪ ((A \ B) ∩ D1) ∪ ((B \ A) \ D1) : Finset V) : Set V) := by
  have hsub : ∀ w, w ∈ ((A ∩ B) ∪ ((A \ B) ∩ D1) ∪ ((B \ A) \ D1) : Finset V) →
      (w ∈ A ∧ (w ∈ B ∨ w ∈ D1)) ∨ (w ∈ B \ A ∧ w ∉ D1) := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hw ⊢
    tauto
  intro u hu v hv huv hadj
  rcases hsub u hu with ⟨hua, hu2⟩ | ⟨hub, hu2⟩ <;> rcases hsub v hv with ⟨hva, hv2⟩ | ⟨hvb, hv2⟩
  · exact hA hua hva huv hadj
  · by_cases hB' : u ∈ B
    · exact hB hB' (Finset.mem_sdiff.mp hvb).1 huv hadj
    · have hD : u ∈ D1 := hu2.resolve_left hB'
      exact hv2 (hcl u v (Finset.mem_sdiff.mpr ⟨hua, hB'⟩) hvb hadj hD)
  · by_cases hB' : v ∈ B
    · exact hB (Finset.mem_sdiff.mp hub).1 hB' huv hadj
    · have hD : v ∈ D1 := hv2.resolve_left hB'
      exact hu2 (hcl v u (Finset.mem_sdiff.mpr ⟨hva, hB'⟩) hub hadj.symm hD)
  · exact hB (Finset.mem_sdiff.mp hub).1 (Finset.mem_sdiff.mp hvb).1 huv hadj

theorem mn_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (y z : V → ℝ) (hy : y ∈ stableVectors G) (hz : z ∈ stableVectors G) :
    AreNeighbors G y z ↔
      (G.induce ((onesSet y \ onesSet z) ∪ (onesSet z \ onesSet y))).Connected := by
  classical
  obtain ⟨Y, hY, rfl⟩ := hy
  obtain ⟨Z, hZ, rfl⟩ := hz
  have hset : (onesSet (incidenceVector Y) \ onesSet (incidenceVector Z)) ∪
      (onesSet (incidenceVector Z) \ onesSet (incidenceVector Y)) =
      (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) := by
    rw [mn_onesSet, mn_onesSet]; push_cast; rfl
  rw [hset]
  constructor
  · rintro ⟨hne, c, hc⟩
    by_contra hH
    have hymax : ∀ x' ∈ stableVectors G, intDot c x' ≤ intDot c (incidenceVector Y) := by
      have : incidenceVector Y ∈ ({incidenceVector Y, incidenceVector Z} : Set (V → ℝ)) := by simp
      rw [← hc] at this; exact this.2
    have hzmax : ∀ x' ∈ stableVectors G, intDot c x' ≤ intDot c (incidenceVector Z) := by
      have : incidenceVector Z ∈ ({incidenceVector Y, incidenceVector Z} : Set (V → ℝ)) := by simp
      rw [← hc] at this; exact this.2
    have hDne : ((Y \ Z) ∪ (Z \ Y)).Nonempty := by
      by_contra hE
      rw [Finset.not_nonempty_iff_eq_empty] at hE
      apply hne; funext u
      have : u ∉ (Y \ Z) ∪ (Z \ Y) := by rw [hE]; simp
      simp only [Finset.mem_union, Finset.mem_sdiff] at this
      simp only [incidenceVector]
      by_cases h1 : u ∈ Y <;> by_cases h2 : u ∈ Z <;> simp_all
    obtain ⟨a0, ha0⟩ := hDne
    set H := G.induce (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) with hHdef
    have hnp : ¬ H.Preconnected := by
      intro hp
      haveI : Nonempty (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) := ⟨⟨a0, by simpa using ha0⟩⟩
      exact hH ⟨hp⟩
    have : ∃ a b : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V), ¬ H.Reachable a b := by
      by_contra h; push_neg at h; exact hnp h
    obtain ⟨a, b, hab⟩ := this
    let D1 : Finset V := Finset.univ.filter fun v =>
      ∃ h : v ∈ (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V), H.Reachable a ⟨v, h⟩
    have hcl : ∀ A B : Finset V, (A = Y ∧ B = Z) ∨ (A = Z ∧ B = Y) →
        ∀ u v, u ∈ A \ B → v ∈ B \ A → G.Adj u v → u ∈ D1 → v ∈ D1 := by
      intro A B hAB u v hu hv huv hu1
      simp only [D1, Finset.mem_filter, Finset.mem_univ, true_and] at hu1 ⊢
      obtain ⟨hu', hr⟩ := hu1
      have hv' : v ∈ (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) := by
        rcases hAB with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hv <;> simp only [Finset.mem_sdiff] at hv <;> simp <;> tauto
      refine ⟨hv', hr.trans (SimpleGraph.Adj.reachable ?_)⟩
      simpa [hHdef] using huv
    have hY' := mn_mix G Y Z D1 hY hZ (hcl Y Z (Or.inl ⟨rfl, rfl⟩))
    have hZ' := mn_mix G Z Y D1 hZ hY (hcl Z Y (Or.inr ⟨rfl, rfl⟩))
    set Y' := ((Y ∩ Z) ∪ ((Y \ Z) ∩ D1) ∪ ((Z \ Y) \ D1) : Finset V) with hY'def
    set Z' := ((Z ∩ Y) ∪ ((Z \ Y) ∩ D1) ∪ ((Y \ Z) \ D1) : Finset V) with hZ'def
    have hsum : ∀ u, incidenceVector Y' u + incidenceVector Z' u =
        incidenceVector Y u + incidenceVector Z u := by
      intro u
      simp only [incidenceVector, hY'def, hZ'def, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff]
      by_cases h1 : u ∈ Y <;> by_cases h2 : u ∈ Z <;> by_cases h3 : u ∈ D1 <;> simp [h1, h2, h3]
    have hlin : intDot c (incidenceVector Y') + intDot c (incidenceVector Z') =
        intDot c (incidenceVector Y) + intDot c (incidenceVector Z) := by
      unfold intDot
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← mul_add, ← mul_add, hsum]
    have h1 := hymax _ ⟨Y', hY', rfl⟩
    have h2 := hymax _ ⟨Z', hZ', rfl⟩
    have h3 := hzmax _ ⟨Y, hY, rfl⟩
    have h4 := hymax _ ⟨Z, hZ, rfl⟩
    have hmem : incidenceVector Y' ∈
        {x | x ∈ stableVectors G ∧ ∀ x' ∈ stableVectors G, intDot c x' ≤ intDot c x} := by
      refine ⟨⟨Y', hY', rfl⟩, fun x' hx' => ?_⟩
      have := hymax x' hx'
      linarith
    rw [hc] at hmem
    have haD1 : a.1 ∈ D1 := by
      simp only [D1, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨a.2, SimpleGraph.Reachable.refl _⟩
    have hbD1 : b.1 ∉ D1 := by
      simp only [D1, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
      intro h hr; exact hab hr
    have ha := a.2
    have hb := b.2
    simp only [Finset.coe_union, Finset.coe_sdiff, Set.mem_union, Set.mem_diff,
      Finset.mem_coe] at ha hb
    rcases hmem with h | h
    · -- Y' = Y as vectors, look at b
      have := congrFun h b.1
      simp only [incidenceVector, hY'def, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff] at this
      rcases hb with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> simp [hb1, hb2, hbD1] at this
    · have := congrFun h a.1
      simp only [incidenceVector, hY'def, Finset.mem_union, Finset.mem_inter,
        Finset.mem_sdiff] at this
      rcases ha with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ <;> simp [ha1, ha2, haD1] at this
  · intro hH
    obtain ⟨T, hTle, hT⟩ := hH.exists_isTree_le
    have hbic : IsBicoloration T
        (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Y \ Z)
        (Finset.univ.filter fun u : (((Y \ Z) ∪ (Z \ Y) : Finset V) : Set V) => u.1 ∈ Z \ Y) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro u h1 h2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff] at h1 h2
        exact h1.2 h2.1
      · ext u
        have := u.2
        simp only [Finset.coe_union, Finset.coe_sdiff, Set.mem_union, Set.mem_diff,
          Finset.mem_coe] at this
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_sdiff]
        tauto
      · intro u v huv
        have hG : G.Adj u.1 v.1 := by
          have := hTle huv
          simpa using this
        have hu := u.2
        have hv := v.2
        simp only [Finset.coe_union, Finset.coe_sdiff, Set.mem_union, Set.mem_diff,
          Finset.mem_coe] at hu hv
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
        have hne : u.1 ≠ v.1 := G.ne_of_adj hG
        rcases hu with hu | hu <;> rcases hv with hv | hv
        · exact absurd hG (hY hu.1 hv.1 hne)
        · exact Or.inl ⟨hu, hv⟩
        · exact Or.inr ⟨hu, hv⟩
        · exact absurd hG (hZ hu.1 hv.1 hne)
    obtain ⟨c', m, hc'⟩ := tb_core T hT _ _ hbic
    have key := ct_core G Y Z hY hZ T hTle c' m hc'
    obtain ⟨⟨a, ha⟩⟩ := hH.nonempty
    refine ⟨?_, fun u => if h : u ∈ (Y \ Z) ∪ (Z \ Y) then (c' ⟨u, by simpa using h⟩ : ℤ)
      else if u ∈ Y ∩ Z then 1 else -1, ?_⟩
    · intro h
      have := congrFun h a
      simp only [Finset.coe_union, Finset.coe_sdiff, Set.mem_union, Set.mem_diff,
        Finset.mem_coe] at ha
      simp only [incidenceVector] at this
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] at this
    · have kY := (key _ ⟨Y, hY, rfl⟩).2.mpr (Or.inl rfl)
      have kZ := (key _ ⟨Z, hZ, rfl⟩).2.mpr (Or.inr rfl)
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx, hmax⟩
        have h1 := hmax _ ⟨Y, hY, rfl⟩
        have h2 := (key x hx).1
        unfold intDot at h1
        exact ((key x hx).2).mp (le_antisymm h2 (by rw [← kY]; exact h1))
      · rintro (rfl | rfl)
        · refine ⟨⟨Y, hY, rfl⟩, fun x' hx' => ?_⟩
          unfold intDot; rw [kY]; exact (key x' hx').1
        · refine ⟨⟨Z, hZ, rfl⟩, fun x' hx' => ?_⟩
          unfold intDot; rw [kZ]; exact (key x' hx').1

end ChvatalPolytopes.Neighbors

open ChvatalPolytopes.Neighbors


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (y z : V → ℝ) (hy : y ∈ stableVectors G) (hz : z ∈ stableVectors G) :
    AreNeighbors G y z ↔
      (G.induce ((onesSet y \ onesSet z) ∪ (onesSet z \ onesSet y))).Connected := by
  exact mn_core G y z hy hz
