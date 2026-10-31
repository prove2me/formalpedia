-- Prove2me | solution 2 for Erdos77.cgms_exponential_improvement
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-30T12:01:15.472208+00:00
-- url     : https://prove2.me/submissions/520533a3-2a6f-489e-9b02-35fd56a2568f

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

-- BEGIN CGProof/SharedBasics.lean

open scoped BigOperators
open Filter Topology

namespace Erdos77.CGFresh

variable {V : Type*}

noncomputable def colorGraph (G : SimpleGraph V) (c : Bool) : SimpleGraph V :=
  if c then G else Gᶜ

noncomputable def neighbors (G : SimpleGraph V) (c : Bool) (x : V)
    (Y : Finset V) : Finset V := by
  classical
  exact Y.filter ((colorGraph G c).Adj x)

noncomputable def minDegree (G : SimpleGraph V) (c : Bool)
    (X Y : Finset V) (hX : X.Nonempty) : ℕ :=
  X.inf' hX (fun x => (neighbors G c x Y).card)

noncomputable def density (G : SimpleGraph V) (c : Bool)
    (X Y : Finset V) (hX : X.Nonempty) : ℝ :=
  (minDegree G c X Y hX : ℝ) / (Y.card : ℝ)

end Erdos77.CGFresh

-- END CGProof/SharedBasics.lean

-- BEGIN CGProof/BookBasics.lean

namespace Erdos77.CGFresh

structure IsBook {V : Type*} (G : SimpleGraph V) (A B : Finset V) : Prop where
  clique : G.IsClique A
  disjoint : Disjoint A B
  cut : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b

namespace IsBook

variable {V : Type*} {G : SimpleGraph V} {A B C : Finset V}

theorem empty (B : Finset V) : IsBook G ∅ B := by
  exact ⟨by simp, by simp, by simp⟩

theorem restrict (h : IsBook G A B) (hC : C ⊆ B) : IsBook G A C :=
  ⟨h.clique, h.disjoint.mono_right hC,
    fun a ha b hb => h.cut a ha b (hC hb)⟩

theorem insert_spine [DecidableEq V] (h : IsBook G A B) {x : V}
    (hxa : ∀ a ∈ A, G.Adj x a) (hC : C ⊆ B)
    (hxc : ∀ c ∈ C, G.Adj x c) : IsBook G (insert x A) C := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Finset.coe_insert] using h.clique.insert (fun a ha _ => hxa a ha)
  · apply Finset.disjoint_left.mpr
    intro a ha hc
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (hxc a hc).ne rfl
    · exact Finset.disjoint_left.mp h.disjoint ha (hC hc)
  · intro a ha c hc
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hxc c hc
    · exact h.cut a ha c (hC hc)

theorem extend_clique [DecidableEq V] (h : IsBook G A B) {K : Finset V}
    (hK : K ⊆ B) (hc : G.IsClique K) : G.IsClique (A ∪ K : Finset V) := by
  intro x hx y hy hxy
  change x ∈ (A ∪ K : Finset V) at hx
  change y ∈ (A ∪ K : Finset V) at hy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · exact h.clique hx hy hxy
  · exact h.cut x hx y (hK hy)
  · exact (h.cut y hy x (hK hx)).symm
  · exact hc hx hy hxy

theorem extend_nclique [DecidableEq V] (h : IsBook G A B) {K : Finset V}
    {k : ℕ} (hK : K ⊆ B) (hc : G.IsNClique k K) :
    G.IsNClique (A.card + k) (A ∪ K) := by
  refine ⟨h.extend_clique hK hc.isClique, ?_⟩
  rw [Finset.card_union_of_disjoint (h.disjoint.mono_right hK), hc.card_eq]

end IsBook

structure BookState (V : Type*) where
  reservoir : Finset V
  pages : Bool → Finset V
  spine : Bool → Finset V

def BookState.Valid {V : Type*} (G : SimpleGraph V) (s : BookState V) : Prop :=
  (∀ c, IsBook (colorGraph G c) (s.spine c) s.reservoir) ∧
  (∀ c, IsBook (colorGraph G c) (s.spine c) (s.pages c)) ∧
  Disjoint (s.spine false) (s.spine true)

end Erdos77.CGFresh

-- END CGProof/BookBasics.lean

-- BEGIN CGProof/NeighborPartition.lean

namespace Erdos77.CGFresh

theorem mem_neighbors {V : Type*} (G : SimpleGraph V) (c : Bool)
    (x y : V) (S : Finset V) :
    y ∈ neighbors G c x S ↔ y ∈ S ∧ (colorGraph G c).Adj x y := by
  classical
  simp only [neighbors, Finset.mem_filter]

theorem neighbors_subset {V : Type*} (G : SimpleGraph V) (c : Bool)
    (x : V) (S : Finset V) : neighbors G c x S ⊆ S := by
  intro y hy
  exact ((mem_neighbors G c x y S).mp hy).1

theorem self_not_neighbors {V : Type*} (G : SimpleGraph V) (c : Bool)
    (x : V) (S : Finset V) : x ∉ neighbors G c x S := by
  intro hx
  exact ((mem_neighbors G c x x S).mp hx).2.ne rfl

theorem neighbors_card_lt {V : Type*} (G : SimpleGraph V) (c : Bool)
    {x : V} {S : Finset V} (hx : x ∈ S) : (neighbors G c x S).card < S.card := by
  classical
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨neighbors_subset G c x S, by
    intro he
    exact self_not_neighbors G c x S (he.symm ▸ hx)⟩

theorem neighbors_partition_card {V : Type*} (G : SimpleGraph V)
    {x : V} {S : Finset V} (hx : x ∈ S) :
    (neighbors G false x S).card + (neighbors G true x S).card + 1 = S.card := by
  classical
  have hd : Disjoint (neighbors G false x S) (neighbors G true x S) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have hb := ((mem_neighbors G false x y S).mp hy).2
    have hr := ((mem_neighbors G true x y S).mp hz).2
    exact hb.2 hr
  have hu : neighbors G false x S ∪ neighbors G true x S = S.erase x := by
    ext y
    simp only [Finset.mem_union, mem_neighbors, colorGraph, Bool.false_eq_true,
      if_false, if_true, SimpleGraph.compl_adj, Finset.mem_erase]
    constructor
    · rintro (⟨hy, hne, _⟩ | ⟨hy, ha⟩)
      · exact ⟨hne.symm, hy⟩
      · exact ⟨ha.ne.symm, hy⟩
    · rintro ⟨hne, hy⟩
      by_cases ha : G.Adj x y
      · exact Or.inr ⟨hy, ha⟩
      · exact Or.inl ⟨hy, hne.symm, ha⟩
  rw [← Finset.card_union_of_disjoint hd, hu]
  exact Finset.card_erase_add_one hx

theorem other_color_large {V : Type*} (G : SimpleGraph V) {S : Finset V}
    {x : V} (hx : x ∈ S) {δ : ℝ} (hδ : 0 ≤ δ) (c : Bool)
    (hsmall : ((neighbors G c x S).card : ℝ) < (1 / 2 - δ) * S.card - 1) :
    ((1 + δ) / 2) * S.card ≤ ((neighbors G (!c) x S).card : ℝ) := by
  have he := neighbors_partition_card G hx
  have her : ((neighbors G false x S).card : ℝ) +
      (neighbors G true x S).card + 1 = S.card := by exact_mod_cast he
  have hp : 0 ≤ δ * (S.card : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
  cases c <;> simp only [Bool.not_false, Bool.not_true] <;> linarith

end Erdos77.CGFresh

-- END CGProof/NeighborPartition.lean

-- BEGIN CGProof/DensityBasics.lean

namespace Erdos77.CGFresh

variable {V : Type*} (G : SimpleGraph V) (c : Bool) (X Y : Finset V)

@[simp] theorem density_mem_neighbors (x y : V) :
    y ∈ neighbors G c x Y ↔ y ∈ Y ∧ (colorGraph G c).Adj x y := by
  classical
  simp [neighbors]

theorem density_neighbors_subset (x : V) : neighbors G c x Y ⊆ Y := by
  classical
  exact Finset.filter_subset _ _

theorem minDegree_le (hX : X.Nonempty) {x : V} (hx : x ∈ X) :
    minDegree G c X Y hX ≤ (neighbors G c x Y).card :=
  Finset.inf'_le _ hx

theorem minDegree_attained (hX : X.Nonempty) :
    ∃ x ∈ X, (neighbors G c x Y).card = minDegree G c X Y hX := by
  have hh : X.inf' hX (fun x => (neighbors G c x Y).card) ≤ minDegree G c X Y hX := le_rfl
  obtain ⟨x, hx, he⟩ := (Finset.inf'_le_iff hX).mp hh
  exact ⟨x, hx, le_antisymm he (minDegree_le G c X Y hX hx)⟩

theorem minDegree_le_card (hX : X.Nonempty) : minDegree G c X Y hX ≤ Y.card := by
  obtain ⟨x, hx⟩ := hX
  exact (minDegree_le G c X Y ⟨x, hx⟩ hx).trans
    (Finset.card_le_card (density_neighbors_subset G c Y x))

theorem density_nonneg (hX : X.Nonempty) : 0 ≤ density G c X Y hX := by
  unfold density
  positivity

theorem density_le_one (hX : X.Nonempty) (hY : Y.Nonempty) : density G c X Y hX ≤ 1 := by
  have hy : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  rw [density, div_le_one hy]
  exact_mod_cast minDegree_le_card G c X Y hX

theorem density_mul_card (hX : X.Nonempty) (hY : Y.Nonempty) :
    density G c X Y hX * (Y.card : ℝ) = minDegree G c X Y hX := by
  unfold density
  exact div_mul_cancel₀ _ (by exact_mod_cast hY.card_pos.ne')

theorem density_le_of_counts (hX : X.Nonempty) (hY : Y.Nonempty) (p : ℝ)
    (hp : ∀ x ∈ X, p * (Y.card : ℝ) ≤ (neighbors G c x Y).card) :
    p ≤ density G c X Y hX := by
  obtain ⟨x, hx, he⟩ := minDegree_attained G c X Y hX
  have hy : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  rw [density, le_div_iff₀ hy, ← he]
  exact hp x hx

theorem density_le_count (hX : X.Nonempty) (hY : Y.Nonempty) {x : V} (hx : x ∈ X) :
    density G c X Y hX * (Y.card : ℝ) ≤ (neighbors G c x Y).card := by
  rw [density_mul_card G c X Y hX hY]
  exact_mod_cast minDegree_le G c X Y hX hx

theorem density_mono_reservoir (X' : Finset V) (hX : X.Nonempty) (hX' : X'.Nonempty)
    (hsub : X' ⊆ X) (hY : Y.Nonempty) :
    density G c X Y hX ≤ density G c X' Y hX' := by
  apply density_le_of_counts G c X' Y hX' hY
  intro x hx
  exact density_le_count G c X Y hX hY (hsub hx)

end Erdos77.CGFresh

-- END CGProof/DensityBasics.lean

-- BEGIN CGProof/KeyStep.lean

namespace Erdos77.CGFresh

structure KeyStep {V : Type*} (G : SimpleGraph V) (X : Finset V)
    (Y : Bool → Finset V) (hX : X.Nonempty) (α : Bool → ℝ) where
  vertex : V
  vertex_mem : vertex ∈ X
  color : Bool
  level : ℝ
  level_lower : -1 ≤ level
  reservoir : Finset V
  reservoir_subset : reservoir ⊆ X
  reservoir_nonempty : reservoir.Nonempty
  pages : Bool → Finset V
  pages_subset : ∀ c, pages c ⊆ neighbors G c vertex (Y c)
  pages_nonempty : ∀ c, (pages c).Nonempty
  pages_card : ∀ c, (pages c).card = minDegree G c X (Y c) hX
  reservoir_card : Real.exp (-20 - 24 * Real.sqrt (level + 1)) * (X.card : ℝ) ≤
    (reservoir.card : ℝ)
  selected_density : density G color X (Y color) hX + level * α color ≤
    density G color reservoir (pages color) reservoir_nonempty
  all_density : ∀ c, density G c X (Y c) hX - α c ≤
    density G c reservoir (pages c) reservoir_nonempty

end Erdos77.CGFresh

-- END CGProof/KeyStep.lean

-- BEGIN CGProof/BookMove.lean

namespace Erdos77.CGFresh

noncomputable def BookState.colorMove {V : Type*} (s : BookState V)
    (j : Bool) (x : V) (R Y : Finset V) : BookState V := by
  classical
  exact ⟨R, Function.update s.pages j Y,
    Function.update s.spine j (insert x (s.spine j))⟩

noncomputable def BookState.boostMove {V : Type*} (s : BookState V)
    (j : Bool) (R Y : Finset V) : BookState V :=
  ⟨R, Function.update s.pages j Y, s.spine⟩

theorem BookState.Valid.colorMove {V : Type*} {G : SimpleGraph V} {s : BookState V}
    (hs : s.Valid G) (j : Bool) {x : V} (hx : x ∈ s.reservoir)
    {R Y : Finset V} (hR : R ⊆ neighbors G j x s.reservoir)
    (hY : Y ⊆ neighbors G j x (s.pages j)) : (s.colorMove j x R Y).Valid G := by
  classical
  have hRS := hR.trans (neighbors_subset G j x s.reservoir)
  have hYS := hY.trans (neighbors_subset G j x (s.pages j))
  have hxa : ∀ a ∈ s.spine j, (colorGraph G j).Adj x a :=
    fun a ha => ((hs.1 j).cut a ha x hx).symm
  have hxR : ∀ a ∈ R, (colorGraph G j).Adj x a :=
    fun a ha => ((mem_neighbors G j x a s.reservoir).mp (hR ha)).2
  have hxY : ∀ a ∈ Y, (colorGraph G j).Adj x a :=
    fun a ha => ((mem_neighbors G j x a (s.pages j)).mp (hY ha)).2
  have hnot (b : Bool) : x ∉ s.spine b := by
    intro hb
    exact Finset.disjoint_left.mp (hs.1 b).disjoint hb hx
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b = j
    · subst b
      simpa only [BookState.colorMove, Function.update_self] using
        (hs.1 j).insert_spine hxa hRS hxR
    · simpa only [BookState.colorMove, Function.update_of_ne hb] using
        (hs.1 b).restrict hRS
  · intro b
    by_cases hb : b = j
    · subst b
      simpa only [BookState.colorMove, Function.update_self] using
        (hs.2.1 j).insert_spine hxa hYS hxY
    · simpa only [BookState.colorMove, Function.update_of_ne hb] using hs.2.1 b
  · cases j <;> simp [BookState.colorMove, Finset.disjoint_insert_left,
      Finset.disjoint_insert_right, hnot, hs.2.2]

theorem BookState.Valid.boostMove {V : Type*} {G : SimpleGraph V} {s : BookState V}
    (hs : s.Valid G) (j : Bool) {R Y : Finset V} (hR : R ⊆ s.reservoir)
    (hY : Y ⊆ s.pages j) : (s.boostMove j R Y).Valid G := by
  refine ⟨fun b => (hs.1 b).restrict hR, ?_, hs.2.2⟩
  intro b
  by_cases hb : b = j
  · subst b
    simpa only [BookState.boostMove, Function.update_self] using (hs.2.1 j).restrict hY
  · simpa only [BookState.boostMove, Function.update_of_ne hb] using hs.2.1 b

theorem colorMove_spine_card {V : Type*} {G : SimpleGraph V} {s : BookState V}
    (hs : s.Valid G) (j : Bool) {x : V} (hx : x ∈ s.reservoir)
    (R Y : Finset V) (b : Bool) :
    ((s.colorMove j x R Y).spine b).card = (s.spine b).card + if b = j then 1 else 0 := by
  classical
  have hnot : x ∉ s.spine j := by
    intro hh
    exact Finset.disjoint_left.mp (hs.1 j).disjoint hh hx
  by_cases hb : b = j
  · subst b
    simp [BookState.colorMove, hnot]
  · simp [BookState.colorMove, hb]

end Erdos77.CGFresh

-- END CGProof/BookMove.lean

-- BEGIN CGProof/KeyMove.lean

namespace Erdos77.CGFresh

theorem neighbors_insert_self {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (c : Bool) (x : V) (S : Finset V) :
    neighbors G c x (insert x S) = neighbors G c x S := by
  ext y
  simp only [mem_neighbors, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hy, ha⟩
    · exact False.elim (ha.ne rfl)
    · exact ⟨hy, ha⟩
  · rintro ⟨hy, ha⟩
    exact ⟨Or.inr hy, ha⟩

theorem exists_large_color {V : Type*} (G : SimpleGraph V) (x : V) (S : Finset V) :
    ∃ c : Bool, (S.card : ℝ) - 1 ≤ 2 * ((neighbors G c x S).card : ℝ) := by
  classical
  have hh := neighbors_partition_card G (Finset.mem_insert_self x S)
  rw [neighbors_insert_self, neighbors_insert_self] at hh
  have hc := Finset.card_le_card (Finset.subset_insert x S)
  have hr : ((neighbors G false x S).card : ℝ) +
      (neighbors G true x S).card + 1 = (insert x S).card := by exact_mod_cast hh
  have hs : (S.card : ℝ) ≤ (insert x S).card := by exact_mod_cast hc
  by_cases h : (S.card : ℝ) - 1 ≤ 2 * ((neighbors G false x S).card : ℝ)
  · exact ⟨false, h⟩
  · exact ⟨true, by linarith⟩

namespace KeyStep

variable {V : Type*} {G : SimpleGraph V} {X : Finset V} {Y : Bool → Finset V}
  {hX : X.Nonempty} {α : Bool → ℝ}

theorem color_density (w : KeyStep G X Y hX α) (j b : Bool)
    (hY : ∀ c, (Y c).Nonempty)
    (hR : (neighbors G j w.vertex w.reservoir).Nonempty) :
    (if b = j then density G b X (Y b) hX - α b else density G b X (Y b) hX) ≤
      density G b (neighbors G j w.vertex w.reservoir)
        (Function.update Y j (w.pages j) b) hR := by
  classical
  by_cases hb : b = j
  · subst b
    simp only [if_true, Function.update_self]
    exact (w.all_density j).trans
      (density_mono_reservoir G j w.reservoir (w.pages j) _ w.reservoir_nonempty hR
        (neighbors_subset G j w.vertex w.reservoir) (w.pages_nonempty j))
  · simp only [if_neg hb, Function.update_of_ne hb]
    exact density_mono_reservoir G b X (Y b) _ hX hR
      ((neighbors_subset G j w.vertex w.reservoir).trans w.reservoir_subset) (hY b)

theorem boost_density (w : KeyStep G X Y hX α) (b : Bool)
    (hY : ∀ c, (Y c).Nonempty) :
    (if b = w.color then density G b X (Y b) hX + w.level * α b else
      density G b X (Y b) hX) ≤
      density G b w.reservoir (Function.update Y w.color (w.pages w.color) b)
        w.reservoir_nonempty := by
  classical
  by_cases hb : b = w.color
  · subst b
    simpa only [if_true, Function.update_self] using w.selected_density
  · simp only [if_neg hb, Function.update_of_ne hb]
    exact density_mono_reservoir G b X (Y b) _ hX w.reservoir_nonempty
      w.reservoir_subset (hY b)

theorem color_reservoir_bound (w : KeyStep G X Y hX α) (L : ℝ)
    (hcut : w.level ≤ L ^ 2) (j : Bool)
    (hj : (w.reservoir.card : ℝ) - 1 ≤ 2 *
      ((neighbors G j w.vertex w.reservoir).card : ℝ)) :
    Real.exp (-(Real.log 2 + 20 + 24 * Real.sqrt (L ^ 2 + 1))) * (X.card : ℝ) - 1 ≤
      ((neighbors G j w.vertex w.reservoir).card : ℝ) := by
  have hs := Real.sqrt_le_sqrt (show w.level + 1 ≤ L ^ 2 + 1 by linarith)
  have he : Real.exp (-20 - 24 * Real.sqrt (L ^ 2 + 1)) ≤
      Real.exp (-20 - 24 * Real.sqrt (w.level + 1)) := Real.exp_le_exp.mpr (by linarith)
  have hm := (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg X.card)).trans w.reservoir_card
  have hid : Real.exp (-(Real.log 2 + 20 + 24 * Real.sqrt (L ^ 2 + 1))) =
      Real.exp (-20 - 24 * Real.sqrt (L ^ 2 + 1)) / 2 := by
    rw [show -(Real.log 2 + 20 + 24 * Real.sqrt (L ^ 2 + 1)) =
      (-20 - 24 * Real.sqrt (L ^ 2 + 1)) - Real.log 2 by ring,
      Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hid]
  linarith

end KeyStep

end Erdos77.CGFresh

-- END CGProof/KeyMove.lean

-- BEGIN CGProof/BookScalar.lean

namespace Erdos77.CGFresh

theorem survival_step (n : ℕ) (hn : 2 ≤ n) :
    (((n : ℝ) - 1) / n) ^ n ≤ ((n : ℝ) / (n + 1)) ^ (n + 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn1 : (0 : ℝ) < n + 1 := by linarith
  have hd : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  let a : ℝ := ((n : ℝ) - 1) / n
  let b : ℝ := (n : ℝ) / (n + 1)
  let c : ℝ := 1 + 1 / ((n : ℝ) ^ 2 - 1)
  have ha : 0 ≤ a := div_nonneg (by linarith) hn0.le
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 1 + (n : ℝ) / ((n : ℝ) ^ 2 - 1) ≤ c ^ n := by
    simpa only [c, mul_one_div] using
      (one_add_mul_le_pow (by
        have : 0 ≤ 1 / ((n : ℝ) ^ 2 - 1) := by positivity
        linarith : (-2 : ℝ) ≤ 1 / ((n : ℝ) ^ 2 - 1)) n)
  have hbc : 1 ≤ b * (1 + (n : ℝ) / ((n : ℝ) ^ 2 - 1)) := by
    dsimp only [b]
    rw [div_mul_eq_mul_div, le_div_iff₀ hn1]
    have hfrac : 1 ≤ (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by
      rw [le_div_iff₀ hd]
      linarith
    have he : (n : ℝ) * (1 + (n : ℝ) / ((n : ℝ) ^ 2 - 1)) =
        n + (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by ring
    rw [he]
    linarith
  have hbc' : 1 ≤ b * c ^ n := hbc.trans (mul_le_mul_of_nonneg_left hc hb)
  have hab : a * c = b := by
    dsimp [a, b, c]
    field_simp
    ring
  change a ^ n ≤ b ^ (n + 1)
  calc
    a ^ n = a ^ n * 1 := by ring
    _ ≤ a ^ n * (b * c ^ n) := mul_le_mul_of_nonneg_left hbc' (pow_nonneg ha _)
    _ = (a * c) ^ n * b := by rw [mul_pow]; ring
    _ = b ^ (n + 1) := by rw [hab, pow_succ]

theorem survival_quarter (t : ℕ) (ht : 2 ≤ t) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (t : ℝ)) ^ t := by
  have hmain : ∀ n : ℕ, 2 ≤ n → (1 / 4 : ℝ) ≤ (((n : ℝ) - 1) / n) ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      simpa only [Nat.cast_succ, add_sub_cancel_right] using
        ih.trans (survival_step n hn)
  have he : (1 : ℝ) - 1 / (t : ℝ) = ((t : ℝ) - 1) / t := by
    have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
    field_simp
  rw [he]
  exact hmain t ht

end Erdos77.CGFresh

-- END CGProof/BookScalar.lean

-- BEGIN CGProof/DensityLedger.lean

namespace Erdos77.CGFresh

structure BookEvent where
  color : Bool
  boost : Bool
  level : ℝ

def colorSteps (e : ℕ → BookEvent) (c : Bool) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => (e i).color = c ∧ (e i).boost = false)

def boostSteps (e : ℕ → BookEvent) (c : Bool) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => (e i).color = c ∧ (e i).boost = true)

noncomputable def densityFactor (e : BookEvent) (c : Bool) (t : ℕ) : ℝ :=
  (if e.color = c ∧ e.boost = false then 1 - 1 / (t : ℝ) else 1) *
  (if e.color = c ∧ e.boost = true then 1 + e.level / (t : ℝ) else 1)

theorem finite_product_ledger (d f : ℕ → ℝ) (δ : ℝ) (N : ℕ)
    (hzero : δ ≤ d 0) (hf : ∀ i < N, 0 ≤ f i)
    (hstep : ∀ i < N, f i * d i ≤ d (i + 1)) :
    δ * ∏ i ∈ Finset.range N, f i ≤ d N := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
      have hh := ih (fun i hi => hf i (by omega)) (fun i hi => hstep i (by omega))
      rw [Finset.prod_range_succ]
      calc
        δ * ((∏ i ∈ Finset.range N, f i) * f N) =
            f N * (δ * ∏ i ∈ Finset.range N, f i) := by ring
        _ ≤ f N * d N := mul_le_mul_of_nonneg_left hh (hf N (by omega))
        _ ≤ d (N + 1) := hstep N (by omega)

theorem density_factor_product (e : ℕ → BookEvent) (c : Bool) (N t : ℕ) :
    (∏ i ∈ Finset.range N, densityFactor (e i) c t) =
      (1 - 1 / (t : ℝ)) ^ (colorSteps e c N).card *
      ∏ i ∈ boostSteps e c N, (1 + (e i).level / (t : ℝ)) := by
  classical
  have he : (∏ i ∈ Finset.range N,
      if (e i).color = c ∧ (e i).boost = false then 1 - 1 / (t : ℝ) else 1) =
      (1 - 1 / (t : ℝ)) ^ (colorSteps e c N).card := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const, colorSteps]
  simp only [densityFactor, Finset.prod_mul_distrib]
  rw [he]
  simp only [boostSteps, Finset.prod_filter]

theorem density_product_bound (e : ℕ → BookEvent) (c : Bool) (d : ℕ → ℝ)
    (δ : ℝ) (N t : ℕ) (ht : 2 ≤ t) (hδ : 0 ≤ δ)
    (hzero : δ ≤ d 0) (hlevel : ∀ i < N, (e i).boost = true → 0 ≤ (e i).level)
    (hstep : ∀ i < N, densityFactor (e i) c t * d i ≤ d (i + 1))
    (hcount : (colorSteps e c N).card ≤ t) :
    δ / 4 * (∏ i ∈ boostSteps e c N, (1 + (e i).level / (t : ℝ))) ≤ d N := by
  classical
  have htR : (2 : ℝ) ≤ t := by exact_mod_cast ht
  have ht0 : (0 : ℝ) < t := by linarith
  have ha0 : 0 ≤ 1 - 1 / (t : ℝ) := by
    have : 1 / (t : ℝ) ≤ 1 := (div_le_one ht0).mpr (by linarith)
    linarith
  have ha1 : 1 - 1 / (t : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (t : ℝ) := by positivity
    linarith
  have hf : ∀ i < N, 0 ≤ densityFactor (e i) c t := by
    intro i hi
    unfold densityFactor
    apply mul_nonneg
    · split_ifs <;> positivity
    · split_ifs with hh
      · have := hlevel i hi hh.2
        positivity
      · positivity
  have hb : 0 ≤ ∏ i ∈ boostSteps e c N, (1 + (e i).level / (t : ℝ)) := by
    apply Finset.prod_nonneg
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have := hlevel i (Finset.mem_range.mp hh.1) hh.2.2
    positivity
  have hsurv := (survival_quarter t ht).trans (pow_le_pow_of_le_one ha0 ha1 hcount)
  have hh := finite_product_ledger d (fun i => densityFactor (e i) c t) δ N hzero hf hstep
  rw [density_factor_product] at hh
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsurv hδ) hb
  calc
    δ / 4 * (∏ i ∈ boostSteps e c N, (1 + (e i).level / (t : ℝ))) =
        (δ * (1 / 4)) * (∏ i ∈ boostSteps e c N, (1 + (e i).level / (t : ℝ))) := by ring
    _ ≤ _ := hm
    _ ≤ d N := by simpa only [mul_assoc] using hh

end Erdos77.CGFresh

-- END CGProof/DensityLedger.lean

-- BEGIN CGProof/EventCounts.lean

namespace Erdos77.CGFresh

def allSteps (e : ℕ → BookEvent) (c : Bool) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => (e i).color = c)

theorem allSteps_partition (e : ℕ → BookEvent) (c : Bool) (N : ℕ) :
    allSteps e c N = colorSteps e c N ∪ boostSteps e c N := by
  ext i
  simp only [allSteps, colorSteps, boostSteps, Finset.mem_filter, Finset.mem_union]
  cases (e i).boost <;> simp

theorem color_boost_disjoint (e : ℕ → BookEvent) (c : Bool) (N : ℕ) :
    Disjoint (colorSteps e c N) (boostSteps e c N) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have h := (Finset.mem_filter.mp hi).2.2
  have h' := (Finset.mem_filter.mp hj).2.2
  rw [h] at h'
  contradiction

theorem allSteps_card (e : ℕ → BookEvent) (c : Bool) (N : ℕ) :
    (allSteps e c N).card = (colorSteps e c N).card + (boostSteps e c N).card := by
  rw [allSteps_partition, Finset.card_union_of_disjoint (color_boost_disjoint e c N)]

theorem allSteps_total (e : ℕ → BookEvent) (N : ℕ) :
    (allSteps e false N).card + (allSteps e true N).card = N := by
  have hd : Disjoint (allSteps e false N) (allSteps e true N) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h := (Finset.mem_filter.mp hi).2
    have h' := (Finset.mem_filter.mp hj).2
    rw [h] at h'
    contradiction
  have hu : allSteps e false N ∪ allSteps e true N = Finset.range N := by
    ext i
    simp only [allSteps, Finset.mem_union, Finset.mem_filter]
    cases (e i).color <;> simp
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_range]

theorem event_count_total (e : ℕ → BookEvent) (N : ℕ) :
    (colorSteps e false N).card + (colorSteps e true N).card +
      (boostSteps e false N).card + (boostSteps e true N).card = N := by
  have h := allSteps_total e N
  rw [allSteps_card, allSteps_card] at h
  omega

theorem colorSteps_succ_card (e : ℕ → BookEvent) (c : Bool) (N : ℕ) :
    (colorSteps e c (N + 1)).card = (colorSteps e c N).card +
      if (e N).color = c ∧ (e N).boost = false then 1 else 0 := by
  unfold colorSteps
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp

theorem boostSteps_succ_card (e : ℕ → BookEvent) (c : Bool) (N : ℕ) :
    (boostSteps e c (N + 1)).card = (boostSteps e c N).card +
      if (e N).color = c ∧ (e N).boost = true then 1 else 0 := by
  unfold boostSteps
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs <;> simp

end Erdos77.CGFresh

-- END CGProof/EventCounts.lean

-- BEGIN CGProof/SizeLedger.lean

namespace Erdos77.CGFresh

theorem reservoir_ledger (R f d : ℕ → ℝ) (N : ℕ)
    (hf0 : ∀ i < N, 0 ≤ f i) (hf1 : ∀ i < N, f i ≤ 1)
    (hd : ∀ i < N, 0 ≤ d i)
    (hstep : ∀ i < N, f i * R i - d i ≤ R (i + 1)) :
    (∏ i ∈ Finset.range N, f i) * R 0 - (∑ i ∈ Finset.range N, d i) ≤ R N := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hh := ih (fun i hi => hf0 i (by omega)) (fun i hi => hf1 i (by omega))
      (fun i hi => hd i (by omega)) (fun i hi => hstep i (by omega))
    have hm := mul_le_mul_of_nonneg_left hh (hf0 N (by omega))
    have hsum : 0 ≤ ∑ i ∈ Finset.range N, d i :=
      Finset.sum_nonneg (fun i hi => hd i (by have := Finset.mem_range.mp hi; omega))
    have hl := mul_le_mul_of_nonneg_right (hf1 N (by omega)) hsum
    have hs := hstep N (by omega)
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    nlinarith

theorem reservoir_exp_ledger (R cost d : ℕ → ℝ) (N : ℕ)
    (hc : ∀ i < N, 0 ≤ cost i) (hd : ∀ i < N, 0 ≤ d i)
    (hstep : ∀ i < N, Real.exp (-cost i) * R i - d i ≤ R (i + 1)) :
    Real.exp (-(∑ i ∈ Finset.range N, cost i)) * R 0 -
      (∑ i ∈ Finset.range N, d i) ≤ R N := by
  have hh := reservoir_ledger R (fun i => Real.exp (-cost i)) d N
    (fun i _ => (Real.exp_pos _).le)
    (fun i hi => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hc i hi))) hd hstep
  have he : (∏ i ∈ Finset.range N, Real.exp (-cost i)) =
      Real.exp (-(∑ i ∈ Finset.range N, cost i)) := by
    rw [← Real.exp_sum, Finset.sum_neg_distrib]
  simpa only [he] using hh

theorem page_ledger (Y : ℕ → ℝ) (e : ℕ → BookEvent) (c : Bool)
    (v : ℝ) (hv : 0 ≤ v) (N : ℕ)
    (hstep : ∀ i < N, (if (e i).color = c then v else 1) * Y i ≤ Y (i + 1)) :
    v ^ (allSteps e c N).card * Y 0 ≤ Y N := by
  have hh := finite_product_ledger Y (fun i => if (e i).color = c then v else 1)
    (Y 0) N le_rfl (fun i _ => by split_ifs <;> positivity) hstep
  have he : (∏ i ∈ Finset.range N, if (e i).color = c then v else 1) =
      v ^ (allSteps e c N).card := by
    rw [← Finset.prod_filter]
    simp only [Finset.prod_const, allSteps]
  rw [he] at hh
  simpa only [mul_comm] using hh

end Erdos77.CGFresh

-- END CGProof/SizeLedger.lean

-- BEGIN CGProof/BoostScalar.lean

namespace Erdos77.CGFresh

theorem log_one_add_lower (x : ℝ) (hx : 0 ≤ x) :
    min (x / 2) 1 ≤ Real.log (1 + x) := by
  have hh := Real.le_log_one_add_of_nonneg hx
  have hp : 0 < x + 2 := by linarith
  by_cases h : x ≤ 2
  · have hm : x / 2 ≤ 1 := by linarith
    rw [min_eq_left hm]
    apply le_trans ?_ hh
    rw [le_div_iff₀ hp]
    nlinarith
  · have hm : 1 ≤ x / 2 := by linarith
    rw [min_eq_right hm]
    apply le_trans ?_ hh
    rw [le_div_iff₀ hp]
    linarith

theorem boost_sqrt_log (L δ t u : ℝ) (hL : 0 < L) (hδ : 0 < δ)
    (ht : 0 < t) (hsize : L ^ 2 ≤ δ * t) (hlow : L ^ 2 ≤ u)
    (hupp : u ≤ 5 * t / δ) :
    Real.sqrt u ≤ (3 * t / L) * Real.log (1 + u / t) := by
  have hu0 : 0 ≤ u := (sq_nonneg L).trans hlow
  have hs := Real.sq_sqrt hu0
  have hs0 := Real.sqrt_nonneg u
  have hLs : L ≤ Real.sqrt u := by nlinarith
  have hlog := log_one_add_lower (u / t) (div_nonneg hu0 ht.le)
  by_cases hsmall : u ≤ 2 * t
  · have hq : u / t / 2 ≤ 1 := by
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      exact (div_le_iff₀ ht).mpr (by linarith)
    rw [min_eq_left hq] at hlog
    have he : (3 * t / L) * Real.log (1 + u / t) =
        (3 * t * Real.log (1 + u / t)) / L := by ring
    rw [he]
    apply (le_div_iff₀ hL).mpr
    have hmul := (div_le_iff₀ (mul_pos ht (by norm_num : (0 : ℝ) < 2))).mp
      (show u / (t * 2) ≤ Real.log (1 + u / t) by simpa only [div_div] using hlog)
    have hsq := mul_le_mul_of_nonneg_left hLs hs0
    nlinarith
  · have hq : 1 ≤ u / t / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      exact (le_div_iff₀ ht).mpr (by linarith)
    rw [min_eq_right hq] at hlog
    have hu : u * δ ≤ 5 * t := (le_div_iff₀ hδ).mp hupp
    have hm := mul_le_mul_of_nonneg_left hsize hu0
    have hn := mul_le_mul_of_nonneg_right hu ht.le
    have hbound : Real.sqrt u ≤ 3 * t / L := by
      rw [le_div_iff₀ hL]
      have : (Real.sqrt u * L) ^ 2 ≤ 5 * t ^ 2 := by nlinarith
      nlinarith
    exact hbound.trans (le_mul_of_one_le_right (by positivity) hlog)

end Erdos77.CGFresh

-- END CGProof/BoostScalar.lean

-- BEGIN CGProof/BoostBudgets.lean

namespace Erdos77.CGFresh

theorem boost_log_budget {I : Type*} (S : Finset I) (u : I → ℝ)
    (δ t : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (ht : 0 < t)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hprod : δ / 4 * (∏ i ∈ S, (1 + u i / t)) ≤ 1 + δ) :
    (∑ i ∈ S, Real.log (1 + u i / t)) ≤ 2 * Real.log (1 / δ) := by
  have hpos (i : I) (hi : i ∈ S) : 0 < 1 + u i / t := by
    have := hu i hi
    positivity
  have hPpos : 0 < ∏ i ∈ S, (1 + u i / t) := Finset.prod_pos hpos
  have hP : (∏ i ∈ S, (1 + u i / t)) ≤ (1 / δ) ^ 2 := by
    calc
      (∏ i ∈ S, (1 + u i / t)) ≤ (1 + δ) * 4 / δ := by
        rw [le_div_iff₀ hδ]
        nlinarith
      _ ≤ (1 / δ) ^ 2 := by
        rw [div_pow, one_pow, div_le_div_iff₀ hδ (sq_pos_of_pos hδ)]
        have hsq : δ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 :=
          (sq_le_sq₀ hδ.le (by norm_num)).mpr hδsmall
        have hh : (1 + δ) * 4 * δ ≤ 1 := by nlinarith
        have hm := mul_le_mul_of_nonneg_right hh hδ.le
        nlinarith
  have hh := Real.log_le_log hPpos hP
  rw [Real.log_prod (fun i hi => (hpos i hi).ne'), Real.log_pow] at hh
  simpa only [Nat.cast_ofNat] using hh

theorem boost_count_budget {I : Type*} (S : Finset I) (u : I → ℝ)
    (δ t L : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (ht : 0 < t) (hL : 0 < L) (hLt : L ^ 2 ≤ t)
    (hu : ∀ i ∈ S, L ^ 2 ≤ u i)
    (hprod : δ / 4 * (∏ i ∈ S, (1 + u i / t)) ≤ 1 + δ) :
    (S.card : ℝ) ≤ (4 * Real.log (1 / δ) / L ^ 2) * t := by
  have hlow (i : I) (hi : i ∈ S) : L ^ 2 / (2 * t) ≤ Real.log (1 + u i / t) := by
    have hq0 : 0 ≤ L ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
    have hq1 : L ^ 2 / t / 2 ≤ 1 := by
      have : L ^ 2 / t ≤ 1 := (div_le_one ht).mpr hLt
      linarith
    have hh := log_one_add_lower (L ^ 2 / t) hq0
    rw [min_eq_left hq1] at hh
    have hm : Real.log (1 + L ^ 2 / t) ≤ Real.log (1 + u i / t) :=
      Real.log_le_log (by positivity) (add_le_add le_rfl (div_le_div_of_nonneg_right (hu i hi) ht.le))
    have he : L ^ 2 / (2 * t) = L ^ 2 / t / 2 := by ring
    rw [he]
    exact hh.trans hm
  have hs := Finset.sum_le_sum hlow
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hu := boost_log_budget S u δ t hδ hδsmall ht
    (fun i hi => (sq_nonneg L).trans (hu i hi)) hprod
  have hh := hs.trans hu
  have hL2 : 0 < L ^ 2 := sq_pos_of_pos hL
  have hd : 0 < 2 * t := by positivity
  have hm := (div_le_iff₀ hd).mp
    (show (S.card : ℝ) * L ^ 2 / (2 * t) ≤ 2 * Real.log (1 / δ) by
      simpa only [mul_div_assoc] using hh)
  rw [div_mul_eq_mul_div, le_div_iff₀ hL2]
  nlinarith

theorem boost_level_upper {I : Type*} (S : Finset I) (u : I → ℝ)
    (δ t : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (ht : 0 < t)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hprod : δ / 4 * (∏ i ∈ S, (1 + u i / t)) ≤ 1 + δ)
    {i : I} (hi : i ∈ S) : u i ≤ 5 * t / δ := by
  have hf (j : I) (hj : j ∈ S) : 1 ≤ 1 + u j / t := by
    have := div_nonneg (hu j hj) ht.le
    linarith
  classical
  have hsingle : 1 + u i / t ≤ ∏ j ∈ S, (1 + u j / t) := by
    rw [← Finset.mul_prod_erase S (fun j => 1 + u j / t) hi]
    exact le_mul_of_one_le_right (by have := hf i hi; linarith)
      (Finset.one_le_prod (fun j hj => hf j (Finset.mem_of_mem_erase hj)))
  have hh := (mul_le_mul_of_nonneg_left hsingle
    (show 0 ≤ δ / 4 by positivity)).trans hprod
  have hm := mul_le_mul_of_nonneg_right hh ht.le
  have he : δ / 4 * (1 + u i / t) * t = δ / 4 * (t + u i) := by
    field_simp
  rw [he] at hm
  rw [le_div_iff₀ hδ]
  have hd := mul_le_mul_of_nonneg_right hδsmall ht.le
  nlinarith

theorem boost_sqrt_budget {I : Type*} (S : Finset I) (u : I → ℝ)
    (δ t L : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (ht : 0 < t) (hL : 0 < L) (hsize : L ^ 2 ≤ δ * t)
    (hu : ∀ i ∈ S, L ^ 2 ≤ u i)
    (hprod : δ / 4 * (∏ i ∈ S, (1 + u i / t)) ≤ 1 + δ) :
    (∑ i ∈ S, Real.sqrt (u i)) ≤ 7 * Real.log (1 / δ) * t / L := by
  have hu0 : ∀ i ∈ S, 0 ≤ u i := fun i hi => (sq_nonneg L).trans (hu i hi)
  have hb (i : I) (hi : i ∈ S) := boost_sqrt_log L δ t (u i) hL hδ ht hsize
    (hu i hi) (boost_level_upper S u δ t hδ hδsmall ht hu0 hprod hi)
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have hu := boost_log_budget S u δ t hδ hδsmall ht hu0 hprod
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ 3 * t / L by positivity)
  have hlog : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ]
    linarith
  calc
    (∑ i ∈ S, Real.sqrt (u i)) ≤ (3 * t / L) * (2 * Real.log (1 / δ)) := hs.trans hm
    _ ≤ 7 * Real.log (1 / δ) * t / L := by
      have : 0 ≤ Real.log (1 / δ) * t / L := by positivity
      ring_nf at this ⊢
      nlinarith

end Erdos77.CGFresh

-- END CGProof/BoostBudgets.lean

-- BEGIN CGProof/BookParameters.lean

namespace Erdos77.CGFresh

noncomputable def bookSlack (L : ℝ) : ℝ := 1 / L^2
noncomputable def bookBoostCount (L : ℝ) : ℝ := 4 * Real.log (1 / bookSlack L) / L^2
noncomputable def bookA (L : ℝ) : ℝ := Real.log 2 + 20 + 24 * Real.sqrt (L^2+1)
noncomputable def bookD (L : ℝ) : ℝ := 2 * bookA L + 88 * bookBoostCount L +
  336 * Real.log (1 / bookSlack L) / L
noncomputable def bookH (L : ℝ) : ℝ := -(1+bookBoostCount L) *
  Real.log (1/2-11*bookSlack L/4) - Real.log 2
noncomputable def bookFraction (L : ℝ) : ℝ := 1 / (1000*L)
noncomputable def bookDeficit (L : ℝ) : ℝ := (bookSlack L)^3 / 4

lemma log_inverse_slack (L : ℝ) : Real.log (1 / bookSlack L) = 2 * Real.log L := by
  simp only [bookSlack, one_div_one_div, Real.log_pow, Nat.cast_ofNat]

lemma bookBoostCount_formula (L : ℝ) : bookBoostCount L = 8 * Real.log L / L^2 := by
  rw [bookBoostCount, log_inverse_slack]
  ring

end Erdos77.CGFresh

-- END CGProof/BookParameters.lean

-- BEGIN CGProof/BookTrace.lean

namespace Erdos77.CGFresh

noncomputable def stateDensity {V : Type*} (G : SimpleGraph V) (s : BookState V)
    (c : Bool) : ℝ :=
  if h : s.reservoir.Nonempty then density G c s.reservoir (s.pages c) h else 0

theorem stateDensity_eq {V : Type*} (G : SimpleGraph V) (s : BookState V)
    (c : Bool) (h : s.reservoir.Nonempty) :
    stateDensity G s c = density G c s.reservoir (s.pages c) h := by
  simp only [stateDensity, dif_pos h]

noncomputable def eventCost (L : ℝ) (e : BookEvent) : ℝ :=
  if e.boost then 20 + 24 * Real.sqrt (e.level + 1) else bookA L

def eventDrop (e : BookEvent) : ℝ := if e.boost then 0 else 1

noncomputable def initialBookState {V : Type*} (W : Finset V) : BookState V :=
  ⟨W, fun _ => W, fun _ => ∅⟩

structure BookTrace {V : Type*} (G : SimpleGraph V) (W : Finset V)
    (L p0 : ℝ) (t N : ℕ) where
  state : ℕ → BookState V
  event : ℕ → BookEvent
  initial : state 0 = initialBookState W
  valid : ∀ i ≤ N, (state i).Valid G
  reservoir_nonempty : ∀ i ≤ N, (state i).reservoir.Nonempty
  pages_nonempty : ∀ i ≤ N, ∀ c, ((state i).pages c).Nonempty
  spine_count : ∀ i ≤ N, ∀ c, ((state i).spine c).card = (colorSteps event c i).card
  spine_le : ∀ i ≤ N, ∀ c, ((state i).spine c).card ≤ t
  level_boost : ∀ i < N, (event i).boost = true → L ^ 2 < (event i).level
  density_step : ∀ i < N, ∀ c,
    densityFactor (event i) c t * (stateDensity G (state i) c - p0 + bookSlack L) ≤
      stateDensity G (state (i + 1)) c - p0 + bookSlack L
  reservoir_step : ∀ i < N,
    Real.exp (-eventCost L (event i)) * ((state i).reservoir.card : ℝ) -
      eventDrop (event i) ≤ ((state (i + 1)).reservoir.card : ℝ)
  page_step : ∀ i < N, ∀ c,
    (if (event i).color = c then stateDensity G (state i) c else 1) *
      (((state i).pages c).card : ℝ) ≤ (((state (i + 1)).pages c).card : ℝ)

namespace BookTrace

variable {V : Type*} {G : SimpleGraph V} {W : Finset V} {L p0 : ℝ} {t N : ℕ}

noncomputable def zero (G : SimpleGraph V) (W : Finset V) (L p0 : ℝ) (t : ℕ)
    (hW : W.Nonempty) : BookTrace G W L p0 t 0 where
  state := fun _ => initialBookState W
  event := fun _ => ⟨false, false, 0⟩
  initial := rfl
  valid := by
    intro i _
    exact ⟨fun _ => IsBook.empty W, fun _ => IsBook.empty W, by simp [initialBookState]⟩
  reservoir_nonempty := fun _ _ => hW
  pages_nonempty := fun _ _ _ => hW
  spine_count := by
    intro i hi c
    have : i = 0 := by omega
    subst i
    simp [initialBookState, colorSteps]
  spine_le := by intro i _ c; simp [initialBookState]
  level_boost := by intro i hi; omega
  density_step := by intro i hi; omega
  reservoir_step := by intro i hi; omega
  page_step := by intro i hi; omega

theorem density_le_one (r : BookTrace G W L p0 t N) (i : ℕ) (hi : i ≤ N)
    (c : Bool) : stateDensity G (r.state i) c ≤ 1 := by
  rw [stateDensity_eq G _ c (r.reservoir_nonempty i hi)]
  exact Erdos77.CGFresh.density_le_one G c _ _ (r.reservoir_nonempty i hi) (r.pages_nonempty i hi c)

theorem density_nonneg (r : BookTrace G W L p0 t N) (i : ℕ) (hi : i ≤ N)
    (c : Bool) : 0 ≤ stateDensity G (r.state i) c := by
  rw [stateDensity_eq G _ c (r.reservoir_nonempty i hi)]
  exact Erdos77.CGFresh.density_nonneg G c _ _ (r.reservoir_nonempty i hi)

theorem product_bound (r : BookTrace G W L p0 t N) (ht : 2 ≤ t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (i : ℕ) (hi : i ≤ N) (c : Bool) :
    bookSlack L / 4 * (∏ j ∈ boostSteps r.event c i, (1 + (r.event j).level / (t : ℝ))) ≤
      1 + bookSlack L := by
  have hδ : 0 ≤ bookSlack L := by unfold bookSlack; positivity
  have hh := density_product_bound r.event c
    (fun j => stateDensity G (r.state j) c - p0 + bookSlack L)
    (bookSlack L) i t ht hδ ?_ ?_ ?_ ?_
  · have hu := r.density_le_one i hi c
    linarith
  · rw [r.initial]
    have := hinit c
    linarith
  · intro j hj hb
    exact (sq_nonneg L).trans (r.level_boost j (by omega) hb).le
  · intro j hj
    exact r.density_step j (by omega) c
  · rw [← r.spine_count i hi c]
    exact r.spine_le i hi c

theorem density_floor (r : BookTrace G W L p0 t N) (ht : 2 ≤ t)
    (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (i : ℕ) (hi : i ≤ N) (c : Bool) :
    p0 - 3 * bookSlack L / 4 ≤ stateDensity G (r.state i) c := by
  have hδ : 0 ≤ bookSlack L := by unfold bookSlack; positivity
  have hh := density_product_bound r.event c
    (fun j => stateDensity G (r.state j) c - p0 + bookSlack L)
    (bookSlack L) i t ht hδ ?_ ?_ ?_ ?_
  · have hp : 1 ≤ ∏ j ∈ boostSteps r.event c i, (1 + (r.event j).level / (t : ℝ)) := by
      apply Finset.one_le_prod
      intro j hj
      have hm := Finset.mem_filter.mp hj
      have hb := r.level_boost j (by have := Finset.mem_range.mp hm.1; omega) hm.2.2
      have hn : 0 ≤ (r.event j).level / (t : ℝ) :=
        div_nonneg ((sq_nonneg L).trans hb.le) (Nat.cast_nonneg _)
      linarith
    have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ bookSlack L / 4 by positivity)
    nlinarith
  · rw [r.initial]
    have := hinit c
    linarith
  · intro j hj hb
    exact (sq_nonneg L).trans (r.level_boost j (by omega) hb).le
  · intro j hj
    exact r.density_step j (by omega) c
  · rw [← r.spine_count i hi c]
    exact r.spine_le i hi c

end BookTrace

end Erdos77.CGFresh

-- END CGProof/BookTrace.lean

-- BEGIN CGProof/EventAccounting.lean

namespace Erdos77.CGFresh

theorem sum_event_split (e : ℕ → BookEvent) (N : ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, f i) =
      (∑ i ∈ colorSteps e false N, f i) + (∑ i ∈ colorSteps e true N, f i) +
      (∑ i ∈ boostSteps e false N, f i) + (∑ i ∈ boostSteps e true N, f i) := by
  have hh : (∑ i ∈ Finset.range N, f i) =
      (∑ i ∈ allSteps e false N, f i) + (∑ i ∈ allSteps e true N, f i) := by
    simp only [allSteps, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases (e i).color <;> simp
  rw [allSteps_partition, allSteps_partition,
    Finset.sum_union (color_boost_disjoint e false N),
    Finset.sum_union (color_boost_disjoint e true N)] at hh
  linarith

theorem sum_event_drop (e : ℕ → BookEvent) (N : ℕ) :
    (∑ i ∈ Finset.range N, eventDrop (e i)) =
      ((colorSteps e false N).card : ℝ) + (colorSteps e true N).card := by
  have hc (c : Bool) : (∑ i ∈ colorSteps e c N, eventDrop (e i)) =
      ((colorSteps e c N).card : ℝ) := by
    calc
      _ = ∑ _i ∈ colorSteps e c N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [eventDrop, (Finset.mem_filter.mp hi).2.2, Bool.false_eq_true, if_false]
      _ = _ := by simp
  have hb (c : Bool) : (∑ i ∈ boostSteps e c N, eventDrop (e i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [eventDrop, (Finset.mem_filter.mp hi).2.2, if_true]
  rw [sum_event_split, hc, hc, hb, hb]
  ring

theorem sum_event_cost (e : ℕ → BookEvent) (N : ℕ) (L : ℝ) :
    (∑ i ∈ Finset.range N, eventCost L (e i)) =
      bookA L * ((colorSteps e false N).card + (colorSteps e true N).card) +
      20 * ((boostSteps e false N).card + (boostSteps e true N).card) +
      24 * ((∑ i ∈ boostSteps e false N, Real.sqrt ((e i).level + 1)) +
        ∑ i ∈ boostSteps e true N, Real.sqrt ((e i).level + 1)) := by
  have hc (c : Bool) : (∑ i ∈ colorSteps e c N, eventCost L (e i)) =
      bookA L * ((colorSteps e c N).card : ℝ) := by
    calc
      _ = ∑ _i ∈ colorSteps e c N, bookA L := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [eventCost, (Finset.mem_filter.mp hi).2.2, Bool.false_eq_true, if_false]
      _ = _ := by simp [mul_comm]
  have hb (c : Bool) : (∑ i ∈ boostSteps e c N, eventCost L (e i)) =
      20 * ((boostSteps e c N).card : ℝ) +
      24 * (∑ i ∈ boostSteps e c N, Real.sqrt ((e i).level + 1)) := by
    calc
      _ = ∑ i ∈ boostSteps e c N, (20 + 24 * Real.sqrt ((e i).level + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [eventCost, (Finset.mem_filter.mp hi).2.2, if_true]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [mul_comm]
  rw [sum_event_split, hc, hc, hb, hb]
  ring

end Erdos77.CGFresh

-- END CGProof/EventAccounting.lean

-- BEGIN CGProof/TraceBudgets.lean

namespace Erdos77.CGFresh

structure BookGuards (L : ℝ) (t : ℕ) : Prop where
  L_pos : 0 < L
  t_two : 2 ≤ t
  slack_pos : 0 < bookSlack L
  slack_small : bookSlack L ≤ 1 / 8
  cutoff_le : L ^ 2 ≤ (t : ℝ)
  horizon : L ^ 2 ≤ bookSlack L * (t : ℝ)
  page_pos : 0 < 1 / 2 - 11 * bookSlack L / 4

theorem bookA_nonneg (L : ℝ) : 0 ≤ bookA L := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hs := Real.sqrt_nonneg (L ^ 2 + 1)
  unfold bookA
  linarith

namespace BookTrace

variable {V : Type*} {G : SimpleGraph V} {W : Finset V} {L p0 : ℝ} {t N : ℕ}

theorem boost_card_bound (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (c : Bool) : ((boostSteps r.event c N).card : ℝ) ≤ bookBoostCount L * t := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by have := hg.t_two; omega)
  have hh := boost_count_budget (boostSteps r.event c N) (fun i => (r.event i).level)
    (bookSlack L) t L hg.slack_pos hg.slack_small ht hg.L_pos hg.cutoff_le ?_
    (r.product_bound hg.t_two hp0 hinit N le_rfl c)
  · exact hh
  · intro i hi
    have hm := Finset.mem_filter.mp hi
    exact (r.level_boost i (Finset.mem_range.mp hm.1) hm.2.2).le

theorem boost_sqrt_bound (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (c : Bool) : (∑ i ∈ boostSteps r.event c N, Real.sqrt ((r.event i).level + 1)) ≤
      7 * Real.log (1 / bookSlack L) * t / L + bookBoostCount L * t := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by have := hg.t_two; omega)
  have hl (i : ℕ) (hi : i ∈ boostSteps r.event c N) : L ^ 2 ≤ (r.event i).level := by
    have hm := Finset.mem_filter.mp hi
    exact (r.level_boost i (Finset.mem_range.mp hm.1) hm.2.2).le
  have hh := boost_sqrt_budget (boostSteps r.event c N) (fun i => (r.event i).level)
    (bookSlack L) t L hg.slack_pos hg.slack_small ht hg.L_pos hg.horizon hl
    (r.product_bound hg.t_two hp0 hinit N le_rfl c)
  have hs : (∑ i ∈ boostSteps r.event c N, Real.sqrt ((r.event i).level + 1)) ≤
      ∑ i ∈ boostSteps r.event c N, (Real.sqrt ((r.event i).level) + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    have h0 : 0 ≤ (r.event i).level := (sq_nonneg L).trans (hl i hi)
    have ha := Real.sq_sqrt h0
    have hb := Real.sq_sqrt (show 0 ≤ (r.event i).level + 1 by linarith)
    have hc := Real.sqrt_nonneg (r.event i).level
    have hd := Real.sqrt_nonneg ((r.event i).level + 1)
    nlinarith
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hs
  have hc := r.boost_card_bound hg hp0 hinit c
  linarith

theorem cost_bound_extra (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (extra : ℝ)
    (hcount : ((colorSteps r.event false N).card : ℝ) +
      (colorSteps r.event true N).card + extra ≤ 2 * t) :
    (∑ i ∈ Finset.range N, eventCost L (r.event i)) + bookA L * extra ≤ bookD L * t := by
  have hc := mul_le_mul_of_nonneg_left hcount (bookA_nonneg L)
  have hb0 := r.boost_card_bound hg hp0 hinit false
  have hb1 := r.boost_card_bound hg hp0 hinit true
  have hs0 := r.boost_sqrt_bound hg hp0 hinit false
  have hs1 := r.boost_sqrt_bound hg hp0 hinit true
  rw [sum_event_cost]
  unfold bookD
  ring_nf at hc hb0 hb1 hs0 hs1 ⊢
  nlinarith

theorem color_count_bound (r : BookTrace G W L p0 t N) (c : Bool) :
    ((colorSteps r.event c N).card : ℝ) ≤ t := by
  rw [← r.spine_count N le_rfl c]
  exact_mod_cast r.spine_le N le_rfl c

theorem cost_bound (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c) :
    (∑ i ∈ Finset.range N, eventCost L (r.event i)) ≤ bookD L * t := by
  have h0 := r.color_count_bound false
  have h1 := r.color_count_bound true
  simpa using r.cost_bound_extra hg hp0 hinit 0 (by linarith)

theorem length_bound (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c) :
    (N : ℝ) ≤ 2 * t + 2 * bookBoostCount L * t := by
  have h0 := r.color_count_bound false
  have h1 := r.color_count_bound true
  have hb0 := r.boost_card_bound hg hp0 hinit false
  have hb1 := r.boost_card_bound hg hp0 hinit true
  have he : ((colorSteps r.event false N).card : ℝ) + (colorSteps r.event true N).card +
      (boostSteps r.event false N).card + (boostSteps r.event true N).card = N := by
    exact_mod_cast event_count_total r.event N
  linarith

end BookTrace

end Erdos77.CGFresh

-- END CGProof/TraceBudgets.lean

-- BEGIN CGProof/TraceExtension.lean

namespace Erdos77.CGFresh

structure BookNext {V : Type*} (G : SimpleGraph V) (L p0 : ℝ) (t : ℕ)
    (old : BookState V) where
  state : BookState V
  event : BookEvent
  valid : state.Valid G
  reservoir_nonempty : state.reservoir.Nonempty
  pages_nonempty : ∀ c, (state.pages c).Nonempty
  spine_count : ∀ c, (state.spine c).card = (old.spine c).card +
    if event.color = c ∧ event.boost = false then 1 else 0
  spine_le : ∀ c, (state.spine c).card ≤ t
  level_boost : event.boost = true → L ^ 2 < event.level
  density_step : ∀ c, densityFactor event c t *
    (stateDensity G old c - p0 + bookSlack L) ≤ stateDensity G state c - p0 + bookSlack L
  reservoir_step : Real.exp (-eventCost L event) * (old.reservoir.card : ℝ) -
    eventDrop event ≤ (state.reservoir.card : ℝ)
  page_step : ∀ c, (if event.color = c then stateDensity G old c else 1) *
    ((old.pages c).card : ℝ) ≤ ((state.pages c).card : ℝ)

theorem colorSteps_congr (e f : ℕ → BookEvent) (N : ℕ)
    (h : ∀ i < N, e i = f i) (c : Bool) : colorSteps e c N = colorSteps f c N := by
  apply Finset.filter_congr
  intro i hi
  rw [h i (Finset.mem_range.mp hi)]

noncomputable def BookTrace.extend {V : Type*} {G : SimpleGraph V} {W : Finset V}
    {L p0 : ℝ} {t N : ℕ} (r : BookTrace G W L p0 t N)
    (w : BookNext G L p0 t (r.state N)) : BookTrace G W L p0 t (N + 1) := by
  classical
  let ss := Function.update r.state (N + 1) w.state
  let ee := Function.update r.event N w.event
  have hs (i : ℕ) (hi : i ≤ N) : ss i = r.state i :=
    Function.update_of_ne (by omega) _ _
  have hsn : ss (N + 1) = w.state := Function.update_self _ _ _
  have he (i : ℕ) (hi : i < N) : ee i = r.event i :=
    Function.update_of_ne (by omega) _ _
  have hen : ee N = w.event := Function.update_self _ _ _
  have hcount (i : ℕ) (hi : i ≤ N) (c : Bool) : colorSteps ee c i = colorSteps r.event c i :=
    colorSteps_congr ee r.event i (fun j hj => he j (by omega)) c
  refine {
    state := ss
    event := ee
    initial := (hs 0 (Nat.zero_le _)).trans r.initial
    valid := ?_
    reservoir_nonempty := ?_
    pages_nonempty := ?_
    spine_count := ?_
    spine_le := ?_
    level_boost := ?_
    density_step := ?_
    reservoir_step := ?_
    page_step := ?_ }
  · intro i hi
    by_cases hh : i = N + 1
    · rw [hh, hsn]; exact w.valid
    · rw [hs i (by omega)]; exact r.valid i (by omega)
  · intro i hi
    by_cases hh : i = N + 1
    · rw [hh, hsn]; exact w.reservoir_nonempty
    · rw [hs i (by omega)]; exact r.reservoir_nonempty i (by omega)
  · intro i hi c
    by_cases hh : i = N + 1
    · rw [hh, hsn]; exact w.pages_nonempty c
    · rw [hs i (by omega)]; exact r.pages_nonempty i (by omega) c
  · intro i hi c
    by_cases hh : i = N + 1
    · rw [hh, hsn, w.spine_count, colorSteps_succ_card, hcount N le_rfl c, hen,
        r.spine_count N le_rfl c]
    · rw [hs i (by omega), hcount i (by omega) c]
      exact r.spine_count i (by omega) c
  · intro i hi c
    by_cases hh : i = N + 1
    · rw [hh, hsn]; exact w.spine_le c
    · rw [hs i (by omega)]; exact r.spine_le i (by omega) c
  · intro i hi
    by_cases hh : i = N
    · rw [hh, hen]; exact w.level_boost
    · rw [he i (by omega)]; exact r.level_boost i (by omega)
  · intro i hi c
    by_cases hh : i = N
    · rw [hh, hen, hs N le_rfl, hsn]; exact w.density_step c
    · rw [he i (by omega), hs i (by omega), hs (i + 1) (by omega)]
      exact r.density_step i (by omega) c
  · intro i hi
    by_cases hh : i = N
    · rw [hh, hen, hs N le_rfl, hsn]; exact w.reservoir_step
    · rw [he i (by omega), hs i (by omega), hs (i + 1) (by omega)]
      exact r.reservoir_step i (by omega)
  · intro i hi c
    by_cases hh : i = N
    · rw [hh, hen, hs N le_rfl, hsn]; exact w.page_step c
    · rw [he i (by omega), hs i (by omega), hs (i + 1) (by omega)]
      exact r.page_step i (by omega) c

end Erdos77.CGFresh

-- END CGProof/TraceExtension.lean

-- BEGIN CGProof/BoostNext.lean

namespace Erdos77.CGFresh

noncomputable def boostNext {V : Type*} {G : SimpleGraph V} {s : BookState V}
    (L p0 : ℝ) (t : ℕ) (hs : s.Valid G) (hX : s.reservoir.Nonempty)
    (hY : ∀ c, (s.pages c).Nonempty) (hst : ∀ c, (s.spine c).card ≤ t)
    (w : KeyStep G s.reservoir s.pages hX
      (fun c => (stateDensity G s c - p0 + bookSlack L) / (t : ℝ)))
    (hcut : L ^ 2 < w.level) : BookNext G L p0 t s := by
  classical
  let s' := s.boostMove w.color w.reservoir (w.pages w.color)
  have hv : s'.Valid G := hs.boostMove w.color w.reservoir_subset
    ((w.pages_subset w.color).trans (neighbors_subset G w.color w.vertex (s.pages w.color)))
  have hYn (b : Bool) : (s'.pages b).Nonempty := by
    by_cases hb : b = w.color
    · subst b
      simpa only [s', BookState.boostMove, Function.update_self] using w.pages_nonempty w.color
    · simpa only [s', BookState.boostMove, Function.update_of_ne hb] using hY b
  refine {
    state := s'
    event := ⟨w.color, true, w.level⟩
    valid := hv
    reservoir_nonempty := w.reservoir_nonempty
    pages_nonempty := hYn
    spine_count := ?_
    spine_le := hst
    level_boost := fun _ => hcut
    density_step := ?_
    reservoir_step := ?_
    page_step := ?_ }
  · intro c
    simp [s', BookState.boostMove]
  · intro c
    have hd := w.boost_density c hY
    have hnew := stateDensity_eq G s' c w.reservoir_nonempty
    have hold := stateDensity_eq G s c hX
    change stateDensity G s' c = density G c w.reservoir
      (Function.update s.pages w.color (w.pages w.color) c) w.reservoir_nonempty at hnew
    rw [← hnew, ← hold] at hd
    by_cases hc : w.color = c
    · subst c
      simp [densityFactor] at hd ⊢
      simp only [div_eq_mul_inv] at hd ⊢
      nlinarith
    · have hc' : c ≠ w.color := Ne.symm hc
      simp only [densityFactor, hc, hc', false_and, if_false, one_mul] at hd ⊢
      linarith
  · simpa only [eventCost, eventDrop, if_true, sub_zero, s', BookState.boostMove,
      neg_add, sub_eq_add_neg, neg_zero, add_zero] using w.reservoir_card
  · intro c
    by_cases hc : w.color = c
    · subst c
      simp only [if_true, s', BookState.boostMove, Function.update_self]
      rw [w.pages_card, stateDensity_eq G s w.color hX,
        density_mul_card G w.color s.reservoir (s.pages w.color) hX (hY w.color)]
    · simp only [if_neg hc, s', BookState.boostMove, Function.update_of_ne (Ne.symm hc), one_mul]
      exact le_rfl

end Erdos77.CGFresh

-- END CGProof/BoostNext.lean

-- BEGIN CGProof/ColorNext.lean

namespace Erdos77.CGFresh

noncomputable def colorNext {V : Type*} {G : SimpleGraph V} {s : BookState V}
    (L p0 : ℝ) (t : ℕ) (hs : s.Valid G) (hX : s.reservoir.Nonempty)
    (hY : ∀ c, (s.pages c).Nonempty) (hst : ∀ c, (s.spine c).card < t)
    (w : KeyStep G s.reservoir s.pages hX
      (fun c => (stateDensity G s c - p0 + bookSlack L) / (t : ℝ)))
    (hcut : w.level ≤ L ^ 2) (j : Bool)
    (hj : (w.reservoir.card : ℝ) - 1 ≤
      2 * ((neighbors G j w.vertex w.reservoir).card : ℝ))
    (hR : (neighbors G j w.vertex w.reservoir).Nonempty) : BookNext G L p0 t s := by
  classical
  let R := neighbors G j w.vertex w.reservoir
  let s' := s.colorMove j w.vertex R (w.pages j)
  have hsub : R ⊆ neighbors G j w.vertex s.reservoir := by
    intro x hx
    have hh := (mem_neighbors G j w.vertex x w.reservoir).mp hx
    exact (mem_neighbors G j w.vertex x s.reservoir).mpr ⟨w.reservoir_subset hh.1, hh.2⟩
  have hv : s'.Valid G := hs.colorMove j w.vertex_mem hsub (w.pages_subset j)
  have hYn (b : Bool) : (s'.pages b).Nonempty := by
    by_cases hb : b = j
    · subst b
      simpa only [s', BookState.colorMove, Function.update_self] using w.pages_nonempty j
    · simpa only [s', BookState.colorMove, Function.update_of_ne hb] using hY b
  refine {
    state := s'
    event := ⟨j, false, w.level⟩
    valid := hv
    reservoir_nonempty := hR
    pages_nonempty := hYn
    spine_count := ?_
    spine_le := ?_
    level_boost := by simp
    density_step := ?_
    reservoir_step := ?_
    page_step := ?_ }
  · intro c
    simpa only [and_true, eq_comm] using colorMove_spine_card hs j w.vertex_mem R (w.pages j) c
  · intro c
    have hh := colorMove_spine_card hs j w.vertex_mem R (w.pages j) c
    have hc := hst c
    change ((s.colorMove j w.vertex R (w.pages j)).spine c).card ≤ t
    rw [hh]
    split_ifs <;> omega
  · intro c
    have hd := w.color_density j c hY hR
    have hnew := stateDensity_eq G s' c hR
    have hold := stateDensity_eq G s c hX
    change stateDensity G s' c = density G c R (Function.update s.pages j (w.pages j) c) hR at hnew
    rw [← hnew, ← hold] at hd
    by_cases hc : j = c
    · subst c
      simp [densityFactor] at hd ⊢
      simp only [div_eq_mul_inv] at hd ⊢
      nlinarith
    · have hc' : c ≠ j := Ne.symm hc
      simp only [densityFactor, hc, hc', false_and, if_false, one_mul] at hd ⊢
      linarith
  · simpa only [eventCost, eventDrop, Bool.false_eq_true, if_false, bookA,
      s', BookState.colorMove, R] using w.color_reservoir_bound L hcut j hj
  · intro c
    by_cases hc : j = c
    · subst c
      simp only [if_true, s', BookState.colorMove, Function.update_self]
      rw [w.pages_card, stateDensity_eq G s j hX,
        density_mul_card G j s.reservoir (s.pages j) hX (hY j)]
    · simp only [if_neg hc, s', BookState.colorMove, Function.update_of_ne (Ne.symm hc), one_mul]
      exact le_rfl

end Erdos77.CGFresh

-- END CGProof/ColorNext.lean

-- BEGIN CGProof/TraceSizes.lean

namespace Erdos77.CGFresh
namespace BookTrace

variable {V : Type*} {G : SimpleGraph V} {W : Finset V} {L p0 : ℝ} {t N : ℕ}

theorem reservoir_raw (r : BookTrace G W L p0 t N) :
    Real.exp (-(∑ i ∈ Finset.range N, eventCost L (r.event i))) * (W.card : ℝ) -
      (∑ i ∈ Finset.range N, eventDrop (r.event i)) ≤ (r.state N).reservoir.card := by
  have hh := reservoir_exp_ledger (fun i => ((r.state i).reservoir.card : ℝ))
    (fun i => eventCost L (r.event i)) (fun i => eventDrop (r.event i)) N ?_ ?_ r.reservoir_step
  · simpa only [r.initial, initialBookState] using hh
  · intro i _
    unfold eventCost
    split_ifs
    · positivity
    · exact bookA_nonneg L
  · intro i _
    unfold eventDrop
    split_ifs <;> norm_num

theorem color_reservoir_positive (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (hsmall : ∀ c, ((r.state N).spine c).card < t)
    (hlarge : Real.exp (bookD L * t) * (2 * (t : ℝ) + 1) ≤ W.card)
    {R : Finset V}
    (hR : Real.exp (-bookA L) * ((r.state N).reservoir.card : ℝ) - 1 ≤ R.card) : R.Nonempty := by
  have hc0 : ((colorSteps r.event false N).card : ℝ) + 1 ≤ t := by
    rw [← r.spine_count N le_rfl false]
    have hh : ((r.state N).spine false).card + 1 ≤ t := by have := hsmall false; omega
    exact_mod_cast hh
  have hc1 : ((colorSteps r.event true N).card : ℝ) ≤ t := r.color_count_bound true
  have hcost := r.cost_bound_extra hg hp0 hinit 1 (by linarith)
  have hdel : (∑ i ∈ Finset.range N, eventDrop (r.event i)) + 1 ≤ 2 * t := by
    rw [sum_event_drop]
    linarith
  have hdel0 : 0 ≤ ∑ i ∈ Finset.range N, eventDrop (r.event i) := by
    rw [sum_event_drop]
    positivity
  have hraw := mul_le_mul_of_nonneg_left r.reservoir_raw (Real.exp_pos (-bookA L)).le
  have hfac : Real.exp (-bookA L) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (bookA_nonneg L))
  have hdc := mul_le_mul_of_nonneg_right hfac hdel0
  have he : Real.exp (-(bookD L * t)) ≤ Real.exp (-bookA L) *
      Real.exp (-(∑ i ∈ Finset.range N, eventCost L (r.event i))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hem := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg W.card)
  have hexp : Real.exp (-(bookD L * t)) * Real.exp (bookD L * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hs := mul_le_mul_of_nonneg_left hlarge (Real.exp_pos (-(bookD L * t))).le
  rw [← mul_assoc, hexp, one_mul] at hs
  have hcard : (0 : ℝ) < R.card := by nlinarith
  exact Finset.card_pos.mp (by exact_mod_cast hcard)

theorem pages_bound (r : BookTrace G W L p0 t N) (hg : BookGuards L t)
    (hp0 : 0 ≤ p0) (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (hbase : 1 / 2 - 2 * bookSlack L ≤ p0) (c : Bool) :
    Real.exp (-(Real.log 2 + bookH L) * t) * (W.card : ℝ) ≤ ((r.state N).pages c).card := by
  let v : ℝ := 1 / 2 - 11 * bookSlack L / 4
  have hv : 0 < v := hg.page_pos
  have hv1 : v ≤ 1 := by have := hg.slack_pos; dsimp [v]; linarith
  have hf (i : ℕ) (hi : i ≤ N) : v ≤ stateDensity G (r.state i) c := by
    have hh := r.density_floor hg.t_two hinit i hi c
    dsimp [v]
    linarith
  have hs := page_ledger (fun i => (((r.state i).pages c).card : ℝ)) r.event c v hv.le N ?_
  · have hc := r.color_count_bound c
    have hb := r.boost_card_bound hg hp0 hinit c
    have hn : ((allSteps r.event c N).card : ℝ) ≤ (1 + bookBoostCount L) * t := by
      rw [allSteps_card, Nat.cast_add]
      nlinarith
    have hl := Real.log_nonpos hv.le hv1
    have hm := mul_le_mul_of_nonpos_right hn hl
    have he : Real.exp (-(Real.log 2 + bookH L) * t) ≤ v ^ (allSteps r.event c N).card := by
      have hid : Real.exp (((allSteps r.event c N).card : ℝ) * Real.log v) =
          v ^ (allSteps r.event c N).card := by rw [Real.exp_nat_mul, Real.exp_log hv]
      rw [← hid]
      apply Real.exp_le_exp.mpr
      dsimp [bookH, v] at hm ⊢
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg W.card)
    have hs' : v ^ (allSteps r.event c N).card * (W.card : ℝ) ≤
        (((r.state N).pages c).card : ℝ) := by
      simpa only [r.initial, initialBookState] using hs
    exact hmul.trans hs'
  · intro i hi
    have hh := r.page_step i hi c
    by_cases he : (r.event i).color = c
    · simp only [if_pos he] at hh ⊢
      exact (mul_le_mul_of_nonneg_right (hf i (by omega)) (Nat.cast_nonneg _)).trans hh
    · simpa only [if_neg he] using hh

end BookTrace
end Erdos77.CGFresh

-- END CGProof/TraceSizes.lean

-- BEGIN CGProof/GramMoments.lean

open scoped BigOperators

namespace Erdos77.CGFresh

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

theorem gram_sum_nonneg (f : X → I → ℝ) :
    0 ≤ ∑ x, ∑ y, ∑ i, f x i * f y i := by
  have he : (∑ x, ∑ y, ∑ i, f x i * f y i) = ∑ i, (∑ x, f x i) ^ 2 := by
    calc
      _ = ∑ x, ∑ i, ∑ y, f x i * f y i := by
        apply Finset.sum_congr rfl
        intro x _
        exact Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ y, f x i * f y i := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
  rw [he]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem gram_mixed_moment_nonneg (f : X → I → ℝ) (g : X → J → ℝ) (n : ℕ) :
    0 ≤ ∑ x, ∑ y, (∑ i, f x i * f y i) * (∑ j, g x j * g y j) ^ n := by
  let h : X → I × (Fin n → J) → ℝ := fun x p => f x p.1 * ∏ a, g x (p.2 a)
  have he (x y : X) :
      (∑ i, f x i * f y i) * (∑ j, g x j * g y j) ^ n =
        ∑ p : I × (Fin n → J), h x p * h y p := by
    rw [Fintype.sum_pow, Fintype.sum_prod_type]
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.prod_mul_distrib]
    dsimp [h]
    ring
  simp_rw [he]
  exact gram_sum_nonneg h

end Erdos77.CGFresh

-- END CGProof/GramMoments.lean

-- BEGIN CGProof/KernelSeries.lean

open scoped BigOperators

namespace Erdos77.CGFresh

noncomputable def rootCosh (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.cosh (Real.sqrt x) else Real.cos (Real.sqrt (-x))

theorem rootCosh_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x ^ n / ((2 * n).factorial : ℝ)) (rootCosh x) := by
  by_cases hx : 0 ≤ x
  · rw [rootCosh, if_pos hx]
    convert Real.hasSum_cosh (Real.sqrt x) using 1
    ext n
    rw [pow_mul, Real.sq_sqrt hx]
  · rw [rootCosh, if_neg hx]
    have hn : 0 ≤ -x := by linarith
    convert Real.hasSum_cos (Real.sqrt (-x)) using 1
    ext n
    rw [pow_mul, Real.sq_sqrt hn]
    congr 1
    rw [← mul_pow]
    simp

theorem rootCosh_ge_neg_one (x : ℝ) : -1 ≤ rootCosh x := by
  unfold rootCosh
  split_ifs
  · linarith [Real.one_le_cosh (Real.sqrt x)]
  · exact Real.neg_one_le_cos _

theorem rootCosh_neg_le_one {x : ℝ} (hx : x < 0) : rootCosh x ≤ 1 := by
  rw [rootCosh, if_neg (not_le.mpr hx)]
  exact Real.cos_le_one _

end Erdos77.CGFresh

-- END CGProof/KernelSeries.lean

-- BEGIN CGProof/KernelMoments.lean

open scoped BigOperators

namespace Erdos77.CGFresh

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

theorem gram_cosh_moment_nonneg (f : X → I → ℝ) (g : X → J → ℝ) :
    0 ≤ ∑ x, ∑ y, (∑ i, f x i * f y i) * rootCosh (∑ j, g x j * g y j) := by
  have hs : HasSum (fun n : ℕ => ∑ x, ∑ y,
      (∑ i, f x i * f y i) * (∑ j, g x j * g y j) ^ n /
        ((2 * n).factorial : ℝ))
      (∑ x, ∑ y, (∑ i, f x i * f y i) * rootCosh (∑ j, g x j * g y j)) := by
    apply hasSum_sum
    intro x _
    apply hasSum_sum
    intro y _
    simpa only [mul_div_assoc] using
      (rootCosh_hasSum (∑ j, g x j * g y j)).mul_left (∑ i, f x i * f y i)
  apply HasSum.nonneg _ hs
  intro n
  simpa only [Finset.sum_div] using
    div_nonneg (gram_mixed_moment_nonneg f g n)
      (Nat.cast_nonneg (2 * n).factorial)

noncomputable def twoKernel (x y : ℝ) : ℝ :=
  x * (2 + rootCosh y) + y * (2 + rootCosh x)

theorem twoKernel_gram_sum_nonneg (f : X → I → ℝ) (g : X → J → ℝ) :
    0 ≤ ∑ x, ∑ y, twoKernel (∑ i, f x i * f y i) (∑ j, g x j * g y j) := by
  have hf := gram_sum_nonneg f
  have hg := gram_sum_nonneg g
  have hfg := gram_cosh_moment_nonneg f g
  have hgf := gram_cosh_moment_nonneg g f
  simp only [twoKernel, mul_add, Finset.sum_add_distrib]
  simp only [← Finset.sum_mul]
  linarith

end Erdos77.CGFresh

-- END CGProof/KernelMoments.lean

-- BEGIN CGProof/KernelBounds.lean

open scoped BigOperators

namespace Erdos77.CGFresh

noncomputable def kernelFactor (x : ℝ) : ℝ := 2 + rootCosh x

theorem kernelFactor_ge_one (x : ℝ) : 1 ≤ kernelFactor x := by
  dsimp [kernelFactor]
  linarith [rootCosh_ge_neg_one x]

theorem kernelFactor_ge_self (x : ℝ) : x ≤ kernelFactor x := by
  by_cases hx : 0 ≤ x
  · have hb := (rootCosh_hasSum x).summable.sum_le_tsum (Finset.range 3)
      (fun n _ => div_nonneg (pow_nonneg hx n) (Nat.cast_nonneg _))
    rw [(rootCosh_hasSum x).tsum_eq] at hb
    norm_num [Finset.sum_range_succ] at hb
    dsimp [kernelFactor]
    nlinarith [sq_nonneg (x - 6)]
  · have h := kernelFactor_ge_one x
    linarith

theorem kernelFactor_neg_le_three {x : ℝ} (hx : x < 0) : kernelFactor x ≤ 3 := by
  dsimp [kernelFactor]
  linarith [rootCosh_neg_le_one hx]

theorem kernelFactor_upper {x : ℝ} (_hx : -6 ≤ x) :
    kernelFactor x ≤ 3 * Real.exp (Real.sqrt (x + 6)) := by
  have hE : 1 ≤ Real.exp (Real.sqrt (x + 6)) := Real.one_le_exp (Real.sqrt_nonneg _)
  by_cases hp : 0 ≤ x
  · have hm : Real.sqrt x ≤ Real.sqrt (x + 6) := Real.sqrt_le_sqrt (by linarith)
    have he : Real.exp (-(Real.sqrt x)) ≤ Real.exp (Real.sqrt x) :=
      Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg x])
    have he2 := Real.exp_le_exp.mpr hm
    rw [kernelFactor, rootCosh, if_pos hp, Real.cosh_eq]
    linarith
  · have hu := kernelFactor_neg_le_three (lt_of_not_ge hp)
    linarith

theorem kernel_ratio_le_one (x : ℝ) : x / kernelFactor x ≤ 1 := by
  rw [div_le_one (by linarith [kernelFactor_ge_one x])]
  exact kernelFactor_ge_self x

end Erdos77.CGFresh

-- END CGProof/KernelBounds.lean

-- BEGIN CGProof/KernelSignBounds.lean

namespace Erdos77.CGFresh

theorem twoKernel_comm (x y : ℝ) : twoKernel x y = twoKernel y x := by
  unfold twoKernel
  ring

theorem twoKernel_bad_left {x y : ℝ} (hx : x < -6) : twoKernel x y ≤ -1 := by
  have hKx := kernelFactor_ge_one x
  have hKy := kernelFactor_ge_one y
  have hsmall := kernelFactor_neg_le_three (show x < 0 by linarith)
  have hmul := mul_le_mul_of_nonneg_right (kernelFactor_ge_self y) (show 0 ≤ kernelFactor x by linarith)
  change x * kernelFactor y + y * kernelFactor x ≤ -1
  have hsum : x + kernelFactor x ≤ -3 := by linarith
  have hh := mul_le_mul_of_nonneg_right hsum (show 0 ≤ kernelFactor y by linarith)
  nlinarith

theorem twoKernel_bad {x y : ℝ} (h : x < -6 ∨ y < -6) : twoKernel x y ≤ -1 := by
  rcases h with hx | hy
  · exact twoKernel_bad_left hx
  · rw [twoKernel_comm]
    exact twoKernel_bad_left hy

theorem twoKernel_good {x y : ℝ} (hx : -6 ≤ x) (hy : -6 ≤ y) :
    twoKernel x y ≤ 18 * Real.exp (Real.sqrt (x + 6) + Real.sqrt (y + 6)) := by
  have hKx := kernelFactor_ge_one x
  have hKy := kernelFactor_ge_one y
  have h1 := mul_le_mul_of_nonneg_right (kernelFactor_ge_self x) (show 0 ≤ kernelFactor y by linarith)
  have h2 := mul_le_mul_of_nonneg_right (kernelFactor_ge_self y) (show 0 ≤ kernelFactor x by linarith)
  have hu := mul_le_mul (kernelFactor_upper hx) (kernelFactor_upper hy)
    (show 0 ≤ kernelFactor y by linarith) (by positivity : 0 ≤ 3 * Real.exp (Real.sqrt (x + 6)))
  rw [Real.exp_add]
  change x * kernelFactor y + y * kernelFactor x ≤ _
  nlinarith

theorem twoKernel_scaled_good {a b : ℝ} (ha : -1 ≤ a) (hb : -1 ≤ b) :
    twoKernel (6 * a) (6 * b) ≤ 18 * Real.exp (6 * Real.sqrt (max a b + 1)) := by
  have h := twoKernel_good (x := 6*a) (y := 6*b) (by linarith) (by linarith)
  have hm : 0 ≤ max a b + 1 := by linarith [le_max_left a b]
  have hsa : Real.sqrt (6*a+6) ≤ 3*Real.sqrt (max a b+1) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hm, le_max_left a b]
  have hsb : Real.sqrt (6*b+6) ≤ 3*Real.sqrt (max a b+1) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hm, le_max_right a b]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))

end Erdos77.CGFresh

-- END CGProof/KernelSignBounds.lean

-- BEGIN CGProof/FiniteExponentialTail.lean

open scoped BigOperators

namespace Erdos77.CGFresh

theorem finite_geometric_upper {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ j ∈ Finset.range N, r ^ j) ≤ 1 / (1-r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  rw [geom_sum_mul_of_le_one hr1.le]
  linarith [pow_nonneg hr N]

theorem finite_exponential_tail_sum {Ω : Type*} (S : Finset Ω) (u : Ω → ℝ)
    (hu : ∀ x ∈ S, 0 ≤ u x) (K : ℝ) (hK : 0 ≤ K)
    (htail : ∀ j : ℕ, ((S.filter (fun x => (j : ℝ) ≤ u x)).card : ℝ) ≤
      K * Real.exp (-24 * (j : ℝ))) :
    (∑ x ∈ S, Real.exp (6*u x)) ≤ K * Real.exp 6 / (1-Real.exp (-18)) := by
  classical
  let N : ℕ := 1 + ∑ x ∈ S, ⌊u x⌋₊
  have hf (x : Ω) (hx : x ∈ S) : ⌊u x⌋₊ < N := by
    have hh := Finset.single_le_sum (fun y (_ : y ∈ S) => Nat.zero_le ⌊u y⌋₊) hx
    dsimp [N]
    omega
  have hp (x : Ω) (hx : x ∈ S) : Real.exp (6*u x) ≤
      Real.exp 6 * ∑ j ∈ Finset.range N, if (j : ℝ) ≤ u x then Real.exp (6*(j : ℝ)) else 0 := by
    have hsingle : Real.exp (6*(⌊u x⌋₊ : ℝ)) ≤
        ∑ j ∈ Finset.range N, if (j : ℝ) ≤ u x then Real.exp (6*(j : ℝ)) else 0 := by
      have h := Finset.single_le_sum (s := Finset.range N)
        (f := fun j : ℕ => if (j : ℝ) ≤ u x then Real.exp (6*(j : ℝ)) else 0)
        (fun j _ => by positivity) (Finset.mem_range.mpr (hf x hx))
      simpa only [if_pos (Nat.floor_le (hu x hx))] using h
    have hlt := Nat.lt_floor_add_one (u x)
    calc
      Real.exp (6*u x) ≤ Real.exp (6 + 6*(⌊u x⌋₊ : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 6 * Real.exp (6*(⌊u x⌋₊ : ℝ)) := Real.exp_add _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (Real.exp_pos _).le
  calc
    _ ≤ ∑ x ∈ S, Real.exp 6 * ∑ j ∈ Finset.range N,
        if (j : ℝ) ≤ u x then Real.exp (6*(j : ℝ)) else 0 := Finset.sum_le_sum hp
    _ = Real.exp 6 * ∑ j ∈ Finset.range N,
        ((S.filter (fun x => (j : ℝ) ≤ u x)).card : ℝ) * Real.exp (6*(j : ℝ)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simp only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp 6 * ∑ j ∈ Finset.range N, K * Real.exp (-18*(j : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply Finset.sum_le_sum
      intro j _
      calc
        _ ≤ (K * Real.exp (-24*(j : ℝ))) * Real.exp (6*(j : ℝ)) :=
          mul_le_mul_of_nonneg_right (htail j) (Real.exp_pos _).le
        _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ = K * Real.exp 6 * ∑ j ∈ Finset.range N, (Real.exp (-18)) ^ j := by
      simp_rw [show ∀ j : ℕ, Real.exp (-18*(j : ℝ)) = (Real.exp (-18)) ^ j from
        fun j => by simpa only [mul_comm] using Real.exp_nat_mul (-18) j]
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have hg := finite_geometric_upper (Real.exp_pos (-18)).le
        (show Real.exp (-18) < 1 by simp) N
      simpa only [mul_one_div, mul_div_assoc] using
        mul_le_mul_of_nonneg_left hg (mul_nonneg hK (Real.exp_pos 6).le)

end Erdos77.CGFresh

-- END CGProof/FiniteExponentialTail.lean

-- BEGIN CGProof/GeometricConstants.lean

namespace Erdos77.CGFresh

theorem geometric_constant_small :
    36 * Real.exp (-14) / (1-Real.exp (-18)) + Real.exp (-20) < 1 := by
  have h2 : (3:ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2:ℝ)]
  have h14 : (1000:ℝ) ≤ Real.exp 14 := by
    calc
      1000 ≤ (3:ℝ)^7 := by norm_num
      _ ≤ (Real.exp 2)^7 := pow_le_pow_left₀ (by norm_num) h2 7
      _ = Real.exp 14 := by rw [← Real.exp_nat_mul]; norm_num
  have e14 : Real.exp (-14) * Real.exp 14 = 1 := by rw [← Real.exp_add]; norm_num
  have hn14 : Real.exp (-14) ≤ 1/1000 := by nlinarith [Real.exp_pos (-14)]
  have e18 : Real.exp (-18) * Real.exp 18 = 1 := by rw [← Real.exp_add]; norm_num
  have hn18 : Real.exp (-18) ≤ 1/2 := by
    nlinarith [Real.add_one_le_exp (18:ℝ), Real.exp_pos (-18)]
  have e20 : Real.exp (-20) * Real.exp 20 = 1 := by rw [← Real.exp_add]; norm_num
  have hn20 : Real.exp (-20) ≤ 1/2 := by
    nlinarith [Real.add_one_le_exp (20:ℝ), Real.exp_pos (-20)]
  have hd : 0 < 1-Real.exp (-18) := by linarith
  have hq : 36 * Real.exp (-14) / (1-Real.exp (-18)) < 1/2 := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  linarith

theorem geometric_constant_identity :
    18 * (2 * Real.exp (-20) * Real.exp 6 / (1-Real.exp (-18))) + Real.exp (-20) =
    36 * Real.exp (-14) / (1-Real.exp (-18)) + Real.exp (-20) := by
  have he : Real.exp (-20) * Real.exp 6 = Real.exp (-14) := by
    rw [← Real.exp_add]; norm_num
  rw [show 2 * Real.exp (-20) * Real.exp 6 = 2 * Real.exp (-14) by rw [mul_assoc, he]]
  ring

end Erdos77.CGFresh

-- END CGProof/GeometricConstants.lean

-- BEGIN CGProof/GeometricTail.lean

open scoped BigOperators

namespace Erdos77.CGFresh

theorem kernel_forces_correlation {Ω : Type*} (S : Finset Ω) (hS : S.Nonempty)
    (a b : Ω → ℝ)
    (hm : 0 ≤ ∑ x ∈ S, twoKernel (6*a x) (6*b x)) :
    ∃ z : ℝ, -1 ≤ z ∧
      (Real.exp (-20-24*Real.sqrt (z+1)) * (S.card : ℝ) ≤
        ((S.filter (fun x => z ≤ a x ∧ -1 ≤ b x)).card : ℝ) ∨
       Real.exp (-20-24*Real.sqrt (z+1)) * (S.card : ℝ) ≤
        ((S.filter (fun x => z ≤ b x ∧ -1 ≤ a x)).card : ℝ)) := by
  classical
  by_contra hn
  push Not at hn
  let E := S.filter (fun x => -1 ≤ a x ∧ -1 ≤ b x)
  let u := fun x => Real.sqrt (max (a x) (b x) + 1)
  have hcard : (E.card : ℝ) < Real.exp (-20) * (S.card : ℝ) := by
    simpa [E] using (hn (-1) le_rfl).1
  have htail (j : ℕ) : ((E.filter (fun x => (j : ℝ) ≤ u x)).card : ℝ) ≤
      (2 * Real.exp (-20) * (S.card : ℝ)) * Real.exp (-24*(j : ℝ)) := by
    let z : ℝ := (j : ℝ)^2-1
    have hl : -1 ≤ z := by dsimp [z]; nlinarith [sq_nonneg (j:ℝ)]
    have hroot : Real.sqrt (z+1) = (j:ℝ) := by
      dsimp [z]
      rw [sub_add_cancel, Real.sqrt_sq (Nat.cast_nonneg j)]
    have hsub : E.filter (fun x => (j : ℝ) ≤ u x) ⊆
        S.filter (fun x => z ≤ a x ∧ -1 ≤ b x) ∪
        S.filter (fun x => z ≤ b x ∧ -1 ≤ a x) := by
      intro x hx
      obtain ⟨hxE, hj⟩ := Finset.mem_filter.mp hx
      obtain ⟨hxS, ha, hb⟩ := Finset.mem_filter.mp hxE
      have hmax : 0 ≤ max (a x) (b x)+1 := by linarith [le_max_left (a x) (b x)]
      have hsq := Real.sq_sqrt hmax
      have hmj : z ≤ max (a x) (b x) := by
        dsimp [u] at hj
        dsimp [z]
        nlinarith [Real.sqrt_nonneg (max (a x) (b x)+1), Nat.cast_nonneg (α := ℝ) j]
      rcases le_max_iff.mp hmj with ha' | hb'
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hxS, ha', hb⟩))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxS, hb', ha⟩))
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hcR : ((E.filter (fun x => (j : ℝ) ≤ u x)).card : ℝ) ≤
        ((S.filter (fun x => z ≤ a x ∧ -1 ≤ b x)).card : ℝ) +
        ((S.filter (fun x => z ≤ b x ∧ -1 ≤ a x)).card : ℝ) := by exact_mod_cast hc
    have h1 := (hn z hl).1
    have h2 := (hn z hl).2
    rw [hroot] at h1 h2
    have he : Real.exp (-20-24*(j:ℝ)) = Real.exp (-20)*Real.exp (-24*(j:ℝ)) := by
      rw [show (-20-24*(j:ℝ)) = -20 + (-24*(j:ℝ)) by ring, Real.exp_add]
    rw [he] at h1 h2
    nlinarith
  have hs := finite_exponential_tail_sum E u (fun x _ => Real.sqrt_nonneg _)
    (2 * Real.exp (-20) * (S.card : ℝ)) (by positivity) htail
  have hgood : (∑ x ∈ E, twoKernel (6*a x) (6*b x)) ≤
      18 * ∑ x ∈ E, Real.exp (6*u x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨_, ha, hb⟩ := Finset.mem_filter.mp hx
    exact twoKernel_scaled_good ha hb
  have hbad : (∑ x ∈ S.filter (fun x => ¬(-1 ≤ a x ∧ -1 ≤ b x)),
      twoKernel (6*a x) (6*b x)) ≤
      -((S.filter (fun x => ¬(-1 ≤ a x ∧ -1 ≤ b x))).card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ S.filter (fun x => ¬(-1 ≤ a x ∧ -1 ≤ b x)), (-1:ℝ) := by
        apply Finset.sum_le_sum
        intro x hx
        have h := (Finset.mem_filter.mp hx).2
        push Not at h
        apply twoKernel_bad
        by_cases ha : -1 ≤ a x
        · exact Or.inr (by linarith [h ha])
        · exact Or.inl (by linarith)
      _ = _ := by simp
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun x => -1 ≤ a x ∧ -1 ≤ b x) (fun x => twoKernel (6*a x) (6*b x))
  have hcards := Finset.card_filter_add_card_filter_not (s := S) (fun x => -1 ≤ a x ∧ -1 ≤ b x)
  have hcardsR : (E.card : ℝ) +
      ((S.filter (fun x => ¬(-1 ≤ a x ∧ -1 ≤ b x))).card : ℝ) = (S.card : ℝ) := by
    dsimp only [E]
    exact_mod_cast hcards
  change (∑ x ∈ E, twoKernel (6*a x) (6*b x)) + _ = _ at hsplit
  have htotal : (S.card : ℝ) ≤ 18*(∑ x ∈ E, Real.exp (6*u x)) + E.card := by
    linarith
  have hC := geometric_constant_small
  rw [← geometric_constant_identity] at hC
  have hpos : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hmul := mul_lt_mul_of_pos_right hC hpos
  have he : 18 * ((2 * Real.exp (-20) * (S.card : ℝ)) * Real.exp 6 /
      (1-Real.exp (-18))) + Real.exp (-20)*(S.card : ℝ) =
      (18*(2*Real.exp (-20)*Real.exp 6/(1-Real.exp (-18)))+Real.exp (-20))*(S.card:ℝ) := by ring
  nlinarith

end Erdos77.CGFresh

-- END CGProof/GeometricTail.lean

-- BEGIN CGProof/GeometricPairs.lean

open scoped BigOperators

namespace Erdos77.CGFresh

variable {X I J : Type*} [Fintype X] [Fintype I] [Fintype J]

omit [Fintype X] in
theorem scaled_gram (f : X → I → ℝ) (x y : X) :
    (∑ i, (Real.sqrt 6 * f x i) * (Real.sqrt 6 * f y i)) =
      6 * ∑ i, f x i * f y i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (Real.sqrt 6)^2 = (6:ℝ) := Real.sq_sqrt (by norm_num)
  calc
    _ = (Real.sqrt 6)^2 * (f x i * f y i) := by ring
    _ = _ := by rw [hs]

theorem geometric_pair_count [Nonempty X] (f : X → I → ℝ) (g : X → J → ℝ) :
    ∃ z : ℝ, -1 ≤ z ∧
      (Real.exp (-20-24*Real.sqrt (z+1)) * (Fintype.card X : ℝ)^2 ≤
        (((Finset.univ : Finset (X × X)).filter (fun p =>
          z ≤ ∑ i, f p.1 i * f p.2 i ∧ -1 ≤ ∑ j, g p.1 j * g p.2 j)).card : ℝ) ∨
       Real.exp (-20-24*Real.sqrt (z+1)) * (Fintype.card X : ℝ)^2 ≤
        (((Finset.univ : Finset (X × X)).filter (fun p =>
          z ≤ ∑ j, g p.1 j * g p.2 j ∧ -1 ≤ ∑ i, f p.1 i * f p.2 i)).card : ℝ)) := by
  classical
  have hm : 0 ≤ ∑ p : X × X, twoKernel (6 * ∑ i, f p.1 i * f p.2 i)
      (6 * ∑ j, g p.1 j * g p.2 j) := by
    have h := twoKernel_gram_sum_nonneg (fun x i => Real.sqrt 6 * f x i)
      (fun x j => Real.sqrt 6 * g x j)
    simp_rw [scaled_gram] at h
    simpa only [Fintype.sum_prod_type] using h
  have h := kernel_forces_correlation (Finset.univ : Finset (X × X)) Finset.univ_nonempty
    (fun p => ∑ i, f p.1 i * f p.2 i) (fun p => ∑ j, g p.1 j * g p.2 j) hm
  simpa only [Finset.card_univ, Fintype.card_prod, Nat.cast_mul, pow_two] using h

end Erdos77.CGFresh

-- END CGProof/GeometricPairs.lean

-- BEGIN CGProof/PairAveraging.lean

open scoped BigOperators

namespace Erdos77.CGFresh

theorem pair_filter_card {X : Type*} [Fintype X] (P : X → X → Prop) [DecidableRel P] :
    ((Finset.univ : Finset (X × X)).filter (fun p => P p.1 p.2)).card =
      ∑ x, ((Finset.univ : Finset X).filter (P x)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

theorem exists_large_fiber {X : Type*} [Fintype X] [Nonempty X]
    (P : X → X → Prop) [DecidableRel P] (a : ℝ)
    (h : a * (Fintype.card X : ℝ)^2 ≤
      (((Finset.univ : Finset (X × X)).filter (fun p => P p.1 p.2)).card : ℝ)) :
    ∃ x, a * (Fintype.card X : ℝ) ≤ (((Finset.univ : Finset X).filter (P x)).card : ℝ) := by
  classical
  by_contra hn
  push Not at hn
  have hs := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset X)) Finset.univ_nonempty
    (fun x _ => hn x)
  rw [pair_filter_card, Nat.cast_sum] at h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  nlinarith

end Erdos77.CGFresh

-- END CGProof/PairAveraging.lean

-- BEGIN CGProof/VectorKey.lean

open scoped BigOperators

namespace Erdos77.CGFresh

theorem exists_vector_key {X I : Type*} [Fintype X] [Nonempty X] [Fintype I]
    (f : Bool → X → I → ℝ) :
    ∃ (c : Bool) (z : ℝ) (x : X) (U : Finset X), -1 ≤ z ∧ U.Nonempty ∧
      Real.exp (-20-24*Real.sqrt (z+1)) * (Fintype.card X : ℝ) ≤ (U.card : ℝ) ∧
      (∀ y ∈ U, z ≤ ∑ i, f c x i * f c y i) ∧
      (∀ d y, y ∈ U → -1 ≤ ∑ i, f d x i * f d y i) := by
  classical
  obtain ⟨z, hz, h⟩ := geometric_pair_count (f true) (f false)
  have hc : ∃ c : Bool, Real.exp (-20-24*Real.sqrt (z+1)) * (Fintype.card X : ℝ)^2 ≤
      (((Finset.univ : Finset (X × X)).filter (fun p =>
        z ≤ (∑ i, f c p.1 i * f c p.2 i) ∧
        -1 ≤ (∑ i, f (!c) p.1 i * f (!c) p.2 i))).card : ℝ) := by
    rcases h with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨c, hc⟩ := hc
  let P := fun x y => z ≤ (∑ i, f c x i * f c y i) ∧
    -1 ≤ (∑ i, f (!c) x i * f (!c) y i)
  obtain ⟨x, hx⟩ := exists_large_fiber P (Real.exp (-20-24*Real.sqrt (z+1))) hc
  let U := (Finset.univ : Finset X).filter (P x)
  have hU : U.Nonempty := by
    apply Finset.card_pos.mp
    have hn : (0:ℝ) < Fintype.card X := Nat.cast_pos.mpr Fintype.card_pos
    have hp : (0:ℝ) < U.card := (mul_pos (Real.exp_pos _) hn).trans_le hx
    exact_mod_cast hp
  refine ⟨c, z, x, U, hz, hU, hx, ?_, ?_⟩
  · intro y hy
    exact (Finset.mem_filter.mp hy).2.1
  · intro d y hy
    have hp := (Finset.mem_filter.mp hy).2
    by_cases hd : d = c
    · subst d
      exact hz.trans hp.1
    · have he : d = !c := by cases d <;> cases c <;> simp_all
      subst d
      exact hp.2

end Erdos77.CGFresh

-- END CGProof/VectorKey.lean

-- BEGIN CGProof/TrimmedNeighbors.lean

namespace Erdos77.CGFresh

noncomputable def trimmedNeighbors {V : Type*} (G : SimpleGraph V) (c : Bool)
    (X Y : Finset V) (hX : X.Nonempty) (x : X) : Finset V :=
  Classical.choose (Finset.exists_subset_card_eq (minDegree_le G c X Y hX x.property))

theorem trimmedNeighbors_subset {V : Type*} (G : SimpleGraph V) (c : Bool)
    (X Y : Finset V) (hX : X.Nonempty) (x : X) :
    trimmedNeighbors G c X Y hX x ⊆ neighbors G c x.val Y :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (minDegree_le G c X Y hX x.property))).1

theorem trimmedNeighbors_card {V : Type*} (G : SimpleGraph V) (c : Bool)
    (X Y : Finset V) (hX : X.Nonempty) (x : X) :
    (trimmedNeighbors G c X Y hX x).card = minDegree G c X Y hX :=
  (Classical.choose_spec (Finset.exists_subset_card_eq (minDegree_le G c X Y hX x.property))).2

theorem trimmedNeighbors_subset_pages {V : Type*} (G : SimpleGraph V) (c : Bool)
    (X Y : Finset V) (hX : X.Nonempty) (x : X) :
    trimmedNeighbors G c X Y hX x ⊆ Y :=
  (trimmedNeighbors_subset G c X Y hX x).trans (density_neighbors_subset G c Y x.val)

end Erdos77.CGFresh

-- END CGProof/TrimmedNeighbors.lean

-- BEGIN CGProof/CenteredVectors.lean

open scoped BigOperators

namespace Erdos77.CGFresh

noncomputable def indicatorVec {V : Type*} (A : Finset V) (x : V) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

noncomputable def centeredVec {V : Type*} (A Y : Finset V) (p : ℝ) (x : V) : ℝ :=
  indicatorVec A x - p * indicatorVec Y x

theorem indicator_inner {V : Type*} [Fintype V] [DecidableEq V] (A B : Finset V) :
    (∑ x, indicatorVec A x * indicatorVec B x) = ((A ∩ B).card : ℝ) := by
  classical
  have he (x : V) : indicatorVec A x * indicatorVec B x =
      if x ∈ A ∩ B then (1:ℝ) else 0 := by
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [indicatorVec, ha, hb]
  simp_rw [he]
  simp only [Finset.sum_boole]
  apply congrArg (fun Z : Finset V => (Z.card : ℝ))
  ext x
  simp

theorem centered_inner {V : Type*} [Fintype V] [DecidableEq V] (A B Y : Finset V)
    (hA : A ⊆ Y) (hB : B ⊆ Y) (p : ℝ)
    (hAc : (A.card : ℝ) = p * (Y.card : ℝ)) (hBc : (B.card : ℝ) = p * (Y.card : ℝ)) :
    (∑ x, centeredVec A Y p x * centeredVec B Y p x) =
      ((A ∩ B).card : ℝ) - p^2 * (Y.card : ℝ) := by
  classical
  have he (x : V) : centeredVec A Y p x * centeredVec B Y p x =
      indicatorVec A x * indicatorVec B x -
      p * (indicatorVec A x * indicatorVec Y x) -
      p * (indicatorVec Y x * indicatorVec B x) +
      p^2 * (indicatorVec Y x * indicatorVec Y x) := by
    dsimp [centeredVec]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum, indicator_inner,
    Finset.inter_eq_left.mpr hA, Finset.inter_eq_right.mpr hB, Finset.inter_self]
  rw [hAc, hBc]
  ring

theorem normalized_centered_inner {V : Type*} [Fintype V] [DecidableEq V] (A B Y : Finset V)
    (hA : A ⊆ Y) (hB : B ⊆ Y) (p d : ℝ) (hd : 0 < d)
    (hAc : (A.card : ℝ) = p * (Y.card : ℝ)) (hBc : (B.card : ℝ) = p * (Y.card : ℝ)) :
    (∑ x, (centeredVec A Y p x / Real.sqrt d) *
      (centeredVec B Y p x / Real.sqrt d)) =
      (((A ∩ B).card : ℝ) - p^2 * (Y.card : ℝ)) / d := by
  have he (x : V) : (centeredVec A Y p x / Real.sqrt d) *
      (centeredVec B Y p x / Real.sqrt d) =
      (centeredVec A Y p x * centeredVec B Y p x) / d := by
    rw [div_mul_div_comm, Real.mul_self_sqrt hd.le]
  simp_rw [he]
  rw [← Finset.sum_div, centered_inner A B Y hA hB p hAc hBc]

end Erdos77.CGFresh

-- END CGProof/CenteredVectors.lean

-- BEGIN CGProof/NormalizedCount.lean

open scoped BigOperators

namespace Erdos77.CGFresh

theorem normalized_inner_count {V : Type*} [Fintype V] [DecidableEq V] (A B Y : Finset V)
    (hA : A ⊆ Y) (hB : B ⊆ Y) (p α z : ℝ) (hp : 0 < p) (hα : 0 < α)
    (hY : Y.Nonempty) (hAc : (A.card : ℝ) = p * (Y.card : ℝ))
    (hBc : (B.card : ℝ) = p * (Y.card : ℝ))
    (h : z ≤ ∑ x, (centeredVec A Y p x / Real.sqrt (α*p*(Y.card : ℝ))) *
      (centeredVec B Y p x / Real.sqrt (α*p*(Y.card : ℝ)))) :
    (p+z*α) * (A.card : ℝ) ≤ ((A ∩ B).card : ℝ) := by
  have hy : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  rw [normalized_centered_inner A B Y hA hB p (α*p*(Y.card:ℝ)) (by positivity) hAc hBc] at h
  have hh := (le_div_iff₀ (show 0 < α*p*(Y.card:ℝ) by positivity)).mp h
  rw [hAc]
  nlinarith

end Erdos77.CGFresh

-- END CGProof/NormalizedCount.lean

-- BEGIN CGProof/KeyExistence.lean

open scoped BigOperators

namespace Erdos77.CGFresh

theorem exists_keyStep {V : Type*} [Fintype V] (G : SimpleGraph V)
    (X : Finset V) (Y : Bool → Finset V) (hX : X.Nonempty)
    (hY : ∀ c, (Y c).Nonempty) (α : Bool → ℝ) (hα : ∀ c, 0 < α c)
    (hp : ∀ c, 0 < density G c X (Y c) hX) :
    Nonempty (KeyStep G X Y hX α) := by
  classical
  let : Nonempty X := hX.to_subtype
  let p := fun c => density G c X (Y c) hX
  let T := fun c (x : X) => trimmedNeighbors G c X (Y c) hX x
  have hT (c : Bool) (x : X) : T c x ⊆ Y c := trimmedNeighbors_subset_pages G c X (Y c) hX x
  have hTc (c : Bool) (x : X) : ((T c x).card : ℝ) = p c * ((Y c).card : ℝ) := by
    rw [show (T c x).card = minDegree G c X (Y c) hX from trimmedNeighbors_card G c X (Y c) hX x]
    exact (density_mul_card G c X (Y c) hX (hY c)).symm
  have hTne (c : Bool) (x : X) : (T c x).Nonempty := by
    have hy : (0:ℝ) < (Y c).card := by exact_mod_cast (hY c).card_pos
    have ht : (0:ℝ) < (T c x).card := by rw [hTc]; exact mul_pos (hp c) hy
    exact Finset.card_pos.mp (by exact_mod_cast ht)
  let f := fun c (x : X) (i : V) => centeredVec (T c x) (Y c) (p c) i /
    Real.sqrt (α c * p c * ((Y c).card : ℝ))
  obtain ⟨c, z, x, U, hz, hU, hcard, hselected, hall⟩ := exists_vector_key f
  let X' : Finset V := U.image Subtype.val
  have hX' : X'.Nonempty := hU.image _
  have hsub : X' ⊆ X := by
    intro y hy
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hy
    exact v.property
  have hcard' : X'.card = U.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hdense (d : Bool) (q : ℝ)
      (hq : ∀ y ∈ U, q ≤ ∑ i, f d x i * f d y i) :
      p d + q * α d ≤ density G d X' (T d x) hX' := by
    apply density_le_of_counts G d X' (T d x) hX' (hTne d x)
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hc := normalized_inner_count (T d x) (T d v) (Y d) (hT d x) (hT d v)
      (p d) (α d) q (hp d) (hα d) (hY d) (hTc d x) (hTc d v) (hq v hv)
    have hi : T d x ∩ T d v ⊆ neighbors G d v.val (T d x) := by
      intro w hw
      obtain ⟨hwx, hwv⟩ := Finset.mem_inter.mp hw
      have ha := (density_mem_neighbors G d (Y d) v.val w).mp
        (trimmedNeighbors_subset G d X (Y d) hX v hwv)
      exact (density_mem_neighbors G d (T d x) v.val w).mpr ⟨hwx, ha.2⟩
    have hiR : ((T d x ∩ T d v).card : ℝ) ≤ (neighbors G d v.val (T d x)).card := by
      exact_mod_cast Finset.card_le_card hi
    exact hc.trans hiR
  refine ⟨{
    vertex := x.val
    vertex_mem := x.property
    color := c
    level := z
    level_lower := hz
    reservoir := X'
    reservoir_subset := hsub
    reservoir_nonempty := hX'
    pages := fun d => T d x
    pages_subset := fun d => trimmedNeighbors_subset G d X (Y d) hX x
    pages_nonempty := fun d => hTne d x
    pages_card := fun d => trimmedNeighbors_card G d X (Y d) hX x
    reservoir_card := ?_
    selected_density := hdense c z hselected
    all_density := ?_ }⟩
  · rw [hcard']
    simpa only [Fintype.card_coe] using hcard
  · intro d
    simpa only [neg_one_mul, sub_eq_add_neg] using hdense d (-1) (fun y hy => hall d y hy)

end Erdos77.CGFresh

-- END CGProof/KeyExistence.lean

-- BEGIN CGProof/NextExistence.lean

namespace Erdos77.CGFresh

theorem BookTrace.exists_next {V : Type*} [Fintype V] {G : SimpleGraph V}
    {W : Finset V} {L p0 : ℝ} {t N : ℕ} (r : BookTrace G W L p0 t N)
    (hg : BookGuards L t) (hp0 : 0 ≤ p0)
    (hinit : ∀ c, p0 ≤ stateDensity G (initialBookState W) c)
    (hbase : 1 / 2 - 2 * bookSlack L ≤ p0)
    (hsmall : ∀ c, ((r.state N).spine c).card < t)
    (hlarge : Real.exp (bookD L * t) * (2 * (t : ℝ) + 1) ≤ W.card) :
    Nonempty (BookNext G L p0 t (r.state N)) := by
  have ht : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by have := hg.t_two; omega)
  let α := fun c => (stateDensity G (r.state N) c - p0 + bookSlack L) / (t : ℝ)
  have hα (c : Bool) : 0 < α c := by
    have hh := r.density_floor hg.t_two hinit N le_rfl c
    have hd := hg.slack_pos
    apply div_pos ?_ ht
    linarith
  have hp (c : Bool) : 0 < density G c (r.state N).reservoir ((r.state N).pages c)
      (r.reservoir_nonempty N le_rfl) := by
    rw [← stateDensity_eq]
    have hh := r.density_floor hg.t_two hinit N le_rfl c
    have hv := hg.page_pos
    linarith
  obtain ⟨w⟩ := exists_keyStep G (r.state N).reservoir (r.state N).pages
    (r.reservoir_nonempty N le_rfl) (r.pages_nonempty N le_rfl) α hα hp
  by_cases hcut : w.level ≤ L ^ 2
  · obtain ⟨j, hj⟩ := exists_large_color G w.vertex w.reservoir
    have hraw := w.color_reservoir_bound L hcut j hj
    have hR := r.color_reservoir_positive hg hp0 hinit hsmall hlarge hraw
    exact ⟨colorNext L p0 t (r.valid N le_rfl) (r.reservoir_nonempty N le_rfl)
      (r.pages_nonempty N le_rfl) hsmall w hcut j hj hR⟩
  · exact ⟨boostNext L p0 t (r.valid N le_rfl) (r.reservoir_nonempty N le_rfl)
      (r.pages_nonempty N le_rfl) (r.spine_le N le_rfl) w (lt_of_not_ge hcut)⟩

end Erdos77.CGFresh

-- END CGProof/NextExistence.lean

-- BEGIN CGProof/BookExistence.lean

namespace Erdos77.CGFresh

theorem exists_large_book {V : Type*} [Fintype V] (G : SimpleGraph V)
    (W : Finset V) (L : ℝ) (t m : ℕ) (hg : BookGuards L t)
    (hlarge : Real.exp (bookD L * t) * (2 * (t : ℝ) + 1) ≤ W.card)
    (hpage : (m : ℝ) ≤ Real.exp (-(Real.log 2 + bookH L) * t) * (W.card : ℝ))
    (hdegree : ∀ c, 1 / 2 - 2 * bookSlack L ≤ stateDensity G (initialBookState W) c) :
    ∃ c : Bool, ∃ A B : Finset V, IsBook (colorGraph G c) A B ∧ A.card = t ∧ m ≤ B.card := by
  classical
  have hW : W.Nonempty := by
    have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have hh : (0 : ℝ) < W.card := lt_of_lt_of_le (mul_pos (Real.exp_pos _) (by linarith)) hlarge
    exact Finset.card_pos.mp (by exact_mod_cast hh)
  let p0 := min (stateDensity G (initialBookState W) false) (stateDensity G (initialBookState W) true)
  have hinit (c : Bool) : p0 ≤ stateDensity G (initialBookState W) c := by
    cases c
    · exact min_le_left _ _
    · exact min_le_right _ _
  have hbase : 1 / 2 - 2 * bookSlack L ≤ p0 := le_min (hdegree false) (hdegree true)
  have hp0 : 0 ≤ p0 := by have := hg.slack_small; linarith
  by_contra hnone
  have build : ∀ N : ℕ, Nonempty (BookTrace G W L p0 t N) := by
    intro N
    induction N with
    | zero => exact ⟨BookTrace.zero G W L p0 t hW⟩
    | succ N ih =>
      obtain ⟨r⟩ := ih
      have hsmall (c : Bool) : ((r.state N).spine c).card < t := by
        have hle := r.spine_le N le_rfl c
        by_contra hh
        have he : ((r.state N).spine c).card = t := by omega
        have hp := hpage.trans (r.pages_bound hg hp0 hinit hbase c)
        have hpc : m ≤ ((r.state N).pages c).card := by exact_mod_cast hp
        exact hnone ⟨c, (r.state N).spine c, (r.state N).pages c,
          (r.valid N le_rfl).2.1 c, he, hpc⟩
      obtain ⟨w⟩ := r.exists_next hg hp0 hinit hbase hsmall hlarge
      exact ⟨r.extend w⟩
  let N := ⌈2 * (t : ℝ) + 2 * bookBoostCount L * t⌉₊ + 1
  obtain ⟨r⟩ := build N
  have hh := r.length_bound hg hp0 hinit
  have hc := Nat.le_ceil (2 * (t : ℝ) + 2 * bookBoostCount L * t)
  dsimp [N] at hh
  push_cast at hh
  linarith

end Erdos77.CGFresh

-- END CGProof/BookExistence.lean

-- BEGIN CGProof/RamseyFinite.lean

namespace Erdos77.CGFresh

theorem ramsey_finset {V : Type*} (G : SimpleGraph V) :
    ∀ k l : ℕ, ∀ S : Finset V, (k + l).choose k ≤ S.card →
      (∃ K ⊆ S, G.IsNClique k K) ∨ (∃ K ⊆ S, Gᶜ.IsNClique l K) := by
  classical
  intro k
  induction k with
  | zero =>
      intro l S _
      exact Or.inl ⟨∅, Finset.empty_subset S, by simp⟩
  | succ k ihk =>
      intro l
      induction l with
      | zero =>
          intro S _
          exact Or.inr ⟨∅, Finset.empty_subset S, by simp⟩
      | succ l ihl =>
          intro S hS
          have hp : 0 < (k + 1 + (l + 1)).choose (k + 1) :=
            Nat.choose_pos (by omega)
          obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hp hS)
          let R := S.filter (G.Adj v)
          let B := S.filter (Gᶜ.Adj v)
          have hR : R ⊆ S := Finset.filter_subset _ _
          have hB : B ⊆ S := Finset.filter_subset _ _
          have hd : Disjoint R B := by
            apply Finset.disjoint_left.mpr
            intro x hx hy
            exact (Finset.mem_filter.mp hy).2.2 (Finset.mem_filter.mp hx).2
          have hu : R ∪ B = S.erase v := by
            ext x
            simp only [R, B, Finset.mem_union, Finset.mem_filter,
              SimpleGraph.compl_adj, Finset.mem_erase]
            constructor
            · rintro (⟨hx, ha⟩ | ⟨hx, hne, _⟩)
              · exact ⟨ha.ne.symm, hx⟩
              · exact ⟨hne.symm, hx⟩
            · rintro ⟨hne, hx⟩
              by_cases ha : G.Adj v x
              · exact Or.inl ⟨hx, ha⟩
              · exact Or.inr ⟨hx, hne.symm, ha⟩
          have hcard : R.card + B.card + 1 = S.card := by
            rw [← Finset.card_union_of_disjoint hd, hu]
            exact Finset.card_erase_add_one hv
          have hpas : (k + 1 + (l + 1)).choose (k + 1) =
              (k + (l + 1)).choose k + (k + 1 + l).choose (k + 1) := by
            rw [show k + 1 + (l + 1) = (k + (l + 1)) + 1 by omega,
              show k + 1 + l = k + (l + 1) by omega]
            exact Nat.choose_succ_succ' _ _
          by_cases hr : (k + (l + 1)).choose k ≤ R.card
          · rcases ihk (l + 1) R hr with ⟨K, hK, hc⟩ | ⟨K, hK, hc⟩
            · left
              refine ⟨insert v K, Finset.insert_subset hv (hK.trans hR), ?_⟩
              exact hc.insert (fun x hx => (Finset.mem_filter.mp (hK hx)).2)
            · exact Or.inr ⟨K, hK.trans hR, hc⟩
          · have hb : (k + 1 + l).choose (k + 1) ≤ B.card := by omega
            rcases ihl B hb with ⟨K, hK, hc⟩ | ⟨K, hK, hc⟩
            · exact Or.inl ⟨K, hK.trans hB, hc⟩
            · right
              refine ⟨insert v K, Finset.insert_subset hv (hK.trans hB), ?_⟩
              exact hc.insert (fun x hx => (Finset.mem_filter.mp (hK hx)).2)

theorem ramsey_finset_pow {V : Type*} (G : SimpleGraph V) (k l : ℕ)
    (S : Finset V) (hS : 2 ^ (k + l) ≤ S.card) :
    (∃ K ⊆ S, G.IsNClique k K) ∨ (∃ K ⊆ S, Gᶜ.IsNClique l K) :=
  ramsey_finset G k l S ((Nat.choose_le_two_pow _ _).trans hS)

end Erdos77.CGFresh

-- END CGProof/RamseyFinite.lean

-- BEGIN CGProof/BookRamsey.lean

namespace Erdos77.CGFresh

def RamseyConclusion {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  (∃ K : Finset V, G.IsNClique k K) ∨ (∃ K : Finset V, Gᶜ.IsNClique k K)

theorem conclusion_of_color {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (c : Bool) {K : Finset V} (h : (colorGraph G c).IsNClique k K) : RamseyConclusion G k := by
  cases c
  · exact Or.inr ⟨K, h⟩
  · exact Or.inl ⟨K, h⟩

theorem conclusion_of_large_spine {V : Type*} {G : SimpleGraph V} {k : ℕ}
    (c : Bool) {A B : Finset V} (h : IsBook (colorGraph G c) A B)
    (hk : k ≤ A.card) : RamseyConclusion G k := by
  obtain ⟨K, hKA, hK⟩ := Finset.exists_subset_card_eq hk
  apply conclusion_of_color c (K := K)
  exact ⟨h.clique.subset hKA, hK⟩

theorem book_forces_clique {V : Type*} {G : SimpleGraph V} {k t : ℕ}
    (c : Bool) {A B : Finset V} (h : IsBook (colorGraph G c) A B)
    (hA : A.card = t) (ht : t ≤ k) (hB : (2*k-t).choose k ≤ B.card) :
    RamseyConclusion G k := by
  classical
  have hn : (k-t)+k = 2*k-t := by omega
  have hb : ((k-t)+k).choose (k-t) ≤ B.card := by
    rw [Nat.choose_symm_add, hn]
    exact hB
  rcases ramsey_finset (colorGraph G c) (k-t) k B hb with ⟨K,hKB,hK⟩ | ⟨K,_,hK⟩
  · have hh := h.extend_nclique hKB hK
    rw [hA, Nat.add_sub_of_le ht] at hh
    exact conclusion_of_color c hh
  · cases c
    · exact Or.inl ⟨K, by simpa [colorGraph] using hK⟩
    · exact Or.inr ⟨K, by simpa [colorGraph] using hK⟩

theorem regularized_long_forces {V : Type*} {G : SimpleGraph V} {k : ℕ}
    {A : Bool → Finset V} {B : Finset V}
    (hbook : ∀ c, IsBook (colorGraph G c) (A c) B)
    (hA : ∀ c, (A c).card ≤ k)
    (hB : 2 ^ (2*k-((A false).card+(A true).card)) ≤ B.card) : RamseyConclusion G k := by
  classical
  have hn : (k-(A true).card)+(k-(A false).card) =
      2*k-((A false).card+(A true).card) := by have := hA false; have := hA true; omega
  rw [← hn] at hB
  rcases ramsey_finset_pow G (k-(A true).card) (k-(A false).card) B hB with
    ⟨K,hKB,hK⟩ | ⟨K,hKB,hK⟩
  · have hh := (hbook true).extend_nclique hKB hK
    rw [Nat.add_sub_of_le (hA true)] at hh
    exact conclusion_of_color true hh
  · have hh := (hbook false).extend_nclique hKB hK
    rw [Nat.add_sub_of_le (hA false)] at hh
    exact conclusion_of_color false hh

end Erdos77.CGFresh

-- END CGProof/BookRamsey.lean

-- BEGIN CGProof/Regularization.lean

namespace Erdos77.CGFresh

structure Regularized {V : Type*} (G : SimpleGraph V) (S : Finset V) (δ : ℝ) where
  reservoir : Finset V
  spine : Bool → Finset V
  reservoir_subset : reservoir ⊆ S
  spine_subset : ∀ c, spine c ⊆ S
  books : ∀ c, IsBook (colorGraph G c) (spine c) reservoir
  disjoint : Disjoint (spine false) (spine true)
  size : ((1 + δ) / 2) ^ ((spine false).card + (spine true).card) * S.card ≤
    (reservoir.card : ℝ)
  degrees : ∀ x ∈ reservoir, ∀ c,
    (1 / 2 - δ) * reservoir.card - 1 ≤ ((neighbors G c x reservoir).card : ℝ)

theorem exists_regularized {V : Type*} (G : SimpleGraph V) (δ : ℝ)
    (hδ : 0 ≤ δ) (S : Finset V) : Nonempty (Regularized G S δ) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hgood : ∀ x ∈ S, ∀ c,
        (1 / 2 - δ) * S.card - 1 ≤ ((neighbors G c x S).card : ℝ)
    · exact ⟨{
        reservoir := S
        spine := fun _ => ∅
        reservoir_subset := Finset.Subset.refl S
        spine_subset := fun _ => Finset.empty_subset S
        books := fun _ => IsBook.empty S
        disjoint := by simp
        size := by simp
        degrees := hgood }⟩
    · push Not at hgood
      obtain ⟨x, hx, c, hc⟩ := hgood
      let j := !c
      let T := neighbors G j x S
      have hTS : T ⊆ S := neighbors_subset G j x S
      have hT : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
        ⟨neighbors_subset G j x S, by
          intro he
          have hxT : x ∈ T := by rw [he]; exact hx
          exact self_not_neighbors G j x S hxT⟩
      obtain ⟨r⟩ := ih T hT
      let A : Bool → Finset V := fun b => if b = j then insert x (r.spine b) else r.spine b
      have hxA (b : Bool) : x ∉ r.spine b := by
        intro hb
        exact self_not_neighbors G j x S (r.spine_subset b hb)
      have hAx (a : V) (b : Bool) (ha : a ∈ r.spine b) : (colorGraph G j).Adj x a :=
        ((mem_neighbors G j x a S).mp (r.spine_subset b ha)).2
      have hWx (a : V) (ha : a ∈ r.reservoir) : (colorGraph G j).Adj x a :=
        ((mem_neighbors G j x a S).mp (r.reservoir_subset ha)).2
      have hsum : (A false).card + (A true).card =
          (r.spine false).card + (r.spine true).card + 1 := by
        cases hj : j <;> simp [A, hj, Finset.card_insert_of_notMem, hxA] <;> omega
      refine ⟨{
        reservoir := r.reservoir
        spine := A
        reservoir_subset := r.reservoir_subset.trans hTS
        spine_subset := ?_
        books := ?_
        disjoint := ?_
        size := ?_
        degrees := r.degrees }⟩
      · intro b
        dsimp only [A]
        split_ifs
        · exact Finset.insert_subset hx ((r.spine_subset b).trans hTS)
        · exact (r.spine_subset b).trans hTS
      · intro b
        dsimp only [A]
        split_ifs with hb
        · subst b
          exact (r.books j).insert_spine (fun a ha => hAx a j ha)
            (Finset.Subset.refl _) hWx
        · exact r.books b
      · cases hj : j <;> simp [A, hj, Finset.disjoint_insert_left,
          Finset.disjoint_insert_right, hxA, r.disjoint]
      · have hq : 0 ≤ (1 + δ) / 2 := by positivity
        have hlarge : ((1 + δ) / 2) * S.card ≤ (T.card : ℝ) :=
          other_color_large G hx hδ c hc
        rw [hsum, pow_succ]
        calc
          ((1 + δ) / 2) ^ ((r.spine false).card + (r.spine true).card) *
              ((1 + δ) / 2) * S.card =
              ((1 + δ) / 2) ^ ((r.spine false).card + (r.spine true).card) *
              (((1 + δ) / 2) * S.card) := by ring
          _ ≤ ((1 + δ) / 2) ^ ((r.spine false).card + (r.spine true).card) * T.card :=
            mul_le_mul_of_nonneg_left hlarge (pow_nonneg hq _)
          _ ≤ (r.reservoir.card : ℝ) := r.size

end Erdos77.CGFresh

-- END CGProof/Regularization.lean

-- BEGIN CGProof/ParameterLimits.lean

open Filter Topology

namespace Erdos77.CGFresh

lemma inv_real_limit : Tendsto (fun L : ℝ => 1/L) atTop (𝓝 0) := by
  simpa only [one_div] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))

lemma log_div_real_limit : Tendsto (fun L : ℝ => Real.log L/L) atTop (𝓝 0) := by
  simpa only [pow_one, one_mul, add_zero] using
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero

lemma sqrt_ratio_limit : Tendsto (fun L : ℝ => Real.sqrt (L^2+1)/L) atTop (𝓝 1) := by
  have hh : Tendsto (fun L : ℝ => Real.sqrt (1+(1/L)^2)) atTop (𝓝 1) := by
    have hin : Tendsto (fun L : ℝ => 1+(1/L)^2) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).add (inv_real_limit.pow 2)
    simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 1).comp hin
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [show (1+(1/L)^2) = (L^2+1)/L^2 by field_simp,
    Real.sqrt_div (by positivity), Real.sqrt_sq hL.le]

lemma bookD_normalized_limit : Tendsto (fun L : ℝ => bookD L/L) atTop (𝓝 48) := by
  have hh := ((inv_real_limit.const_mul (2*Real.log 2+40)).add
    (sqrt_ratio_limit.const_mul 48)).add
    (((log_div_real_limit.mul (inv_real_limit.pow 2)).const_mul 704).add
      ((log_div_real_limit.mul inv_real_limit).const_mul 672))
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  rw [bookD, bookA, bookBoostCount_formula, log_inverse_slack]
  field_simp
  ring

lemma bookD_fraction_limit :
    Tendsto (fun L : ℝ => bookD L * bookFraction L) atTop (𝓝 (48/1000)) := by
  have hh := bookD_normalized_limit.div_const 1000
  convert hh using 1
  ext L
  dsimp [bookFraction]
  ring

end Erdos77.CGFresh

-- END CGProof/ParameterLimits.lean

-- BEGIN CGProof/PageLossBounds.lean

namespace Erdos77.CGFresh

theorem page_loss_bounds {δ B : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/11) (hB : 0 ≤ B) :
    0 ≤ -(1+B)*Real.log (1/2-11*δ/4)-Real.log 2 ∧
    -(1+B)*Real.log (1/2-11*δ/4)-Real.log 2 ≤ 11*δ+2*B := by
  let v : ℝ := 1/2-11*δ/4
  have hv : 0 < v := by dsimp [v]; linarith
  have hvq : 1/4 ≤ v := by dsimp [v]; linarith
  have hvh : v ≤ 1/2 := by dsimp [v]; linarith
  have hhalf : Real.log (1/2:ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hquarter : Real.log (1/4:ℝ) = -2*Real.log 2 := by
    rw [one_div, Real.log_inv, show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hlow := Real.log_le_log hv hvh
  rw [hhalf] at hlow
  have hhigh := Real.log_le_log (show (0:ℝ)<1/4 by norm_num) hvq
  rw [hquarter] at hhigh
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hlog : -Real.log v ≤ 2 := by linarith
  have hratio := Real.log_le_sub_one_of_pos (show 0 < (1/2:ℝ)/v by positivity)
  rw [Real.log_div (by norm_num) hv.ne', hhalf] at hratio
  have hr : (1/2:ℝ)/v-1 ≤ 11*δ := by
    apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hv).mpr
    have hh := mul_nonneg hδ (sub_nonneg.mpr hvq)
    dsimp [v] at *
    nlinarith
  have hnonneg : 0 ≤ -Real.log v := by linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  change 0 ≤ -(1+B)*Real.log v-Real.log 2 ∧ _ ≤ _
  constructor
  · nlinarith [mul_nonneg hB hnonneg]
  · nlinarith [mul_le_mul_of_nonneg_left hlog hB]

end Erdos77.CGFresh

-- END CGProof/PageLossBounds.lean

-- BEGIN CGProof/SmallParameterLimits.lean

open Filter Topology
namespace Erdos77.CGFresh

lemma slack_limit : Tendsto bookSlack atTop (𝓝 0) := by
  change Tendsto (fun L : ℝ => 1/L^2) atTop (𝓝 0)
  simpa [div_pow] using inv_real_limit.pow 2

lemma page_fraction_limit :
    Tendsto (fun L : ℝ => bookH L / bookFraction L) atTop (𝓝 0) := by
  have hu : Tendsto (fun L : ℝ => 11000/L + 16000*(Real.log L/L)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (inv_real_limit.const_mul 11000).add (log_div_real_limit.const_mul 16000)
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_gt_atTop (4:ℝ)] with L hL
    have hp : 0 < L := by linarith
    have hs : bookSlack L ≤ 1/11 := by dsimp [bookSlack]; apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr; nlinarith
    have hb : 0 ≤ bookBoostCount L := by rw [bookBoostCount_formula]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) (sq_nonneg L)
    have h := page_loss_bounds (show 0 ≤ bookSlack L by dsimp [bookSlack]; positivity) hs hb
    exact div_nonneg h.1 (by dsimp [bookFraction]; positivity)
  · filter_upwards [eventually_gt_atTop (4:ℝ)] with L hL
    have hp : 0 < L := by linarith
    have hs : bookSlack L ≤ 1/11 := by dsimp [bookSlack]; apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr; nlinarith
    have hb : 0 ≤ bookBoostCount L := by rw [bookBoostCount_formula]; exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) (sq_nonneg L)
    have h := page_loss_bounds (show 0 ≤ bookSlack L by dsimp [bookSlack]; positivity) hs hb
    have hh := div_le_div_of_nonneg_right h.2 (show 0 ≤ bookFraction L by dsimp [bookFraction]; positivity)
    change bookH L / bookFraction L ≤ _ at hh
    convert hh using 1
    rw [bookBoostCount_formula]
    dsimp [bookSlack, bookFraction]
    field_simp
    ring

lemma deficit_fraction_limit :
    Tendsto (fun L : ℝ => (bookDeficit L + (bookSlack L)^2 * Real.log 2) /
      (bookFraction L)^2) atTop (𝓝 0) := by
  have hh := ((inv_real_limit.pow 4).const_mul 250000).add
    ((inv_real_limit.pow 2).const_mul (1000000*Real.log 2))
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  dsimp [bookDeficit, bookSlack, bookFraction]
  field_simp
  ring

end Erdos77.CGFresh

-- END CGProof/SmallParameterLimits.lean

-- BEGIN CGProof/ParameterChoice.lean

open Filter Topology
namespace Erdos77.CGFresh

structure RamseyParameters (L : ℝ) : Prop where
  large : 4 ≤ L
  slack_small : bookSlack L ≤ 1/16
  fraction_pos : 0 < bookFraction L
  fraction_small : bookFraction L ≤ 1/2
  deficit_pos : 0 < bookDeficit L
  deficit_small : bookDeficit L < Real.log 2
  reservoir_gap : bookD L * bookFraction L < Real.log 2
  page_gap : 0 < (bookFraction L)^2/6 - bookH L*bookFraction L -
    bookDeficit L - (bookSlack L)^2*Real.log 2

theorem exists_ramsey_parameters : ∃ L : ℝ, RamseyParameters L := by
  have hl : (48/1000:ℝ) < Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (show (0:ℝ) ≤ 1 by norm_num)
    norm_num at h
    linarith
  have hD := bookD_fraction_limit.eventually (gt_mem_nhds hl)
  have hH := page_fraction_limit.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/24))
  have hd := deficit_fraction_limit.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/24))
  obtain ⟨L, hL, hD, hH, hd⟩ := ((eventually_ge_atTop (4:ℝ)).and (hD.and (hH.and hd))).exists
  have hp : 0 < L := by linarith
  have he : 0 < bookFraction L := by dsimp [bookFraction]; positivity
  have hδ : 0 < bookSlack L := by dsimp [bookSlack]; positivity
  have hδs : bookSlack L ≤ 1/16 := by
    dsimp [bookSlack]
    apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  have hes : bookFraction L ≤ 1/2 := by
    dsimp [bookFraction]
    apply (div_le_iff₀ (by positivity : 0 < 1000*L)).mpr
    linarith
  have hHp := (div_lt_iff₀ he).mp hH
  have hdp := (div_lt_iff₀ (sq_pos_of_pos he)).mp hd
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdef : 0 < bookDeficit L := by dsimp [bookDeficit]; positivity
  refine ⟨L, ⟨hL, hδs, he, hes, hdef, ?_, hD, ?_⟩⟩
  · have hs := mul_nonneg (sq_nonneg (bookSlack L)) hlog.le
    have he2 : (bookFraction L)^2 ≤ 1/4 := by nlinarith
    nlinarith
  · have hh := mul_lt_mul_of_pos_right hHp he
    nlinarith

end Erdos77.CGFresh

-- END CGProof/ParameterChoice.lean

-- BEGIN CGProof/FloorScale.lean

open Filter Topology
namespace Erdos77.CGFresh

noncomputable def bookSize (L : ℝ) (k : ℕ) : ℕ := ⌊bookFraction L * k⌋₊

lemma floor_linear_ratio (e : ℝ) (he : 0 ≤ e) :
    Tendsto (fun k : ℕ => (⌊e*k⌋₊ : ℝ)/(k:ℝ)) atTop (𝓝 e) := by
  have herr : Tendsto (fun k : ℕ => ((⌊e*k⌋₊ : ℝ)-e*k)/(k:ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := -1) (B := 0) _ _ tendsto_natCast_atTop_atTop
    · exact Eventually.of_forall fun k => by linarith [Nat.lt_floor_add_one (e*(k:ℝ))]
    · exact Eventually.of_forall fun k => sub_nonpos.mpr (Nat.floor_le (mul_nonneg he (Nat.cast_nonneg k)))
  have hh := herr.add_const e
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp
  ring

lemma bookSize_ratio {L : ℝ} (h : RamseyParameters L) :
    Tendsto (fun k : ℕ => (bookSize L k:ℝ)/(k:ℝ)) atTop (𝓝 (bookFraction L)) :=
  floor_linear_ratio _ h.fraction_pos.le

lemma bookSize_large {L : ℝ} (h : RamseyParameters L) (C : ℝ) :
    ∀ᶠ k : ℕ in atTop, C ≤ (bookSize L k:ℝ) := by
  have hh : Tendsto (fun k : ℕ => bookFraction L*(k:ℝ)-1) atTop atTop :=
    by
      simpa only [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right (atTop : Filter ℕ) (-1:ℝ)
          (tendsto_natCast_atTop_atTop.const_mul_atTop h.fraction_pos))
  filter_upwards [hh.eventually (eventually_ge_atTop C)] with k hk
  exact hk.trans (by dsimp [bookSize]; linarith [Nat.lt_floor_add_one (bookFraction L*(k:ℝ))])

lemma bookSize_le {L : ℝ} (h : RamseyParameters L) (k : ℕ) : bookSize L k ≤ k := by
  apply Nat.floor_le_of_le
  exact (mul_le_mul_of_nonneg_right (h.fraction_small.trans (by norm_num : (1/2:ℝ)≤1)) (Nat.cast_nonneg k)).trans_eq (one_mul _)

end Erdos77.CGFresh

-- END CGProof/FloorScale.lean

-- BEGIN CGProof/BinomialStep.lean

namespace Erdos77.CGFresh

theorem binomial_ratio_bound {k t : ℝ} (hk : 0 < k) (ht : 0 ≤ t) (htk : t < k) :
    (k-t)/(2*k-t) ≤ (1/2)*Real.exp (-t/(2*k)) := by
  have hd : 0 < 2*k-t := by linarith
  have hu : t/(2*k) ≤ t/(2*k-t) :=
    div_le_div_of_nonneg_left ht hd (by linarith)
  have he : (k-t)/(2*k-t) = (1/2)*(1-t/(2*k-t)) := by
    field_simp [hd.ne', show k*2-t ≠ 0 by nlinarith]
    ring
  rw [he]
  have hb := Real.add_one_le_exp (-t/(2*k))
  rw [neg_div] at hb ⊢
  linarith

theorem choose_decrement_bound (k t : ℕ) (htk : t < k) :
    ((2*k-(t+1)).choose k : ℝ) ≤
      ((2*k-t).choose k : ℝ) * ((1/2)*Real.exp (-(t:ℝ)/(2*(k:ℝ)))) := by
  have hk : 0 < k := by omega
  have hn : 2*k-(t+1)+1 = 2*k-t := by omega
  have hm : 2*k-t-k = k-t := by omega
  have hr := Nat.choose_mul_succ_eq (2*k-(t+1)) k
  rw [hn, hm] at hr
  have htkR : (t:ℝ) < k := by exact_mod_cast htk
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hd : (0:ℝ) < 2*(k:ℝ)-(t:ℝ) := by linarith
  have hrec : ((2*k-(t+1)).choose k : ℝ) * (2*(k:ℝ)-(t:ℝ)) =
      ((2*k-t).choose k : ℝ) * ((k:ℝ)-(t:ℝ)) := by
    have hh := congrArg (fun x : ℕ => (x:ℝ)) hr
    push_cast [Nat.cast_sub (show t ≤ 2*k by omega), Nat.cast_sub (show t ≤ k by omega)] at hh
    exact hh
  have he : ((2*k-(t+1)).choose k : ℝ) =
      ((2*k-t).choose k : ℝ) * (((k:ℝ)-(t:ℝ))/(2*(k:ℝ)-(t:ℝ))) := by
    apply (eq_div_iff hd.ne').mpr at hrec
    simpa only [mul_div_assoc] using hrec
  rw [he]
  exact mul_le_mul_of_nonneg_left
    (binomial_ratio_bound (by exact_mod_cast hk) (Nat.cast_nonneg t) (by exact_mod_cast htk))
    (Nat.cast_nonneg _)

end Erdos77.CGFresh

-- END CGProof/BinomialStep.lean

-- BEGIN CGProof/BinomialGain.lean

namespace Erdos77.CGFresh

theorem choose_decrement_product (k t : ℕ) (htk : t ≤ k) :
    ((2*k-t).choose k : ℝ) ≤ ((2*k).choose k : ℝ) * (1/2:ℝ)^t *
      Real.exp (-((t:ℝ)*((t:ℝ)-1))/(4*(k:ℝ))) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have ht : t < k := by omega
    have h := (choose_decrement_bound k t ht).trans
      (mul_le_mul_of_nonneg_right (ih (by omega)) (by positivity))
    have he : ((2*k).choose k : ℝ) * (1/2:ℝ)^t *
        Real.exp (-((t:ℝ)*((t:ℝ)-1))/(4*(k:ℝ))) *
        ((1/2)*Real.exp (-(t:ℝ)/(2*(k:ℝ)))) =
        ((2*k).choose k : ℝ) * (1/2:ℝ)^(t+1) *
        Real.exp (-(((t+1:ℕ):ℝ)*(((t+1:ℕ):ℝ)-1))/(4*(k:ℝ))) := by
      rw [pow_succ]
      have hx : -((t:ℝ)*((t:ℝ)-1))/(4*(k:ℝ)) + -(t:ℝ)/(2*(k:ℝ)) =
          -(((t+1:ℕ):ℝ)*(((t+1:ℕ):ℝ)-1))/(4*(k:ℝ)) := by
        push_cast
        ring
      rw [← hx, Real.exp_add]
      ring
    exact h.trans_eq he

theorem binomial_off_diagonal_gain (k t : ℕ) (ht : 3 ≤ t) (htk : t ≤ k) :
    ((2*k-t).choose k : ℝ) ≤
      Real.exp (-(t:ℝ)^2/(6*(k:ℝ))) * (2:ℝ)^(2*k-t) := by
  have hk : 0 < k := by omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have htR : (3:ℝ) ≤ t := by exact_mod_cast ht
  have hc : ((2*k).choose k : ℝ) ≤ (2:ℝ)^(2*k) := by
    exact_mod_cast Nat.choose_le_two_pow (2*k) k
  have he : (2:ℝ)^(2*k) * (1/2:ℝ)^t = (2:ℝ)^(2*k-t) := by
    rw [div_pow, one_pow, mul_one_div, div_eq_mul_inv]
    exact (pow_sub₀ (2:ℝ) (by norm_num : (2:ℝ) ≠ 0) (show t ≤ 2*k by omega)).symm
  have h := (choose_decrement_product k t htk).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) (by positivity))
  rw [he] at h
  have hex : -((t:ℝ)*((t:ℝ)-1))/(4*(k:ℝ)) ≤ -(t:ℝ)^2/(6*(k:ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hp := mul_nonneg (show 0 ≤ (t:ℝ) by positivity) (sub_nonneg.mpr htR)
    have hh := mul_nonneg hp hkR.le
    nlinarith
  exact h.trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hex) (by positivity))

end Erdos77.CGFresh

-- END CGProof/BinomialGain.lean

-- BEGIN CGProof/EndpointLimits.lean

open Filter Topology
namespace Erdos77.CGFresh

noncomputable def reservoirRate (L : ℝ) : ℝ :=
  Real.log 4 - bookDeficit L - (bookSlack L)^2*Real.log 2

lemma bookH_nonneg {L : ℝ} (h : RamseyParameters L) : 0 ≤ bookH L := by
  have hp : 0 < L := by linarith [h.large]
  exact (page_loss_bounds (by dsimp [bookSlack]; positivity)
    (h.slack_small.trans (by norm_num)) (by
      rw [bookBoostCount_formula]
      exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [h.large]))) (sq_nonneg L))).1

lemma reservoir_rate_gap {L : ℝ} (h : RamseyParameters L) :
    bookD L*bookFraction L < reservoirRate L := by
  have hl : (1/2:ℝ) ≤ Real.log 2 := by
    have hh := Real.le_log_one_add_of_nonneg (show (0:ℝ)≤1 by norm_num)
    norm_num at hh
    linarith
  have hg := h.page_gap
  have hh := mul_nonneg (bookH_nonneg h) h.fraction_pos.le
  have he : (bookFraction L)^2 ≤ 1/4 := by nlinarith [h.fraction_small,h.fraction_pos]
  have hlog : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  dsimp [reservoirRate]
  rw [hlog]
  linarith [h.reservoir_gap]

lemma log_linear_ratio : Tendsto (fun k : ℕ => Real.log (2*(k:ℝ)+1)/(k:ℝ)) atTop (𝓝 0) := by
  have hu : Tendsto (fun k : ℕ => 2*(k:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hl : Tendsto (fun k : ℕ => Real.log (2*(k:ℝ)+1)/(2*(k:ℝ)+1)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using log_div_real_limit.comp hu
  have hi : Tendsto (fun k : ℕ => 1/(k:ℝ)) atTop (𝓝 0) :=
    inv_real_limit.comp tendsto_natCast_atTop_atTop
  have hh := hl.mul (hi.const_add 2)
  norm_num at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with k hk
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  field_simp

lemma book_log_ratio {L : ℝ} (h : RamseyParameters L) :
    Tendsto (fun k : ℕ => Real.log (2*(bookSize L k:ℝ)+1)/(k:ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ log_linear_ratio
  · exact Eventually.of_forall fun k => div_nonneg (Real.log_nonneg (by have hh := Nat.cast_nonneg (bookSize L k) (α := ℝ); linarith)) (Nat.cast_nonneg k)
  · exact Eventually.of_forall fun k => div_le_div_of_nonneg_right
      (Real.log_le_log (by positivity) (by exact_mod_cast (show 2*bookSize L k+1≤2*k+1 by have := bookSize_le h k; omega))) (Nat.cast_nonneg k)

lemma eventual_reservoir_size {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop, Real.exp (bookD L*(bookSize L k:ℝ))*(2*(bookSize L k:ℝ)+1) ≤
      Real.exp (reservoirRate L*(k:ℝ)) := by
  have hh := ((bookSize_ratio h).const_mul (bookD L)).add (book_log_ratio h)
  simp only [add_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds (reservoir_rate_gap h)), eventually_gt_atTop (0:ℕ)] with k hk hkp
  have hkR : (0:ℝ)<k := by exact_mod_cast hkp
  have hx : bookD L*(bookSize L k:ℝ)+Real.log (2*(bookSize L k:ℝ)+1) ≤ reservoirRate L*(k:ℝ) := by
    have he : bookD L*((bookSize L k:ℝ)/(k:ℝ))+Real.log (2*(bookSize L k:ℝ)+1)/(k:ℝ) =
      (bookD L*(bookSize L k:ℝ)+Real.log (2*(bookSize L k:ℝ)+1))/(k:ℝ) := by ring
    rw [he] at hk
    exact ((div_lt_iff₀ hkR).mp hk).le
  have hh := Real.exp_le_exp.mpr hx
  simpa only [Real.exp_add, Real.exp_log (by positivity : (0:ℝ)<2*(bookSize L k:ℝ)+1)] using hh

end Erdos77.CGFresh

-- END CGProof/EndpointLimits.lean

-- BEGIN CGProof/PageEndpoint.lean

open Filter Topology
namespace Erdos77.CGFresh

lemma eventual_page_exponent {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop,
      -((bookSize L k:ℝ)^2)/(6*(k:ℝ)) + (2*(k:ℝ)-(bookSize L k:ℝ))*Real.log 2 ≤
      reservoirRate L*(k:ℝ) - (Real.log 2+bookH L)*(bookSize L k:ℝ) := by
  have hh := (((bookSize_ratio h).pow 2).div_const 6).sub
    ((bookSize_ratio h).const_mul (bookH L))
  have hl : bookDeficit L+(bookSlack L)^2*Real.log 2 <
      (bookFraction L)^2/6-bookH L*bookFraction L := by linarith [h.page_gap]
  filter_upwards [hh.eventually (lt_mem_nhds hl), eventually_gt_atTop (0:ℕ)] with k hk hkp
  have hkR : (0:ℝ)<k := by exact_mod_cast hkp
  have hm := mul_lt_mul_of_pos_right hk hkR
  have he : (((bookSize L k:ℝ)/(k:ℝ))^2/6-bookH L*((bookSize L k:ℝ)/(k:ℝ)))*(k:ℝ) =
      (bookSize L k:ℝ)^2/(6*(k:ℝ))-bookH L*(bookSize L k:ℝ) := by
    field_simp
  rw [he] at hm
  have hlog : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  dsimp [reservoirRate]
  rw [hlog, neg_div]
  nlinarith

lemma eventual_page_binomial {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop,
      ((2*k-bookSize L k).choose k:ℝ) ≤
      Real.exp (-(Real.log 2+bookH L)*(bookSize L k:ℝ))*
        Real.exp (reservoirRate L*(k:ℝ)) := by
  filter_upwards [eventual_page_exponent h, bookSize_large h 3] with k hk ht
  have htN : 3 ≤ bookSize L k := by exact_mod_cast ht
  have hb := binomial_off_diagonal_gain k (bookSize L k) htN (bookSize_le h k)
  have hp : (2:ℝ)^(2*k-bookSize L k) =
      Real.exp ((2*(k:ℝ)-(bookSize L k:ℝ))*Real.log 2) := by
    rw [show 2*(k:ℝ)-(bookSize L k:ℝ) = ((2*k-bookSize L k:ℕ):ℝ) by
      rw [Nat.cast_sub (by have := bookSize_le h k; omega), Nat.cast_mul, Nat.cast_ofNat]]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [hp, ← Real.exp_add] at hb
  apply hb.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

end Erdos77.CGFresh

-- END CGProof/PageEndpoint.lean

-- BEGIN CGProof/InitialDensity.lean

open Filter Topology
namespace Erdos77.CGFresh

lemma reservoirRate_pos {L : ℝ} (h : RamseyParameters L) : 0 < reservoirRate L := by
  have hd : 0 < bookD L := by
    have hp : 0 < L := by linarith [h.large]
    have hb : 0 ≤ bookBoostCount L := by
      rw [bookBoostCount_formula]
      exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [h.large]))) (sq_nonneg L)
    have hl : 0 ≤ Real.log (1/bookSlack L) := by
      rw [log_inverse_slack]
      exact mul_nonneg (by norm_num) (Real.log_nonneg (by linarith [h.large]))
    have ha : 0 < bookA L := by
      dsimp [bookA]
      have := Real.log_nonneg (by norm_num : (1:ℝ)≤2)
      positivity
    dsimp [bookD]
    positivity
  exact (mul_pos hd h.fraction_pos).trans (reservoir_rate_gap h)

lemma eventual_density_room {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop, 1 ≤ bookSlack L * Real.exp (reservoirRate L*(k:ℝ)) := by
  have hp : 0 < L := by linarith [h.large]
  have hd : 0 < bookSlack L := by dsimp [bookSlack]; positivity
  have hh : Tendsto (fun k : ℕ => bookSlack L*Real.exp (reservoirRate L*(k:ℝ))) atTop atTop :=
    (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (reservoirRate_pos h))).const_mul_atTop hd
  exact hh.eventually (eventually_ge_atTop 1)

lemma regularized_degree_bound (δ W d : ℝ) (_hδ : 0 ≤ δ) (hroom : 1 ≤ δ*W)
    (hdegree : (1/2-δ)*W-1 ≤ d) : (1/2-2*δ)*W ≤ d := by
  nlinarith

end Erdos77.CGFresh

-- END CGProof/InitialDensity.lean

-- BEGIN CGProof/RegularizationScalars.lean

namespace Erdos77.CGFresh

lemma log_regularization_ratio {δ : ℝ} (hd : 0 < δ) (hd1 : δ ≤ 1) :
    δ/2 ≤ Real.log (1+δ) := by
  have hh := Real.le_log_one_add_of_nonneg hd.le
  apply le_trans _ hh
  apply (le_div_iff₀ (by linarith : 0<δ+2)).mpr
  nlinarith

lemma regularization_power (δ : ℝ) (hd : 0 < δ) (s : ℕ) :
    ((1+δ)/2)^s = Real.exp ((s:ℝ)*(Real.log (1+δ)-Real.log 2)) := by
  rw [Real.exp_nat_mul, Real.exp_sub, Real.exp_log (by linarith : 0<1+δ), Real.exp_log (by norm_num : (0:ℝ)<2)]

lemma regularized_small_bound {L : ℝ} (h : RamseyParameters L) (k s : ℕ) (n : ℝ)
    (hn : Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ)) ≤ n)
    (hs : (s:ℝ) ≤ (bookSlack L)^2*(k:ℝ)) :
    Real.exp (reservoirRate L*(k:ℝ)) ≤ ((1+bookSlack L)/2)^s*n := by
  have hp : 0 < L := by linarith [h.large]
  have hd : 0 < bookSlack L := by dsimp [bookSlack]; positivity
  have hlog : 0 ≤ Real.log (1+bookSlack L) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [regularization_power _ hd]
  apply le_trans _ (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hs hl2
  have hh2 := mul_nonneg (Nat.cast_nonneg s) hlog
  dsimp [reservoirRate]
  nlinarith

lemma regularized_large_bound {L : ℝ} (h : RamseyParameters L) (k s : ℕ) (n : ℝ)
    (hn : Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ)) ≤ n)
    (hs : (bookSlack L)^2*(k:ℝ) ≤ (s:ℝ)) (hs2 : s ≤ 2*k) :
    (2:ℝ)^(2*k-s) ≤ ((1+bookSlack L)/2)^s*n := by
  have hp : 0 < L := by linarith [h.large]
  have hd : 0 < bookSlack L := by dsimp [bookSlack]; positivity
  have hlog := log_regularization_ratio hd (h.slack_small.trans (by norm_num))
  have hh := mul_le_mul_of_nonneg_right hs (show 0≤bookSlack L/2 by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg s)
  have hc : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  rw [regularization_power _ hd]
  apply le_trans _ (mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le)
  rw [← Real.exp_add]
  have he : (2:ℝ)^(2*k-s) = Real.exp (((2*k-s:ℕ):ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [he]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_sub hs2, Nat.cast_mul, Nat.cast_ofNat, hc]
  dsimp [bookDeficit]
  have hn0 := mul_nonneg (pow_nonneg hd.le 3) (Nat.cast_nonneg k)
  nlinarith

end Erdos77.CGFresh

-- END CGProof/RegularizationScalars.lean

-- BEGIN CGProof/CeilingAbsorption.lean

open Filter Topology
namespace Erdos77.CGFresh

noncomputable def candidateOrder (L : ℝ) (k : ℕ) : ℕ :=
  ⌈Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ))⌉₊

lemma candidateOrder_lower (L : ℝ) (k : ℕ) :
    Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ)) ≤ (candidateOrder L k:ℝ) :=
  Nat.le_ceil _

lemma eventual_candidateOrder_upper {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop, (candidateOrder L k:ℝ) ≤
      Real.exp ((Real.log 4-bookDeficit L/2)*(k:ℝ)) := by
  have ha : 0 < Real.log 4-bookDeficit L := by
    have hl : Real.log 2 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    linarith [h.deficit_small]
  have hh : Tendsto (fun k : ℕ => Real.exp ((bookDeficit L/2)*(k:ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith [h.deficit_pos]))
  filter_upwards [hh.eventually (eventually_ge_atTop (2:ℝ))] with k hk
  have he : 1 ≤ Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ)) :=
    Real.one_le_exp (mul_nonneg ha.le (Nat.cast_nonneg k))
  have hc : (candidateOrder L k:ℝ) < Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ))+1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hm := mul_le_mul_of_nonneg_right hk (Real.exp_pos ((Real.log 4-bookDeficit L)*(k:ℝ))).le
  have hid : Real.exp ((bookDeficit L/2)*(k:ℝ))*Real.exp ((Real.log 4-bookDeficit L)*(k:ℝ)) =
      Real.exp ((Real.log 4-bookDeficit L/2)*(k:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hid] at hm
  linarith

lemma improved_base {L : ℝ} (h : RamseyParameters L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ k : ℕ,
      Real.exp ((Real.log 4-bookDeficit L/2)*(k:ℝ)) = (4-ε)^k := by
  let b := Real.exp (Real.log 4-bookDeficit L/2)
  have hb : b < 4 := by
    have hh : Real.log 4-bookDeficit L/2 < Real.log 4 := by linarith [h.deficit_pos]
    have hx := Real.exp_lt_exp.mpr hh
    rw [Real.exp_log (by norm_num : (0:ℝ)<4)] at hx
    exact hx
  refine ⟨4-b, by linarith, fun k => ?_⟩
  rw [show 4-(4-b)=b by ring, mul_comm, Real.exp_nat_mul]

end Erdos77.CGFresh

-- END CGProof/CeilingAbsorption.lean

-- BEGIN CGProof/FinalScalarBundle.lean

open Filter Topology
namespace Erdos77.CGFresh

lemma eventual_book_guards {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop, BookGuards L (bookSize L k) ∧ 3 ≤ bookSize L k := by
  filter_upwards [bookSize_large h (L^4), bookSize_large h 3] with k hk ht
  have hp : 0 < L := by linarith [h.large]
  have hδ : 0 < bookSlack L := by dsimp [bookSlack]; positivity
  have htN : 3 ≤ bookSize L k := by exact_mod_cast ht
  have hcut : L^2 ≤ (bookSize L k:ℝ) := by
    have hL2 : 1 ≤ L^2 := by nlinarith [h.large]
    nlinarith [sq_nonneg (L^2-1)]
  have hhor : L^2 ≤ bookSlack L*(bookSize L k:ℝ) := by
    dsimp [bookSlack]
    rw [one_div, inv_mul_eq_div]
    apply (le_div_iff₀ (sq_pos_of_pos hp)).mpr
    nlinarith
  exact ⟨⟨hp, by omega, hδ, h.slack_small.trans (by norm_num), hcut, hhor,
    by linarith [h.slack_small]⟩, htN⟩

theorem eventual_final_scalars {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop,
      BookGuards L (bookSize L k) ∧ 3 ≤ bookSize L k ∧ bookSize L k ≤ k ∧
      1 ≤ bookSlack L*Real.exp (reservoirRate L*(k:ℝ)) ∧
      Real.exp (bookD L*(bookSize L k:ℝ))*(2*(bookSize L k:ℝ)+1) ≤ Real.exp (reservoirRate L*(k:ℝ)) ∧
      ((2*k-bookSize L k).choose k:ℝ) ≤
        Real.exp (-(Real.log 2+bookH L)*(bookSize L k:ℝ))*Real.exp (reservoirRate L*(k:ℝ)) ∧
      (candidateOrder L k:ℝ) ≤ Real.exp ((Real.log 4-bookDeficit L/2)*(k:ℝ)) := by
  filter_upwards [eventual_book_guards h, eventual_density_room h,
    eventual_reservoir_size h, eventual_page_binomial h, eventual_candidateOrder_upper h] with k hg hr hres hpage hceil
  exact ⟨hg.1,hg.2,bookSize_le h k,hr,hres,hpage,hceil⟩

end Erdos77.CGFresh

-- END CGProof/FinalScalarBundle.lean

-- BEGIN CGProof/GraphEndpoint.lean

open Filter Topology
namespace Erdos77.CGFresh

theorem eventual_candidate_forces {L : ℝ} (h : RamseyParameters L) :
    ∀ᶠ k : ℕ in atTop, ∀ G : SimpleGraph (Fin (candidateOrder L k)), RamseyConclusion G k := by
  filter_upwards [eventual_final_scalars h] with k hk G
  classical
  rcases hk with ⟨hg, _, ht, hroom, hres, hpage, _⟩
  let n := candidateOrder L k
  let δ := bookSlack L
  obtain ⟨r⟩ := exists_regularized G δ hg.slack_pos.le Finset.univ
  have hsize : ((1+δ)/2)^((r.spine false).card+(r.spine true).card)*(n:ℝ) ≤ r.reservoir.card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using r.size
  by_cases hbig : ∃ c, k ≤ (r.spine c).card
  · obtain ⟨c,hc⟩ := hbig
    exact conclusion_of_large_spine c (r.books c) hc
  have hsmall (c : Bool) : (r.spine c).card < k := by
    by_contra hh
    exact hbig ⟨c, by omega⟩
  let s := (r.spine false).card+(r.spine true).card
  have hs : s ≤ 2*k := by have := hsmall false; have := hsmall true; omega
  by_cases hlong : δ^2*(k:ℝ) ≤ (s:ℝ)
  · have hh := (regularized_large_bound h k s (n:ℝ) (candidateOrder_lower L k) hlong hs).trans hsize
    have hn : 2^(2*k-s) ≤ r.reservoir.card := by exact_mod_cast hh
    exact regularized_long_forces r.books (fun c => (hsmall c).le) hn
  have hW : Real.exp (reservoirRate L*(k:ℝ)) ≤ r.reservoir.card :=
    (regularized_small_bound h k s (n:ℝ) (candidateOrder_lower L k) (le_of_not_ge hlong)).trans hsize
  have hWn : r.reservoir.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast lt_of_lt_of_le (Real.exp_pos _) hW
  have hroom' : 1 ≤ δ*(r.reservoir.card:ℝ) :=
    hroom.trans (mul_le_mul_of_nonneg_left hW hg.slack_pos.le)
  have hdegree (c : Bool) : 1/2-2*bookSlack L ≤ stateDensity G (initialBookState r.reservoir) c := by
    rw [stateDensity_eq G (initialBookState r.reservoir) c hWn]
    apply density_le_of_counts G c r.reservoir r.reservoir hWn hWn
    intro x hx
    exact regularized_degree_bound δ _ _ hg.slack_pos.le hroom' (r.degrees x hx c)
  have hp : ((2*k-bookSize L k).choose k:ℝ) ≤
      Real.exp (-(Real.log 2+bookH L)*(bookSize L k:ℝ))*(r.reservoir.card:ℝ) :=
    hpage.trans (mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le)
  obtain ⟨c,A,B,hbook,hA,hB⟩ := exists_large_book G r.reservoir L (bookSize L k)
    ((2*k-bookSize L k).choose k) hg (hres.trans hW) hp hdegree
  exact book_forces_clique c hbook hA ht hB

end Erdos77.CGFresh

-- END CGProof/GraphEndpoint.lean

-- BEGIN CGProof/NativeConclusion.lean

open Filter Topology
namespace Erdos77.CGFresh

theorem native_cgms_exponential_improvement :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, (diagonalRamsey k : ℝ) ≤ (4 - ε) ^ k := by
  obtain ⟨L,hL⟩ := exists_ramsey_parameters
  obtain ⟨ε,hε,hbase⟩ := improved_base hL
  refine ⟨ε,hε,?_⟩
  filter_upwards [eventual_candidate_forces hL, eventual_candidateOrder_upper hL] with k hk hupper
  have hm : candidateOrder L k ∈ {n : ℕ | ∀ G : SimpleGraph (Fin n),
      (∃ s : Finset (Fin n), G.IsNClique k s) ∨
      (∃ s : Finset (Fin n), Gᶜ.IsNClique k s)} := hk
  have hnat : diagonalRamsey k ≤ candidateOrder L k := Nat.sInf_le hm
  have hr : (diagonalRamsey k:ℝ) ≤ (candidateOrder L k:ℝ) := by exact_mod_cast hnat
  rw [← hbase k]
  exact hr.trans hupper

end Erdos77.CGFresh

-- END CGProof/NativeConclusion.lean

-- BEGIN CGProof/Canonical.lean

open Filter Topology

namespace Erdos77
theorem cgms_exponential_improvement :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, (diagonalRamsey k : ℝ) ≤ (4 - ε) ^ k := by
  exact CGFresh.native_cgms_exponential_improvement
end Erdos77

-- END CGProof/Canonical.lean

open Erdos77

theorem solution :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, (diagonalRamsey k : ℝ) ≤ (4 - ε) ^ k := by
  exact Erdos77.cgms_exponential_improvement
