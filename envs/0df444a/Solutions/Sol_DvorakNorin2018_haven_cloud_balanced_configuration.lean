-- Prove2me | solution 1 for DvorakNorin2018.haven_cloud_balanced_configuration
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-13T18:13:10.001102+00:00
-- url     : https://prove2.me/submissions/49556f46-92c7-42fd-8683-3600fa12207b

import Definitions.Def_DvorakNorin2018_HavenCloudConfiguration
import Theorems.Thm_DvorakNorin2018_cloud_separator_equivalence
import Theorems.Thm_DvorakNorin2018_tame_cloud_normalization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped Classical BigOperators
namespace StableMSR.Recovery.Havens
open TreewidthApprox.Pushed
variable {V : Type} [DecidableEq V]
lemma mem_of_walk_closed {G : SimpleGraph V} {C D : Finset V}
    (hclosed : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ D → y ∈ C)
    {u v : V} (p : G.Walk u v) (hu : u ∈ C)
    (hp : ∀ z ∈ p.support, z ∈ D) : v ∈ C := by
  induction p with
  | nil => exact hu
  | @cons u v w huv p ih =>
    apply ih (hclosed u hu v huv (hp v (by simp)))
    intro z hz
    exact hp z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr hz)

lemma flap_contains_touching {G : SimpleGraph V} {W C D : Finset V}
    (hC : IsFlap G W C) (hD : ConnectedSet G D)
    (havoid : Disjoint W D) (htouch : Touch G C D) : D ⊆ C := by
  obtain ⟨u, huD, huC⟩ : ∃ u, u ∈ D ∧ u ∈ C := by
    rcases htouch with ⟨u, huC, huD⟩ | ⟨x, hx, y, hy, hxy⟩
    · exact ⟨u, huD, huC⟩
    · exact ⟨y, hy, hC.closed x hx y hxy (fun hyW =>
        Finset.disjoint_left.mp havoid hyW hy)⟩
  intro v hv
  obtain ⟨p, hp⟩ := hD.2 u huD v hv
  exact mem_of_walk_closed (fun x hx y hxy hy =>
    hC.closed x hx y hxy (fun hyW => Finset.disjoint_left.mp havoid hyW hy)) p huC hp

/-- Dvořák–Norin Observation 3, monotonicity of a haven. -/
theorem Haven.mono {G : SimpleGraph V} {k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) {W W' : Finset V} (hW : W.card < k)
    (hW' : W'.card < k) (hsub : W ⊆ W') : β W' ⊆ β W := by
  apply flap_contains_touching (hβ.flap W hW) (hβ.flap W' hW').connected
  · exact Finset.disjoint_left.mpr (fun v hv hvβ =>
      Finset.disjoint_left.mp (hβ.flap W' hW').avoids (hsub hv) hvβ)
  · exact hβ.touch W W' hW hW'

/-- A connected set avoiding the separator lies entirely on one side. -/
lemma connected_subset_side {G : SimpleGraph V} {U L S R C : Finset V}
    (hpart : IsPartition3 U L S R) (hno : NoEdge G L R)
    (hC : ConnectedSet G C) (hsub : C ⊆ U) (havoid : Disjoint S C) :
    C ⊆ L ∨ C ⊆ R := by
  have hside : ∀ v ∈ C, v ∈ L ∨ v ∈ R := by
    intro v hv
    have hvU := hsub hv
    rw [← hpart.2.2.2] at hvU
    rcases Finset.mem_union.mp hvU with hvLS | hvR
    · rcases Finset.mem_union.mp hvLS with hvL | hvS
      · exact Or.inl hvL
      · exact False.elim (Finset.disjoint_left.mp havoid hvS hv)
    · exact Or.inr hvR
  obtain ⟨u, hu⟩ := hC.1
  rcases hside u hu with huL | huR
  · left
    intro v hv
    obtain ⟨p, hp⟩ := hC.2 u hu v hv
    apply mem_of_walk_closed (D := C) _ p huL hp
    intro x hx y hxy hy
    rcases hside y hy with hyL | hyR
    · exact hyL
    · exact False.elim (hno x hx y hyR hxy)
  · right
    intro v hv
    obtain ⟨p, hp⟩ := hC.2 u hu v hv
    apply mem_of_walk_closed (D := C) _ p huR hp
    intro x hx y hxy hy
    rcases hside y hy with hyL | hyR
    · exact False.elim (hno y hyL x hx hxy.symm)
    · exact hyR

/-- One separator step shrinks the haven's component by a factor of `2/3`
while adding at most `a` vertices to the deletion set. -/
theorem Haven.shrink_step {G : SimpleGraph V} {a k : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β)
    (hsep : HasBalancedSeparations G a) (Y : Finset V) (hY : Y.card + a < k) :
    ∃ Y', Y ⊆ Y' ∧ Y'.card ≤ Y.card + a ∧
      3 * (β Y').card ≤ 2 * (β Y).card := by
  have hYk : Y.card < k := lt_of_le_of_lt (Nat.le_add_right _ _) hY
  obtain ⟨L, S, R, hpart, hno, hScard, hL, hR⟩ := hsep (β Y)
  have hcard : (Y ∪ S).card ≤ Y.card + a :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left hScard _)
  have hYS : (Y ∪ S).card < k := hcard.trans_lt hY
  have hflap := hβ.flap (Y ∪ S) hYS
  have hsub := hβ.mono hYk hYS (Finset.subset_union_left : Y ⊆ Y ∪ S)
  have havoid : Disjoint S (β (Y ∪ S)) := Finset.disjoint_left.mpr (by
    intro v hv hvβ
    exact Finset.disjoint_left.mp hflap.avoids (Finset.mem_union_right Y hv) hvβ)
  refine ⟨Y ∪ S, Finset.subset_union_left, hcard, ?_⟩
  rcases connected_subset_side hpart hno hflap.connected hsub havoid with h | h
  · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card h)).trans hL
  · exact (Nat.mul_le_mul_left 3 (Finset.card_le_card h)).trans hR

/-- Dvořák–Norin Lemma 4, with denominators cleared over natural numbers.
This is equivalent to `|β(Y')| ≤ (2/3)^r * |β(Y)|`. -/
theorem Haven.shrink {G : SimpleGraph V} {a k : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β)
    (hsep : HasBalancedSeparations G a) (r : ℕ) (Y : Finset V)
    (hY : Y.card + a * r < k) :
    ∃ Y', Y ⊆ Y' ∧ Y'.card ≤ Y.card + a * r ∧
      3 ^ r * (β Y').card ≤ 2 ^ r * (β Y).card := by
  induction r generalizing Y with
  | zero => exact ⟨Y, Finset.Subset.refl _, by simp, by simp⟩
  | succ r ih =>
    simp only [Nat.mul_succ] at hY
    have hYa : Y.card + a < k := by omega
    obtain ⟨Y₁, hsub₁, hcard₁, hshrink₁⟩ := hβ.shrink_step hsep Y hYa
    have hY₁ : Y₁.card + a * r < k := by omega
    obtain ⟨Y₂, hsub₂, hcard₂, hshrink₂⟩ := ih Y₁ hY₁
    refine ⟨Y₂, hsub₁.trans hsub₂, by simp only [Nat.mul_succ]; omega, ?_⟩
    calc
      3 ^ (r + 1) * (β Y₂).card = 3 * (3 ^ r * (β Y₂).card) := by ring
      _ ≤ 3 * (2 ^ r * (β Y₁).card) := Nat.mul_le_mul_left 3 hshrink₂
      _ = 2 ^ r * (3 * (β Y₁).card) := by ring
      _ ≤ 2 ^ r * (2 * (β Y).card) := Nat.mul_le_mul_left _ hshrink₁
      _ = 2 ^ (r + 1) * (β Y).card := by ring

/-- Connected union implies touching, the form used in the published definition
of a haven. Thus the `Touch` interface does not strengthen that definition. -/
lemma touch_of_connected_union {G : SimpleGraph V} {C D : Finset V}
    (hC : C.Nonempty) (hD : D.Nonempty) (hCD : ConnectedSet G (C ∪ D)) :
    Touch G C D := by
  classical
  by_contra hn
  obtain ⟨u, hu⟩ := hC
  obtain ⟨v, hv⟩ := hD
  obtain ⟨p, hp⟩ := hCD.2 u (Finset.mem_union_left D hu) v (Finset.mem_union_right C hv)
  have hvC : v ∈ C := by
    apply mem_of_walk_closed (D := C ∪ D) _ p hu hp
    intro x hx y hxy hy
    rcases Finset.mem_union.mp hy with hyC | hyD
    · exact hyC
    · exact False.elim (hn (Or.inr ⟨x, hx, y, hyD, hxy⟩))
  exact hn (Or.inl ⟨v, hvC, hv⟩)

/-- Construct the haven interface directly from the paper's connected-union
condition and its component assignments. -/
theorem Haven.of_connected_unions {G : SimpleGraph V} {k : ℕ}
    {β : Finset V → Finset V}
    (hf : ∀ W, W.card < k → IsFlap G W (β W))
    (hc : ∀ W W', W.card < k → W'.card < k → ConnectedSet G (β W ∪ β W')) :
    Haven G k β where
  flap := hf
  touch W W' hW hW' := touch_of_connected_union (hf W hW).connected.1
    (hf W' hW').connected.1 (hc W W' hW hW')

/-- This lexicographic minimum exists; only well-ordering of natural numbers
is needed, even if the ambient vertex type is infinite. -/
theorem exists_minimum_cut (β : Finset V → Finset V) (m : ℕ) :
    ∃ W, IsMinimumCut β m W := by
  classical
  have hex : ∃ t : ℕ, ∃ W : Finset V, W.card ≤ m ∧ (β W).card = t :=
    ⟨(β ∅).card, ∅, by simp, rfl⟩
  obtain ⟨W₀, hW₀, hβW₀⟩ := Nat.find_spec hex
  have hex' : ∃ s : ℕ, ∃ W : Finset V,
      W.card ≤ m ∧ (β W).card = Nat.find hex ∧ W.card = s :=
    ⟨W₀.card, W₀, hW₀, hβW₀, rfl⟩
  obtain ⟨W, hW, hβW, hcardW⟩ := Nat.find_spec hex'
  refine ⟨W, hW, ?_, ?_⟩
  · intro Y hY
    rw [hβW]
    exact Nat.find_min' hex ⟨Y, hY, rfl⟩
  · intro Y hY heq
    rw [hcardW]
    exact Nat.find_min' hex' ⟨Y, hY, heq.trans hβW, rfl⟩

/-- A minimum haven component uses the entire allowed deletion budget.
This proves the cardinality assertion at the start of Dvořák–Norin Lemma7. -/
theorem Haven.minimum_cut_card {G : SimpleGraph V} {k m : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β) (hm : m < k)
    {W : Finset V} (hmin : IsMinimumCut β m W) : W.card = m := by
  classical
  by_contra hne
  have hlt : W.card < m := lt_of_le_of_ne hmin.card_le hne
  have hWk := hmin.card_le.trans_lt hm
  obtain ⟨v, hv⟩ := (hβ.flap W hWk).connected.1
  have hvW : v ∉ W := fun hvW => Finset.disjoint_left.mp (hβ.flap W hWk).avoids hvW hv
  have hinsert : (insert v W).card ≤ m := by rw [Finset.card_insert_of_notMem hvW]; omega
  have hinsK := hinsert.trans_lt hm
  have hsub : β (insert v W) ⊆ β W := hβ.mono hWk hinsK (Finset.subset_insert _ _)
  have hvnot : v ∉ β (insert v W) := fun h =>
    Finset.disjoint_left.mp (hβ.flap (insert v W) hinsK).avoids (Finset.mem_insert_self _ _) h
  have hstrict : β (insert v W) ⊂ β W := Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun heq => hvnot (heq.symm ▸ hv)⟩
  exact (not_lt_of_ge (hmin.component_min (insert v W) hinsert)) (Finset.card_lt_card hstrict)

/-- Every vertex in the lexicographically minimum deletion set has a neighbor
in its haven component (the other first-paragraph assertion of Lemma7). -/
theorem Haven.minimum_cut_boundary {G : SimpleGraph V} {k m : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β) (hm : m < k)
    {W : Finset V} (hmin : IsMinimumCut β m W) :
    ∀ w ∈ W, ∃ v ∈ β W, G.Adj w v := by
  classical
  intro w hw
  by_contra hn
  have hWk := hmin.card_le.trans_lt hm
  have herase : (W.erase w).card ≤ m := (Finset.card_le_card (Finset.erase_subset _ _)).trans hmin.card_le
  have heraseK := herase.trans_lt hm
  have hf := hβ.flap W hWk
  have hferase : IsFlap G (W.erase w) (β W) := by
    refine ⟨hf.connected, ?_, ?_⟩
    · exact Finset.disjoint_left.mpr (fun x hx hxβ =>
        Finset.disjoint_left.mp hf.avoids (Finset.mem_of_mem_erase hx) hxβ)
    · intro x hx y hxy hy
      apply hf.closed x hx y hxy
      intro hyW
      have hyw : y = w := by
        by_contra hne
        exact hy (Finset.mem_erase.mpr ⟨hne, hyW⟩)
      subst y
      exact hn ⟨x, hx, hxy.symm⟩
  have hsub₁ : β W ⊆ β (W.erase w) := hβ.mono heraseK hWk (Finset.erase_subset _ _)
  have hsub₂ : β (W.erase w) ⊆ β W :=
    flap_contains_touching hferase (hβ.flap (W.erase w) heraseK).connected
      (hβ.flap (W.erase w) heraseK).avoids (hβ.touch W (W.erase w) hWk heraseK)
  have heq : β (W.erase w) = β W := Finset.Subset.antisymm hsub₂ hsub₁
  have hmincard := hmin.cut_min (W.erase w) herase (congrArg Finset.card heq)
  exact (not_lt_of_ge hmincard) (Finset.card_erase_lt_of_mem hw)

/-- The minimum deletion set needed by Dvořák–Norin Lemma7 exists with its
full budget and all its vertices incident with the chosen component. -/
theorem Haven.exists_minimum_cut {G : SimpleGraph V} {k m : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β) (hm : m < k) :
    ∃ W, IsMinimumCut β m W ∧ W.card = m ∧ ∀ w ∈ W, ∃ v ∈ β W, G.Adj w v := by
  obtain ⟨W, hW⟩ := StableMSR.Recovery.Havens.exists_minimum_cut β m
  exact ⟨W, hW, hβ.minimum_cut_card hm hW, hβ.minimum_cut_boundary hm hW⟩

/-- Dvořák–Norin Observation 3, the orientation of a separation selected by
a haven: if one chosen component is on the left, the separator's component
is on the left as well. -/
theorem Haven.orient_separation {G : SimpleGraph V} {k : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β)
    {W U L S R : Finset V} (hW : W.card < k) (hS : S.card < k)
    (hpart : IsPartition3 U L S R) (hno : NoEdge G L R)
    (hleft : β W ⊆ L) (hcover : β S ⊆ U) : β S ⊆ L := by
  have hf := hβ.flap S hS
  rcases connected_subset_side hpart hno hf.connected hcover hf.avoids with h | h
  · exact h
  · exfalso
    rcases hβ.touch W S hW hS with ⟨v, hvW, hvS⟩ | ⟨x, hx, y, hy, hxy⟩
    · exact Finset.disjoint_left.mp hpart.2.1 (hleft hvW) (h hvS)
    · exact hno x (hleft hx) y (h hy) hxy

/-- The numerical shrinking contradiction in Dvořák–Norin Lemma7:
a deletion set of size at most `7a` cannot select a component of size at
most fifteen times the component minimized with budget `14a`. -/
theorem Haven.minimum_cut_no_small_component {G : SimpleGraph V} {a k : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β)
    (hsep : HasBalancedSeparations G a) (hk : 14 * a < k)
    {W : Finset V} (hmin : IsMinimumCut β (14 * a) W)
    {Y : Finset V} (hY : Y.card ≤ 7 * a) :
    15 * (β W).card < (β Y).card := by
  have hbudget : Y.card + a * 7 < k := by omega
  obtain ⟨Y', _, hY', hshr⟩ := hβ.shrink hsep 7 Y hbudget
  have hY'budget : Y'.card ≤ 14 * a := by omega
  have hminimal := hmin.component_min Y' hY'budget
  have hnonempty := (hβ.flap W (hmin.card_le.trans_lt hk)).connected.1.card_pos
  norm_num at hshr
  omega

/-- A direct combinatorial obstruction used before applying max-flow/min-cut
in Lemma7: no low-order separation can enclose the minimized haven component
in a side of size at most fifteen times that component. -/
theorem Haven.minimum_cut_no_small_side {G : SimpleGraph V} {a k : ℕ}
    {β : Finset V → Finset V} (hβ : Haven G k β)
    (hsep : HasBalancedSeparations G a) (hk : 14 * a < k)
    {W : Finset V} (hmin : IsMinimumCut β (14 * a) W)
    {U L S R : Finset V} (hpart : IsPartition3 U L S R) (hno : NoEdge G L R)
    (hleft : β W ⊆ L) (hcover : β S ⊆ U) (hS : S.card ≤ 7 * a) :
    15 * (β W).card < L.card := by
  have hSk : S.card < k := by omega
  have hsubset := hβ.orient_separation (hmin.card_le.trans_lt hk) hSk hpart hno hleft hcover
  exact (hβ.minimum_cut_no_small_component hsep hk hmin hS).trans_le (Finset.card_le_card hsubset)

end StableMSR.Recovery.Havens
namespace StableMSR.Recovery.Havens
open TreewidthApprox.Pushed
lemma cloud_from_separator_bounds {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (W : Finset V) (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hsep : ∀ L S R : Finset V, IsPartition3 Finset.univ L S R →
      NoEdge G L R → W ⊆ L ∪ S → s < (L.card : ℝ) + α * S.card) :
    ∃ p : TameCloud.Data V, TameCloud.Cloud G W α p ∧ s < TameCloud.total p := by
  obtain ⟨g,f,hg,hf,hgraph,hW,hcons,hbound,hvalue⟩ :=
    (DvorakNorin2018.cloud_separator_equivalence G W α s hα hs).mpr hsep
  exact ⟨(g,fun a => f a.1 a.2),⟨hg,fun a => hf a.1 a.2,hgraph,hW,hcons,hbound⟩,hvalue⟩
end StableMSR.Recovery.Havens
namespace StableMSR.Recovery.Havens
open TreewidthApprox.Pushed
/-- The actual minimum haven cut excludes every low-charge cloud obstruction. -/
theorem Haven.minimum_cut_weighted_separators {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a)
    (hk : 15*a < k) {W : Finset V} (hmin : IsMinimumCut β (14*a) W) :
    let s : ℝ := 14 * (β W).card
    let α : ℝ := s / (7*a)
    ∀ L S R : Finset V, IsPartition3 Finset.univ L S R → NoEdge (outsideGraph G (β W)) L R →
      W ⊆ L ∪ S → s < (L.card : ℝ) + α * S.card := by
  classical
  dsimp only
  intro L S R hpart hno hW
  by_contra hn
  have hc : (L.card : ℝ) + (14*(β W).card/(7*(a : ℝ))) * S.card ≤ 14*(β W).card := le_of_not_gt hn
  have hWk : W.card < k := hmin.card_le.trans_lt (by omega)
  have hflap := hβ.flap W hWk
  have hBpos : (0 : ℝ) < ((β W).card : ℝ) := by exact_mod_cast hflap.connected.1.card_pos
  have haR : (0 : ℝ) < 7 * (a : ℝ) := by have : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega); positivity
  have halpha : 0 < 14*((β W).card : ℝ)/(7*(a : ℝ)) := by positivity
  have hrel : (14*((β W).card : ℝ)/(7*(a : ℝ))) * (7*(a : ℝ)) = 14*(β W).card :=
    div_mul_cancel₀ _ (ne_of_gt haR)
  have hScard : S.card ≤ 7*a := by
    have hmul : (14*((β W).card : ℝ)/(7*(a : ℝ))) * S.card ≤
        (14*((β W).card : ℝ)/(7*(a : ℝ))) * (7*(a : ℝ)) := by
      rw [hrel]; have hLN : (0 : ℝ) ≤ (L.card : ℝ) := Nat.cast_nonneg _; linarith
    have hle : (S.card : ℝ) ≤ 7*(a : ℝ) := (mul_le_mul_iff_right₀ halpha).mp hmul
    exact_mod_cast hle
  have hLcard : L.card ≤ 14*(β W).card := by
    have hnα : 0 ≤ (14*((β W).card : ℝ)/(7*(a : ℝ))) * S.card := by positivity
    have hl : (L.card : ℝ) ≤ 14*(β W).card := by linarith
    exact_mod_cast hl
  have hRnotW : ∀ y ∈ R, y ∉ W := by
    intro y hy hyW
    rcases Finset.mem_union.mp (hW hyW) with hyL | hyS
    · exact Finset.disjoint_left.mp hpart.2.1 hyL hy
    · exact Finset.disjoint_left.mp hpart.2.2.1 hyS hy
  have hp' : IsPartition3 Finset.univ (L ∪ β W) (S \ β W) (R \ β W) := by
    refine ⟨Finset.disjoint_left.mpr ?_,Finset.disjoint_left.mpr ?_,Finset.disjoint_left.mpr ?_,?_⟩
    · intro v hv hs
      obtain ⟨hs,hn⟩ := Finset.mem_sdiff.mp hs
      rcases Finset.mem_union.mp hv with hl | hb
      · exact Finset.disjoint_left.mp hpart.1 hl hs
      · exact hn hb
    · intro v hv hr
      obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hr
      rcases Finset.mem_union.mp hv with hl | hb
      · exact Finset.disjoint_left.mp hpart.2.1 hl hr
      · exact hn hb
    · intro v hs hr
      exact Finset.disjoint_left.mp hpart.2.2.1 (Finset.mem_sdiff.mp hs).1 (Finset.mem_sdiff.mp hr).1
    · ext v
      have hu : v ∈ L ∪ S ∪ R := by rw [hpart.2.2.2]; exact Finset.mem_univ v
      simp only [Finset.mem_union] at hu
      simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ]
      tauto
  have hn' : NoEdge G (L ∪ β W) (R \ β W) := by
    intro x hx y hy hxy
    obtain ⟨hyR,hyB⟩ := Finset.mem_sdiff.mp hy
    rcases Finset.mem_union.mp hx with hxL | hxB
    · by_cases hxB : x ∈ β W
      · exact hyB (hflap.closed x hxB y hxy (hRnotW y hyR))
      · exact hno x hxL y hyR ⟨hxy,hxB,hyB⟩
    · exact hyB (hflap.closed x hxB y hxy (hRnotW y hyR))
  have hbound := hβ.minimum_cut_no_small_side hsep (by omega) hmin hp' hn'
    (Finset.subset_union_right) (Finset.subset_univ _) ((Finset.card_le_card (Finset.sdiff_subset : S \ β W ⊆ S)).trans hScard)
  have hcL := Finset.card_union_le L (β W)
  omega

/-- The cloud construction in Lemma 7(a), before restricting to active vertices. -/
theorem Haven.minimum_cut_large_tame_cloud {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) (hk : 15*a < k) :
    ∃ W : Finset V, IsMinimumCut β (14*a) W ∧ W.card = 14*a ∧
      (∀ w ∈ W, ∃ v ∈ β W, G.Adj w v) ∧
      ∃ p : TameCloud.Data V,
        TameCloud.Cloud (outsideGraph G (β W)) W (14*(β W).card/(7*(a : ℝ))) p ∧
        TameCloud.Tame W (14*(β W).card/(7*(a : ℝ))) p ∧
        14*((β W).card : ℝ) < TameCloud.total p := by
  classical
  obtain ⟨W,hmin,hcard,hboundary⟩ := hβ.exists_minimum_cut (m := 14*a) (by omega)
  have hf := hβ.flap W (hmin.card_le.trans_lt (by omega))
  have hb : (0 : ℝ) < ((β W).card : ℝ) := by exact_mod_cast hf.connected.1.card_pos
  have har : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr (by omega)
  have hα : 0 < 14*((β W).card : ℝ)/(7*(a : ℝ)) := by positivity
  obtain ⟨p,hp,hps⟩ := cloud_from_separator_bounds (outsideGraph G (β W)) W
    (14*(β W).card/(7*(a : ℝ))) (14*(β W).card) hα.le (by positivity)
    (hβ.minimum_cut_weighted_separators hsep ha hk hmin)
  obtain ⟨q,hq,htame,ht⟩ := DvorakNorin2018.tame_cloud_normalization (outsideGraph G (β W)) W
    (14*(β W).card/(7*(a : ℝ))) (TameCloud.total p) hα (lt_trans (by positivity) hps) p hp rfl
  exact ⟨W,hmin,hcard,hboundary,q,hq,htame,ht.symm ▸ hps⟩

lemma partition_swap {V : Type} [Fintype V] [DecidableEq V] {U L S R : Finset V}
    (h : IsPartition3 U L S R) : IsPartition3 U R S L := by
  refine ⟨h.2.2.1.symm,h.2.1.symm,h.1.symm,?_⟩
  rw [← h.2.2.2]; ext v; simp only [Finset.mem_union]; tauto

/-- A haven-oriented balanced separation has the required boundary bound. -/
theorem Haven.oriented_boundary_bound {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hk : 15*a < k)
    {W X L S R : Finset V} (hmin : IsMinimumCut β (14*a) W)
    (hX : Disjoint X (β W)) (hWX : W ⊆ X)
    (hpart : IsPartition3 (X ∪ β W) L S R) (hno : NoEdge G L R) (hS : S.card ≤ a)
    (horient : β (W ∪ (S ∩ β W)) ⊆ R) :
    ((L ∩ W) ∪ (S ∩ X)).card ≤ a := by
  classical
  have hWk : W.card < k := hmin.card_le.trans_lt (by omega)
  have hf := hβ.flap W hWk
  have hWcard := hβ.minimum_cut_card (by omega : 14*a < k) hmin
  have hWboundary := hβ.minimum_cut_boundary (by omega : 14*a < k) hmin
  by_cases hBR : β W ⊆ R
  · have hLW : L ∩ W = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hwL,hwW⟩ := Finset.mem_inter.mp hw
      obtain ⟨v,hv,hAdj⟩ := hWboundary w hwW
      exact hno w hwL v (hBR hv) hAdj
    rw [hLW,Finset.empty_union]
    exact (Finset.card_le_card Finset.inter_subset_left).trans hS
  · let D := W ∪ (S ∩ β W)
    let Y := D \ L
    have hDcard : D.card ≤ 15*a := by
      change (W ∪ (S ∩ β W)).card ≤ 15*a
      have h₁ := Finset.card_union_le W (S ∩ β W)
      have h₂ := Finset.card_le_card (Finset.inter_subset_left : S ∩ β W ⊆ S)
      omega
    have hDk : D.card < k := hDcard.trans_lt hk
    have hYcard : Y.card ≤ D.card := Finset.card_le_card Finset.sdiff_subset
    have hYk : Y.card < k := hYcard.trans_lt hDk
    have hBD : β D ⊆ β W := hβ.mono hWk hDk Finset.subset_union_left
    have hDY : β D ⊆ β Y := hβ.mono hYk hDk Finset.sdiff_subset
    have hflapY : IsFlap G Y (β D) := by
      refine ⟨(hβ.flap D hDk).connected,?_,?_⟩
      · exact Finset.disjoint_left.mpr (fun v hv hb =>
          Finset.disjoint_left.mp (hβ.flap D hDk).avoids (Finset.mem_sdiff.mp hv).1 hb)
      · intro x hx y hxy hy
        apply (hβ.flap D hDk).closed x hx y hxy
        intro hyD
        have hyL : y ∈ L := by
          by_contra hn
          exact hy (Finset.mem_sdiff.mpr ⟨hyD,hn⟩)
        exact hno y hyL x (horient hx) hxy.symm
    have hYD : β Y ⊆ β D := flap_contains_touching hflapY (hβ.flap Y hYk).connected
      (hβ.flap Y hYk).avoids (hβ.touch D Y hDk hYk)
    have heq : β Y = β D := Finset.Subset.antisymm hYD hDY
    have hproper : β D ⊂ β W := Finset.ssubset_iff_subset_ne.mpr
      ⟨hBD,fun he => hBR (he ▸ horient)⟩
    have hsmall : (β Y).card < (β W).card := by rw [heq]; exact Finset.card_lt_card hproper
    have hYbig : 14*a < Y.card := by
      by_contra hn
      have hh := hmin.component_min Y (le_of_not_gt hn)
      omega
    have hLS : Disjoint (L ∩ W) (S ∩ X) := Finset.disjoint_left.mpr (by
      intro v hv hv'; exact Finset.disjoint_left.mp hpart.1 (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hv').1)
    have hSB : Disjoint (W \ L) (S ∩ β W) := Finset.disjoint_left.mpr (by
      intro v hv hv'; exact Finset.disjoint_left.mp hf.avoids (Finset.mem_sdiff.mp hv).1 (Finset.mem_inter.mp hv').2)
    have hYeq : Y = (W \ L) ∪ (S ∩ β W) := by
      ext v
      have hnot : v ∈ S → v ∉ L := fun hv => fun hl => Finset.disjoint_left.mp hpart.1 hl hv
      simp only [Y,D,Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
      tauto
    have hXSB : Disjoint (S ∩ X) (S ∩ β W) := Finset.disjoint_left.mpr (by
      intro v hv hv'; exact Finset.disjoint_left.mp hX (Finset.mem_inter.mp hv).2 (Finset.mem_inter.mp hv').2)
    have hScount : (S ∩ X).card + (S ∩ β W).card ≤ S.card := by
      rw [← Finset.card_union_of_disjoint hXSB]
      exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    have hWcount := Finset.card_inter_add_card_sdiff W L
    have htarget := Finset.card_union_of_disjoint hLS
    have hYcount : Y.card = (W \ L).card + (S ∩ β W).card := by
      rw [hYeq,Finset.card_union_of_disjoint hSB]
    have hcomm : (W ∩ L).card = (L ∩ W).card := by rw [Finset.inter_comm]
    omega

/-- The balanced-separation conclusion of Lemma 7(b), before naming the subgraph. -/
theorem Haven.minimum_cut_balanced_boundary {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (hk : 15*a < k)
    {W X : Finset V} (hmin : IsMinimumCut β (14*a) W)
    (hX : Disjoint X (β W)) (hWX : W ⊆ X) :
    ∃ L S R : Finset V, IsPartition3 (X ∪ β W) L S R ∧ NoEdge G L R ∧
      S.card ≤ a ∧ 3*L.card ≤ 2*(X ∪ β W).card ∧
      3*R.card ≤ 2*(X ∪ β W).card ∧ ((L ∩ W) ∪ (S ∩ X)).card ≤ a := by
  classical
  obtain ⟨L,S,R,hp,hn,hS,hL,hR⟩ := hsep (X ∪ β W)
  let D := W ∪ (S ∩ β W)
  have hWk : W.card < k := hmin.card_le.trans_lt (by omega)
  have hDcard : D.card ≤ 15*a := by
    change (W ∪ (S ∩ β W)).card ≤ 15*a
    have h₁ := Finset.card_union_le W (S ∩ β W)
    have h₂ := Finset.card_le_card (Finset.inter_subset_left : S ∩ β W ⊆ S)
    have h₃ := hmin.card_le
    omega
  have hDk : D.card < k := hDcard.trans_lt hk
  have hsub : β D ⊆ β W := hβ.mono hWk hDk Finset.subset_union_left
  have havoid : Disjoint S (β D) := Finset.disjoint_left.mpr (by
    intro v hv hb
    exact Finset.disjoint_left.mp (hβ.flap D hDk).avoids
      (Finset.mem_union_right W (Finset.mem_inter.mpr ⟨hv,hsub hb⟩)) hb)
  have hcover : β D ⊆ X ∪ β W := hsub.trans Finset.subset_union_right
  rcases connected_subset_side hp hn (hβ.flap D hDk).connected hcover havoid with hleft | hright
  · refine ⟨R,S,L,partition_swap hp,?_,hS,hR,hL,?_⟩
    · intro x hx y hy h; exact hn y hy x hx h.symm
    · exact hβ.oriented_boundary_bound hk hmin hX hWX (partition_swap hp)
        (fun x hx y hy h => hn y hy x hx h.symm) hS hleft
  · exact ⟨L,S,R,hp,hn,hS,hL,hR,hβ.oriented_boundary_bound hk hmin hX hWX hp hn hS hright⟩

lemma sinks_active {V : Type} [Fintype V] {G : SimpleGraph V} {W : Finset V}
    {α : ℝ} {p : TameCloud.Data V} (hp : TameCloud.Cloud G W α p) : W ⊆ activeVertices W p := by
  classical
  intro v hv
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  by_cases he : p.1 v = 1
  · exact Or.inl he
  · exact Or.inr ⟨lt_of_le_of_ne (hp.supply v).2 he,Or.inr hv⟩

lemma inactive_zero {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {W : Finset V}
    {α : ℝ} {p : TameCloud.Data V} (hp : TameCloud.Cloud G W α p)
    {v : V} (hv : v ∉ activeVertices W p) :
    p.1 v = 0 ∧ (∀ u, p.2 (u,v) = 0) ∧ ∀ u, p.2 (v,u) = 0 := by
  classical
  have hn : ¬ (p.1 v = 1 ∨ TameCloud.Hungry W p v) := by
    intro h; exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have hlt : p.1 v < 1 := lt_of_le_of_ne (hp.supply v).2 (fun he => hn (Or.inl he))
  have hvW : v ∉ W := fun h => hn (Or.inr ⟨hlt,Or.inr h⟩)
  have hc0 : TameCloud.congestion p v ≤ 0 := le_of_not_gt (fun h => hn (Or.inr ⟨hlt,Or.inl h⟩))
  have hinc : 0 ≤ TameCloud.incoming p v := Finset.sum_nonneg (fun u _ => hp.flow (u,v))
  have hg0 := (hp.supply v).1
  have hc : TameCloud.congestion p v = 0 := by dsimp [TameCloud.congestion] at *; linarith
  have hg : p.1 v = 0 := by dsimp [TameCloud.congestion] at hc; linarith
  have hin : TameCloud.incoming p v = 0 := by dsimp [TameCloud.congestion] at hc; linarith
  refine ⟨hg,?_,?_⟩
  · intro u
    have hle : p.2 (u,v) ≤ TameCloud.incoming p v := Finset.single_le_sum
      (fun x _ => hp.flow (x,v)) (Finset.mem_univ u)
    rw [hin] at hle
    exact le_antisymm hle (hp.flow (u,v))
  · intro u
    have hout : (∑ x, p.2 (v,x)) = 0 := (hp.conserve v hvW).symm.trans hc
    have hle := Finset.single_le_sum (fun x _ => hp.flow (v,x)) (Finset.mem_univ u)
    rw [hout] at hle
    exact le_antisymm hle (hp.flow (v,u))

lemma active_avoids_deleted {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {W B : Finset V} {α : ℝ} {p : TameCloud.Data V}
    (hWB : Disjoint W B) (hp : TameCloud.Cloud (outsideGraph G B) W α p) :
    Disjoint (activeVertices W p) B := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hvB
  have hW : v ∉ W := fun h => Finset.disjoint_left.mp hWB h hvB
  have hflowin : ∀ u, p.2 (u,v) = 0 := fun u => hp.support u v (fun h => h.2.2 hvB)
  have hflowout : ∀ u, p.2 (v,u) = 0 := fun u => hp.support v u (fun h => h.2.1 hvB)
  have hc : TameCloud.congestion p v = 0 := by rw [hp.conserve v hW]; simp [hflowout]
  have hg : p.1 v = 0 := by
    have hin : TameCloud.incoming p v = 0 := by simp [TameCloud.incoming,hflowin]
    dsimp [TameCloud.congestion] at hc; rw [hin] at hc; simpa using hc
  obtain ⟨_,hactive⟩ := Finset.mem_filter.mp hv
  rcases hactive with hsat | hh
  · rw [hg] at hsat; exact zero_ne_one hsat
  · rcases hh.2 with hpos | hmem
    · rw [hc] at hpos; exact (lt_irrefl 0) hpos
    · exact hW hmem

lemma Haven.configuration_separation {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {k : ℕ} {β : Finset V → Finset V} (hβ : Haven G k β)
    {W X : Finset V} (hW : W.card < k) (hWX : W ⊆ X) (hXB : Disjoint X (β W)) :
    X ∩ (W ∪ β W) = W ∧ (W ∪ β W) \ W = β W ∧
      IsPartition3 (X ∪ β W) (X \ W) W (β W) ∧ NoEdge G (X \ W) (β W) := by
  classical
  have hf := hβ.flap W hW
  have hWB := hf.avoids
  refine ⟨?_,?_,?_,?_⟩
  · ext v
    have hx := fun (hvX : v ∈ X) (hvB : v ∈ β W) => Finset.disjoint_left.mp hXB hvX hvB
    have hw := fun (hvW : v ∈ W) => hWX hvW
    simp only [Finset.mem_inter,Finset.mem_union]
    tauto
  · ext v
    have hh := fun (hvW : v ∈ W) (hvB : v ∈ β W) => Finset.disjoint_left.mp hWB hvW hvB
    simp only [Finset.mem_sdiff,Finset.mem_union]
    tauto
  · refine ⟨Finset.disjoint_left.mpr ?_,Finset.disjoint_left.mpr ?_,hWB,?_⟩
    · intro v hv hw; exact (Finset.mem_sdiff.mp hv).2 hw
    · intro v hv hb; exact Finset.disjoint_left.mp hXB (Finset.mem_sdiff.mp hv).1 hb
    · ext v
      have hw := fun (hvW : v ∈ W) => hWX hvW
      simp only [Finset.mem_union,Finset.mem_sdiff]
      tauto
  · intro x hx y hy hxy
    obtain ⟨hxX,hxW⟩ := Finset.mem_sdiff.mp hx
    exact Finset.disjoint_left.mp hXB hxX (hf.closed y hy x hxy.symm hxW)

/-- The complete haven-based configuration in Lemma 7: its large tame cloud,
active support and special balanced-separator bound, in ambient vertex notation. -/
theorem Haven.large_tame_balanced_configuration {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) (hk : 15*a < k) :
    ∃ (W X : Finset V) (p : TameCloud.Data V), IsMinimumCut β (14*a) W ∧
      W.card = 14*a ∧ W ⊆ X ∧ Disjoint X (β W) ∧ X = activeVertices W p ∧
      X ∩ (W ∪ β W) = W ∧ (W ∪ β W) \ W = β W ∧
      IsPartition3 (X ∪ β W) (X \ W) W (β W) ∧ NoEdge G (X \ W) (β W) ∧
      TameCloud.Cloud (outsideGraph G (β W)) W (14*(β W).card/(7*(a : ℝ))) p ∧
      TameCloud.Tame W (14*(β W).card/(7*(a : ℝ))) p ∧
      14*((β W).card : ℝ) < TameCloud.total p ∧
      (∀ v ∉ X, p.1 v = 0 ∧ (∀ u, p.2 (u,v) = 0) ∧ ∀ u, p.2 (v,u) = 0) ∧
      ∃ L S R : Finset V, IsPartition3 (X ∪ β W) L S R ∧ NoEdge G L R ∧
        S.card ≤ a ∧ 3*L.card ≤ 2*(X ∪ β W).card ∧
        3*R.card ≤ 2*(X ∪ β W).card ∧ ((L ∩ W) ∪ (S ∩ X)).card ≤ a := by
  classical
  obtain ⟨W,hmin,hcard,_,p,hp,htame,hsupply⟩ := hβ.minimum_cut_large_tame_cloud hsep ha hk
  have hWB := (hβ.flap W (hmin.card_le.trans_lt (by omega))).avoids
  let X := activeVertices W p
  have hWX : W ⊆ X := sinks_active hp
  have hXB : Disjoint X (β W) := active_avoids_deleted hWB hp
  obtain ⟨hi,hz,hpart,hno⟩ := hβ.configuration_separation
    (hmin.card_le.trans_lt (by omega)) hWX hXB
  refine ⟨W,X,p,hmin,hcard,hWX,hXB,rfl,hi,hz,hpart,hno,hp,htame,hsupply,?_,?_⟩
  · intro v hv; exact inactive_zero hp hv
  · exact hβ.minimum_cut_balanced_boundary hsep hk hmin hXB hWX
end StableMSR.Recovery.Havens

open TreewidthApprox.Pushed StableMSR.Recovery StableMSR.Recovery.Havens
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a k : ℕ} {β : Finset V → Finset V}
    (hβ : Haven G k β) (hsep : HasBalancedSeparations G a) (ha : 1 ≤ a) (hk : 15*a < k) :
    ∃ (W X : Finset V) (p : TameCloud.Data V), IsMinimumCut β (14*a) W ∧
      W.card = 14*a ∧ W ⊆ X ∧ Disjoint X (β W) ∧ X = activeVertices W p ∧
      X ∩ (W ∪ β W) = W ∧ (W ∪ β W) \ W = β W ∧
      IsPartition3 (X ∪ β W) (X \ W) W (β W) ∧ NoEdge G (X \ W) (β W) ∧
      TameCloud.Cloud (outsideGraph G (β W)) W (14*(β W).card/(7*(a : ℝ))) p ∧
      TameCloud.Tame W (14*(β W).card/(7*(a : ℝ))) p ∧
      14*((β W).card : ℝ) < TameCloud.total p ∧
      (∀ v ∉ X, p.1 v = 0 ∧ (∀ u, p.2 (u,v) = 0) ∧ ∀ u, p.2 (v,u) = 0) ∧
      ∃ L S R : Finset V, IsPartition3 (X ∪ β W) L S R ∧ NoEdge G L R ∧
        S.card ≤ a ∧ 3*L.card ≤ 2*(X ∪ β W).card ∧
        3*R.card ≤ 2*(X ∪ β W).card ∧ ((L ∩ W) ∪ (S ∩ X)).card ≤ a := by
  exact hβ.large_tame_balanced_configuration hsep ha hk
