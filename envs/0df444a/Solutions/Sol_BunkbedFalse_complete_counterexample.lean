-- Prove2me | solution 1 for BunkbedFalse.complete_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-10-01T01:01:23.494673+00:00
-- url     : https://prove2.me/submissions/39b12fcf-ff49-4ae7-9ea9-b9e373e8963b

import Definitions.Def_BunkbedComplete
import Definitions.Def_BunkbedSubstituted
import Theorems.Thm_BunkbedFalse_sub_invariants
import Theorems.Thm_BunkbedAux_sum_weight_eq_one
import Theorems.Thm_BunkbedFalse_simulation
import Theorems.Thm_BunkbedFalse_robust_hyperedge
import Theorems.Thm_BunkbedFalse_gadget_eq1_at_half
import Theorems.Thm_BunkbedAux_partition_sum_eq_total
import Theorems.Thm_BunkbedAux_probOf_mem_unitInterval

/-!
# Theorem 6.1: a counterexample to the complete bunkbed conjecture

Source: Gladkov–Pak–Zimin (2025), Section 6, pp. 9.
We use the same pendant construction, with 216630 leaves at each of the three
original posts. The resulting graph has 657112 vertices and at most 664332 edges.
The larger choice replaces the paper's decimal gap estimate by the exact lower
bound on a nonzero fair-percolation gap: one configuration has mass 2^(-28884).
All new arguments below are proved in Lean; the imports are previously proved
mission lemmas supplying the original counterexample's gadget probabilities.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace BunkbedCompleteSupport
open Finset SimpleGraph Bunkbed
variable {V : Type*} [Fintype V] [DecidableEq V]

def switchVtx (U : Finset V) (q : V × Fin 2) : V × Fin 2 :=
  if q.1 ∈ U then (q.1, 1 - q.2) else q

theorem switchVtx_involutive (U : Finset V) :
    Function.Involutive (switchVtx U : V × Fin 2 → V × Fin 2) := by
  have hfin : ∀ i : Fin 2, (1 : Fin 2) - (1 - i) = i := by decide
  intro q
  by_cases h : q.1 ∈ U
  · have h1 : switchVtx U q = (q.1, 1 - q.2) := by unfold switchVtx; rw [if_pos h]
    rw [h1]
    unfold switchVtx
    rw [if_pos (show ((q.1, 1 - q.2) : V × Fin 2).1 ∈ U from h)]
    simp [hfin]
  · have h1 : switchVtx U q = q := by unfold switchVtx; rw [if_neg h]
    rw [h1, h1]

theorem reach_map_of_adj_reach {W W' : Type*} (G : SimpleGraph W) (G' : SimpleGraph W')
    (f : W → W') (h : ∀ a b, G.Adj a b → G'.Reachable (f a) (f b))
    {x y : W} (hxy : G.Reachable x y) : G'.Reachable (f x) (f y) := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem reach_of_adj_reach (G₁ G₂ : SimpleGraph W)
    (h : ∀ a b, G₁.Adj a b → G₂.Reachable a b) {x y : W} (hxy : G₁.Reachable x y) :
    G₂.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih => exact (h _ _ hadj).trans ih

theorem ofEdges_mono {B C : Finset (Sym2 W)} (h : B ⊆ C) : ofEdges B ≤ ofEdges C := by
  intro a b hab
  rw [ofEdges, fromEdgeSet_adj] at hab ⊢
  exact ⟨h hab.1, hab.2⟩

theorem sum_powerset_union {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    {E F : Finset α} (hEF : Disjoint E F) (f : Finset α → M) :
    ∑ SE ∈ E.powerset, ∑ SF ∈ F.powerset, f (SE ∪ SF) = ∑ S ∈ (E ∪ F).powerset, f S := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => p.1 ∪ p.2) (fun S => (S ∩ E, S ∩ F)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [mem_product, mem_powerset] at hp
    exact mem_powerset.2 (union_subset_union hp.1 hp.2)
  · intro S hS
    simp only [mem_powerset] at hS
    exact mem_product.2 ⟨mem_powerset.2 inter_subset_right, mem_powerset.2 inter_subset_right⟩
  · rintro ⟨a, b⟩ hp
    simp only [mem_product, mem_powerset] at hp
    have hEF' := Finset.disjoint_left.1 hEF
    refine Prod.ext ?_ ?_
    · ext e
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hu | hu, hE⟩
        · exact hu
        · exact absurd (hp.2 hu) (hEF' hE)
      · intro he; exact ⟨Or.inl he, hp.1 he⟩
    · ext e
      simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hu | hu, hF⟩
        · exact absurd hF (hEF' (hp.1 hu))
        · exact hu
      · intro he; exact ⟨Or.inr he, hp.2 he⟩
  · intro S hS
    simp only [mem_powerset] at hS
    ext e; simp only [mem_union, mem_inter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h; rcases mem_union.1 (hS h) with h' | h'
      exacts [Or.inl ⟨h, h'⟩, Or.inr ⟨h, h'⟩]
  · intro p _; rfl

theorem weight_union {EG EH : Finset (Sym2 V)} (hEF : Disjoint EG EH) (w : Sym2 V → ℚ)
    {SG SH : Finset (Sym2 V)} (hSG : SG ⊆ EG) (hSH : SH ⊆ EH) :
    weight (EG ∪ EH) w (SG ∪ SH) = weight EG w SG * weight EH w SH := by
  classical
  have hdisj : Disjoint SG SH :=
    Finset.disjoint_of_subset_left hSG (Finset.disjoint_of_subset_right hSH hEF)
  have hL := Finset.disjoint_left.1 hEF
  have hsd : (EG ∪ EH) \ (SG ∪ SH) = (EG \ SG) ∪ (EH \ SH) := by
    ext e; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hEu, hSu⟩
      rcases hEu with h | h
      · exact Or.inl ⟨h, fun hc => hSu (Or.inl hc)⟩
      · exact Or.inr ⟨h, fun hc => hSu (Or.inr hc)⟩
    · rintro (⟨h, hn⟩ | ⟨h, hn⟩)
      · exact ⟨Or.inl h, by rintro (hc | hc); exacts [hn hc, hL h (hSH hc)]⟩
      · exact ⟨Or.inr h, by rintro (hc | hc); exacts [hL (hSG hc) h, hn hc]⟩
  have hdisj' : Disjoint (EG \ SG) (EH \ SH) :=
    Finset.disjoint_of_subset_left sdiff_subset
      (Finset.disjoint_of_subset_right sdiff_subset hEF)
  rw [weight, weight, weight, Finset.prod_union hdisj, hsd, Finset.prod_union hdisj']
  ring

end BunkbedCompleteSupport


namespace Bunkbed.Complete
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma weight_half {E S : Finset (Sym2 V)} (hS : S ⊆ E) :
    weight E (fun _ => (1 / 2 : ℚ)) S = (1 / 2 : ℚ) ^ E.card := by
  unfold weight
  norm_num only [show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num,
    Finset.prod_const, ← pow_add]
  rw [Finset.card_sdiff_of_subset hS, Nat.add_sub_of_le (Finset.card_le_card hS)]

/-- At fair percolation the bunkbed probability counts pairs of edge subsets. -/
lemma bbProb_half_count (E : Finset (Sym2 V)) (T : Finset V) (x y : V × Fin 2) :
    bbProb E (fun _ => (1 / 2 : ℚ)) T x y =
      (((E.powerset ×ˢ E.powerset).filter
        (fun S => (bbGraph T S.1 S.2).Reachable x y)).card : ℚ) *
        (1 / 2 : ℚ) ^ (2 * E.card) := by
  unfold bbProb
  rw [← Finset.sum_boole, Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S₀ h₀ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun S₁ h₁ => ?_
  rw [weight_half (Finset.mem_powerset.1 h₀), weight_half (Finset.mem_powerset.1 h₁)]
  rw [show 2 * E.card = E.card + E.card by omega, pow_add]
  ring

/-- A strict gap in a finite fair bunkbed model is at least one configuration's mass. -/
lemma bbProb_half_gap {E : Finset (Sym2 V)} {T : Finset V} {x y z : V × Fin 2}
    (h : bbProb E (fun _ => (1 / 2 : ℚ)) T x y <
      bbProb E (fun _ => (1 / 2 : ℚ)) T x z) :
    bbProb E (fun _ => (1 / 2 : ℚ)) T x y -
      bbProb E (fun _ => (1 / 2 : ℚ)) T x z ≤ -(1 / 2 : ℚ) ^ (2 * E.card) := by
  rw [bbProb_half_count, bbProb_half_count] at h ⊢
  have hp : 0 < (1 / 2 : ℚ) ^ (2 * E.card) := pow_pos (by norm_num) _
  have hc := (mul_lt_mul_iff_left₀ hp).1 h
  have hn : ((E.powerset ×ˢ E.powerset).filter
      (fun S => (bbGraph T S.1 S.2).Reachable x y)).card + 1 ≤
      ((E.powerset ×ˢ E.powerset).filter
      (fun S => (bbGraph T S.1 S.2).Reachable x z)).card := by exact_mod_cast hc
  have hq : ((((E.powerset ×ˢ E.powerset).filter
      (fun S => (bbGraph T S.1 S.2).Reachable x y)).card : ℚ) + 1) ≤
      (((E.powerset ×ˢ E.powerset).filter
      (fun S => (bbGraph T S.1 S.2).Reachable x z)).card : ℚ) := by exact_mod_cast hn
  nlinarith

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exchange the two configurations on a selected set of base edges. -/
def exchange (A S R : Finset (Sym2 V)) : Finset (Sym2 V) := (S \ A) ∪ (R ∩ A)

lemma mem_exchange {A S R : Finset (Sym2 V)} {e : Sym2 V} :
    e ∈ exchange A S R ↔ (e ∈ S ∧ e ∉ A) ∨ (e ∈ R ∧ e ∈ A) := by
  simp [exchange]

lemma exchange_twice (A S R : Finset (Sym2 V)) :
    exchange A (exchange A S R) (exchange A R S) = S := by
  ext e; simp only [mem_exchange]; tauto

lemma exchange_subset {A E S R : Finset (Sym2 V)} (hS : S ⊆ E) (hR : R ⊆ E) :
    exchange A S R ⊆ E := by
  intro e he; rcases mem_exchange.1 he with h | h
  exacts [hS h.1, hR h.1]

lemma bb_horizontal {T : Finset V} {S R : Finset (Sym2 V)} {a b : V}
    (h : s(a,b) ∈ S) : (bbGraph T S R).Reachable (a,0) (b,0) := by
  by_cases hab : a = b
  · subst b; rfl
  · apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).2
    refine ⟨Finset.mem_union_left _ (Finset.mem_union_left _ ?_), ?_⟩
    · exact Finset.mem_image_of_mem (liftLvl 0) h
    · simpa using hab

lemma bb_horizontal' {T : Finset V} {S R : Finset (Sym2 V)} {a b : V}
    (h : s(a,b) ∈ R) : (bbGraph T S R).Reachable (a,1) (b,1) := by
  by_cases hab : a = b
  · subst b; rfl
  · apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).2
    refine ⟨Finset.mem_union_left _ (Finset.mem_union_right _ ?_), ?_⟩
    · exact Finset.mem_image_of_mem (liftLvl 1) h
    · simpa using hab

lemma bb_post {T : Finset V} {S R : Finset (Sym2 V)} {a : V}
    (h : a ∈ T) (i j : Fin 2) : (bbGraph T S R).Reachable (a,i) (a,j) := by
  have hp : (bbGraph T S R).Reachable (a,0) (a,1) := by
    apply SimpleGraph.Adj.reachable
    apply (SimpleGraph.fromEdgeSet_adj _).2
    exact ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem _ h), by simp⟩
  fin_cases i <;> fin_cases j
  · rfl
  · exact hp
  · exact hp.symm
  · rfl

/-- Edges meeting the region whose layers are exchanged. -/
def touching (E : Finset (Sym2 V)) (U : Finset V) : Finset (Sym2 V) :=
  E.filter (fun e => ∃ a ∈ e, a ∈ U)

lemma touching_pair {E : Finset (Sym2 V)} {U : Finset V} {a b : V}
    (he : s(a,b) ∈ E) : s(a,b) ∈ touching E U ↔ a ∈ U ∨ b ∈ U := by
  simp [touching, he]

lemma switch_horizontal {E S R : Finset (Sym2 V)} {T U : Finset V}
    (hcut : ∀ a ∈ U, ∀ b, s(a,b) ∈ E → b ∉ U → b ∈ T)
    (hS : S ⊆ E) {a b : V} (he : s(a,b) ∈ S) :
    (bbGraph T (exchange (touching E U) S R) (exchange (touching E U) R S)).Reachable
      (switchVtx U (a,0)) (switchVtx U (b,0)) := by
  have hE := hS he
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
  · simp only [switchVtx, ha, hb, ↓reduceIte, show (1 : Fin 2) - 0 = 1 from rfl]
    apply bb_horizontal'
    exact mem_exchange.2 (Or.inr ⟨he, (touching_pair hE).2 (Or.inl ha)⟩)
  · simp only [switchVtx, ha, hb, ↓reduceIte, show (1 : Fin 2) - 0 = 1 from rfl]
    exact (bb_horizontal' (mem_exchange.2 (Or.inr
      ⟨he, (touching_pair hE).2 (Or.inl ha)⟩))).trans (bb_post (hcut a ha b hE hb) 1 0)
  · simp only [switchVtx, ha, hb, ↓reduceIte, show (1 : Fin 2) - 0 = 1 from rfl]
    have hat : a ∈ T := hcut b hb a (by simpa [Sym2.eq_swap] using hE) ha
    exact (bb_post hat 0 1).trans (bb_horizontal'
      (mem_exchange.2 (Or.inr ⟨he, (touching_pair hE).2 (Or.inr hb)⟩)))
  · simp only [switchVtx, ha, hb, ↓reduceIte]
    exact bb_horizontal (mem_exchange.2 (Or.inl ⟨he, by simpa [touching_pair hE] using And.intro ha hb⟩))

lemma switch_horizontal' {E S R : Finset (Sym2 V)} {T U : Finset V}
    (hcut : ∀ a ∈ U, ∀ b, s(a,b) ∈ E → b ∉ U → b ∈ T)
    (hR : R ⊆ E) {a b : V} (he : s(a,b) ∈ R) :
    (bbGraph T (exchange (touching E U) S R) (exchange (touching E U) R S)).Reachable
      (switchVtx U (a,1)) (switchVtx U (b,1)) := by
  have hE := hR he
  by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
  · simp only [switchVtx, ha, hb, ↓reduceIte, show (1 : Fin 2) - 1 = 0 from rfl]
    apply bb_horizontal
    exact mem_exchange.2 (Or.inr ⟨he, (touching_pair hE).2 (Or.inl ha)⟩)
  · simp only [switchVtx, ha, hb, ↓reduceIte, show (1 : Fin 2) - 1 = 0 from rfl]
    exact (bb_horizontal (mem_exchange.2 (Or.inr
      ⟨he, (touching_pair hE).2 (Or.inl ha)⟩))).trans (bb_post (hcut a ha b hE hb) 0 1)
  · simp only [switchVtx, ha, hb, ↓reduceIte, show (1 : Fin 2) - 1 = 0 from rfl]
    have hat : a ∈ T := hcut b hb a (by simpa [Sym2.eq_swap] using hE) ha
    exact (bb_post hat 1 0).trans (bb_horizontal
      (mem_exchange.2 (Or.inr ⟨he, (touching_pair hE).2 (Or.inr hb)⟩)))
  · simp only [switchVtx, ha, hb, ↓reduceIte]
    exact bb_horizontal' (mem_exchange.2 (Or.inl ⟨he, by simpa [touching_pair hE] using And.intro ha hb⟩))

lemma switch_reach {E S R : Finset (Sym2 V)} {T U : Finset V}
    (hcut : ∀ a ∈ U, ∀ b, s(a,b) ∈ E → b ∉ U → b ∈ T)
    (hS : S ⊆ E) (hR : R ⊆ E) {x y : V × Fin 2}
    (h : (bbGraph T S R).Reachable x y) :
    (bbGraph T (exchange (touching E U) S R) (exchange (touching E U) R S)).Reachable
      (switchVtx U x) (switchVtx U y) := by
  apply reach_map_of_adj_reach _ _ (switchVtx U) _ h
  intro x y hxy
  have hm := (SimpleGraph.fromEdgeSet_adj _).1 hxy
  rcases Finset.mem_union.1 hm.1 with hm | hm
  · rcases Finset.mem_union.1 hm with hm | hm
    · obtain ⟨e,he,heq⟩ := Finset.mem_image.1 hm
      induction e using Sym2.ind with | _ a b =>
        rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact switch_horizontal hcut hS he
        · exact (switch_horizontal hcut hS he).symm
    · obtain ⟨e,he,heq⟩ := Finset.mem_image.1 hm
      induction e using Sym2.ind with | _ a b =>
        rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact switch_horizontal' hcut hR he
        · exact (switch_horizontal' hcut hR he).symm
  · obtain ⟨a,ha,heq⟩ := Finset.mem_image.1 hm
    rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
      unfold switchVtx <;> split <;> exact bb_post ha _ _

lemma switch_reach_iff {E S R : Finset (Sym2 V)} {T U : Finset V}
    (hcut : ∀ a ∈ U, ∀ b, s(a,b) ∈ E → b ∉ U → b ∈ T)
    (hS : S ⊆ E) (hR : R ⊆ E) (x y : V × Fin 2) :
    (bbGraph T (exchange (touching E U) S R) (exchange (touching E U) R S)).Reachable
      (switchVtx U x) (switchVtx U y) ↔ (bbGraph T S R).Reachable x y := by
  refine ⟨fun h => ?_, switch_reach hcut hS hR⟩
  have hh := switch_reach hcut (exchange_subset hS hR) (exchange_subset hR hS) h
  simpa only [exchange_twice, switchVtx_involutive U x, switchVtx_involutive U y] using hh

/-- A cut consisting of retained posts makes the two target levels equiprobable. -/
theorem bbProb_half_cut {E : Finset (Sym2 V)} {T U : Finset V} {u v : V}
    (hcut : ∀ a ∈ U, ∀ b, s(a,b) ∈ E → b ∉ U → b ∈ T)
    (hu : u ∉ U) (hv : v ∈ U) :
    bbProb E (fun _ => (1 / 2 : ℚ)) T (u,0) (v,0) =
      bbProb E (fun _ => (1 / 2 : ℚ)) T (u,0) (v,1) := by
  unfold bbProb
  rw [← Finset.sum_product', ← Finset.sum_product']
  let f : Finset (Sym2 V) × Finset (Sym2 V) → Finset (Sym2 V) × Finset (Sym2 V) :=
    fun S => (exchange (touching E U) S.1 S.2, exchange (touching E U) S.2 S.1)
  have hmap : ∀ S ∈ E.powerset ×ˢ E.powerset, f S ∈ E.powerset ×ˢ E.powerset := by
    intro S hS
    simp only [mem_product, mem_powerset] at hS ⊢
    exact ⟨exchange_subset hS.1 hS.2, exchange_subset hS.2 hS.1⟩
  have hinv : ∀ S, f (f S) = S := by
    intro S; exact Prod.ext (exchange_twice _ _ _) (exchange_twice _ _ _)
  refine Finset.sum_nbij' f f hmap hmap (fun S _ => hinv S) (fun S _ => hinv S) ?_
  intro S hS
  have hs := Finset.mem_product.1 hS
  have hs0 := Finset.mem_powerset.1 hs.1
  have hs1 := Finset.mem_powerset.1 hs.2
  have hi := switch_reach_iff hcut hs0 hs1 (u,0) (v,0)
  simp only [switchVtx, hu, hv, ↓reduceIte, show (1 : Fin 2) - 0 = 1 from rfl] at hi
  change (if (bbGraph T S.1 S.2).Reachable (u,0) (v,0) then (1 : ℚ) else 0) * _ * _ =
    (if (bbGraph T (exchange (touching E U) S.1 S.2)
      (exchange (touching E U) S.2 S.1)).Reachable (u,0) (v,1) then (1 : ℚ) else 0) * _ * _
  rw [if_congr hi rfl rfl, weight_half hs0, weight_half hs1,
    weight_half (exchange_subset hs0 hs1), weight_half (exchange_subset hs1 hs0)]

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph Bunkbed.Sub Bunkbed.Hyper

/-- Position along the path left after deleting the three original transversal vertices. -/
def pathPosition (v : Fin 7222) : ℕ :=
  if v.val < 10 then
    if v.val = 0 then 0 else
    if v.val = 2 then 1203 else
    if v.val = 5 then 2406 else
    if v.val = 4 then 3609 else
    if v.val = 3 then 4812 else
    if v.val = 7 then 6015 else 7218
  else 1203 * ((v.val - 10) / 1202) + (v.val - 10) % 1202 + 1

lemma mem_subT (v : Fin 7222) : v ∈ subT ↔ v.val = 1 ∨ v.val = 6 ∨ v.val = 8 := by
  simp only [subT, hollomT, Finset.image_insert, Finset.image_singleton,
    Finset.mem_insert, Finset.mem_singleton]
  simp [iota, Fin.ext_iff]

lemma position_le (v : Fin 7222) : pathPosition v ≤ 7218 := by
  unfold pathPosition
  have := v.isLt
  split_ifs <;> omega

lemma position_injective {v w : Fin 7222} (hv : v ∉ subT) (hw : w ∉ subT)
    (h : pathPosition v = pathPosition w) : v = w := by
  rw [mem_subT] at hv hw
  apply Fin.ext
  unfold pathPosition at h
  split_ifs at h <;> omega

lemma position_emb (i : Fin 6) (k : Fin 1205) (hk : 1 ≤ k.val) :
    pathPosition (emb i k) = 1203 * i.val + k.val - 1 := by
  have hki := k.isLt
  have hii := i.isLt
  by_cases h1 : k.val = 1
  · have hke : k = 1 := Fin.ext h1
    subst k
    fin_cases i <;> decide
  by_cases hl : k.val = 1204
  · have hke : k = 1204 := Fin.ext hl
    subst k
    fin_cases i <;> decide
  have hk0 : k.val ≠ 0 := by omega
  simp only [emb, pathPosition, embN, hk0, h1, hl, ↓reduceIte]
  have he : ¬ 10 + 1202 * i.val + (k.val - 2) < 10 := by omega
  rw [if_neg he]
  omega

lemma emb_path_not_post (i : Fin 6) (k : Fin 1205) (hk : 1 ≤ k.val) : emb i k ∉ subT := by
  rw [mem_subT]
  have hki := k.isLt
  simp only [emb, embN]
  by_cases h1 : k.val = 1
  · simp only [show k.val ≠ 0 by omega, h1, ↓reduceIte]
    fin_cases i <;> decide
  by_cases hl : k.val = 1204
  · simp only [show k.val ≠ 0 by omega, h1, hl, ↓reduceIte]
    fin_cases i <;> decide
  simp only [show k.val ≠ 0 by omega, h1, hl, ↓reduceIte]
  omega

lemma sub_edge_path {a b : Fin 7222} (he : s(a,b) ∈ subEdges)
    (ha : a ∉ subT) (hb : b ∉ subT) :
    pathPosition a + 1 = pathPosition b ∨ pathPosition b + 1 = pathPosition a := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 he
  obtain ⟨e,he,heq⟩ := Finset.mem_image.1 hi
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.1 he
  have hc := (Finset.mem_filter.1 hxy).2
  simp only [Prod.fst, Prod.snd] at hc heq
  rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases hc with ⟨hx,_⟩ | ⟨hx,hy⟩
    · subst x
      exfalso; apply ha
      rw [mem_subT]
      fin_cases i <;> simp [emb, embN, hollomTr]
    · left; rw [position_emb i x hx, position_emb i y (by omega)]; omega
  · rcases hc with ⟨hx,_⟩ | ⟨hx,hy⟩
    · subst x
      exfalso; apply hb
      rw [mem_subT]
      fin_cases i <;> simp [emb, embN, hollomTr]
    · right; rw [position_emb i x hx, position_emb i y (by omega)]; omega

lemma bbProb_post_target {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (T : Finset V) {v : V} (hv : v ∈ T) (x : V × Fin 2) :
    bbProb E (fun _ => (1 / 2 : ℚ)) T x (v,0) =
      bbProb E (fun _ => (1 / 2 : ℚ)) T x (v,1) := by
  unfold bbProb
  refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun R _ => ?_
  have hi : (bbGraph T S R).Reachable x (v,0) ↔ (bbGraph T S R).Reachable x (v,1) :=
    ⟨fun h => h.trans (bb_post hv 0 1), fun h => h.trans (bb_post hv 1 0)⟩
  rw [if_congr hi rfl rfl]

/-- Any extra retained post makes the two connection probabilities equal. -/
theorem sub_extra_post (T : Finset (Fin 7222)) (hT : subT ⊆ T) (hne : T ≠ subT) :
    bbProb subEdges (fun _ => (1 / 2 : ℚ)) T (iota 0,0) (iota 9,0) =
      bbProb subEdges (fun _ => (1 / 2 : ℚ)) T (iota 0,0) (iota 9,1) := by
  by_cases hv : iota 9 ∈ T
  · exact bbProb_post_target _ _ hv _
  have hn : ¬ T ⊆ subT := fun h => hne (Finset.Subset.antisymm h hT)
  obtain ⟨t,ht,hnt⟩ := Finset.not_subset.1 hn
  let U := Finset.univ.filter (fun v : Fin 7222 => v ∉ T ∧ pathPosition t < pathPosition v)
  apply bbProb_half_cut (U := U)
  · intro a ha b hab hb
    have ha' := (Finset.mem_filter.1 ha).2
    by_contra hbT
    have hb' : pathPosition b ≤ pathPosition t := by simpa [U, hbT] using hb
    have ha0 : a ∉ subT := fun h => ha'.1 (hT h)
    have hb0 : b ∉ subT := fun h => hbT (hT h)
    have hp := sub_edge_path hab ha0 hb0
    have he : pathPosition b = pathPosition t := by omega
    have hbt := position_injective hb0 hnt he
    exact hbT (hbt ▸ ht)
  · simp [U, pathPosition, iota]
  · have hlt : pathPosition t < 7218 := by
      have hle := position_le t
      by_contra hh
      have ht9 : t = iota 9 := position_injective hnt (by rw [mem_subT]; norm_num [iota])
        (by simpa [pathPosition, iota] using (show pathPosition t = 7218 by omega))
      exact hv (ht9 ▸ ht)
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hv, hlt⟩

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma lift_injective (i : Fin 2) : Function.Injective (liftLvl i : Sym2 V → _) :=
  Sym2.map.injective (fun _ _ h => congrArg Prod.fst h)

lemma post_injective : Function.Injective (fun v : V => s((v,(0 : Fin 2)),(v,1))) := by
  intro a b h
  rcases Sym2.eq_iff.1 h with h | h
  · exact congrArg Prod.fst h.1
  · exact congrArg Prod.fst h.1

lemma disjoint_lifts (E F : Finset (Sym2 V)) :
    Disjoint (E.image (liftLvl 0)) (F.image (liftLvl 1)) := by
  apply Finset.disjoint_left.2
  intro e he hf
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.1 he
  obtain ⟨e₁,_,hb⟩ := Finset.mem_image.1 hf
  induction a using Sym2.ind with | _ a b =>
    induction e₁ using Sym2.ind with | _ c d =>
      simp only [liftLvl, Sym2.map_pair_eq] at hb
      rcases Sym2.eq_iff.1 hb with hh | hh <;>
        have h01 := congrArg Prod.snd hh.1 <;> norm_num at h01

lemma disjoint_posts (E : Finset (Sym2 V)) (T : Finset V) (i : Fin 2) :
    Disjoint (E.image (liftLvl i)) (T.image (fun v => s((v,(0 : Fin 2)),(v,1)))) := by
  apply Finset.disjoint_left.2
  intro e he hf
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.1 he
  obtain ⟨v,_,hv⟩ := Finset.mem_image.1 hf
  induction a using Sym2.ind with | _ a b =>
    simp only [liftLvl, Sym2.map_pair_eq] at hv
    rcases Sym2.eq_iff.1 hv with hh | hh <;>
      have h0 := congrArg Prod.snd hh.1 <;>
      have h1 := congrArg Prod.snd hh.2 <;>
      simp only [Prod.snd] at h0 h1 <;> omega

lemma sum_powerset_image {α β M : Type*} [DecidableEq α] [DecidableEq β]
    [AddCommMonoid M] (S : Finset α) (f : α → β) (hf : Function.Injective f)
    (g : Finset β → M) :
    ∑ R ∈ (S.image f).powerset, g R = ∑ R ∈ S.powerset, g (R.image f) := by
  rw [Finset.powerset_image, Finset.sum_image (Finset.image_injective hf).injOn]

lemma completeEdges_card (E : Finset (Sym2 V)) :
    (completeEdges E).card = 2 * E.card + Fintype.card V := by
  rw [completeEdges, Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.2 ⟨disjoint_posts E _ 0, disjoint_posts E _ 1⟩),
    Finset.card_union_of_disjoint (disjoint_lifts E E),
    Finset.card_image_of_injective _ (lift_injective 0),
    Finset.card_image_of_injective _ (lift_injective 1),
    Finset.card_image_of_injective _ post_injective, Finset.card_univ]
  omega

/-- Fair percolation on the Cartesian product is the uniform average over post sets. -/
theorem completeProb_average (E : Finset (Sym2 V)) (x y : V × Fin 2) :
    completeProb E (1 / 2) x y =
      (1 / 2 : ℚ) ^ Fintype.card V *
        ∑ T ∈ (Finset.univ : Finset V).powerset, bbProb E (fun _ => (1 / 2 : ℚ)) T x y := by
  unfold completeProb connProbU connProb probOf
  have hhalf : ∑ S ∈ (completeEdges E).powerset,
        (if (ofEdges S).Reachable x y then weight (completeEdges E) (fun _ => (1/2:ℚ)) S else 0)
      = ∑ S ∈ (completeEdges E).powerset,
        (if (ofEdges S).Reachable x y then (1:ℚ) else 0) *
          (1/2:ℚ) ^ (2 * E.card + Fintype.card V) := by
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [weight_half (Finset.mem_powerset.1 hS), completeEdges_card]
    split <;> simp
  rw [hhalf, completeEdges,
    ← sum_powerset_union (Finset.disjoint_union_left.2
      ⟨disjoint_posts E _ 0, disjoint_posts E _ 1⟩)]
  rw [← sum_powerset_union (disjoint_lifts E E)]
  rw [sum_powerset_image _ _ (lift_injective 0)]
  simp_rw [sum_powerset_image _ _ (lift_injective 1),
    sum_powerset_image _ _ post_injective]
  conv_lhs =>
    arg 2
    ext S
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [bbProb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun S hS =>
    Finset.sum_congr rfl fun R hR => ?_
  rw [weight_half (Finset.mem_powerset.1 hS), weight_half (Finset.mem_powerset.1 hR)]
  rw [pow_add, show 2 * E.card = E.card + E.card by omega, pow_add]
  ring

end Bunkbed.Complete

namespace Bunkbed.Complete

/-- Six independent pendant paths suppress a missing post by more than a factor of two. -/
lemma six_path_bound : (7 / 8 : ℚ) ^ 6 < 1 / 2 := by norm_num

/-- The integer choice used below avoids an unverified decimal estimate of the gap. -/
lemma amplification_numeric :
    3 * (7 / 8 : ℚ) ^ 216630 < (1 / 2 : ℚ) ^ 36103 := by
  have h : (7 / 8 : ℚ) ^ 216630 < (1 / 2 : ℚ) ^ 36105 := by
    rw [show 216630 = 6 * 36105 by omega, pow_mul]
    exact pow_lt_pow_left₀ six_path_bound (by positivity) (by omega)
  have hp : 0 < (1 / 2 : ℚ) ^ 36103 := pow_pos (by norm_num) _
  have he : (1 / 2 : ℚ) ^ 36105 = (1 / 2 : ℚ) ^ 36103 / 4 := by
    rw [show 36105 = 36103 + 2 by omega, pow_add]
    norm_num
    ring
  rw [he] at h
  generalize (7 / 8 : ℚ) ^ 216630 = r at *
  generalize (1 / 2 : ℚ) ^ 36103 = c at *
  linarith

/-- A quantitative form of the last inequality in the proof of Theorem 6.1. -/
theorem amplified_gap_negative (δ D A : ℚ)
    (hδ : δ ≤ -(1 / 2 : ℚ) ^ 28884)
    (hA : 1 - (3 / 2 : ℚ) * (7 / 8 : ℚ) ^ 216630 ≤ A)
    (hA1 : A ≤ 1)
    (hD : D ≤ 1 - A + A * δ * (1 / 2 : ℚ) ^ 7219) : D < 0 := by
  have hp : 0 < (1 / 2 : ℚ) ^ 7219 := pow_pos (by norm_num) _
  have hq : 0 < (1 / 2 : ℚ) ^ 28884 := pow_pos (by norm_num) _
  have hr : 0 < (1 / 2 : ℚ) ^ 36103 := pow_pos (by norm_num) _
  have hr1 : (1 / 2 : ℚ) ^ 36103 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hnum := amplification_numeric
  have hadd : (1 / 2 : ℚ) ^ 28884 * (1 / 2 : ℚ) ^ 7219 =
      (1 / 2 : ℚ) ^ 36103 := by rw [← pow_add]
  generalize (7 / 8 : ℚ) ^ 216630 = r at *
  generalize (1 / 2 : ℚ) ^ 28884 = b at *
  generalize (1 / 2 : ℚ) ^ 7219 = c at *
  generalize (1 / 2 : ℚ) ^ 36103 = d at *
  have hAhalf : (1 / 2 : ℚ) < A := by linarith
  have hd : δ * c ≤ -d := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hd (by linarith : 0 ≤ A)
  have hmul' := mul_lt_mul_of_pos_right hAhalf hr
  nlinarith

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A three-edge path supplies an additional post precisely when all three edges are open. -/
def path3Edges (v : Fin 4 → W) (A : Finset (Fin 3)) : Finset (Sym2 W) :=
  A.image (fun i => s(v i.castSucc, v i.succ))

def path3Retraction (v : Fin 4 → W) (A : Finset (Fin 3)) (w : W) : W :=
  if w = v 1 then (if 0 ∉ A ∧ 1 ∈ A ∧ 2 ∈ A then v 3 else v 0)
  else if w = v 2 then (if 2 ∈ A then v 3 else v 0) else w

lemma reachable_of_mem_edge {C : Finset (Sym2 W)} {a b : W} (h : s(a,b) ∈ C) :
    (ofEdges C).Reachable a b := by
  by_cases hab : a = b
  · subst b; rfl
  · exact ((SimpleGraph.fromEdgeSet_adj _).2 ⟨h,hab⟩).reachable

lemma path3_retract_fixed (v : Fin 4 → W) (A : Finset (Fin 3)) {w : W}
    (h1 : w ≠ v 1) (h2 : w ≠ v 2) : path3Retraction v A w = w := by
  simp [path3Retraction,h1,h2]

lemma path3_retract_edge (v : Fin 4 → W) (hv : Function.Injective v)
    (A : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ A) :
    (ofEdges (if A = Finset.univ then {s(v 0,v 3)} else ∅)).Reachable
      (path3Retraction v A (v i.castSucc)) (path3Retraction v A (v i.succ)) := by
  have heq : ∀ i j : Fin 4, v i = v j ↔ i = j := fun i j => hv.eq_iff
  have hall : A = univ ↔ (0 ∈ A ∧ 1 ∈ A ∧ 2 ∈ A) := by
    constructor
    · rintro rfl; simp
    · intro h; ext i; fin_cases i <;> simp_all
  have hp : (ofEdges ({s(v 0,v 3)} : Finset (Sym2 W))).Reachable (v 0) (v 3) :=
    reachable_of_mem_edge (Finset.mem_singleton_self _)
  fin_cases i
  · change (0 : Fin 3) ∈ A at hi
    change (ofEdges (if A = univ then {s(v 0,v 3)} else ∅)).Reachable
      (path3Retraction v A (v 0)) (path3Retraction v A (v 1))
    simp only [path3Retraction, heq]
    by_cases h1 : 1 ∈ A <;> by_cases h2 : 2 ∈ A <;>
      simp_all [hall, Fin.ext_iff]
  · change (1 : Fin 3) ∈ A at hi
    change (ofEdges (if A = univ then {s(v 0,v 3)} else ∅)).Reachable
      (path3Retraction v A (v 1)) (path3Retraction v A (v 2))
    simp only [path3Retraction, heq]
    by_cases h0 : 0 ∈ A <;> by_cases h2 : 2 ∈ A <;>
      simp_all [hall, Fin.ext_iff]
  · change (2 : Fin 3) ∈ A at hi
    change (ofEdges (if A = univ then {s(v 0,v 3)} else ∅)).Reachable
      (path3Retraction v A (v 2)) (path3Retraction v A (v 3))
    simp only [path3Retraction, heq]
    by_cases h0 : 0 ∈ A <;> by_cases h1 : 1 ∈ A <;>
      simp_all [hall, Fin.ext_iff]

/-- Replacing an isolated three-edge path by its induced boundary connection preserves reachability. -/
theorem path3_reach (C : Finset (Sym2 W)) (v : Fin 4 → W) (hv : Function.Injective v)
    (hC : ∀ e ∈ C, v 1 ∉ e ∧ v 2 ∉ e)
    (A : Finset (Fin 3)) {x y : W}
    (hx1 : x ≠ v 1) (hx2 : x ≠ v 2) (hy1 : y ≠ v 1) (hy2 : y ≠ v 2) :
    (ofEdges (C ∪ path3Edges v A)).Reachable x y ↔
      (ofEdges (C ∪ if A = univ then {s(v 0,v 3)} else ∅)).Reachable x y := by
  constructor
  · intro h
    have hh := reach_map_of_adj_reach (ofEdges (C ∪ path3Edges v A))
      (ofEdges (C ∪ if A = univ then {s(v 0,v 3)} else ∅)) (path3Retraction v A) ?_ h
    · simpa only [path3_retract_fixed v A hx1 hx2, path3_retract_fixed v A hy1 hy2] using hh
    intro a b hab
    have he := (SimpleGraph.fromEdgeSet_adj _).1 hab
    rcases Finset.mem_union.1 he.1 with hc | hp
    · have hs := hC _ hc
      have ha1 : a ≠ v 1 := fun hh => hs.1 (by simp [← hh])
      have ha2 : a ≠ v 2 := fun hh => hs.2 (by simp [← hh])
      have hb1 : b ≠ v 1 := fun hh => hs.1 (by simp [← hh])
      have hb2 : b ≠ v 2 := fun hh => hs.2 (by simp [← hh])
      rw [path3_retract_fixed v A ha1 ha2, path3_retract_fixed v A hb1 hb2]
      exact reachable_of_mem_edge (Finset.mem_union_left _ hc)
    · obtain ⟨i,hi,heq⟩ := Finset.mem_image.1 hp
      have hr := (path3_retract_edge v hv A i hi).mono
        (ofEdges_mono (Finset.subset_union_right (s₁ := C)))
      rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hr
      · exact hr.symm
  · intro h
    apply reach_of_adj_reach _ _ _ h
    intro a b hab
    have he := (SimpleGraph.fromEdgeSet_adj _).1 hab
    rcases Finset.mem_union.1 he.1 with hc | hp
    · exact reachable_of_mem_edge (Finset.mem_union_left _ hc)
    · by_cases hA : A = univ
      · rw [if_pos hA, Finset.mem_singleton] at hp
        have he0 : ∀ i : Fin 3, (ofEdges (C ∪ path3Edges v A)).Reachable
            (v i.castSucc) (v i.succ) := by
          intro i
          apply reachable_of_mem_edge
          exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, by simp [hA], rfl⟩)
        have hh := ((he0 0).trans (he0 1)).trans (he0 2)
        rcases Sym2.eq_iff.1 hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact hh
        · exact hh.symm
      · simp [hA] at hp

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {W : Type*} [Fintype W] [DecidableEq W]

def expectation (E : Finset (Sym2 W)) (w : Sym2 W → ℚ) (f : Finset (Sym2 W) → ℚ) : ℚ :=
  ∑ S ∈ E.powerset, weight E w S * f S

lemma connProb_expectation (E : Finset (Sym2 W)) (w : Sym2 W → ℚ) (x y : W) :
    connProb E w x y = expectation E w (fun S => if (ofEdges S).Reachable x y then 1 else 0) := by
  unfold connProb probOf expectation
  apply Finset.sum_congr rfl
  intro S _; split <;> simp_all

lemma expectation_congr (E : Finset (Sym2 W)) (w : Sym2 W → ℚ)
    (f g : Finset (Sym2 W) → ℚ) (h : ∀ S ⊆ E, f S = g S) :
    expectation E w f = expectation E w g := by
  apply Finset.sum_congr rfl
  intro S hS; rw [h S (Finset.mem_powerset.1 hS)]

lemma expectation_union {E F : Finset (Sym2 W)} (hEF : Disjoint E F) (w : Sym2 W → ℚ)
    (f : Finset (Sym2 W) → ℚ) :
    expectation (E ∪ F) w f =
      expectation E w (fun S => expectation F w (fun R => f (S ∪ R))) := by
  unfold expectation
  rw [← sum_powerset_union hEF]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [weight_union hEF w (Finset.mem_powerset.1 hS) (Finset.mem_powerset.1 hR)]
  ring

lemma expectation_weight_congr (E : Finset (Sym2 W)) (w z : Sym2 W → ℚ)
    (hw : ∀ e ∈ E, w e = z e) (f : Finset (Sym2 W) → ℚ) :
    expectation E w f = expectation E z f := by
  refine Finset.sum_congr rfl fun S hS => ?_
  have hs := Finset.mem_powerset.1 hS
  have hh : weight E w S = weight E z S := by
    unfold weight
    congr 1
    · exact Finset.prod_congr rfl fun e he => hw e (hs he)
    · exact Finset.prod_congr rfl fun e he => congrArg (1 - ·) (hw e (Finset.mem_sdiff.1 he).1)
  rw [hh]

lemma expectation_insert {E : Finset (Sym2 W)} {e : Sym2 W} (he : e ∉ E)
    (w : Sym2 W → ℚ) (f : Finset (Sym2 W) → ℚ) :
    expectation (insert e E) w f =
      (1 - w e) * expectation E w f + w e * expectation E w (fun S => f (insert e S)) := by
  unfold expectation
  rw [Finset.sum_powerset_insert he, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hes : e ∉ S := fun h => he (Finset.mem_powerset.1 hS h)
    unfold weight
    rw [Finset.insert_sdiff_of_notMem _ hes, Finset.prod_insert (by simp [he])]
    ring
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hes : e ∉ S := fun h => he (Finset.mem_powerset.1 hS h)
    unfold weight
    rw [Finset.prod_insert hes, Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem he]
    ring

lemma expectation_linear (E : Finset (Sym2 W)) (w : Sym2 W → ℚ)
    (f g : Finset (Sym2 W) → ℚ) (a b : ℚ) :
    expectation E w (fun S => a * f S + b * g S) =
      a * expectation E w f + b * expectation E w g := by
  unfold expectation
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- Independently forcing an existing edge open updates its retention probability. -/
lemma expectation_force {E : Finset (Sym2 W)} {e : Sym2 W} (he : e ∈ E)
    (w : Sym2 W → ℚ) (f : Finset (Sym2 W) → ℚ) (r : ℚ) :
    expectation E w (fun S => r * f S + (1-r) * f (insert e S)) =
      expectation E (Function.update w e (1-r*(1-w e))) f := by
  have hEE : E = insert e (E.erase e) := (Finset.insert_erase he).symm
  rw [hEE, expectation_insert (Finset.notMem_erase _ _),
    expectation_insert (Finset.notMem_erase _ _)]
  have hw : ∀ a ∈ E.erase e, Function.update w e (1-r*(1-w e)) a = w a := by
    intro a ha; exact Function.update_of_ne (Finset.mem_erase.1 ha).1 _ _
  rw [expectation_weight_congr _ _ w hw, expectation_weight_congr _ _ w hw]
  simp only [Function.update_self, Finset.insert_idem]
  rw [expectation_linear, expectation_linear]
  ring

lemma path3_edge_injective (v : Fin 4 → W) (hv : Function.Injective v) :
    Function.Injective (fun i : Fin 3 => s(v i.castSucc, v i.succ)) := by
  intro i j hij
  rcases Sym2.eq_iff.1 hij with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Fin.ext (by simpa only [Fin.val_castSucc] using congrArg (fun x : Fin 4 => x.val) (hv h1))
  · have h1' := congrArg Fin.val (hv h1)
    have h2' := congrArg Fin.val (hv h2)
    simp only [Fin.val_castSucc, Fin.val_succ] at h1' h2'
    omega

lemma path3_disjoint (C : Finset (Sym2 W)) (v : Fin 4 → W)
    (hC : ∀ e ∈ C, v 1 ∉ e ∧ v 2 ∉ e) : Disjoint C (path3Edges v univ) := by
  refine Finset.disjoint_left.2 fun e he hf => ?_
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hf
  have hc := hC _ he
  fin_cases i
  · exact hc.1 (by simp)
  · exact hc.1 (by simp)
  · exact hc.2 (by simp)

lemma expectation_path3 (C : Finset (Sym2 W)) (v : Fin 4 → W) (hv : Function.Injective v)
    (hC : ∀ e ∈ C, v 1 ∉ e ∧ v 2 ∉ e)
    (w : Sym2 W → ℚ) (hw : ∀ e ∈ path3Edges v univ, w e = 1 / 2)
    {x y : W} (hx1 : x ≠ v 1) (hx2 : x ≠ v 2) (hy1 : y ≠ v 1) (hy2 : y ≠ v 2) :
    expectation (path3Edges v univ) w
      (fun R => if (ofEdges (C ∪ R)).Reachable x y then 1 else 0) =
      (7/8 : ℚ) * (if (ofEdges C).Reachable x y then 1 else 0) +
      (1/8 : ℚ) * (if (ofEdges (insert s(v 0,v 3) C)).Reachable x y then 1 else 0) := by
  rw [expectation_weight_congr _ w (fun _ => 1 / 2) hw]
  unfold expectation path3Edges
  rw [sum_powerset_image _ _ (path3_edge_injective v hv)]
  have hcard : (univ.image (fun i : Fin 3 => s(v i.castSucc, v i.succ))).card = 3 := by
    rw [Finset.card_image_of_injective _ (path3_edge_injective v hv)]; rfl
  have hsum : ∀ A ∈ (univ : Finset (Fin 3)).powerset,
      weight (univ.image (fun i : Fin 3 => s(v i.castSucc, v i.succ))) (fun _ => (1/2:ℚ))
        (A.image (fun i : Fin 3 => s(v i.castSucc, v i.succ))) = 1/8 := by
    intro A hA
    rw [weight_half (Finset.image_subset_image (Finset.mem_powerset.1 hA)), hcard]
    norm_num
  simp_rw [Finset.sum_congr rfl (fun A hA => congrArg
    (· * (if (ofEdges (C ∪ A.image (fun i : Fin 3 => s(v i.castSucc,v i.succ)))).Reachable x y
      then (1:ℚ) else 0)) (hsum A hA))]
  have hreach : ∀ A : Finset (Fin 3),
      (if (ofEdges (C ∪ A.image (fun i : Fin 3 => s(v i.castSucc,v i.succ)))).Reachable x y
        then (1:ℚ) else 0) =
      if A = univ then (if (ofEdges (insert s(v 0,v 3) C)).Reachable x y then 1 else 0)
        else (if (ofEdges C).Reachable x y then 1 else 0) := by
    intro A
    change (if (ofEdges (C ∪ path3Edges v A)).Reachable x y then (1:ℚ) else 0) = _
    rw [if_congr (path3_reach C v hv hC A hx1 hx2 hy1 hy2) rfl rfl]
    split <;> simp_all [Finset.union_singleton]
  simp_rw [hreach]
  rw [← Finset.mul_sum]
  have hsplit (a b : ℚ) : (∑ A ∈ (univ : Finset (Fin 3)).powerset,
      if A = univ then b else a) = 7*a+b := by
    have hh : ∀ A : Finset (Fin 3), (if A = univ then b else a) =
        a + (if A = univ then b-a else 0) := by intro A; split <;> ring
    simp_rw [hh]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    norm_num
    ring
  rw [hsplit]
  ring

/-- A fair isolated three-edge path in parallel with an existing edge boosts its probability. -/
theorem connProb_path3 (C : Finset (Sym2 W)) (v : Fin 4 → W) (hv : Function.Injective v)
    (hC : ∀ e ∈ C, v 1 ∉ e ∧ v 2 ∉ e) (hpost : s(v 0,v 3) ∈ C)
    (w : Sym2 W → ℚ) (hw : ∀ e ∈ path3Edges v univ, w e = 1 / 2)
    {x y : W} (hx1 : x ≠ v 1) (hx2 : x ≠ v 2) (hy1 : y ≠ v 1) (hy2 : y ≠ v 2) :
    connProb (C ∪ path3Edges v univ) w x y =
      connProb C (Function.update w s(v 0,v 3) (1-(7/8)*(1-w s(v 0,v 3)))) x y := by
  rw [connProb_expectation, expectation_union (path3_disjoint C v hC), connProb_expectation]
  have hh := expectation_congr C w _ _ (fun S hS =>
    expectation_path3 S v hv (fun e he => hC e (hS he)) w hw hx1 hx2 hy1 hy2)
  rw [hh]
  convert expectation_force hpost w
    (fun S => if (ofEdges S).Reachable x y then (1:ℚ) else 0) (7/8) using 1 <;> norm_num

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

abbrev baseVertex (x : V × Fin 2) : (V ⊕ J) × Fin 2 := (Sum.inl x.1,x.2)

def basePost (x : V) : Sym2 ((V ⊕ J) × Fin 2) := s((Sum.inl x,0),(Sum.inl x,1))

lemma basePost_injective : Function.Injective (basePost : V → Sym2 ((V ⊕ J) × Fin 2)) := by
  intro x y h
  rcases Sym2.eq_iff.1 h with h | h <;>
    exact Sum.inl.inj (congrArg Prod.fst h.1)

noncomputable def postW (q : V → ℚ) (e : Sym2 ((V ⊕ J) × Fin 2)) : ℚ :=
  if h : ∃ x, e = basePost x then q (Classical.choose h) else 1 / 2

lemma postW_post (q : V → ℚ) (x : V) : postW (J := J) q (basePost x) = q x := by
  classical
  unfold postW
  rw [dif_pos ⟨x,rfl⟩]
  congr 1
  exact basePost_injective (Classical.choose_spec (show ∃ y : V, basePost (J := J) x = basePost y from ⟨x,rfl⟩)).symm

lemma postW_other (q : V → ℚ) {e : Sym2 ((V ⊕ J) × Fin 2)}
    (he : ∀ x, e ≠ basePost x) : postW q e = 1 / 2 := by
  classical
  rw [postW, dif_neg (by simpa using he)]

lemma postW_update (q : V → ℚ) (x : V) (a : ℚ) :
    Function.update (postW (J := J) q) (basePost x) a = postW (Function.update q x a) := by
  classical
  funext e
  by_cases he : ∃ y, e = basePost y
  · obtain ⟨y,rfl⟩ := he
    by_cases hy : y = x
    · subst y; simp [postW_post]
    · rw [Function.update_of_ne (fun hh => hy (basePost_injective hh)),
        postW_post, postW_post, Function.update_of_ne hy]
  · have hn : ∀ x, e ≠ basePost x := by simpa using he
    rw [Function.update_of_ne (hn x), postW_other q hn, postW_other _ hn]

def pendantPath (parent : J → V) (j : J) (i : Fin 4) : (V ⊕ J) × Fin 2 :=
  if i = 0 then (Sum.inl (parent j),0) else
  if i = 1 then (Sum.inr j,0) else
  if i = 2 then (Sum.inr j,1) else (Sum.inl (parent j),1)

lemma pendantPath_injective (parent : J → V) (j : J) : Function.Injective (pendantPath parent j) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [pendantPath, Fin.ext_iff]

lemma pendantPath_mem (parent : J → V) (j : J) (i : Fin 4) :
    (pendantPath parent j i).1 = Sum.inl (parent j) ∨ (pendantPath parent j i).1 = Sum.inr j := by
  fin_cases i <;> simp [pendantPath]

lemma pendantPath_interior (parent : J → V) (j : J) (i : Fin 3) :
    (Sum.inr j, (0 : Fin 2)) ∈ s(pendantPath parent j i.castSucc,pendantPath parent j i.succ) ∨
    (Sum.inr j, (1 : Fin 2)) ∈ s(pendantPath parent j i.castSucc,pendantPath parent j i.succ) := by
  fin_cases i <;> simp [pendantPath, Fin.ext_iff]

lemma postW_path (q : V → ℚ) (parent : J → V) (j : J)
    (e : Sym2 ((V ⊕ J) × Fin 2)) (he : e ∈ path3Edges (pendantPath parent j) univ) :
    postW q e = 1 / 2 := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 he
  apply postW_other
  intro x hx
  have hm := pendantPath_interior parent j i
  rw [hx] at hm
  simp [basePost] at hm

def pendantCore (E : Finset (Sym2 V)) : Finset (Sym2 ((V ⊕ J) × Fin 2)) :=
  (completeEdges E).image (Sym2.map baseVertex)

lemma pendantCore_post (E : Finset (Sym2 V)) (x : V) : basePost (J := J) x ∈ pendantCore E := by
  apply Finset.mem_image.2
  exact ⟨s((x,0),(x,1)), Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)), rfl⟩

lemma pendantCore_support (E : Finset (Sym2 V)) {e : Sym2 ((V ⊕ J) × Fin 2)}
    (he : e ∈ pendantCore E) (j : J) (l : Fin 2) : (Sum.inr j,l) ∉ e := by
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.1 he
  induction f using Sym2.ind with | _ a b => simp [baseVertex]

lemma pendantPath_support (parent : J → V) {j k : J} (hjk : j ≠ k)
    {e : Sym2 ((V ⊕ J) × Fin 2)} (he : e ∈ path3Edges (pendantPath parent k) univ)
    (l : Fin 2) : (Sum.inr j,l) ∉ e := by
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 he
  simp only [Sym2.mem_iff]
  intro h
  rcases h with h | h
  all_goals
    have hh := congrArg Prod.fst h
    rcases pendantPath_mem parent k _ with hh' | hh' <;>
      rw [hh'] at hh
    · cases hh
    · exact hjk (Sum.inr.inj hh)

def boostedQ (I : Finset J) (parent : J → V) (q : V → ℚ) (x : V) : ℚ :=
  1 - (1-q x) * (7/8 : ℚ) ^ (I.filter (fun j => parent j = x)).card

lemma boostedQ_insert (I : Finset J) {j : J} (hj : j ∉ I) (parent : J → V) (q : V → ℚ) :
    boostedQ I parent (Function.update q (parent j) (1-(7/8)*(1-q (parent j)))) =
      boostedQ (insert j I) parent q := by
  classical
  funext x
  by_cases hx : x = parent j
  · subst x
    have hjf : j ∉ I.filter (fun k => parent k = parent j) := fun h => hj (Finset.mem_filter.1 h).1
    simp only [boostedQ, Function.update_self, Finset.filter_insert,
      eq_self, ↓reduceIte]
    rw [Finset.card_insert_of_notMem hjf, pow_succ]
    ring
  · rw [boostedQ, boostedQ, Function.update_of_ne hx, Finset.filter_insert, if_neg (Ne.symm hx)]

/-- Eliminate any finite family of pendant three-edge paths. -/
theorem pendant_collapse (E : Finset (Sym2 V)) (parent : J → V) (I : Finset J)
    (q : V → ℚ) (x y : V × Fin 2) :
    connProb (pendantCore E ∪ I.biUnion (fun j => path3Edges (pendantPath parent j) univ))
      (postW q) (baseVertex x) (baseVertex y) =
    connProb (pendantCore (J := J) E) (postW (boostedQ I parent q)) (baseVertex x) (baseVertex y) := by
  classical
  induction I using Finset.induction_on generalizing q with
  | empty =>
    have hq : boostedQ (∅ : Finset J) parent q = q := by funext v; simp [boostedQ]
    simp [hq]
  | @insert j I hj ih =>
    rw [Finset.biUnion_insert]
    have hset : pendantCore E ∪ (path3Edges (pendantPath parent j) univ ∪
        I.biUnion (fun k => path3Edges (pendantPath parent k) univ)) =
      (pendantCore E ∪ I.biUnion (fun k => path3Edges (pendantPath parent k) univ)) ∪
        path3Edges (pendantPath parent j) univ := by
      ext e; simp only [Finset.mem_union]; tauto
    rw [hset]
    have hC : ∀ e ∈ pendantCore E ∪ I.biUnion (fun k => path3Edges (pendantPath parent k) univ),
        pendantPath parent j 1 ∉ e ∧ pendantPath parent j 2 ∉ e := by
      intro e he
      simp only [pendantPath, show (1 : Fin 4) ≠ 0 from by decide,
        show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, ↓reduceIte]
      rcases Finset.mem_union.1 he with he | he
      · exact ⟨pendantCore_support E he j 0, pendantCore_support E he j 1⟩
      · obtain ⟨k,hk,he⟩ := Finset.mem_biUnion.1 he
        have hjk : j ≠ k := fun h => hj (h ▸ hk)
        exact ⟨pendantPath_support parent hjk he 0, pendantPath_support parent hjk he 1⟩
    have hpost : s(pendantPath parent j 0,pendantPath parent j 3) = basePost (parent j) := by
      simp [pendantPath,basePost]
    rw [connProb_path3 _ _ (pendantPath_injective parent j) hC
      (by rw [hpost]; exact Finset.mem_union_left _ (pendantCore_post E _)) _
      (postW_path q parent j)
      (by simp [pendantPath,baseVertex]) (by simp [pendantPath,baseVertex])
      (by simp [pendantPath,baseVertex]) (by simp [pendantPath,baseVertex])]
    rw [hpost, postW_post, postW_update, ih, boostedQ_insert I hj]

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

lemma reach_image (f : V → W) (hf : Function.Injective f) (E : Finset (Sym2 V)) (x y : V) :
    (ofEdges (E.image (Sym2.map f))).Reachable (f x) (f y) ↔ (ofEdges E).Reachable x y := by
  classical
  letI : Nonempty V := ⟨x⟩
  have hinv : ∀ v, Function.invFun f (f v) = v := Function.leftInverse_invFun hf
  constructor
  · intro h
    have hh := reach_map_of_adj_reach _ (ofEdges E) (Function.invFun f) ?_ h
    · simpa only [hinv] using hh
    intro a b hab
    obtain ⟨e,he,heq⟩ := Finset.mem_image.1 ((SimpleGraph.fromEdgeSet_adj _).1 hab).1
    induction e using Sym2.ind with | _ a' b' =>
      rcases Sym2.eq_iff.1 heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        simp only [Sym2.map_mk, hinv]
      · exact reachable_of_mem_edge he
      · exact (reachable_of_mem_edge he).symm
  · intro h
    apply reach_map_of_adj_reach _ _ f _ h
    intro a b hab
    apply reachable_of_mem_edge
    exact Finset.mem_image_of_mem (Sym2.map f) ((SimpleGraph.fromEdgeSet_adj _).1 hab).1

lemma weight_image {A : Type*} [DecidableEq A] (E S : Finset A)
    (f : A → Sym2 W) (hf : Function.Injective f) (w : Sym2 W → ℚ) :
    weight (E.image f) w (S.image f) =
      (∏ a ∈ S, w (f a)) * ∏ a ∈ E \ S, (1-w (f a)) := by
  rw [weight, ← Finset.image_sdiff E S hf, Finset.prod_image hf.injOn, Finset.prod_image hf.injOn]

lemma connProb_relabel (E : Finset (Sym2 V)) (f : V → W) (hf : Function.Injective f)
    (w : Sym2 W → ℚ) (x y : V) :
    connProb (E.image (Sym2.map f)) w (f x) (f y) =
      connProb E (fun e => w (Sym2.map f e)) x y := by
  rw [connProb_expectation, connProb_expectation, expectation, expectation,
    sum_powerset_image _ _ (Sym2.map.injective hf)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [weight_image _ _ _ (Sym2.map.injective hf), if_congr (reach_image f hf S x y) rfl rfl]
  rfl

lemma product_connProb_posts (E : Finset (Sym2 V)) (w : Sym2 (V × Fin 2) → ℚ) (q : V → ℚ)
    (h0 : ∀ e ∈ E, w (liftLvl 0 e) = 1/2)
    (h1 : ∀ e ∈ E, w (liftLvl 1 e) = 1/2)
    (hp : ∀ v, w s((v,0),(v,1)) = q v) (x y : V × Fin 2) :
    connProb (completeEdges E) w x y = randomPostProb E q x y := by
  rw [connProb_expectation, completeEdges, expectation_union
      (Finset.disjoint_union_left.2 ⟨disjoint_posts E _ 0, disjoint_posts E _ 1⟩),
    expectation_union (disjoint_lifts E E)]
  unfold expectation
  rw [sum_powerset_image _ _ (lift_injective 0)]
  simp_rw [sum_powerset_image _ _ (lift_injective 1), sum_powerset_image _ _ post_injective]
  have wh (i : Fin 2) (hi : ∀ e ∈ E, w (liftLvl i e) = 1/2) (S : Finset (Sym2 V))
      (hS : S ⊆ E) : weight (E.image (liftLvl i)) w (S.image (liftLvl i)) =
        weight E (fun _ => (1/2:ℚ)) S := by
    rw [weight_image _ _ _ (lift_injective i), weight]
    congr 1
    · exact Finset.prod_congr rfl fun e he => hi e (hS he)
    · exact Finset.prod_congr rfl fun e he => congrArg (1-·) (hi e (Finset.mem_sdiff.1 he).1)
  have wp (T : Finset V) :
      weight (univ.image (fun v : V => s((v,(0:Fin 2)),(v,1)))) w
        (T.image (fun v => s((v,(0:Fin 2)),(v,1)))) = postWeight q T := by
    rw [weight_image _ _ _ post_injective]
    simp only [hp,postWeight]
  simp_rw [wp, Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext S
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  unfold randomPostProb
  rw [← Finset.powerset_univ]
  simp only [bbProb,Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => Finset.sum_congr rfl fun S hS =>
    Finset.sum_congr rfl fun R hR => ?_
  rw [wh 0 h0 S (Finset.mem_powerset.1 hS), wh 1 h1 R (Finset.mem_powerset.1 hR)]
  change _ = postWeight q T * ((if (ofEdges (S.image (liftLvl 0) ∪ R.image (liftLvl 1) ∪ T.image (fun v => s((v,0),(v,1))))).Reachable x y then 1 else 0) * _ * _)
  ring

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma postWeight_nonneg (q : V → ℚ) (h0 : ∀ v, 0 ≤ q v) (h1 : ∀ v, q v ≤ 1) (T : Finset V) :
    0 ≤ postWeight q T :=
  mul_nonneg (Finset.prod_nonneg fun v _ => h0 v)
    (Finset.prod_nonneg fun v _ => sub_nonneg.2 (h1 v))

lemma post_missing_mass (q : V → ℚ) (v : V) :
    ∑ T : Finset V, (if v ∉ T then postWeight q T else 0) = 1-q v := by
  classical
  rw [← Finset.powerset_univ]
  let f : V → ℚ := fun x => if x = v then 0 else q x
  have he : ∀ T : Finset V,
      (if v ∉ T then postWeight q T else 0) =
        (∏ x ∈ T, f x) * ∏ x ∈ (univ : Finset V) \ T, (1-q x) := by
    intro T
    by_cases hv : v ∈ T
    · rw [if_neg (not_not_intro hv)]
      have hf : ∏ x ∈ T, f x = 0 := Finset.prod_eq_zero hv (by simp [f])
      rw [hf,zero_mul]
    · rw [if_pos hv,postWeight]
      congr 1
      exact Finset.prod_congr rfl fun x hx => by
        simp only [f,if_neg (fun h : x = v => hv (h ▸ hx))]
  simp_rw [he]
  rw [← Finset.prod_add]
  have hp : ∀ x, f x + (1-q x) = if x = v then 1-q v else 1 := by
    intro x; by_cases hx : x = v <;> simp [f,hx]
  simp_rw [hp]
  simp

lemma bbProb_half_unit (E : Finset (Sym2 V)) (T : Finset V) (x y : V × Fin 2) :
    0 ≤ bbProb E (fun _ => (1/2:ℚ)) T x y ∧ bbProb E (fun _ => (1/2:ℚ)) T x y ≤ 1 := by
  have hw : ∀ S ⊆ E, 0 ≤ weight E (fun _ => (1/2:ℚ)) S := by
    intro S hS; rw [weight_half hS]; positivity
  have hsum : (∑ S ∈ E.powerset, ∑ R ∈ E.powerset,
      weight E (fun _ => (1/2:ℚ)) S * weight E (fun _ => (1/2:ℚ)) R) = 1 := by
    simp_rw [← Finset.mul_sum, BunkbedAux.sum_weight_eq_one]
    simp [BunkbedAux.sum_weight_eq_one]
  constructor
  · apply Finset.sum_nonneg
    intro S hS
    apply Finset.sum_nonneg
    intro R hR
    apply mul_nonneg
    · apply mul_nonneg
      · split <;> norm_num
      · exact hw S (mem_powerset.1 hS)
    · exact hw R (mem_powerset.1 hR)
  · apply le_trans (b := ∑ S ∈ E.powerset, ∑ R ∈ E.powerset,
        weight E (fun _ => (1/2:ℚ)) S * weight E (fun _ => (1/2:ℚ)) R) ?_ (le_of_eq hsum)
    apply Finset.sum_le_sum
    intro S hS
    apply Finset.sum_le_sum
    intro R hR
    split
    · simp
    · simp only [zero_mul]
      exact mul_nonneg (hw S (mem_powerset.1 hS)) (hw R (mem_powerset.1 hR))

/-- Only missing distinguished posts can make a positive contribution. -/
lemma randomPost_gap_bound (E : Finset (Sym2 V)) (T₀ : Finset V) (u v : V)
    (q : V → ℚ) (h0 : ∀ v, 0 ≤ q v) (h1 : ∀ v, q v ≤ 1)
    (hcancel : ∀ T, T₀ ⊆ T → T ≠ T₀ →
      bbProb E (fun _ => (1/2:ℚ)) T (u,0) (v,0) =
        bbProb E (fun _ => (1/2:ℚ)) T (u,0) (v,1)) :
    randomPostProb E q (u,0) (v,0) - randomPostProb E q (u,0) (v,1) ≤
      (∑ t ∈ T₀, (1-q t)) + postWeight q T₀ *
        (bbProb E (fun _ => (1/2:ℚ)) T₀ (u,0) (v,0) -
          bbProb E (fun _ => (1/2:ℚ)) T₀ (u,0) (v,1)) := by
  classical
  let d := fun T => bbProb E (fun _ => (1/2:ℚ)) T (u,0) (v,0) -
    bbProb E (fun _ => (1/2:ℚ)) T (u,0) (v,1)
  have hpoint (T : Finset V) : postWeight q T * d T ≤
      (∑ t ∈ T₀, if t ∉ T then postWeight q T else 0) +
        (if T = T₀ then postWeight q T₀ * d T₀ else 0) := by
    have hw := postWeight_nonneg q h0 h1 T
    by_cases hT : T = T₀
    · subst T
      simp
      exact Finset.sum_nonneg fun t ht => by simp [ht]
    by_cases hsub : T₀ ⊆ T
    · have hd : d T = 0 := sub_eq_zero.2 (hcancel T hsub hT)
      rw [hd,mul_zero,if_neg hT,add_zero]
      exact Finset.sum_nonneg fun _ _ => by split <;> linarith
    · obtain ⟨t,ht,hnt⟩ := Finset.not_subset.1 hsub
      have hd : d T ≤ 1 := by
        have hl := (bbProb_half_unit E T (u,0) (v,0)).2
        have hr := (bbProb_half_unit E T (u,0) (v,1)).1
        dsimp [d]; linarith
      have hm := mul_le_mul_of_nonneg_left hd hw
      have hs : postWeight q T ≤ ∑ t ∈ T₀, if t ∉ T then postWeight q T else 0 := by
        have hh := Finset.single_le_sum
          (f := fun t => if t ∉ T then postWeight q T else 0)
          (fun _ _ => by split <;> linarith) ht
        simpa only [if_pos hnt] using hh
      rw [if_neg hT,add_zero]
      exact (by simpa only [mul_one] using hm : postWeight q T * d T ≤ postWeight q T).trans hs
  have hs := Finset.sum_le_sum (s := (univ : Finset (Finset V))) (fun T _ => hpoint T)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at hs
  simp only [Finset.mem_univ, ↓reduceIte] at hs
  rw [Finset.sum_comm] at hs
  simp_rw [post_missing_mass] at hs
  simpa only [randomPostProb, ← Finset.sum_sub_distrib, ← mul_sub, d] using hs

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

lemma baseVertex_injective : Function.Injective (baseVertex : V × Fin 2 → (V ⊕ J) × Fin 2) := by
  intro x y h
  apply Prod.ext
  · exact Sum.inl.inj (congrArg Prod.fst h)
  · exact congrArg (fun z : (V ⊕ J) × Fin 2 => z.2) h

lemma postW_lift (q : V → ℚ) (i : Fin 2) (e : Sym2 V) :
    postW (J := J) q (Sym2.map baseVertex (liftLvl i e)) = 1/2 := by
  apply postW_other
  intro x h
  induction e using Sym2.ind with | _ a b =>
    rcases Sym2.eq_iff.1 h with hh | hh <;>
      have h0 := congrArg Prod.snd hh.1 <;>
      have h1 := congrArg Prod.snd hh.2 <;>
      simp only [baseVertex,liftLvl,Prod.snd] at h0 h1 <;> omega

lemma pendantCore_prob (E : Finset (Sym2 V)) (q : V → ℚ) (x y : V × Fin 2) :
    connProb (pendantCore (J := J) E) (postW q) (baseVertex x) (baseVertex y) =
      randomPostProb E q x y := by
  rw [pendantCore,connProb_relabel _ _ baseVertex_injective]
  exact product_connProb_posts E _ q (fun e _ => postW_lift q 0 e)
    (fun e _ => postW_lift q 1 e) (fun v => postW_post q v) x y

lemma pendantPath_edges (parent : J → V) (j : J) :
    path3Edges (pendantPath parent j) univ =
      {s((Sum.inl (parent j),(0:Fin 2)),(Sum.inr j,0)),
       s((Sum.inr j,0),(Sum.inr j,1)),
       s((Sum.inl (parent j),1),(Sum.inr j,1))} := by
  rw [path3Edges, show (univ : Finset (Fin 3)) = {0,1,2} by decide]
  simp only [Finset.image_insert,Finset.image_singleton]
  change {s((Sum.inl (parent j),(0:Fin 2)),(Sum.inr j,0)),
      s((Sum.inr j,0),(Sum.inr j,1)), s((Sum.inr j,1),(Sum.inl (parent j),1))} = _
  rw [show s((Sum.inr j,(1:Fin 2)),(Sum.inl (parent j),1)) =
      s((Sum.inl (parent j),(1:Fin 2)),(Sum.inr j,1)) from Sym2.eq_swap]

lemma complete_pendant_edges (E : Finset (Sym2 V)) (parent : J → V) :
    completeEdges (pendantEdges E parent) =
      pendantCore E ∪ univ.biUnion (fun j => path3Edges (pendantPath parent j) univ) := by
  have hposts : (univ : Finset (V ⊕ J)).image (fun x => s((x,(0:Fin 2)),(x,1))) =
      (univ : Finset V).image (basePost (J := J)) ∪
      (univ : Finset J).image (fun j => s((Sum.inr j,(0:Fin 2)),(Sum.inr j,1))) := by
    ext e
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_union]
    constructor
    · rintro ⟨x,rfl⟩; cases x with
      | inl x => exact Or.inl ⟨x,rfl⟩
      | inr j => exact Or.inr ⟨j,rfl⟩
    · rintro (⟨x,rfl⟩ | ⟨j,rfl⟩)
      · exact ⟨Sum.inl x,rfl⟩
      · exact ⟨Sum.inr j,rfl⟩
  have hmap (i : Fin 2) : (liftLvl i) ∘ (Sym2.map (Sum.inl : V → V ⊕ J)) =
      (Sym2.map baseVertex) ∘ (liftLvl i) := by
    funext e; induction e using Sym2.ind with | _ a b => rfl
  simp only [completeEdges,pendantEdges,Finset.image_union,Finset.image_image]
  rw [hposts,hmap 0,hmap 1]
  simp only [pendantCore,completeEdges,Finset.image_union,Finset.image_image,
    pendantPath_edges]
  ext e
  simp only [Finset.mem_union,Finset.mem_image,Finset.mem_biUnion,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  simp only [Function.comp_apply,basePost,liftLvl,Sym2.map_mk,baseVertex]
  aesop

/-- Exact transfer from pendant-vertex percolation to independent strengthened posts. -/
theorem completeProb_pendant (E : Finset (Sym2 V)) (parent : J → V) (x y : V × Fin 2) :
    completeProb (pendantEdges E parent) (1/2) (baseVertex x) (baseVertex y) =
      randomPostProb E (boostedQ univ parent (fun _ => 1/2)) x y := by
  have hw : postW (J := J) (fun _ : V => (1/2:ℚ)) = fun _ => 1/2 := by
    classical
    funext e
    unfold postW
    split <;> rfl
  rw [completeProb,connProbU,complete_pendant_edges,← hw,pendant_collapse,pendantCore_prob]

end Bunkbed.Complete

namespace Bunkbed.Complete
open Bunkbed Bunkbed.Hyper Bunkbed.Sub Finset SimpleGraph

lemma sub_strict_gap :
    bbProb subEdges (fun _ => (1/2:ℚ)) subT (iota 0,0) (iota 9,0) <
      bbProb subEdges (fun _ => (1/2:ℚ)) subT (iota 0,0) (iota 9,1) := by
  rw [BunkbedFalse.simulation 0 9 0, BunkbedFalse.simulation 0 9 1]
  have h0 : ∀ e, 0 ≤ gadgetW 1204 (1 / 2 : ℚ) e := by intro e; simp only [gadgetW]; split <;> norm_num
  have h1 : ∀ e, gadgetW 1204 (1 / 2 : ℚ) e ≤ 1 := by intro e; simp only [gadgetW]; split <;> norm_num
  refine BunkbedFalse.robust_hyperedge _ ?_ ?_ ?_ ?_ ?_
  · intro s
    cases s <;> simp only [Pabc,Pa_b_c,Pa_bc,Pab_c,Pac_b] <;>
      exact (BunkbedAux.probOf_mem_unitInterval _ _ h0 h1 _).1
  · have ht := BunkbedAux.partition_sum_eq_total (gadgetE 1204) (gadgetW 1204 (1/2))
      (0 : Fin 1205) 1 (Fin.last 1204)
    rw [BunkbedAux.sum_weight_eq_one] at ht
    simp only
    linarith
  · exact BunkbedFalse.gadget_eq1_at_half.1
  · exact BunkbedFalse.gadget_eq1_at_half.2.1
  · exact BunkbedFalse.gadget_eq1_at_half.2.2

lemma sub_edges_loopfree : ∀ e ∈ subEdges, ¬ e.IsDiag := by
  intro e he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.1 he
  obtain ⟨ef,hef,rfl⟩ := Finset.mem_image.1 hi
  obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.1 hef
  have hc := (Finset.mem_filter.1 hxy).2
  simp only [Prod.fst,Prod.snd] at hc ⊢
  rw [Sym2.map_mk,Sym2.mk_isDiag_iff]
  intro h
  rcases hc with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · subst x
    have hyn : 1 ≤ y.val := Nat.one_le_iff_ne_zero.2 (fun hv => hy (Fin.ext hv))
    have hz : emb i 0 ∈ subT := by rw [mem_subT]; fin_cases i <;> simp [emb,embN,hollomTr]
    exact emb_path_not_post i y hyn (h ▸ hz)
  · have hp := congrArg pathPosition h
    rw [position_emb i x hx,position_emb i y (by omega)] at hp
    omega

lemma sub_edges_card : subEdges.card = 14442 := by
  have he : (ofEdges subEdges).edgeFinset = subEdges := by
    ext e
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_fromEdgeSet]
    simp only [Set.mem_sdiff,Finset.mem_coe,Sym2.mem_diagSet]
    exact ⟨fun h => h.1, fun h => ⟨h,sub_edges_loopfree e h⟩⟩
  rw [← he]
  exact BunkbedFalse.sub_invariants.1

lemma sub_quantitative_gap :
    bbProb subEdges (fun _ => (1/2:ℚ)) subT (iota 0,0) (iota 9,0) -
      bbProb subEdges (fun _ => (1/2:ℚ)) subT (iota 0,0) (iota 9,1) ≤ -(1/2:ℚ)^28884 := by
  have h := bbProb_half_gap sub_strict_gap
  rwa [sub_edges_card] at h

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph Bunkbed.Sub

abbrev Clone := subT × Fin 216630
abbrev cloneParent (j : Clone) : Fin 7222 := j.1.val

def cloneQ (x : Fin 7222) : ℚ :=
  if x ∈ subT then 1 - (1/2:ℚ) * (7/8:ℚ)^216630 else 1/2

lemma clone_fiber (x : Fin 7222) :
    ((univ : Finset Clone).filter (fun j => cloneParent j = x)).card =
      if x ∈ subT then 216630 else 0 := by
  classical
  by_cases hx : x ∈ subT
  · rw [if_pos hx]
    let e : {j : Clone // cloneParent j = x} ≃ Fin 216630 := {
      toFun := fun j => j.1.2
      invFun := fun k => ⟨(⟨x,hx⟩,k),rfl⟩
      left_inv := fun j => by
        apply Subtype.ext
        apply Prod.ext
        · exact Subtype.ext j.2.symm
        · rfl
      right_inv := fun _ => rfl }
    simpa only [Fintype.card_subtype,Fintype.card_fin] using Fintype.card_congr e
  · rw [if_neg hx]
    apply Finset.card_eq_zero.2
    apply Finset.eq_empty_iff_forall_notMem.2
    intro j hj
    exact hx ((Finset.mem_filter.1 hj).2 ▸ j.1.property)

lemma clone_boost : boostedQ univ cloneParent (fun _ => (1/2:ℚ)) = cloneQ := by
  funext x
  rw [boostedQ,clone_fiber,cloneQ]
  split <;> norm_num

lemma cloneQ_unit : (∀ x, 0 ≤ cloneQ x) ∧ (∀ x, cloneQ x ≤ 1) := by
  have hr0 : 0 ≤ (7/8:ℚ)^216630 := pow_nonneg (by norm_num) _
  have hr1 : (7/8:ℚ)^216630 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold cloneQ
  generalize (7/8:ℚ)^216630 = r at *
  constructor <;> intro x <;> split <;> linarith

lemma clone_missing : ∑ t ∈ subT, (1-cloneQ t) = (3/2:ℚ)*(7/8:ℚ)^216630 := by
  have hc := BunkbedFalse.sub_invariants.2.1
  have h : ∀ t ∈ subT, (1-cloneQ t) = (1/2:ℚ)*(7/8:ℚ)^216630 := by
    intro t ht; rw [cloneQ,if_pos ht]; ring
  rw [Finset.sum_congr rfl h,Finset.sum_const,hc]
  norm_num
  ring

lemma clone_exact_mass : postWeight cloneQ subT =
    (1-(1/2:ℚ)*(7/8:ℚ)^216630)^3 * (1/2:ℚ)^7219 := by
  have hc := BunkbedFalse.sub_invariants.2.1
  rw [postWeight]
  have ht : ∏ v ∈ subT, cloneQ v = (1-(1/2:ℚ)*(7/8:ℚ)^216630)^3 := by
    rw [Finset.prod_congr rfl (fun v hv => show cloneQ v = _ from by rw [cloneQ,if_pos hv])]
    rw [Finset.prod_const,hc]
  have hn : ∏ v ∈ (univ : Finset (Fin 7222)) \ subT, (1-cloneQ v) = (1/2:ℚ)^7219 := by
    have hq : ∀ v ∈ (univ : Finset (Fin 7222)) \ subT, (1-cloneQ v) = (1/2:ℚ) := by
      intro v hv
      rw [cloneQ,if_neg (Finset.mem_sdiff.1 hv).2]
      norm_num
    rw [Finset.prod_congr rfl hq,Finset.prod_const,
      Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,hc]
  rw [ht,hn]

/-- The independent-post model induced by all clones has a strictly negative gap. -/
theorem clone_random_gap :
    randomPostProb subEdges cloneQ (iota 0,0) (iota 9,0) <
      randomPostProb subEdges cloneQ (iota 0,0) (iota 9,1) := by
  have hgap := randomPost_gap_bound subEdges subT (iota 0) (iota 9) cloneQ
    cloneQ_unit.1 cloneQ_unit.2 sub_extra_post
  rw [clone_missing,clone_exact_mass] at hgap
  have hd := sub_quantitative_gap
  have hn := amplification_numeric
  have hpow : (1/2:ℚ)^28884 * (1/2:ℚ)^7219 = (1/2:ℚ)^36103 := by rw [← pow_add]
  have hpos : 0 < (1/2:ℚ)^7219 := pow_pos (by norm_num) _
  have hdpos : 0 < (1/2:ℚ)^36103 := pow_pos (by norm_num) _
  have hdle : (1/2:ℚ)^36103 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr0 : 0 ≤ (7/8:ℚ)^216630 := pow_nonneg (by norm_num) _
  have hr1 : (7/8:ℚ)^216630 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  generalize (7/8:ℚ)^216630 = r at *
  generalize (1/2:ℚ)^28884 = b at *
  generalize (1/2:ℚ)^7219 = c at *
  generalize (1/2:ℚ)^36103 = d at *
  have hbern := one_add_mul_le_pow (show (-2:ℚ) ≤ -(1/2:ℚ)*r by linarith) 3
  have hA : (1/2:ℚ) ≤ (1-(1/2:ℚ)*r)^3 := by nlinarith
  have hbase :
      (bbProb subEdges (fun _ => (1/2:ℚ)) subT (iota 0,0) (iota 9,0) -
       bbProb subEdges (fun _ => (1/2:ℚ)) subT (iota 0,0) (iota 9,1)) * c ≤ -d := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hbase (show 0 ≤ (1-(1/2:ℚ)*r)^3 by linarith)
  have ha := mul_le_mul_of_nonneg_right hA (le_of_lt hdpos)
  nlinarith

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph BunkbedCompleteSupport
variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

lemma edgeFinset_le_card (E : Finset (Sym2 V)) : (ofEdges E).edgeFinset.card ≤ E.card := by
  apply Finset.card_le_card
  intro e he
  rw [SimpleGraph.mem_edgeFinset,SimpleGraph.edgeSet_fromEdgeSet] at he
  exact he.1

lemma pendant_card_le (E : Finset (Sym2 V)) (parent : J → V) :
    (pendantEdges E parent).card ≤ E.card + Fintype.card J := by
  apply (Finset.card_union_le _ _).trans
  exact Nat.add_le_add (Finset.card_image_le) (by simpa using (Finset.card_image_le
    (s := (univ : Finset J)) (f := fun j => s(Sum.inl (parent j),Sum.inr j))))

lemma pendant_connected (E : Finset (Sym2 V)) (hE : (ofEdges E).Connected) (parent : J → V) :
    (ofEdges (pendantEdges E parent)).Connected := by
  obtain ⟨u⟩ := hE.nonempty
  have hr (v : V) : (ofEdges (pendantEdges E parent)).Reachable (Sum.inl u) (Sum.inl v) := by
    exact ((reach_image Sum.inl Sum.inl_injective E u v).2 (hE.preconnected u v)).mono
      (ofEdges_mono Finset.subset_union_left)
  have hall (v : V ⊕ J) : (ofEdges (pendantEdges E parent)).Reachable (Sum.inl u) v := by
    cases v with
    | inl v => exact hr v
    | inr j =>
      apply (hr (parent j)).trans
      apply reachable_of_mem_edge
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  rw [SimpleGraph.connected_iff]
  exact ⟨fun x y => (hall x).symm.trans (hall y),⟨Sum.inl u⟩⟩

variable {W : Type*} [Fintype W] [DecidableEq W]

lemma completeEdges_relabel (E : Finset (Sym2 V)) (f : V ≃ W) :
    completeEdges (E.image (Sym2.map f)) =
      (completeEdges E).image (Sym2.map (fun x : V × Fin 2 => (f x.1,x.2))) := by
  have hmap (i : Fin 2) : liftLvl i ∘ Sym2.map f =
      Sym2.map (fun x : V × Fin 2 => (f x.1,x.2)) ∘ liftLvl i := by
    funext e; induction e using Sym2.ind with | _ a b => rfl
  unfold completeEdges
  simp only [Finset.image_union,Finset.image_image,hmap]
  congr 1
  ext e
  simp only [Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨w,rfl⟩
    exact ⟨f.symm w,by simp⟩
  · rintro ⟨v,rfl⟩
    exact ⟨f v,rfl⟩

lemma completeProb_relabel (E : Finset (Sym2 V)) (f : V ≃ W) (x y : V × Fin 2) :
    completeProb (E.image (Sym2.map f)) (1/2) (f x.1,x.2) (f y.1,y.2) =
      completeProb E (1/2) x y := by
  unfold completeProb connProbU
  rw [completeEdges_relabel]
  have hi : Function.Injective (fun x : V × Fin 2 => (f x.1,x.2)) := by
    intro a b h
    exact Prod.ext (f.injective (congrArg Prod.fst h))
      (congrArg (fun z : W × Fin 2 => z.2) h)
  exact connProb_relabel _ _ hi _ x y

lemma connected_relabel (E : Finset (Sym2 V)) (hE : (ofEdges E).Connected) (f : V ≃ W) :
    (ofEdges (E.image (Sym2.map f))).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun x y => ?_, ?_⟩
  · have h := (reach_image f f.injective E (f.symm x) (f.symm y)).2
      (hE.preconnected _ _)
    simpa using h
  · obtain ⟨x⟩ := hE.nonempty
    exact ⟨f x⟩

end Bunkbed.Complete

namespace Bunkbed.Complete
open Finset SimpleGraph Bunkbed.Sub

lemma clone_card : Fintype.card Clone = 649890 := by
  change Fintype.card (subT × Fin 216630) = _
  rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,BunkbedFalse.sub_invariants.2.1]

lemma enlarged_card : Fintype.card (Fin 7222 ⊕ Clone) = 657112 := by
  rw [Fintype.card_sum,Fintype.card_fin,clone_card]

lemma enlarged_gap :
    completeProb (pendantEdges subEdges cloneParent) (1/2)
        (baseVertex (iota 0,0)) (baseVertex (iota 9,0)) <
      completeProb (pendantEdges subEdges cloneParent) (1/2)
        (baseVertex (iota 0,0)) (baseVertex (iota 9,1)) := by
  rw [completeProb_pendant,completeProb_pendant,clone_boost]
  exact clone_random_gap

end Bunkbed.Complete

open Bunkbed Bunkbed.Sub Bunkbed.Complete Finset SimpleGraph

/-- Theorem 6.1, with an exact rational estimate in place of the decimal estimate in the source. -/
theorem solution :
    ∃ (n : ℕ) (E : Finset (Sym2 (Fin n))) (u v : Fin n),
      n < 1000000 ∧ (ofEdges E).edgeFinset.card < 1000000 ∧
      (ofEdges E).Connected ∧
      completeProb E (1 / 2) (u, 0) (v, 0) <
        completeProb E (1 / 2) (u, 0) (v, 1) := by
  classical
  let W := Fin 7222 ⊕ Clone
  let f : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let E := pendantEdges subEdges cloneParent
  refine ⟨Fintype.card W, E.image (Sym2.map f), f (Sum.inl (iota 0)), f (Sum.inl (iota 9)),
    ?_, ?_, ?_, ?_⟩
  · change Fintype.card (Fin 7222 ⊕ Clone) < 1000000
    rw [enlarged_card]; norm_num
  · have h0 := edgeFinset_le_card (E.image (Sym2.map f))
    have h1 : (E.image (Sym2.map f)).card ≤ E.card := Finset.card_image_le
    have h2 := pendant_card_le subEdges cloneParent
    rw [sub_edges_card,clone_card] at h2
    exact lt_of_le_of_lt (h0.trans (h1.trans h2)) (by norm_num)
  · exact connected_relabel E (pendant_connected subEdges BunkbedFalse.sub_invariants.2.2 cloneParent) f
  · have h0 := completeProb_relabel E f (baseVertex (iota 0,0)) (baseVertex (iota 9,0))
    have h1 := completeProb_relabel E f (baseVertex (iota 0,0)) (baseVertex (iota 9,1))
    calc
      _ = completeProb E (1/2) (baseVertex (iota 0,0)) (baseVertex (iota 9,0)) := h0
      _ < completeProb E (1/2) (baseVertex (iota 0,0)) (baseVertex (iota 9,1)) := enlarged_gap
      _ = _ := h1.symm

#print axioms solution
