-- Prove2me | solution 1 for Balinski61.Whitney.max_flow_min_cut
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T07:29:42.836081+00:00
-- url     : https://prove2.me/submissions/37c4bd98-8589-46a9-82a3-ddc4a259d10c

import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Tactic
import Definitions.Def_Balinski61_Whitney_Network

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace SolBalinski61MaxFlowMinCut

open Balinski61.Whitney
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (capV : V → ℝ) (capE : Sym2 V → ℝ) (ps pk : V)

/-! ### Section 1: Linearity, Bounds, Compactness, and Weak Duality -/

lemma loadV_linear (a b : ℝ) (f g : G.Path ps pk → ℝ) (x : V) :
    loadV G (fun C => a * f C + b * g C) x = a * loadV G f x + b * loadV G g x := by
  simp only [loadV, Finset.sum_add_distrib, Finset.mul_sum]

lemma loadE_linear (a b : ℝ) (f g : G.Path ps pk → ℝ) (e : Sym2 V) :
    loadE G (fun C => a * f C + b * g C) e = a * loadE G f e + b * loadE G g e := by
  simp only [loadE, Finset.sum_add_distrib, Finset.mul_sum]

lemma flowValue_linear (a b : ℝ) (f g : G.Path ps pk → ℝ) :
    flowValue G (fun C => a * f C + b * g C) = a * flowValue G f + b * flowValue G g := by
  simp only [flowValue, Finset.sum_add_distrib, Finset.mul_sum]

lemma loadV_shift (f : G.Path ps pk → ℝ) (C C' : G.Path ps pk) (ε : ℝ) (x : V) :
    loadV G (fun D => f D - (if D = C then ε else 0) + (if D = C' then ε else 0)) x =
      loadV G f x - (if x ∈ (C : G.Walk ps pk).support then ε else 0) +
        (if x ∈ (C' : G.Walk ps pk).support then ε else 0) := by
  simp only [loadV, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]

lemma loadE_shift (f : G.Path ps pk → ℝ) (C C' : G.Path ps pk) (ε : ℝ) (e : Sym2 V) :
    loadE G (fun D => f D - (if D = C then ε else 0) + (if D = C' then ε else 0)) e =
      loadE G f e - (if e ∈ (C : G.Walk ps pk).edges then ε else 0) +
        (if e ∈ (C' : G.Walk ps pk).edges then ε else 0) := by
  simp only [loadE, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_filter, Finset.mem_univ, true_and]

lemma flowValue_shift (f : G.Path ps pk → ℝ) (C C' : G.Path ps pk) (ε : ℝ) :
    flowValue G (fun D => f D - (if D = C then ε else 0) + (if D = C' then ε else 0)) =
      flowValue G f := by
  simp only [flowValue, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  ring

lemma loadV_add_single (f : G.Path ps pk → ℝ) (C : G.Path ps pk) (ε : ℝ) (x : V) :
    loadV G (fun D => f D + (if D = C then ε else 0)) x =
      loadV G f x + (if x ∈ (C : G.Walk ps pk).support then ε else 0) := by
  simp only [loadV, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma loadE_add_single (f : G.Path ps pk → ℝ) (C : G.Path ps pk) (ε : ℝ) (e : Sym2 V) :
    loadE G (fun D => f D + (if D = C then ε else 0)) e =
      loadE G f e + (if e ∈ (C : G.Walk ps pk).edges then ε else 0) := by
  simp only [loadE, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_filter,
    Finset.mem_univ, true_and]

lemma flowValue_add_single (f : G.Path ps pk → ℝ) (C : G.Path ps pk) (ε : ℝ) :
    flowValue G (fun D => f D + (if D = C then ε else 0)) = flowValue G f + ε := by
  simp only [flowValue, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma isFlow_combo {f g : G.Path ps pk → ℝ}
    (hf : IsFlow G capV capE ps pk f) (hg : IsFlow G capV capE ps pk g)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    IsFlow G capV capE ps pk (fun C => a * f C + b * g C) := by
  refine ⟨fun C => add_nonneg (mul_nonneg ha (hf.1 C)) (mul_nonneg hb (hg.1 C)),
    fun x => ?_, fun e he => ?_⟩
  · rw [loadV_linear]
    calc a * loadV G f x + b * loadV G g x ≤ a * capV x + b * capV x := by
          gcongr
          · exact hf.2.1 x
          · exact hg.2.1 x
      _ = capV x := by rw [← add_mul, hab, one_mul]
  · rw [loadE_linear]
    calc a * loadE G f e + b * loadE G g e ≤ a * capE e + b * capE e := by
          gcongr
          · exact hf.2.2 e he
          · exact hg.2.2 e he
      _ = capE e := by rw [← add_mul, hab, one_mul]

lemma flow_le_capV_source {f : G.Path ps pk → ℝ} (hf : IsFlow G capV capE ps pk f)
    (C : G.Path ps pk) : f C ≤ capV ps := by
  calc f C ≤ loadV G f ps := by
        unfold loadV
        exact Finset.single_le_sum (f := f) (fun D _ => hf.1 D) (by simp)
    _ ≤ capV ps := hf.2.1 ps

def IsMaxFlow (f : G.Path ps pk → ℝ) : Prop :=
  IsFlow G capV capE ps pk f ∧
    ∀ g : G.Path ps pk → ℝ, IsFlow G capV capE ps pk g → flowValue G g ≤ flowValue G f

lemma exists_isMaxFlow (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e) :
    ∃ f : G.Path ps pk → ℝ, IsMaxFlow G capV capE ps pk f := by
  classical
  set K := {f : G.Path ps pk → ℝ | IsFlow G capV capE ps pk f} with hKdef
  have hsub : K ⊆ Set.Icc 0 (fun _ => capV ps) := fun f hf =>
    ⟨fun C => hf.1 C, fun C => flow_le_capV_source G capV capE ps pk hf C⟩
  have hclosed : IsClosed K := by
    have hK : K = (⋂ C, {f : G.Path ps pk → ℝ | 0 ≤ f C}) ∩
        ((⋂ x, {f : G.Path ps pk → ℝ | loadV G f x ≤ capV x}) ∩
          ⋂ e : G.edgeSet, {f : G.Path ps pk → ℝ | loadE G f e.1 ≤ capE e.1}) := by
      ext f
      simp only [hKdef, IsFlow, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Subtype.forall]
    rw [hK]
    refine (isClosed_iInter fun C => isClosed_le continuous_const (continuous_apply C)).inter
      ((isClosed_iInter fun x => ?_).inter (isClosed_iInter fun e => ?_))
    · exact isClosed_le (continuous_finsetSum _ fun C _ => continuous_apply C) continuous_const
    · exact isClosed_le (continuous_finsetSum _ fun C _ => continuous_apply C) continuous_const
  have hcompact : IsCompact K := isCompact_Icc.of_isClosed_subset hclosed hsub
  have hzero : (0 : G.Path ps pk → ℝ) ∈ K := by
    refine ⟨fun _ => le_rfl, fun x => ?_, fun e he => ?_⟩
    · simpa [loadV] using hcapV x
    · simpa [loadE] using hcapE e he
  obtain ⟨f, hfK, hmax⟩ := hcompact.exists_isMaxOn ⟨0, hzero⟩
    (continuous_finsetSum _ fun C _ => continuous_apply C).continuousOn
  exact ⟨f, hfK, fun g hg => hmax hg⟩

lemma sum_mul_card_filter_support (f : G.Path ps pk → ℝ) (X : Finset V) :
    ∑ C : G.Path ps pk,
      f C * (X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card =
      ∑ x ∈ X, loadV G f x := by
  simp only [loadV, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, mul_one]
  rw [Finset.sum_comm' (t' := X)
    (s' := fun x => Finset.univ.filter (fun C : G.Path ps pk => x ∈ (C : G.Walk ps pk).support))]
  intro C x
  simp [and_comm]

lemma sum_mul_card_filter_edges (f : G.Path ps pk → ℝ) (F : Finset (Sym2 V)) :
    ∑ C : G.Path ps pk,
      f C * (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card =
      ∑ e ∈ F, loadE G f e := by
  simp only [loadE, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, mul_one]
  rw [Finset.sum_comm' (t' := F)
    (s' := fun e => Finset.univ.filter (fun C : G.Path ps pk => e ∈ (C : G.Walk ps pk).edges))]
  intro C e
  simp [and_comm]

lemma flowValue_le_cutValue {f : G.Path ps pk → ℝ} (hf : IsFlow G capV capE ps pk f)
    {X : Finset V} {F : Finset (Sym2 V)} (hdisc : IsDisconnecting G ps pk X F) :
    flowValue G f ≤ cutValue capV capE X F := by
  have h1 : ∀ C : G.Path ps pk,
      (1 : ℝ) ≤ (X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card +
        (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card := by
    intro C
    have hpos : 0 < (X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card +
        (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card := by
      rcases hdisc.2 C.1 with ⟨x, hxX, hxC⟩ | ⟨e, heF, heC⟩
      · have : 0 < (X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card :=
          Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxX, hxC⟩⟩
        omega
      · have : 0 < (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card :=
          Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heF, heC⟩⟩
        omega
    exact_mod_cast hpos
  calc flowValue G f
      ≤ ∑ C : G.Path ps pk,
          f C * ((X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card +
            (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card) := by
        unfold flowValue
        refine Finset.sum_le_sum fun C _ => ?_
        nlinarith [hf.1 C, h1 C]
    _ = ∑ x ∈ X, loadV G f x + ∑ e ∈ F, loadE G f e := by
        simp only [ mul_add, Finset.sum_add_distrib,
          sum_mul_card_filter_support, sum_mul_card_filter_edges]
    _ ≤ cutValue capV capE X F := by
        unfold cutValue
        gcongr with x hx e he
        · exact hf.2.1 x
        · exact hf.2.2 e (hdisc.1 e he)

/-! ### Section 2: Universally Saturated Vertices/Edges and Averaging Maximal Flows -/

def SatAllV (x : V) : Prop :=
  ∀ g : G.Path ps pk → ℝ, IsMaxFlow G capV capE ps pk g → loadV G g x = capV x

def SatAllE (e : Sym2 V) : Prop :=
  ∀ g : G.Path ps pk → ℝ, IsMaxFlow G capV capE ps pk g → loadE G g e = capE e

lemma exists_pos_le {α : Type*} (A : Finset α) (s : α → ℝ) (hs : ∀ a ∈ A, 0 < s a) :
    ∃ ε > 0, ∀ a ∈ A, ε ≤ s a := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨a₀, ha₀, hmin⟩ := A.exists_min_image s hne
    exact ⟨s a₀, hs a₀ ha₀, hmin⟩

lemma exists_slack_V {f : G.Path ps pk → ℝ} (hf : IsMaxFlow G capV capE ps pk f)
    (A : Finset V) (hA : ∀ x ∈ A, ¬ SatAllV G capV capE ps pk x) :
    ∃ g : G.Path ps pk → ℝ, IsMaxFlow G capV capE ps pk g ∧
      (∃ c > 0, ∀ C, c * f C ≤ g C) ∧
      ∀ x ∈ A, loadV G g x < capV x := by
  induction A using Finset.induction_on with
  | empty => exact ⟨f, hf, ⟨1, one_pos, fun C => by simp⟩, by simp⟩
  | insert a A ha ih =>
    obtain ⟨g, hg, ⟨c, hc, hgc⟩, hgA⟩ := ih (fun x hx => hA x (Finset.mem_insert_of_mem hx))
    have hna := hA a (Finset.mem_insert_self a A)
    simp only [SatAllV, not_forall] at hna
    obtain ⟨h, hh, hne⟩ := hna
    have hlt : loadV G h a < capV a := lt_of_le_of_ne (hh.1.2.1 a) hne
    refine ⟨fun C => (1 / 2) * g C + (1 / 2) * h C,
      ⟨isFlow_combo G capV capE ps pk hg.1 hh.1 (by norm_num) (by norm_num) (by norm_num),
        fun g' hg' => ?_⟩,
      ⟨c / 2, by positivity, fun C => ?_⟩, fun x hx => ?_⟩
    · rw [flowValue_linear]
      have := hg.2 g' hg'
      have := hh.2 g' hg'
      linarith
    · have := hgc C
      have := hh.1.1 C
      linarith
    · rw [loadV_linear]
      rcases Finset.mem_insert.mp hx with rfl | hx
      · have := hg.1.2.1 x
        linarith
      · have := hgA x hx
        have := hh.1.2.1 x
        linarith

lemma exists_slack_VE {f : G.Path ps pk → ℝ} (hf : IsMaxFlow G capV capE ps pk f)
    (A : Finset V) (hA : ∀ x ∈ A, ¬ SatAllV G capV capE ps pk x)
    (B : Finset (Sym2 V)) (hBedge : ∀ e ∈ B, e ∈ G.edgeSet)
    (hB : ∀ e ∈ B, ¬ SatAllE G capV capE ps pk e) :
    ∃ g : G.Path ps pk → ℝ, IsMaxFlow G capV capE ps pk g ∧
      (∃ c > 0, ∀ C, c * f C ≤ g C) ∧
      (∀ x ∈ A, loadV G g x < capV x) ∧
      (∀ e ∈ B, loadE G g e < capE e) := by
  induction B using Finset.induction_on with
  | empty =>
    obtain ⟨g, hg, hc, hgA⟩ := exists_slack_V G capV capE ps pk hf A hA
    exact ⟨g, hg, hc, hgA, by simp⟩
  | insert e₀ B he₀ ih =>
    obtain ⟨g, hg, ⟨c, hc, hgc⟩, hgA, hgB⟩ := ih
      (fun e he => hBedge e (Finset.mem_insert_of_mem he))
      (fun e he => hB e (Finset.mem_insert_of_mem he))
    have hne₀ := hB e₀ (Finset.mem_insert_self e₀ B)
    simp only [SatAllE, not_forall] at hne₀
    obtain ⟨h, hh, hne⟩ := hne₀
    have he₀_mem : e₀ ∈ G.edgeSet := hBedge e₀ (Finset.mem_insert_self e₀ B)
    have hlt : loadE G h e₀ < capE e₀ := lt_of_le_of_ne (hh.1.2.2 e₀ he₀_mem) hne
    refine ⟨fun C => (1 / 2) * g C + (1 / 2) * h C,
      ⟨isFlow_combo G capV capE ps pk hg.1 hh.1 (by norm_num) (by norm_num) (by norm_num),
        fun g' hg' => ?_⟩,
      ⟨c / 2, by positivity, fun C => ?_⟩, fun x hx => ?_, fun e he => ?_⟩
    · rw [flowValue_linear]
      have := hg.2 g' hg'
      have := hh.2 g' hg'
      linarith
    · have := hgc C
      have := hh.1.1 C
      linarith
    · rw [loadV_linear]
      have := hgA x hx
      have := hh.1.2.1 x
      linarith
    · rw [loadE_linear]
      rcases Finset.mem_insert.mp he with rfl | he
      · have := hg.1.2.2 e he₀_mem
        linarith
      · have := hgB e he
        have := hh.1.2.2 e (hBedge e (Finset.mem_insert_of_mem he))
        linarith

lemma exists_satAll_of_walk (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e)
    (W : G.Walk ps pk) :
    (∃ x ∈ W.support, SatAllV G capV capE ps pk x) ∨
      (∃ e ∈ W.edges, SatAllE G capV capE ps pk e) := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  rcases hcon with ⟨hnoV, hnoE⟩
  set C : G.Path ps pk := W.toPath
  have hsubV : ∀ x ∈ (C : G.Walk ps pk).support, ¬ SatAllV G capV capE ps pk x :=
    fun x hx => hnoV x (Walk.support_toPath_subset_support W hx)
  have hsubE : ∀ e ∈ (C : G.Walk ps pk).edges, ¬ SatAllE G capV capE ps pk e :=
    fun e he => hnoE e (Walk.edges_toPath_subset_edges W he)
  obtain ⟨f, hf⟩ := exists_isMaxFlow G capV capE ps pk hcapV hcapE
  obtain ⟨g, hg, -, hslackV, hslackE⟩ := exists_slack_VE G capV capE ps pk hf
    (C : G.Walk ps pk).support.toFinset (fun x hx => hsubV x (List.mem_toFinset.mp hx))
    (C : G.Walk ps pk).edges.toFinset
    (fun e he => Walk.edges_subset_edgeSet C.1 (List.mem_toFinset.mp he))
    (fun e he => hsubE e (List.mem_toFinset.mp he))
  obtain ⟨ε₁, hε₁, hε₁le⟩ := exists_pos_le (C : G.Walk ps pk).support.toFinset
    (fun x => capV x - loadV G g x)
    (fun x hx => sub_pos.mpr (hslackV x hx))
  obtain ⟨ε₂, hε₂, hε₂le⟩ := exists_pos_le (C : G.Walk ps pk).edges.toFinset
    (fun e => capE e - loadE G g e)
    (fun e he => sub_pos.mpr (hslackE e he))
  set ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  have hflow : IsFlow G capV capE ps pk (fun D => g D + (if D = C then ε else 0)) := by
    refine ⟨fun D => ?_, fun x => ?_, fun e he => ?_⟩
    · have := hg.1.1 D
      dsimp only
      split_ifs <;> linarith
    · rw [loadV_add_single]
      split_ifs with hx
      · have := hε₁le x (List.mem_toFinset.mpr hx)
        have : ε ≤ ε₁ := min_le_left _ _
        linarith
      · simpa using hg.1.2.1 x
    · rw [loadE_add_single]
      split_ifs with heC
      · have := hε₂le e (List.mem_toFinset.mpr heC)
        have : ε ≤ ε₂ := min_le_right _ _
        linarith
      · simpa using hg.1.2.2 e he
  have hle := hg.2 _ hflow
  rw [flowValue_add_single] at hle
  linarith

/-! ### Section 3: `ReachBefore`, `ReachAfter`, and the Disconnecting Set `(cutX, cutF)` -/

def ReachAfter (v : V) : Prop :=
  ∃ W : G.Walk ps v,
    (∀ x ∈ W.support, ¬ SatAllV G capV capE ps pk x) ∧
    (∀ e ∈ W.edges, ¬ SatAllE G capV capE ps pk e)

def ReachBefore (v : V) : Prop :=
  ∃ W : G.Walk ps v,
    (∀ x ∈ W.support.dropLast, ¬ SatAllV G capV capE ps pk x) ∧
    (∀ e ∈ W.edges, ¬ SatAllE G capV capE ps pk e)

lemma reachBefore_source : ReachBefore G capV capE ps pk ps :=
  ⟨Walk.nil, by simp, by simp⟩

lemma not_reachAfter_sink (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e) :
    ¬ ReachAfter G capV capE ps pk pk := by
  rintro ⟨W, hV, hE⟩
  rcases exists_satAll_of_walk G capV capE ps pk hcapV hcapE W with ⟨x, hx, hs⟩ | ⟨e, he, hs⟩
  · exact hV x hx hs
  · exact hE e he hs

lemma mem_support_dropLast_or_eq_end {u v : V} (W : G.Walk u v) {x : V} (hx : x ∈ W.support) :
    x ∈ W.support.dropLast ∨ x = v := by
  have hne : W.support ≠ [] := Walk.support_ne_nil W
  have hlast : W.support.getLast hne = v := Walk.getLast_support W
  have happ := List.dropLast_append_getLast hne
  rw [hlast] at happ
  rw [← happ, List.mem_append, List.mem_singleton] at hx
  exact hx

lemma mem_support_of_mem_dropLast {u v : V} (W : G.Walk u v) {x : V}
    (hx : x ∈ W.support.dropLast) : x ∈ W.support := by
  have hne : W.support ≠ [] := Walk.support_ne_nil W
  have happ := List.dropLast_append_getLast hne
  rw [← happ, List.mem_append]
  exact Or.inl hx

lemma reachBefore_of_reachAfter {v : V} (h : ReachAfter G capV capE ps pk v) :
    ReachBefore G capV capE ps pk v := by
  rcases h with ⟨W, hV, hE⟩
  exact ⟨W, fun x hx => hV x (mem_support_of_mem_dropLast G W hx), hE⟩

lemma not_satAllV_of_reachAfter {v : V} (h : ReachAfter G capV capE ps pk v) :
    ¬ SatAllV G capV capE ps pk v := by
  rcases h with ⟨W, hV, -⟩
  exact hV v W.end_mem_support

lemma reachAfter_of_reachBefore {v : V} (hb : ReachBefore G capV capE ps pk v)
    (hns : ¬ SatAllV G capV capE ps pk v) : ReachAfter G capV capE ps pk v := by
  rcases hb with ⟨W, hV, hE⟩
  refine ⟨W, fun x hx => ?_, hE⟩
  rcases mem_support_dropLast_or_eq_end G W hx with hx' | rfl
  · exact hV x hx'
  · exact hns

lemma reachBefore_of_reachAfter_adj {u v : V} (hu : ReachAfter G capV capE ps pk u)
    (hadj : G.Adj u v) (he : ¬ SatAllE G capV capE ps pk s(u, v)) :
    ReachBefore G capV capE ps pk v := by
  rcases hu with ⟨W, hV, hE⟩
  refine ⟨W.concat hadj, ?_, ?_⟩
  · rw [Walk.support_concat, List.dropLast_concat]
    exact hV
  · intro e he'
    rw [Walk.edges_concat, List.concat_eq_append, List.mem_append, List.mem_singleton] at he'
    rcases he' with he' | rfl
    · exact hE e he'
    · exact he

open Classical in
noncomputable def cutX : Finset V :=
  Finset.univ.filter (fun x => ReachBefore G capV capE ps pk x ∧ ¬ ReachAfter G capV capE ps pk x)

open Classical in
noncomputable def cutF : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ u w, e = s(u, w) ∧
    ReachAfter G capV capE ps pk u ∧ ¬ ReachBefore G capV capE ps pk w)

lemma satAllV_of_mem_cutX {x : V} (hx : x ∈ cutX G capV capE ps pk) :
    SatAllV G capV capE ps pk x := by
  classical
  simp only [cutX, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  by_contra hns
  exact hx.2 (reachAfter_of_reachBefore G capV capE ps pk hx.1 hns)

lemma satAllE_of_mem_cutF {e : Sym2 V} (he : e ∈ cutF G capV capE ps pk) :
    SatAllE G capV capE ps pk e := by
  classical
  simp only [cutF, Finset.mem_filter, mem_edgeFinset] at he
  rcases he with ⟨heG, u, w, rfl, hu, hnw⟩
  have hadj : G.Adj u w := by simpa [mem_edgeSet] using heG
  by_contra hns
  exact hnw (reachBefore_of_reachAfter_adj G capV capE ps pk hu hadj hns)

lemma reachAfter_end_of_avoid {u w : V} (W : G.Walk u w)
    (hu : ReachBefore G capV capE ps pk u)
    (hX : ∀ x ∈ W.support, x ∉ cutX G capV capE ps pk)
    (hF : ∀ e ∈ W.edges, e ∉ cutF G capV capE ps pk) :
    ReachAfter G capV capE ps pk w := by
  classical
  induction W with
  | @nil u =>
    have huX := hX u (by simp)
    simp only [cutX, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at huX
    exact huX hu
  | @cons u v w hadj W' ih =>
    have huX := hX u (by simp)
    simp only [cutX, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at huX
    have huAfter : ReachAfter G capV capE ps pk u := huX hu
    have heF := hF s(u, v) (by simp)
    simp only [cutF, Finset.mem_filter, mem_edgeFinset, mem_edgeSet] at heF
    have hvBefore : ReachBefore G capV capE ps pk v := by
      by_contra hnv
      exact heF ⟨hadj, u, v, rfl, huAfter, hnv⟩
    exact ih hvBefore
      (fun x hx => hX x (by simp [hx]))
      (fun e he => hF e (by simp [he]))

lemma isDisconnecting_cutXF (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e) :
    IsDisconnecting G ps pk (cutX G capV capE ps pk) (cutF G capV capE ps pk) := by
  classical
  refine ⟨fun e he => ?_, fun W => ?_⟩
  · simp only [cutF, Finset.mem_filter, mem_edgeFinset] at he
    exact he.1
  · by_contra hcon
    simp only [not_or, not_exists, not_and] at hcon
    have hX : ∀ x ∈ W.support, x ∉ cutX G capV capE ps pk := fun x hx hxX => hcon.1 x hxX hx
    have hF : ∀ e ∈ W.edges, e ∉ cutF G capV capE ps pk := fun e he heF => hcon.2 e heF he
    exact not_reachAfter_sink G capV capE ps pk hcapV hcapE
      (reachAfter_end_of_avoid G capV capE ps pk W (reachBefore_source G capV capE ps pk) hX hF)

/-! ### Section 4: Rerouting Along Positive-Flow Paths -/

lemma not_mem_dropUntil_of_mem_takeUntil_ne {u w : V} {W : G.Walk u w} (hW : W.IsPath)
    {v : V} (hv : v ∈ W.support) {x : V}
    (hx : x ∈ (W.takeUntil v hv).support) (hne : x ≠ v) :
    x ∉ (W.dropUntil v hv).support := by
  have happ : (W.takeUntil v hv).append (W.dropUntil v hv) = W := Walk.take_spec W hv
  have hnodup : W.support.Nodup := hW.support_nodup
  rw [← happ, Walk.support_append] at hnodup
  have hlast : (W.takeUntil v hv).support.getLast ((W.takeUntil v hv).support_ne_nil) = v :=
    Walk.getLast_support _
  have hsplit := List.dropLast_append_getLast ((W.takeUntil v hv).support_ne_nil)
  rw [hlast] at hsplit
  rw [← hsplit, List.mem_append, List.mem_singleton] at hx
  have hx_drop : x ∈ (W.takeUntil v hv).support.dropLast := hx.resolve_right hne
  have hhead : (W.dropUntil v hv).support = v :: (W.dropUntil v hv).support.tail := by
    conv_lhs => rw [← List.cons_head_tail ((W.dropUntil v hv).support_ne_nil)]
    rw [Walk.head_support]
  rw [← hsplit, List.append_assoc, List.singleton_append, ← hhead] at hnodup
  intro hx_in
  exact (List.nodup_append.mp hnodup).2.2 x hx_drop x hx_in rfl

lemma not_mem_edges_dropUntil_of_mem_takeUntil {u w : V} {W : G.Walk u w} (hW : W.IsPath)
    {v : V} (hv : v ∈ W.support) {e : Sym2 V} (he : e ∈ (W.takeUntil v hv).edges) :
    e ∉ (W.dropUntil v hv).edges := by
  have happ : (W.takeUntil v hv).append (W.dropUntil v hv) = W := Walk.take_spec W hv
  have hnodup : W.edges.Nodup := hW.edges_nodup
  rw [← happ, Walk.edges_append] at hnodup
  intro he_in
  exact (List.nodup_append.mp hnodup).2.2 e he e he_in rfl

lemma not_satAll_takeUntil_of_reachBefore {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0)
    {v : V} (hv : v ∈ (C : G.Walk ps pk).support)
    (hr : ReachBefore G capV capE ps pk v) :
    (∀ x₀ ∈ ((C : G.Walk ps pk).takeUntil v hv).support,
      x₀ ≠ v → ¬ SatAllV G capV capE ps pk x₀) ∧
    (∀ e₀ ∈ ((C : G.Walk ps pk).takeUntil v hv).edges,
      ¬ SatAllE G capV capE ps pk e₀) := by
  classical
  rcases hr with ⟨Q, hQV, hQE⟩
  set R_v : G.Walk v pk := (C : G.Walk ps pk).dropUntil v hv
  set W' : G.Walk ps pk := Q.append R_v
  set C' : G.Path ps pk := W'.toPath
  have hC'_V : ∀ x ∈ (C' : G.Walk ps pk).support,
      x ∈ Q.support.dropLast ∨ x ∈ R_v.support := by
    intro x hx
    have hxW' := Walk.support_toPath_subset_support W' hx
    rw [Walk.mem_support_append_iff] at hxW'
    rcases hxW' with hxQ | hxR
    · rcases mem_support_dropLast_or_eq_end G Q hxQ with hx' | rfl
      · exact Or.inl hx'
      · exact Or.inr (Walk.start_mem_support R_v)
    · exact Or.inr hxR
  have hC'_E : ∀ e ∈ (C' : G.Walk ps pk).edges,
      e ∈ Q.edges ∨ e ∈ R_v.edges := by
    intro e he
    have heW' := Walk.edges_toPath_subset_edges W' he
    rw [Walk.edges_append, List.mem_append] at heW'
    exact heW'
  obtain ⟨g, hg, ⟨c, hc, hgc⟩, hslackV, hslackE⟩ := exists_slack_VE G capV capE ps pk hf
    Q.support.dropLast.toFinset (fun x hx => hQV x (List.mem_toFinset.mp hx))
    Q.edges.toFinset
    (fun e he => Walk.edges_subset_edgeSet Q (List.mem_toFinset.mp he))
    (fun e he => hQE e (List.mem_toFinset.mp he))
  have hgC : 0 < g C := lt_of_lt_of_le
    (mul_pos hc (lt_of_le_of_ne (hf.1.1 C) (Ne.symm hpos))) (hgc C)
  obtain ⟨ε₁, hε₁, hε₁le⟩ := exists_pos_le Q.support.dropLast.toFinset
    (fun x => capV x - loadV G g x) (fun x hx => sub_pos.mpr (hslackV x hx))
  obtain ⟨ε₂, hε₂, hε₂le⟩ := exists_pos_le Q.edges.toFinset
    (fun e => capE e - loadE G g e) (fun e he => sub_pos.mpr (hslackE e he))
  set ε := min (min ε₁ ε₂) (g C)
  have hε : 0 < ε := lt_min (lt_min hε₁ hε₂) hgC
  have hε_le₁ : ε ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hε_le₂ : ε ≤ ε₂ := (min_le_left _ _).trans (min_le_right _ _)
  have hε_leC : ε ≤ g C := min_le_right _ _
  set g' : G.Path ps pk → ℝ :=
    fun D => g D - (if D = C then ε else 0) + (if D = C' then ε else 0)
  have hflow' : IsFlow G capV capE ps pk g' := by
    refine ⟨fun D => ?_, fun x => ?_, fun e he => ?_⟩
    · have := hg.1.1 D
      dsimp only [g']
      split_ifs with h1 h2 <;> (try subst h1) <;> linarith
    · dsimp only [g']
      rw [loadV_shift]
      have hle := hg.1.2.1 x
      by_cases h1 : x ∈ (C : G.Walk ps pk).support <;>
        by_cases h2 : x ∈ (C' : G.Walk ps pk).support <;>
        simp only [h1, h2, if_true, if_false]
      · linarith
      · linarith
      · rcases hC'_V x h2 with hxQ | hxR
        · have := hε₁le x (List.mem_toFinset.mpr hxQ)
          linarith
        · exact absurd (Walk.support_dropUntil_subset_support C.1 hv hxR) h1
      · linarith
    · dsimp only [g']
      rw [loadE_shift]
      have hle := hg.1.2.2 e he
      by_cases h1 : e ∈ (C : G.Walk ps pk).edges <;>
        by_cases h2 : e ∈ (C' : G.Walk ps pk).edges <;>
        simp only [h1, h2, if_true, if_false]
      · linarith
      · linarith
      · rcases hC'_E e h2 with heQ | heR
        · have := hε₂le e (List.mem_toFinset.mpr heQ)
          linarith
        · exact absurd (Walk.edges_dropUntil_subset_edges C.1 hv heR) h1
      · linarith
  have hmax' : IsMaxFlow G capV capE ps pk g' := ⟨hflow', fun g'' hg'' => by
    dsimp only [g']; rw [flowValue_shift]; exact hg.2 g'' hg''⟩
  refine ⟨fun x₀ hx₀ hne hsatV => ?_, fun e₀ he₀ hsatE => ?_⟩
  · have hx₀_C : x₀ ∈ (C : G.Walk ps pk).support :=
      Walk.support_takeUntil_subset_support C.1 hv hx₀
    have hx₀_not_C' : x₀ ∉ (C' : G.Walk ps pk).support := by
      intro hx₀'
      rcases hC'_V x₀ hx₀' with hxQ | hxR
      · exact hQV x₀ hxQ hsatV
      · exact not_mem_dropUntil_of_mem_takeUntil_ne G C.2 hv hx₀ hne hxR
    have hsat' := hsatV g' hmax'
    dsimp only [g'] at hsat'
    rw [loadV_shift, if_pos hx₀_C, if_neg hx₀_not_C'] at hsat'
    have := hg.1.2.1 x₀
    linarith
  · have he₀_C : e₀ ∈ (C : G.Walk ps pk).edges :=
      Walk.edges_takeUntil_subset_edges C.1 hv he₀
    have he₀_not_C' : e₀ ∉ (C' : G.Walk ps pk).edges := by
      intro he₀'
      rcases hC'_E e₀ he₀' with heQ | heR
      · exact hQE e₀ heQ hsatE
      · exact not_mem_edges_dropUntil_of_mem_takeUntil G C.2 hv he₀ heR
    have hsat' := hsatE g' hmax'
    dsimp only [g'] at hsat'
    rw [loadE_shift, if_pos he₀_C, if_neg he₀_not_C'] at hsat'
    have := hg.1.2.2 e₀ (Walk.edges_subset_edgeSet C.1 he₀_C)
    linarith

/-! ### Section 5: Prefix Order on a Simple Path and Unique Crossing of `(cutX, cutF)` -/

lemma mem_takeUntil_total {u w : V} (W : G.Walk u w)
    {x y : V} (hx : x ∈ W.support) (hy : y ∈ W.support) :
    x ∈ (W.takeUntil y hy).support ∨ y ∈ (W.takeUntil x hx).support := by
  induction W with
  | nil =>
    rw [Walk.mem_support_nil_iff] at hx hy
    subst hx hy
    left
    exact Walk.start_mem_support _
  | @cons u u' w hadj W' ih =>
    by_cases hux : u = x
    · subst hux; left; exact Walk.start_mem_support _
    · by_cases huy : u = y
      · subst huy; right; exact Walk.start_mem_support _
      · have hx' : x ∈ W'.support := by
          simp only [Walk.support_cons, List.mem_cons] at hx
          exact hx.resolve_left (Ne.symm hux)
        have hy' : y ∈ W'.support := by
          simp only [Walk.support_cons, List.mem_cons] at hy
          exact hy.resolve_left (Ne.symm huy)
        have htx : (Walk.cons hadj W').takeUntil x hx = (W'.takeUntil x hx').cons hadj :=
          Walk.takeUntil_cons hx' hux hadj
        have hty : (Walk.cons hadj W').takeUntil y hy = (W'.takeUntil y hy').cons hadj :=
          Walk.takeUntil_cons hy' huy hadj
        simp only [htx, hty, Walk.support_cons, List.mem_cons]
        rcases ih hx' hy' with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

lemma edge_takeUntil_step {u w : V} {W : G.Walk u w} (hW : W.IsPath)
    {a b : V} (he : s(a, b) ∈ W.edges)
    (ha : a ∈ W.support) (hb : b ∈ W.support) :
    ((W.takeUntil b hb).support = (W.takeUntil a ha).support ++ [b] ∧
      (W.takeUntil b hb).edges = (W.takeUntil a ha).edges ++ [s(a, b)]) ∨
    ((W.takeUntil a ha).support = (W.takeUntil b hb).support ++ [a] ∧
      (W.takeUntil a ha).edges = (W.takeUntil b hb).edges ++ [s(a, b)]) := by
  induction W with
  | nil => simp at he
  | @cons u u' w hadj W' ih =>
    rw [Walk.cons_isPath_iff] at hW
    rcases hW with ⟨hW', hu_not_mem⟩
    rw [Walk.edges_cons, List.mem_cons] at he
    rcases he with he_head | he_tail
    · rw [Sym2.eq_iff] at he_head
      rcases he_head with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        have hab : a ≠ b := hadj.ne
        have h2 : (Walk.cons hadj W').takeUntil b hb = Walk.cons hadj Walk.nil := by
          rw [Walk.takeUntil_cons W'.start_mem_support hab hadj, Walk.takeUntil_first]
        simp [h2]
      · right
        have hab : b ≠ a := hadj.ne
        have h2 : (Walk.cons hadj W').takeUntil a ha = Walk.cons hadj Walk.nil := by
          rw [Walk.takeUntil_cons W'.start_mem_support hab hadj, Walk.takeUntil_first]
        simp [h2, Sym2.eq_swap]
    · have ha' : a ∈ W'.support := W'.fst_mem_support_of_mem_edges he_tail
      have hb' : b ∈ W'.support := W'.snd_mem_support_of_mem_edges he_tail
      have hua : u ≠ a := fun h => hu_not_mem (h ▸ ha')
      have hub : u ≠ b := fun h => hu_not_mem (h ▸ hb')
      have hta : (Walk.cons hadj W').takeUntil a ha = (W'.takeUntil a ha').cons hadj :=
        Walk.takeUntil_cons ha' hua hadj
      have htb : (Walk.cons hadj W').takeUntil b hb = (W'.takeUntil b hb').cons hadj :=
        Walk.takeUntil_cons hb' hub hadj
      simp only [hta, htb, Walk.support_cons, Walk.edges_cons, List.cons_append]
      rcases ih hW' he_tail ha' hb' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨congrArg (u :: ·) h1, congrArg (s(u, u') :: ·) h2⟩
      · right; exact ⟨congrArg (u :: ·) h1, congrArg (s(u, u') :: ·) h2⟩

lemma reachAfter_of_mem_takeUntil_ne {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0)
    {v : V} (hv : v ∈ (C : G.Walk ps pk).support)
    (hr : ReachBefore G capV capE ps pk v)
    {x : V} (hx : x ∈ ((C : G.Walk ps pk).takeUntil v hv).support) (hne : x ≠ v) :
    ReachAfter G capV capE ps pk x := by
  obtain ⟨hnoV, hnoE⟩ := not_satAll_takeUntil_of_reachBefore G capV capE ps pk hf hpos hv hr
  have hxC : x ∈ (C : G.Walk ps pk).support := Walk.support_takeUntil_subset_support C.1 hv hx
  refine ⟨(C : G.Walk ps pk).takeUntil x hxC, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ (((C : G.Walk ps pk).takeUntil v hv).takeUntil x hx).support := by
      rwa [Walk.takeUntil_takeUntil (C : G.Walk ps pk) hv hx]
    have hz_in : z ∈ ((C : G.Walk ps pk).takeUntil v hv).support :=
      Walk.support_takeUntil_subset_support _ hx hz'
    have hzv : z ≠ v := by
      rintro rfl
      exact Walk.notMem_support_takeUntil_support_takeUntil_subset hne hv hx hz
    exact hnoV z hz_in hzv
  · intro e he
    have he' : e ∈ (((C : G.Walk ps pk).takeUntil v hv).takeUntil x hx).edges := by
      rwa [Walk.takeUntil_takeUntil (C : G.Walk ps pk) hv hx]
    exact hnoE e (Walk.edges_takeUntil_subset_edges _ hx he')

lemma reachAfter_of_mem_takeUntil_reachAfter {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0)
    {v : V} (hv : v ∈ (C : G.Walk ps pk).support)
    (hr : ReachAfter G capV capE ps pk v)
    {x : V} (hx : x ∈ ((C : G.Walk ps pk).takeUntil v hv).support) :
    ReachAfter G capV capE ps pk x := by
  by_cases hxv : x = v
  · exact hxv ▸ hr
  · exact reachAfter_of_mem_takeUntil_ne G capV capE ps pk hf hpos hv
      (reachBefore_of_reachAfter G capV capE ps pk hr) hx hxv

lemma card_cutX_inter_le_one {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0) :
    ((cutX G capV capE ps pk).filter (fun x => x ∈ (C : G.Walk ps pk).support)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x₁ hx₁ x₂ hx₂
  simp only [Finset.mem_filter, cutX, Finset.mem_univ, true_and] at hx₁ hx₂
  by_contra hne
  rcases mem_takeUntil_total G C.1 hx₁.2 hx₂.2 with h12 | h21
  · exact hx₁.1.2 (reachAfter_of_mem_takeUntil_ne G capV capE ps pk hf hpos hx₂.2 hx₂.1.1 h12 hne)
  · exact hx₂.1.2 (reachAfter_of_mem_takeUntil_ne G capV capE ps pk hf hpos hx₁.2 hx₁.1.1 h21
      (Ne.symm hne))

lemma cutF_step_of_mem_edges {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0)
    {a b : V} (he : s(a, b) ∈ (C : G.Walk ps pk).edges)
    (ha : ReachAfter G capV capE ps pk a) (hnb : ¬ ReachBefore G capV capE ps pk b) :
    ∃ (haC : a ∈ (C : G.Walk ps pk).support) (hbC : b ∈ (C : G.Walk ps pk).support),
      ((C : G.Walk ps pk).takeUntil b hbC).support =
        ((C : G.Walk ps pk).takeUntil a haC).support ++ [b] ∧
      ((C : G.Walk ps pk).takeUntil b hbC).edges =
        ((C : G.Walk ps pk).takeUntil a haC).edges ++ [s(a, b)] := by
  have haC : a ∈ (C : G.Walk ps pk).support := C.1.fst_mem_support_of_mem_edges he
  have hbC : b ∈ (C : G.Walk ps pk).support := C.1.snd_mem_support_of_mem_edges he
  refine ⟨haC, hbC, ?_⟩
  rcases edge_takeUntil_step G C.2 he haC hbC with h | h
  · exact h
  · exfalso
    have hb_in : b ∈ ((C : G.Walk ps pk).takeUntil a haC).support := by
      rw [h.1]; exact List.mem_append_left _ (Walk.end_mem_support _)
    exact hnb (reachBefore_of_reachAfter G capV capE ps pk
      (reachAfter_of_mem_takeUntil_reachAfter G capV capE ps pk hf hpos haC ha hb_in))

lemma not_cutX_and_cutF_both {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0)
    {x : V} (hx : x ∈ (cutX G capV capE ps pk).filter (fun x => x ∈ (C : G.Walk ps pk).support))
    {e : Sym2 V} (he : e ∈ (cutF G capV capE ps pk).filter (fun e => e ∈ (C : G.Walk ps pk).edges)) :
    False := by
  classical
  have he_cutF : e ∈ cutF G capV capE ps pk := (Finset.mem_filter.mp he).1
  simp only [Finset.mem_filter, cutX, cutF, Finset.mem_univ, true_and] at hx he
  rcases hx with ⟨⟨hxBefore, hnxAfter⟩, hxC⟩
  rcases he with ⟨⟨_, a, b, rfl, haAfter, hnbBefore⟩, heC⟩
  obtain ⟨haC, hbC, hsupp, hedges⟩ := cutF_step_of_mem_edges G capV capE ps pk hf hpos heC haAfter hnbBefore
  rcases mem_takeUntil_total G C.1 hxC hbC with hxb | hbx
  · rw [hsupp, List.mem_append, List.mem_singleton] at hxb
    rcases hxb with hxa | rfl
    · exact hnxAfter (reachAfter_of_mem_takeUntil_reachAfter G capV capE ps pk hf hpos haC haAfter hxa)
    · exact hnbBefore hxBefore
  · have he_in : s(a, b) ∈ ((C : G.Walk ps pk).takeUntil x hxC).edges := by
      have hsub := Walk.edges_takeUntil_subset_edges ((C : G.Walk ps pk).takeUntil x hxC) hbx
      rw [Walk.takeUntil_takeUntil (C : G.Walk ps pk) hxC hbx] at hsub
      exact hsub (by rw [hedges]; exact List.mem_append_right _ (by simp))
    have hnoE := (not_satAll_takeUntil_of_reachBefore G capV capE ps pk hf hpos hxC hxBefore).2
    exact hnoE s(a, b) he_in (satAllE_of_mem_cutF G capV capE ps pk he_cutF)

lemma card_cutF_inter_le_one {f : G.Path ps pk → ℝ}
    (hf : IsMaxFlow G capV capE ps pk f) {C : G.Path ps pk} (hpos : f C ≠ 0) :
    ((cutF G capV capE ps pk).filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro e₁ he₁ e₂ he₂
  simp only [Finset.mem_filter, cutF] at he₁ he₂
  rcases he₁ with ⟨⟨_, a₁, b₁, rfl, ha₁, hnb₁⟩, he₁C⟩
  rcases he₂ with ⟨⟨_, a₂, b₂, rfl, ha₂, hnb₂⟩, he₂C⟩
  obtain ⟨ha₁C, hb₁C, hsupp₁, -⟩ := cutF_step_of_mem_edges G capV capE ps pk hf hpos he₁C ha₁ hnb₁
  obtain ⟨ha₂C, hb₂C, hsupp₂, -⟩ := cutF_step_of_mem_edges G capV capE ps pk hf hpos he₂C ha₂ hnb₂
  have hb_eq : b₁ = b₂ := by
    rcases mem_takeUntil_total G C.1 hb₁C hb₂C with h12 | h21
    · rw [hsupp₂, List.mem_append, List.mem_singleton] at h12
      rcases h12 with h12 | h12
      · exact absurd (reachBefore_of_reachAfter G capV capE ps pk
          (reachAfter_of_mem_takeUntil_reachAfter G capV capE ps pk hf hpos ha₂C ha₂ h12)) hnb₁
      · exact h12
    · rw [hsupp₁, List.mem_append, List.mem_singleton] at h21
      rcases h21 with h21 | h21
      · exact absurd (reachBefore_of_reachAfter G capV capE ps pk
          (reachAfter_of_mem_takeUntil_reachAfter G capV capE ps pk hf hpos ha₁C ha₁ h21)) hnb₂
      · exact h21.symm
  subst hb_eq
  have hsupp_eq : ((C : G.Walk ps pk).takeUntil a₁ ha₁C).support =
      ((C : G.Walk ps pk).takeUntil a₂ ha₂C).support :=
    List.append_inj_left' (hsupp₁.symm.trans hsupp₂) rfl
  have ha_eq : a₁ = a₂ := by
    have h1 := Walk.getLast_support ((C : G.Walk ps pk).takeUntil a₁ ha₁C)
    have h2 := Walk.getLast_support ((C : G.Walk ps pk).takeUntil a₂ ha₂C)
    rw [← h1, ← h2]
    congr 1
  rw [ha_eq]

lemma card_cutXF_inter_eq_one (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e)
    {f : G.Path ps pk → ℝ} (hf : IsMaxFlow G capV capE ps pk f)
    {C : G.Path ps pk} (hpos : f C ≠ 0) :
    ((cutX G capV capE ps pk).filter (fun x => x ∈ (C : G.Walk ps pk).support)).card +
      ((cutF G capV capE ps pk).filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card = 1 := by
  classical
  set SX := (cutX G capV capE ps pk).filter (fun x => x ∈ (C : G.Walk ps pk).support)
  set SF := (cutF G capV capE ps pk).filter (fun e => e ∈ (C : G.Walk ps pk).edges)
  have hdisc := isDisconnecting_cutXF G capV capE ps pk hcapV hcapE
  have hge1 : 1 ≤ SX.card + SF.card := by
    rcases hdisc.2 C.1 with ⟨x, hxX, hxC⟩ | ⟨e, heF, heC⟩
    · have : 0 < SX.card := Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxX, hxC⟩⟩
      omega
    · have : 0 < SF.card := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heF, heC⟩⟩
      omega
  have hleX : SX.card ≤ 1 := card_cutX_inter_le_one G capV capE ps pk hf hpos
  have hleF : SF.card ≤ 1 := card_cutF_inter_le_one G capV capE ps pk hf hpos
  have hnot_both : ¬ (0 < SX.card ∧ 0 < SF.card) := by
    rintro ⟨hX, hF⟩
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hX
    obtain ⟨e, he⟩ := Finset.card_pos.mp hF
    exact not_cutX_and_cutF_both G capV capE ps pk hf hpos hx he
  omega

end SolBalinski61MaxFlowMinCut

open Balinski61.Whitney
open SolBalinski61MaxFlowMinCut

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (capV : V → ℝ) (capE : Sym2 V → ℝ) (ps pk : V)
    (_hG : G.Connected) (hcapV : ∀ x, 0 ≤ capV x) (hcapE : ∀ e ∈ G.edgeSet, 0 ≤ capE e)
    (_hst : ps ≠ pk) :
    ∃ M : ℝ,
      (∃ f : G.Path ps pk → ℝ, IsFlow G capV capE ps pk f ∧ flowValue G f = M) ∧
      (∀ f : G.Path ps pk → ℝ, IsFlow G capV capE ps pk f → flowValue G f ≤ M) ∧
      (∃ (X : Finset V) (F : Finset (Sym2 V)),
        IsDisconnecting G ps pk X F ∧ cutValue capV capE X F = M) ∧
      (∀ (X : Finset V) (F : Finset (Sym2 V)),
        IsDisconnecting G ps pk X F → M ≤ cutValue capV capE X F) := by
  classical
  obtain ⟨f, hf⟩ := exists_isMaxFlow G capV capE ps pk hcapV hcapE
  set X := cutX G capV capE ps pk
  set F := cutF G capV capE ps pk
  have hdisc : IsDisconnecting G ps pk X F := isDisconnecting_cutXF G capV capE ps pk hcapV hcapE
  have hval_eq : cutValue capV capE X F = flowValue G f := by
    have h1 : flowValue G f =
        ∑ C : G.Path ps pk,
          f C * ((X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card +
            (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card) := by
      unfold flowValue
      refine Finset.sum_congr rfl fun C _ => ?_
      by_cases h0 : f C = 0
      · simp [h0]
      · have hcard := card_cutXF_inter_eq_one G capV capE ps pk hcapV hcapE hf h0
        have hcard' : ((X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card : ℝ) +
            ((F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card : ℝ) = 1 := by
          exact_mod_cast hcard
        rw [hcard', mul_one]
    have h2 : ∑ C : G.Path ps pk,
        f C * ((X.filter (fun x => x ∈ (C : G.Walk ps pk).support)).card +
          (F.filter (fun e => e ∈ (C : G.Walk ps pk).edges)).card) =
        ∑ x ∈ X, loadV G f x + ∑ e ∈ F, loadE G f e := by
      simp only [mul_add, Finset.sum_add_distrib,
        sum_mul_card_filter_support, sum_mul_card_filter_edges]
    have h3 : ∑ x ∈ X, loadV G f x + ∑ e ∈ F, loadE G f e = cutValue capV capE X F := by
      unfold cutValue
      congr 1
      · exact Finset.sum_congr rfl fun x hx => satAllV_of_mem_cutX G capV capE ps pk hx f hf
      · exact Finset.sum_congr rfl fun e he => satAllE_of_mem_cutF G capV capE ps pk he f hf
    exact (h1.trans (h2.trans h3)).symm
  refine ⟨flowValue G f, ⟨f, hf.1, rfl⟩, fun g hg => hf.2 g hg, ⟨X, F, hdisc, hval_eq⟩,
    fun X' F' hdisc' => flowValue_le_cutValue G capV capE ps pk hf.1 hdisc'⟩
