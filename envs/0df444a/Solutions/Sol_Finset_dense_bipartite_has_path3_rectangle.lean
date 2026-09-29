-- Prove2me | solution 1 for Finset.dense_bipartite_has_path3_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T06:31:42.127785+00:00
-- url     : https://prove2.me/submissions/ff59463f-a4f9-425b-b01c-e088ce03e942

import Mathlib
import Theorems.Thm_Finset_graph_high_degree_subset_lb
import Theorems.Thm_Finset_graph_pair_dependentRandomChoice

open scoped Pointwise
namespace Finset

/--
**Pointwise count helper (step 5).** Given the witness from
`graph_dependentRandomChoice_payoff_pointwise_witness`, partition the path-3 Finset
`(B ×ˢ A).filter ((a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E)` by the
second coordinate `q.2 = a₁ ∈ U`. For `a₁` that is a popular neighbour of
`b` and a non-bad partner of `a`, the corresponding fiber has cardinality
`≥ τ`. There are at least `(δ/8)|U|` such `a₁`, giving the final bound
`(δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|²`.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_count {G : Type*} [DecidableEq G]
    (δ : ℝ) (A B : Finset G) (E : Finset (G × G)) (U A' B' : Finset G) (τ : ℝ)
    (hU_sub : U ⊆ A) (_hA'_sub_U : A' ⊆ U) (_hB'_sub : B' ⊆ B)
    (hτ_nn : 0 ≤ τ)
    (hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ)
    (hbadPartner : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ))
    (hpopCol : ∀ b ∈ B',
      (δ / 4) * (U.card : ℝ) ≤
        ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ))
    (a : G) (ha : a ∈ A') (b : G) (hb : b ∈ B') :
    (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
      (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- "Popular neighbours of b in U" and "non-bad partners of a in U".
  set Nb : Finset G := U.filter (fun a₁ ↦ (a₁, b) ∈ E) with hNb_def
  set Bad : Finset G := U.filter (fun a₁ ↦
    ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ) with hBad_def
  have hNb_lb : (δ / 4) * (U.card : ℝ) ≤ (Nb.card : ℝ) := hpopCol b hb
  have hBad_ub : (Bad.card : ℝ) ≤ (δ / 8) * (U.card : ℝ) := hbadPartner a ha
  -- Good := Nb \ Bad.  |Good| ≥ |Nb| - |Bad| ≥ (δ/8)|U|.
  set Good : Finset G := Nb \ Bad with hGood_def
  have hGood_sub_Nb : Good ⊆ Nb := Finset.sdiff_subset
  have hNb_sub_U : Nb ⊆ U := Finset.filter_subset _ _
  have hGood_sub_U : Good ⊆ U := hGood_sub_Nb.trans hNb_sub_U
  have hGood_card_lb : (δ / 8) * (U.card : ℝ) ≤ (Good.card : ℝ) := by
    -- |Nb \ Bad| ≥ |Nb| - |Bad|, via Nb ⊆ (Nb \ Bad) ∪ Bad.
    have hUnion : Nb ⊆ (Nb \ Bad) ∪ Bad := by
      intro x hx
      by_cases hxBad : x ∈ Bad
      · exact Finset.mem_union_right _ hxBad
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxBad⟩)
    have h1 : Nb.card ≤ ((Nb \ Bad) ∪ Bad).card := Finset.card_le_card hUnion
    have h2 : ((Nb \ Bad) ∪ Bad).card ≤ (Nb \ Bad).card + Bad.card :=
      Finset.card_union_le _ _
    have hreal : (Nb.card : ℝ) ≤ ((Nb \ Bad).card : ℝ) + (Bad.card : ℝ) := by
      have : (Nb.card : ℕ) ≤ (Nb \ Bad).card + Bad.card := le_trans h1 h2
      exact_mod_cast this
    have hGood_card_eq : ((Nb \ Bad).card : ℝ) = (Good.card : ℝ) := by
      rw [hGood_def]
    linarith [hreal, hNb_lb, hBad_ub, hGood_card_eq]
  -- For each a₁ ∈ Good: (a₁, b) ∈ E and codeg_E(a, a₁) ≥ τ.
  have hGood_codeg : ∀ a₁ ∈ Good,
      τ ≤ ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) ∧ (a₁, b) ∈ E := by
    intro a₁ ha₁
    rw [hGood_def, Finset.mem_sdiff, hNb_def, Finset.mem_filter, hBad_def,
      Finset.mem_filter] at ha₁
    obtain ⟨⟨ha₁U, ha₁bE⟩, hnotBad⟩ := ha₁
    refine ⟨?_, ha₁bE⟩
    by_contra hlt
    push Not at hlt
    exact hnotBad ⟨ha₁U, hlt⟩
  -- Path Finset of interest.
  set paths : Finset (G × G) := (B ×ˢ A).filter fun q : G × G ↦
    (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E with hpaths_def
  -- Fiber over the second coordinate: for each a₁, witness pairs (b₁, a₁).
  set fiber : G → Finset (G × G) := fun a₁ ↦
    (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).image (fun b₁ ↦ (b₁, a₁))
    with hfiber_def
  -- fiber a₁ has the same cardinality as the inner filter (image of an injection).
  have hfiber_card : ∀ a₁,
      (fiber a₁).card = (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card := by
    intro a₁
    rw [hfiber_def]
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
  -- For a₁ ∈ Good, fiber a₁ ⊆ paths.
  have hfiber_sub : ∀ a₁ ∈ Good, fiber a₁ ⊆ paths := by
    intro a₁ ha₁ p hp
    rw [hfiber_def, Finset.mem_image] at hp
    obtain ⟨b₁, hb₁, hpeq⟩ := hp
    rw [Finset.mem_filter] at hb₁
    obtain ⟨hb₁B, habE, ha₁b₁E⟩ := hb₁
    have ha₁U : a₁ ∈ U := hGood_sub_U ha₁
    have ha₁A : a₁ ∈ A := hU_sub ha₁U
    obtain ⟨_, ha₁bE⟩ := hGood_codeg a₁ ha₁
    rw [hpaths_def, Finset.mem_filter, Finset.mem_product]
    rw [← hpeq]
    exact ⟨⟨hb₁B, ha₁A⟩, habE, ha₁b₁E, ha₁bE⟩
  -- Pairwise disjointness of fibers (different a₁ → different second coord).
  have hfiber_disjoint : (Good : Set G).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro p hpx hpy
    rw [hfiber_def, Finset.mem_image] at hpx hpy
    obtain ⟨bx, _, hpx_eq⟩ := hpx
    obtain ⟨by_, _, hpy_eq⟩ := hpy
    have hsnd : p.2 = x := by rw [← hpx_eq]
    have hsnd' : p.2 = y := by rw [← hpy_eq]
    exact hxy (hsnd.symm.trans hsnd')
  -- |⋃_{a₁ ∈ Good} fiber a₁| = Σ_{a₁ ∈ Good} |fiber a₁|.
  have hbiUnion_card : (Good.biUnion fiber).card = ∑ a₁ ∈ Good, (fiber a₁).card := by
    exact Finset.card_biUnion (fun x hx y hy hxy ↦ hfiber_disjoint hx hy hxy)
  -- The biUnion is contained in paths.
  have hbiUnion_sub : Good.biUnion fiber ⊆ paths := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    exact hfiber_sub a₁ ha₁ hp
  have hcard_path_lb : (∑ a₁ ∈ Good, (fiber a₁).card : ℕ) ≤ paths.card := by
    calc (∑ a₁ ∈ Good, (fiber a₁).card : ℕ)
        = (Good.biUnion fiber).card := hbiUnion_card.symm
      _ ≤ paths.card := Finset.card_le_card hbiUnion_sub
  have hcard_path_lb_real : (∑ a₁ ∈ Good, ((fiber a₁).card : ℝ)) ≤ (paths.card : ℝ) := by
    have h : ((∑ a₁ ∈ Good, (fiber a₁).card : ℕ) : ℝ) ≤ (paths.card : ℝ) := by
      exact_mod_cast hcard_path_lb
    push_cast at h; exact h
  -- Σ_{a₁ ∈ Good} |fiber a₁| ≥ |Good| · τ.
  have hsum_lb : (Good.card : ℝ) * τ ≤ ∑ a₁ ∈ Good, ((fiber a₁).card : ℝ) := by
    rw [show (Good.card : ℝ) * τ = ∑ _a₁ ∈ Good, τ from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a₁ ha₁ ↦ ?_
    have hcard := hfiber_card a₁
    have hcodeg := (hGood_codeg a₁ ha₁).1
    have : ((fiber a₁).card : ℝ) =
        ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) := by
      exact_mod_cast hcard
    rw [this]
    exact hcodeg
  -- Combine: paths ≥ |Good| · τ ≥ (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  have hGood_τ : (δ / 8) * (U.card : ℝ) * τ ≤ (Good.card : ℝ) * τ :=
    mul_le_mul_of_nonneg_right hGood_card_lb hτ_nn
  linarith [hUτ_bound, hGood_τ, hsum_lb, hcard_path_lb_real]

/--
**Popular columns helper.** For `U ⊆ A` with row degree `≥ ρ · |B|` for every
`a ∈ U` (in the sense of `|{b ∈ B : (a, b) ∈ E}| ≥ ρ · |B|`), the rare/popular
split on columns produces `B' ⊆ B` of cardinality `≥ (ρ/2) · |B|` such that
every `b ∈ B'` has `|{a ∈ U : (a, b) ∈ E}| ≥ (ρ/2) · |U|`.
-/
private lemma graph_dependentRandomChoice_popular_columns {G : Type*} [DecidableEq G]
    (A B : Finset G) (hAB : A.card = B.card)
    (E : Finset (G × G)) (_hE_sub : E ⊆ A ×ˢ B)
    (U : Finset G) (hU_sub : U ⊆ A)
    (hU_pos : (0 : ℝ) < (U.card : ℝ))
    (ρ : ℝ) (hρ_pos : 0 < ρ) (_hρ_le_one : ρ ≤ 1)
    (hrowDeg_lb : ∀ a ∈ U, ρ * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      (∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤
        ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ)) := by
  classical
  -- |B| > 0 since |B| = |A| and U ⊆ A nonempty.
  have hBcard_nat : B.card = A.card := hAB.symm
  have hUcard_le_A : (U.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hU_sub
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le hU_pos hUcard_le_A
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
    rw [this]; exact hA_pos
  -- Column count.
  set colCount : G → ℕ := fun b ↦ (U.filter (fun a ↦ (a, b) ∈ E)).card with hcolCount_def
  set B' : Finset G := B.filter (fun b ↦ (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ)) with hB'_def
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  -- Edge count from U: Σ_a∈U rowDeg(a) ≥ ρ|U||B|.  Also = Σ_b colCount b.
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  -- Σ over U of rowDeg = Σ over B of colCount: both count {(a, b) ∈ U × B : (a, b) ∈ E}.
  have hSwap : ∑ a ∈ U, (rowDeg a : ℕ) = ∑ b ∈ B, (colCount b : ℕ) := by
    have hrowDeg_eq : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcolCount_eq : ∀ b, colCount b = ∑ a ∈ U, (if (a, b) ∈ E then 1 else 0) := fun b ↦ by
      simp only [colCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [hrowDeg_eq, hcolCount_eq]
    rw [Finset.sum_comm]
  have hSwap_real :
      ∑ a ∈ U, (rowDeg a : ℝ) = ∑ b ∈ B, (colCount b : ℝ) := by
    have : ((∑ a ∈ U, rowDeg a : ℕ) : ℝ) = ((∑ b ∈ B, colCount b : ℕ) : ℝ) := by
      exact_mod_cast hSwap
    push_cast at this; exact this
  -- Σ_{a ∈ U} rowDeg(a) ≥ ρ|U||B|.
  have hrow_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) := by
    have hsum : ∑ _a ∈ U, ρ * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) :=
      Finset.sum_le_sum fun a haU ↦ hrowDeg_lb a haU
    have hconst : ∑ _a ∈ U, ρ * (B.card : ℝ) = (U.card : ℝ) * (ρ * (B.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst] at hsum
    linarith
  have hcol_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ b ∈ B, (colCount b : ℝ) := by
    rw [← hSwap_real]; exact hrow_sum_lb
  -- Rare columns contribute < (ρ/2)|U| each.
  have hrare_col : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    rw [show ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) =
            ∑ _b ∈ B \ B', ((ρ / 2) * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun b hb ↦ ?_
    rw [Finset.mem_sdiff, hB'_def, Finset.mem_filter] at hb
    have hnot := hb.2
    by_contra hgt
    push Not at hgt
    exact hnot ⟨hb.1, le_of_lt hgt⟩
  have hrare_col' : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      (B.card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    have h : ((B \ B').card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := B) (t := B'))
    have hnn : 0 ≤ (ρ / 2) * (U.card : ℝ) := by
      have : 0 ≤ ρ / 2 := by linarith
      exact mul_nonneg this (le_of_lt hU_pos)
    have := mul_le_mul_of_nonneg_right h hnn
    linarith
  -- Split column-sum.
  have hcol_split : ∑ b ∈ B, (colCount b : ℝ) =
      (∑ b ∈ B', (colCount b : ℝ)) + ∑ b ∈ B \ B', (colCount b : ℝ) := by
    rw [← Finset.sum_sdiff hB'_sub]; ring
  have hpop_col_lb : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
      ∑ b ∈ B', (colCount b : ℝ) := by
    nlinarith [hcol_split, hcol_sum_lb, hrare_col']
  -- Σ over B' of colCount ≤ |B'| · |U|.
  have hcolCount_le : ∀ b, (colCount b : ℝ) ≤ (U.card : ℝ) := fun b ↦ by
    have h : (colCount b : ℕ) ≤ U.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast h
  have hpop_col_ub : ∑ b ∈ B', (colCount b : ℝ) ≤ (B'.card : ℝ) * (U.card : ℝ) := by
    rw [show (B'.card : ℝ) * (U.card : ℝ) = ∑ _b ∈ B', (U.card : ℝ) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun b _ ↦ hcolCount_le b
  -- Divide through by |U|.
  have hB'_lb : (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    have hchain : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
        (B'.card : ℝ) * (U.card : ℝ) := le_trans hpop_col_lb hpop_col_ub
    have hrew : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) =
        ((ρ / 2) * (B.card : ℝ)) * (U.card : ℝ) := by ring
    rw [hrew] at hchain
    exact le_of_mul_le_mul_right hchain hU_pos
  have hpop_col_prop : ∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ) := by
    intro b hb
    rw [hB'_def, Finset.mem_filter] at hb
    exact hb.2
  exact ⟨B', hB'_sub, hB'_lb, hpop_col_prop⟩

/--
**Markov refinement helper.** Given `U` and a bad-pair count bound
`#{(a, a') ∈ U×U : codeg_E(a, a') < τ} ≤ κ · |U|²`, produce
`A' ⊆ U` with `|A'| ≥ |U|/2` (when `κ ≤ 1/4`) such that for every
`a ∈ A'` the bad-partner count `#{a' ∈ U : codeg_E(a, a') < τ}` is
`≤ 2κ · |U|`.  Used inside `graph_dependentRandomChoice_payoff_pointwise_witness` with
`κ := δ/16`, giving `2κ = δ/8`.
-/
private lemma graph_dependentRandomChoice_markov_refinement {G : Type*} [DecidableEq G]
    (B U : Finset G) (E : Finset (G × G)) (τ : ℝ) (κ : ℝ)
    (hκ_pos : 0 < κ) (hUpos : (0 : ℝ) < (U.card : ℝ))
    (hbadCount : (((U ×ˢ U).filter fun p : G × G ↦
        ((B.filter fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
      ≤ κ * (U.card : ℝ) ^ 2) :
    ∃ A' : Finset G, A' ⊆ U ∧
      (1 - 1 / 2) * (U.card : ℝ) ≤ (A'.card : ℝ) ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ 2 * κ * (U.card : ℝ)) := by
  classical
  -- Bad partners of `a` in U.
  set badPartner : G → Finset G := fun a ↦
    U.filter (fun a₁ ↦
      ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPartner_def
  set A' : Finset G := U.filter (fun a ↦
    ((badPartner a).card : ℝ) ≤ 2 * κ * (U.card : ℝ)) with hA'_def
  have hA'_sub : A' ⊆ U := Finset.filter_subset _ _
  -- Sum of bad-partner cards equals bad-pair count (fiber over first coord).
  set badPairs : Finset (G × G) := (U ×ˢ U).filter (fun p : G × G ↦
    ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPairs_def
  have hbadSum : (badPairs.card : ℝ) = ∑ a ∈ U, ((badPartner a).card : ℝ) := by
    have hN : badPairs.card = ∑ a ∈ U, (badPartner a).card := by
      rw [hbadPairs_def, hbadPartner_def]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcast : ((∑ a ∈ U, (badPartner a).card : ℕ) : ℝ) = (badPairs.card : ℝ) := by
      exact_mod_cast hN.symm
    push_cast at hcast; linarith
  -- Markov lower bound on Σ over U \ A'.
  have hsum_split :
      ∑ a ∈ U, ((badPartner a).card : ℝ) =
        (∑ a ∈ A', ((badPartner a).card : ℝ)) +
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [← Finset.sum_sdiff hA'_sub]; ring
  have hsum_diff_ge :
      ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [show ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) =
            ∑ _a ∈ U \ A', (2 * κ * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hA'_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hge
    push Not at hge
    exact hnot ⟨ha.1, le_of_lt hge⟩
  have hpartner_nn : ∀ a, 0 ≤ ((badPartner a).card : ℝ) := fun a ↦ Nat.cast_nonneg _
  have hsum_A'_nn : 0 ≤ ∑ a ∈ A', ((badPartner a).card : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ hpartner_nn a
  -- Combine: |U\A'| · 2κ|U| ≤ Σ over U ≤ |badPairs| ≤ κ|U|².  Hence |U\A'| ≤ |U|/2.
  have hdiff_card_le : ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
      κ * (U.card : ℝ) ^ 2 := by
    calc ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ))
        ≤ ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := hsum_diff_ge
      _ ≤ ∑ a ∈ U, ((badPartner a).card : ℝ) := by linarith
      _ = (badPairs.card : ℝ) := hbadSum.symm
      _ ≤ κ * (U.card : ℝ) ^ 2 := hbadCount
  have hcoeff_pos : 0 < 2 * κ * (U.card : ℝ) := by positivity
  have hdiff_le_half : ((U \ A').card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have heq : κ * (U.card : ℝ) ^ 2 = ((U.card : ℝ) / 2) * (2 * κ * (U.card : ℝ)) := by ring
    rw [heq] at hdiff_card_le
    exact le_of_mul_le_mul_right hdiff_card_le hcoeff_pos
  have hA'_card_real : ((U \ A').card : ℝ) + (A'.card : ℝ) = (U.card : ℝ) := by
    have h : (U \ A').card + A'.card = U.card := Finset.card_sdiff_add_card_eq_card hA'_sub
    exact_mod_cast h
  have hA'_lb : (U.card : ℝ) / 2 ≤ (A'.card : ℝ) := by linarith
  refine ⟨A', hA'_sub, ?_, ?_⟩
  · linarith
  · intro a ha
    rw [hA'_def, Finset.mem_filter] at ha
    exact ha.2

/--
**Witness for the DRC pointwise payoff (steps 1-4).** Internal helper.
Composes `graph_high_degree_subset_lb` (rare/popular row split) with
`graph_pair_dependentRandomChoice` (Fox-Sudakov 5.1 pair-DRC) and a Markov + rare/popular
column split.  Returns the four pieces needed by the pointwise count
step: a "core" set `U ⊆ A`, the "non-bad" refinement `A' ⊆ U`, the
"popular column" refinement `B' ⊆ B`, and the codegree threshold
`τ ≥ 0` that interpolates the bad-partner bound for `a ∈ A'` and the
final `(δ⁵/2¹²)|A|²` count.

The arithmetic identity `(δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ` is established
here (using `m := |Apop|`-relative density and `|U| · τ`-style
cancellation) so the count helper need not redo it.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_witness {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ U A' B' : Finset G, ∃ τ : ℝ,
      U ⊆ A ∧ A' ⊆ U ∧ B' ⊆ B ∧
      0 ≤ τ ∧
      (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ (δ / 8) * (U.card : ℝ)) ∧
      (∀ b ∈ B',
        (δ / 4) * (U.card : ℝ) ≤
          ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ)) := by
  classical
  -- Cardinality positivity.
  have hApos : 0 < A.card := hA.card_pos
  have hA_real_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_real_pos
  have hBcard_nat : B.card = A.card := hAB.symm
  have hB_real_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
  have hB_real_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hB_real_eq]; exact hA_real_pos
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; rw [hBcard_nat]; exact hApos
  -- δ bounds.
  have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
  -- Step 1: apply rare/popular row split.
  obtain ⟨hApop_lb, hEpop_lb⟩ :=
    graph_high_degree_subset_lb δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  -- Define A₁ (popular rows) and E₁ (edges with popular first coord).
  set A₁ : Finset G := A.filter (fun a ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) with hA₁_def
  have hA₁_sub : A₁ ⊆ A := Finset.filter_subset _ _
  -- |A₁| ≥ (δ/2)|A| > 0, so A₁ is nonempty.
  have hA₁_card_pos : (0 : ℝ) < (A₁.card : ℝ) := by
    have : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    linarith
  have hA₁_card_pos_nat : 0 < A₁.card := by exact_mod_cast hA₁_card_pos
  have hA₁_ne : A₁.Nonempty := Finset.card_pos.mp hA₁_card_pos_nat
  set E₁ : Finset (G × G) := E.filter (fun p ↦ p.1 ∈ A₁) with hE₁_def
  have hE₁_sub_E : E₁ ⊆ E := Finset.filter_subset _ _
  -- E₁ characterisation: edges with first coord in A₁.
  have hE₁_iff : ∀ p, p ∈ E₁ ↔ p ∈ E ∧ p.1 ∈ A₁ := fun p ↦ by
    simp [E₁, Finset.mem_filter]
  -- E₁ ⊆ A₁ ×ˢ B.
  have hE₁_sub : E₁ ⊆ A₁ ×ˢ B := by
    intro p hp
    rw [hE₁_iff] at hp
    obtain ⟨hpE, hpA₁⟩ := hp
    have hpAB := hE_sub hpE
    rw [Finset.mem_product] at hpAB ⊢
    exact ⟨hpA₁, hpAB.2⟩
  -- The edge count for E₁: this matches the popular-edge form of `graph_high_degree_subset_lb`.
  -- |E₁| = |E.filter (popular first coord)| ≥ (δ/2)·|A|·|B|.
  have hE₁_card_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    -- The popular-edge filter from `graph_high_degree_subset_lb` matches E₁:
    --   E.filter (popular p.1) = E.filter (p.1 ∈ A₁)
    have hfilter_eq :
        E.filter (fun p : G × G ↦
          (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ)) = E₁ := by
      ext p
      simp only [E₁, Finset.mem_filter, hA₁_def]
      constructor
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨hpE, hpAB.1, hpop⟩
      · rintro ⟨hpE, _, hpop⟩
        exact ⟨hpE, hpop⟩
    rw [← hfilter_eq]; exact hEpop_lb
  -- Step 2: invoke graph_pair_dependentRandomChoice on (A₁, B, E₁) with density c₀ = (δ/2)|A|/|A₁|.
  set m : ℝ := (A₁.card : ℝ) with hm_def
  have hm_pos : 0 < m := hA₁_card_pos
  have hm_le_A : m ≤ (A.card : ℝ) := by
    have : (A₁.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA₁_sub
    exact this
  -- Density c₀ for pair-DRC: c₀ * m * |B| = (δ/2) * |A| * |B|.
  set c₀ : ℝ := (δ / 2) * (A.card : ℝ) / m with hc₀_def
  have hc₀_pos : 0 < c₀ := by
    have hnum : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    exact div_pos hnum hm_pos
  -- c₀ ≤ 1, because (δ/2)|A| ≤ m (= |A₁|).
  have hc₀_le_one : c₀ ≤ 1 := by
    rw [hc₀_def]
    rw [div_le_one hm_pos]
    exact hApop_lb
  -- c₀ * |A₁| = (δ/2) * |A|.
  have hc₀_mul_m : c₀ * m = (δ / 2) * (A.card : ℝ) := by
    rw [hc₀_def]; field_simp
  -- Density hypothesis for graph_pair_dependentRandomChoice.
  have hF_dense_drc : c₀ * (A₁.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    have : c₀ * (A₁.card : ℝ) * (B.card : ℝ) = (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by
      rw [show (A₁.card : ℝ) = m from rfl]; rw [hc₀_mul_m]
    rw [this]; exact hE₁_card_lb
  -- ε = δ/16.
  set ε : ℝ := δ / 16 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_le_one : ε ≤ 1 := by
    rw [hε_def]; linarith
  -- Invoke graph_pair_dependentRandomChoice.
  obtain ⟨U, hU_sub_A₁, hU_card_lb_drc, hbad_card_le⟩ :=
    graph_pair_dependentRandomChoice A₁ B hA₁_ne hB E₁ hE₁_sub c₀ hc₀_pos hc₀_le_one hF_dense_drc
      ε hε_pos hε_le_one
  have hU_sub : U ⊆ A := hU_sub_A₁.trans hA₁_sub
  -- (c₀/2) * |A₁| = (δ/4) * |A|.
  have hU_card_lb : (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) := by
    have heq : c₀ / 2 * (A₁.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      have := hc₀_mul_m
      rw [show (A₁.card : ℝ) = m from rfl]
      linarith
    linarith [hU_card_lb_drc, heq]
  have hU_card_pos : (0 : ℝ) < (U.card : ℝ) := by
    have : 0 < (δ / 4) * (A.card : ℝ) := by positivity
    linarith
  have hU_card_pos_nat : 0 < U.card := by exact_mod_cast hU_card_pos
  have hU_ne : U.Nonempty := Finset.card_pos.mp hU_card_pos_nat
  -- τ_drc = (ε * c₀²/2) * |B|.  Goal `τ := τ_drc`.
  set τ : ℝ := (ε * c₀ ^ 2 / 2) * (B.card : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by
    rw [hτ_def]
    have h1 : 0 ≤ ε * c₀ ^ 2 / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_real_pos
    exact mul_nonneg h1 h2
  -- The arithmetic identity: (δ⁵/2¹²)|A|² ≤ (δ/8) · |U| · τ.
  -- We use: (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A|, and τ ≥ ?
  -- Key: τ = (δ/16)·c₀²/2·|B| = (δ/32)·c₀²·|A|.
  -- And c₀² · |A₁|² = (δ/2)² · |A|², so c₀² = δ²|A|²/(4·m²).
  -- Hence τ · m² = (δ/32) · (δ²/4) · |A|³ = δ³|A|³/128.
  -- Want: (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  -- Using |U| ≥ (δ/4)|A| and τ ≥ (δ³/2⁷)|A| (since m ≤ |A|, so |A|³/m² ≥ |A|).
  have hτ_lb : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) ≤ τ := by
    -- τ = (δ/16) · c₀² / 2 · |B| = (δ/32) · c₀² · |A|.
    -- c₀ · m = (δ/2)|A|, so c₀² · m² = δ²|A|²/4.
    -- τ · m² = (δ/32) · δ²|A|²/4 · |A| = δ³|A|³/128.
    -- τ = δ³|A|³ / (128 m²).  Since m ≤ |A|: τ ≥ δ³|A|/128.
    have hc₀sq : c₀ ^ 2 * m ^ 2 = ((δ / 2) * (A.card : ℝ)) ^ 2 := by
      have h := hc₀_mul_m
      calc c₀ ^ 2 * m ^ 2 = (c₀ * m) ^ 2 := by ring
        _ = ((δ / 2) * (A.card : ℝ)) ^ 2 := by rw [h]
    have hm_sq_pos : 0 < m ^ 2 := by positivity
    have hm_sq_le : m ^ 2 ≤ (A.card : ℝ) ^ 2 := by
      have hm_nn : 0 ≤ m := le_of_lt hm_pos
      exact pow_le_pow_left₀ hm_nn hm_le_A 2
    -- τ * m² = (ε * c₀²/2) * |B| * m² = (ε / 2) * (c₀² · m²) * |B|
    --        = (δ / 32) * ((δ/2)|A|)² * |A| = δ³|A|³/128.
    have hτ_m_sq : τ * m ^ 2 = δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by
      have : τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ) := hτ_def
      rw [this, hB_real_eq, hε_def]
      have : (δ / 16 * c₀ ^ 2 / 2) * (A.card : ℝ) * m ^ 2
          = (δ / 32) * (c₀ ^ 2 * m ^ 2) * (A.card : ℝ) := by ring
      rw [this, hc₀sq]
      ring
    -- (δ³/2⁷)|A| · m² ≤ τ · m² ↔ (δ³/2⁷)|A| ≤ τ if m² > 0.
    -- Use (δ³/2⁷)|A| · m² ≤ (δ³/2⁷)|A| · |A|² = (δ³/128)|A|³ = τ · m².
    have hineq : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤ τ * m ^ 2 := by
      rw [hτ_m_sq]
      have : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤
            (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 := by
        have hLcoeff_nn : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hm_sq_le hLcoeff_nn
      have heq2 : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 =
          δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by ring
      linarith
    exact le_of_mul_le_mul_right hineq hm_sq_pos
  -- Now establish the bound (δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ via
  -- (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A| and τ ≥ δ³/128 · |A|, product ≥ δ⁵|A|²/2¹².
  have hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ := by
    have h1 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) ≤ (δ / 8) * (U.card : ℝ) := by
      have h8 : (0 : ℝ) ≤ δ / 8 := by linarith
      exact mul_le_mul_of_nonneg_left hU_card_lb h8
    have h2 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) ≤
        (δ / 8) * (U.card : ℝ) * τ := by
      have hLHS_nn : 0 ≤ (δ / 8) * ((δ / 4) * (A.card : ℝ)) := by positivity
      have hLHS_nn' : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
      exact mul_le_mul h1 hτ_lb hLHS_nn' (le_trans hLHS_nn h1)
    have hrew : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) =
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 := by ring
    linarith
  -- Bad-pair count in U using the E-codegree.  It is bounded by the E₁-bad count from
  -- graph_pair_dependentRandomChoice, since codeg_E ≥ codeg_{E₁}.
  have hbadCountE : (((U ×ˢ U).filter fun p : G × G ↦
      ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ)
    ≤ ε * (U.card : ℝ) ^ 2 := by
    -- Pointwise: codeg_E(p) < τ ⟹ codeg_{E₁}(p) ≤ codeg_E(p) < τ.
    have hbadE_sub : ((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ) ⊆
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hsub : (B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
                  (B.filter (fun y ↦ (p.2, y) ∈ E₁)) ⊆
                  B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_filter] at hy
        simp only [Finset.mem_filter]
        exact ⟨hy.1.1, hE₁_sub_E hy.1.2, hE₁_sub_E hy.2.2⟩
      have hcard : (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
          (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) ≤
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hp.2]
    have h := Finset.card_le_card hbadE_sub
    have hreal : (((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ) ≤
        (((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ).card : ℝ) := by
      exact_mod_cast h
    -- `τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ)` by definition; substitute.
    have hfilter_eq :
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) =
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) <
          (ε * c₀ ^ 2 / 2) * (B.card : ℝ)) := by rfl
    rw [hfilter_eq] at hreal
    linarith
  -- Apply Markov refinement helper.
  obtain ⟨A', hA'_sub_U, hA'_half, hA'_prop⟩ :=
    graph_dependentRandomChoice_markov_refinement (G := G) B U E τ ε hε_pos hU_card_pos hbadCountE
  -- `hA'_half`: (1 - 1/2) * |U| ≤ |A'|, i.e. |U|/2 ≤ |A'|.
  -- `hA'_prop`: ∀ a ∈ A', ((badPartner a).card : ℝ) ≤ 2ε|U| = (δ/8)|U|.
  -- So we get the (δ/8)|U| bound directly: 2 * (δ/16) = δ/8.
  have htwo_eps : (2 : ℝ) * ε = δ / 8 := by rw [hε_def]; ring
  have hA'_prop_clean : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ) := by
    intro a ha
    have h := hA'_prop a ha
    have hrew : (2 * ε * (U.card : ℝ)) = (δ / 8) * (U.card : ℝ) := by
      rw [show (2 * ε * (U.card : ℝ)) = 2 * ε * (U.card : ℝ) from rfl, htwo_eps]
    linarith [hrew]
  -- |A'| ≥ |U|/2 ≥ (δ/8)|A|.
  have hA'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) := by
    have h1 : (δ / 8) * (A.card : ℝ) ≤ (U.card : ℝ) / 2 := by linarith [hU_card_lb]
    have : (1 - 1 / 2) * (U.card : ℝ) = (U.card : ℝ) / 2 := by ring
    linarith [hA'_half, this]
  -- Step 4: popular columns via `graph_dependentRandomChoice_popular_columns`.
  -- Row-degree lower bound for a ∈ U (which is ⊆ A₁): rowDeg_E(a) ≥ (δ/2)|B|.
  have hrowDeg_lb : ∀ a ∈ U, (δ / 2) * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ) := by
    intro a haU
    have haA₁ : a ∈ A₁ := hU_sub_A₁ haU
    rw [hA₁_def, Finset.mem_filter] at haA₁
    exact haA₁.2
  -- δ/2 > 0 and ≤ 1 since δ ≤ 1.
  have hρ_pos : (0 : ℝ) < δ / 2 := by positivity
  have hρ_le : δ / 2 ≤ 1 := by linarith
  obtain ⟨B', hB'_sub, hB'_lb_drc, hpopCol⟩ :=
    graph_dependentRandomChoice_popular_columns (G := G) A B hAB E hE_sub U hU_sub hU_card_pos
      (δ / 2) hρ_pos hρ_le hrowDeg_lb
  -- (δ/2)/2 = δ/4. So |B'| ≥ (δ/4)|B| = (δ/4)|A| ≥ (δ/8)|A|.
  have hB'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) := by
    have h3 : (δ / 8) * (A.card : ℝ) ≤ (δ / 4) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hA_nn
    have hquarter_eq : (δ / 2) / 2 * (B.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      rw [hB_real_eq]; ring
    linarith [hB'_lb_drc, hquarter_eq]
  -- Popular-column property: for b ∈ B', (δ/4)|U| ≤ |{a ∈ U : (a, b) ∈ E}|.
  have hpopCol_clean : ∀ b ∈ B', (δ / 4) * (U.card : ℝ) ≤
      ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ) := by
    intro b hb
    have h := hpopCol b hb
    have hrew : (δ / 2) / 2 * (U.card : ℝ) = (δ / 4) * (U.card : ℝ) := by ring
    linarith [hrew]
  refine ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, hU_card_lb,
    hA'_card_lb, hB'_card_lb, hUτ_bound, hA'_prop_clean, hpopCol_clean⟩

/--
**DRC payoff: pointwise path-3 count.** Given the pair-DRC witness `U ⊆ A`
(from `graph_pair_dependentRandomChoice`), define the "non-bad" set
`A' := { a ∈ U : few a' ∈ U with codegree < (δ³/2⁷) n }` and the "popular"
set `B' := { b ∈ B : (δ/4) |U| ≤ |N_U(b)| }`. For `a ∈ A'`, `b ∈ B'`, the
length-3 path count `P(a, b) ≥ (δ⁵ / 2¹²) n²`.

Proof: of the `(δ/4)|U|` vertices in `U ∩ N(b)`, at most `(δ/8)|U|` are bad
partners of `a`, leaving `≥ (δ/8)|U|` non-bad partners `a₁`. Each non-bad
partner has `|N(a) ∩ N(a₁)| ≥ (δ³/2⁷) n` choices of `b₁`. Total:
`P(a, b) ≥ (δ/8)|U| · (δ³/2⁷) n ≥ (δ/8)(δ/4)n · (δ³/128) n = (δ⁵/2¹²) n²`.
-/
lemma graph_dependentRandomChoice_payoff_pointwise {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  obtain ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, _hU_card, hA'_card,
    hB'_card, hUτ_bound, hbadPartner, hpopCol⟩ :=
    graph_dependentRandomChoice_payoff_pointwise_witness δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  refine ⟨A', B', hA'_sub_U.trans hU_sub, hB'_sub, hA'_card, hB'_card, ?_⟩
  intro a ha b hb
  exact graph_dependentRandomChoice_payoff_pointwise_count δ A B E U A' B' τ hU_sub hA'_sub_U hB'_sub
    hτ_nn hUτ_bound hbadPartner hpopCol a ha b hb

end Finset

open Finset in
theorem solution {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ^5 / 2^12) * (A.card : ℝ)^2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- The Fox-Sudakov DRC payload is packaged in `graph_dependentRandomChoice_payoff_pointwise`,
  -- which assembles `graph_pair_dependentRandomChoice`, `graph_high_degree_subset_lb`, and the
  -- final pointwise path-3 count step (see those lemmas for the breakdown).
  exact graph_dependentRandomChoice_payoff_pointwise δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
