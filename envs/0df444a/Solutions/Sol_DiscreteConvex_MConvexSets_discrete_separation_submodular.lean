-- Prove2me | solution 1 for DiscreteConvex.MConvexSets.discrete_separation_submodular
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T17:27:04.419509+00:00
-- url     : https://prove2.me/submissions/6960e2c2-df64-40b7-8e9e-c038d67d8f8b

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_SupermodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValuedBot
import Definitions.Def_DiscreteConvex_MConvexSets_ToEReal
import Definitions.Def_DiscreteConvex_MConvexSets_ToERealOfBot

set_option linter.unusedSectionVars false

namespace FrankSep

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `ρ` is submodular on the subsets of `S`. -/
def SubOn (S : Finset V) (ρ : Finset V → WithTop ℝ) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, ρ (X ∪ Y) + ρ (X ∩ Y) ≤ ρ X + ρ Y

/-- every finite value of `ρ` lies in the additive subgroup `G`. -/
def ValIn (G : AddSubgroup ℝ) (ρ : Finset V → WithTop ℝ) : Prop :=
  ∀ X, ρ X = ⊤ ∨ ∃ g ∈ G, ρ X = (g : WithTop ℝ)

/-- contraction of `ρ` by the amount `α` placed on `e`. -/
def con (ρ : Finset V → WithTop ℝ) (e : V) (α : ℝ) (Y : Finset V) : WithTop ℝ :=
  min (ρ Y) (ρ (insert e Y) + ((-α : ℝ) : WithTop ℝ))

lemma wt_cases (w : WithTop ℝ) : w = ⊤ ∨ ∃ r : ℝ, w = r := by
  induction w using WithTop.recTopCoe <;> simp

lemma coe_le_add_neg {s α : ℝ} {w : WithTop ℝ} (h : (s : WithTop ℝ) ≤ w + ((-α : ℝ) : WithTop ℝ)) :
    ((α + s : ℝ) : WithTop ℝ) ≤ w := by
  induction w using WithTop.recTopCoe with
  | top => exact le_top
  | coe w =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    rw [WithTop.coe_le_coe]
    linarith

lemma add_neg_add (w1 w2 : WithTop ℝ) (α : ℝ) :
    w1 + ((-α : ℝ) : WithTop ℝ) + w2 + (α : WithTop ℝ) = w1 + w2 := by
  rw [add_right_comm w1, add_assoc (w1 + w2), ← WithTop.coe_add, neg_add_cancel,
    WithTop.coe_zero, add_zero]

lemma add_neg_add' (w1 w2 : WithTop ℝ) (α : ℝ) :
    w1 + (w2 + ((-α : ℝ) : WithTop ℝ)) + (α : WithTop ℝ) = w1 + w2 := by
  rw [← add_assoc, add_assoc (w1 + w2), ← WithTop.coe_add, neg_add_cancel,
    WithTop.coe_zero, add_zero]

lemma valIn_sum {G : AddSubgroup ℝ} {ρ1 ρ2 : Finset V → WithTop ℝ} (h1 : ValIn G ρ1)
    (h2 : ValIn G ρ2) {A B : Finset V} {r : ℝ} (h : ρ1 A + ρ2 B = (r : WithTop ℝ)) : r ∈ G := by
  rcases h1 A with h1 | ⟨g1, hg1, h1⟩
  · rw [h1, top_add] at h; exact absurd h WithTop.top_ne_coe
  rcases h2 B with h2 | ⟨g2, hg2, h2⟩
  · rw [h2, add_top] at h; exact absurd h WithTop.top_ne_coe
  rw [h1, h2, ← WithTop.coe_add, WithTop.coe_inj] at h
  rw [← h]; exact G.add_mem hg1 hg2

lemma subOn_con {S : Finset V} {e : V} (he : e ∉ S) {ρ : Finset V → WithTop ℝ}
    (hρ : SubOn (insert e S) ρ) (α : ℝ) : SubOn S (con ρ e α) := by
  intro X hX Y hY
  have hXe : e ∉ X := fun h => he (hX h)
  have hYe : e ∉ Y := fun h => he (hY h)
  have hX' : X ⊆ insert e S := hX.trans (subset_insert _ _)
  have hY' : Y ⊆ insert e S := hY.trans (subset_insert _ _)
  have hXi : insert e X ⊆ insert e S := insert_subset_insert _ hX
  have hYi : insert e Y ⊆ insert e S := insert_subset_insert _ hY
  set c : WithTop ℝ := ((-α : ℝ) : WithTop ℝ)
  -- the four mixed inequalities
  have ff : ρ (X ∪ Y) + ρ (X ∩ Y) ≤ ρ X + ρ Y := hρ X hX' Y hY'
  have gg : ρ (insert e (X ∪ Y)) + c + (ρ (insert e (X ∩ Y)) + c) ≤
      ρ (insert e X) + c + (ρ (insert e Y) + c) := by
    have := hρ _ hXi _ hYi
    rw [← insert_union_distrib, ← insert_inter_distrib] at this
    calc ρ (insert e (X ∪ Y)) + c + (ρ (insert e (X ∩ Y)) + c)
        = (ρ (insert e (X ∪ Y)) + ρ (insert e (X ∩ Y))) + (c + c) := by ac_rfl
      _ ≤ (ρ (insert e X) + ρ (insert e Y)) + (c + c) := by gcongr
      _ = _ := by ac_rfl
  have fg : ρ (insert e (X ∪ Y)) + c + ρ (X ∩ Y) ≤ ρ X + (ρ (insert e Y) + c) := by
    have := hρ _ hX' _ hYi
    rw [union_insert, inter_insert_of_notMem hXe] at this
    calc ρ (insert e (X ∪ Y)) + c + ρ (X ∩ Y) = (ρ (insert e (X ∪ Y)) + ρ (X ∩ Y)) + c := by
          ac_rfl
      _ ≤ (ρ X + ρ (insert e Y)) + c := by gcongr
      _ = _ := by ac_rfl
  have gf : ρ (insert e (X ∪ Y)) + c + ρ (X ∩ Y) ≤ ρ (insert e X) + c + ρ Y := by
    have := hρ _ hXi _ hY'
    rw [insert_union, insert_inter_of_notMem hYe] at this
    calc ρ (insert e (X ∪ Y)) + c + ρ (X ∩ Y) = (ρ (insert e (X ∪ Y)) + ρ (X ∩ Y)) + c := by
          ac_rfl
      _ ≤ (ρ (insert e X) + ρ Y) + c := by gcongr
      _ = _ := by ac_rfl
  unfold con
  rcases le_total (ρ X) (ρ (insert e X) + c) with hx | hx <;>
  rcases le_total (ρ Y) (ρ (insert e Y) + c) with hy | hy
  · rw [min_eq_left hx, min_eq_left hy]
    exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans ff
  · rw [min_eq_left hx, min_eq_right hy]
    exact (add_le_add (min_le_right _ _) (min_le_left _ _)).trans fg
  · rw [min_eq_right hx, min_eq_left hy]
    exact (add_le_add (min_le_right _ _) (min_le_left _ _)).trans gf
  · rw [min_eq_right hx, min_eq_right hy]
    exact (add_le_add (min_le_right _ _) (min_le_right _ _)).trans gg

/-- The induction for the max–min formula, with an optimal vector whose entries lie in `G`. -/
theorem exists_opt (G : AddSubgroup ℝ) (hG : (1 : ℝ) ∈ G) (S : Finset V) :
    ∀ ρ1 ρ2 : Finset V → WithTop ℝ, ρ1 ∅ = 0 → ρ2 ∅ = 0 → ρ1 S ≠ ⊤ → SubOn S ρ1 → SubOn S ρ2 →
    ValIn G ρ1 → ValIn G ρ2 →
    ∃ x : V → ℝ, (∀ v, x v ∈ G) ∧
      (∀ X ⊆ S, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ1 X ∧
        ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ ρ2 X) ∧
      ∃ U ⊆ S, ρ1 U + ρ2 (S \ U) ≤ ((∑ v ∈ S, x v : ℝ) : WithTop ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro ρ1 ρ2 h1 h2 _ _ _ _ _
    refine ⟨0, fun _ => G.zero_mem, fun X hX => ?_, ∅, subset_refl _, ?_⟩
    · rw [subset_empty.1 hX, h1, h2]; simp
    · simp [h1, h2]
  | @insert e S he ih =>
    intro ρ1 ρ2 h1 h2 hS hs1 hs2 hv1 hv2
    set T := insert e S with hT
    -- the minimum `m`
    let f : Finset V → WithTop ℝ := fun X => ρ1 X + ρ2 (T \ X)
    obtain ⟨X0, hX0, hmin⟩ := T.powerset.exists_min_image f ⟨T, mem_powerset_self T⟩
    replace hmin : ∀ X ⊆ T, f X0 ≤ f X := fun X hX => hmin X (mem_powerset.2 hX)
    have hfT : f T ≠ ⊤ := by simp only [f, sdiff_self, bot_eq_empty, h2, add_zero]; exact hS
    obtain ⟨mr, hmr⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top hfT (hmin T subset_rfl))
    -- `A*` and `D*`
    let a : Finset V → WithTop ℝ := fun U => ρ1 U + ρ2 (S \ U)
    let dd : Finset V → WithTop ℝ := fun U => ρ1 (insert e U) + ρ2 (T \ U)
    obtain ⟨U1, hU1, ha⟩ := S.powerset.exists_min_image a ⟨S, mem_powerset_self S⟩
    obtain ⟨U2, hU2, hd⟩ := S.powerset.exists_min_image dd ⟨S, mem_powerset_self S⟩
    rw [mem_powerset] at hU1 hU2
    have hU1e : e ∉ U1 := fun h => he (hU1 h)
    have hU2e : e ∉ U2 := fun h => he (hU2 h)
    have hST : S ⊆ T := subset_insert _ _
    -- submodularity: `2m ≤ A* + D*`
    have h2m : f X0 + f X0 ≤ a U1 + dd U2 := by
      have k1 := hs1 U1 (hU1.trans hST) (insert e U2) (insert_subset_insert _ hU2)
      rw [union_insert, inter_insert_of_notMem hU1e] at k1
      have k2 := hs2 (S \ U1) (sdiff_subset.trans hST) (T \ U2) sdiff_subset
      have e1 : S \ U1 ∪ T \ U2 = T \ (U1 ∩ U2) := by
        ext x
        simp only [hT, mem_union, mem_sdiff, mem_insert, mem_inter]
        by_cases hx : x = e
        · subst hx; simp [he, hU1e, hU2e]
        · have := @hU1 x; have := @hU2 x; simp only [hx, false_or]; tauto
      have e2 : S \ U1 ∩ (T \ U2) = T \ insert e (U1 ∪ U2) := by
        ext x
        simp only [hT, mem_union, mem_sdiff, mem_insert, mem_inter]
        by_cases hx : x = e
        · subst hx; simp [he]
        · have := @hU1 x; have := @hU2 x; simp only [hx, false_or]; tauto
      rw [e1, e2] at k2
      calc f X0 + f X0 ≤ f (U1 ∩ U2) + f (insert e (U1 ∪ U2)) :=
            add_le_add (hmin _ (inter_subset_left.trans (hU1.trans hST)))
              (hmin _ (insert_subset_insert _ (union_subset hU1 hU2)))
        _ = (ρ1 (insert e (U1 ∪ U2)) + ρ1 (U1 ∩ U2)) +
              (ρ2 (T \ (U1 ∩ U2)) + ρ2 (T \ insert e (U1 ∪ U2))) := by
            simp only [f]; ac_rfl
        _ ≤ (ρ1 U1 + ρ1 (insert e U2)) + (ρ2 (S \ U1) + ρ2 (T \ U2)) := add_le_add k1 k2
        _ = a U1 + dd U2 := by simp only [a, dd]; ac_rfl
    -- `m ≤ A* + ρi {e}`
    have hsing : ∀ ρ : Finset V → WithTop ℝ, ρ ∅ = 0 → SubOn T ρ → ∀ U ⊆ S,
        ρ (insert e U) ≤ ρ U + ρ {e} := by
      intro ρ h0 hs U hU
      have := hs U (hU.trans hST) {e} (singleton_subset_iff.2 (mem_insert_self _ _))
      have hUe : e ∉ U := fun h => he (hU h)
      rwa [union_singleton, inter_singleton_of_notMem hUe, h0, add_zero] at this
    have hb1 : f X0 ≤ a U1 + ρ1 {e} := by
      calc f X0 ≤ f (insert e U1) := hmin _ (insert_subset_insert _ hU1)
        _ = ρ1 (insert e U1) + ρ2 (S \ U1) := by
            simp only [f, hT, insert_sdiff_insert, sdiff_insert_of_notMem he]
        _ ≤ ρ1 U1 + ρ1 {e} + ρ2 (S \ U1) := add_le_add_left (hsing ρ1 h1 hs1 U1 hU1) _
        _ = a U1 + ρ1 {e} := by simp only [a]; rw [add_right_comm]
    have hb2 : f X0 ≤ a U1 + ρ2 {e} := by
      calc f X0 ≤ f U1 := hmin _ (hU1.trans hST)
        _ = ρ1 U1 + ρ2 (insert e (S \ U1)) := by
            simp only [f, hT, insert_sdiff_of_notMem _ hU1e]
        _ ≤ ρ1 U1 + (ρ2 (S \ U1) + ρ2 {e}) :=
            add_le_add_right (hsing ρ2 h2 hs2 _ sdiff_subset) _
        _ = a U1 + ρ2 {e} := by simp only [a]; rw [add_assoc]
    -- choice of `α`
    obtain ⟨α, hαG, Ha, Hd, He1, He2⟩ : ∃ α ∈ G, f X0 ≤ a U1 + (α : WithTop ℝ) ∧
        f X0 + (α : WithTop ℝ) ≤ dd U2 ∧ (α : WithTop ℝ) ≤ ρ1 {e} ∧ (α : WithTop ℝ) ≤ ρ2 {e} := by
      by_cases hA : a U1 = ⊤
      · -- `A* = ⊤`: any small enough `α` works
        have lb : ∀ w : WithTop ℝ, ∃ r : ℝ, ∀ s ≤ r, (s : WithTop ℝ) ≤ w := by
          intro w
          induction w using WithTop.recTopCoe with
          | top => exact ⟨0, fun _ _ => le_top⟩
          | coe w => exact ⟨w, fun s hs => WithTop.coe_le_coe.2 hs⟩
        obtain ⟨r1, hr1⟩ := lb (ρ1 {e})
        obtain ⟨r2, hr2⟩ := lb (ρ2 {e})
        obtain ⟨r3, hr3⟩ := lb (dd U2)
        set r := min (min r1 r2) (r3 - mr)
        refine ⟨(⌊r⌋ : ℝ), ?_, by rw [hA, top_add]; exact le_top, ?_, hr1 _ ?_, hr2 _ ?_⟩
        · have := G.zsmul_mem hG ⌊r⌋; simpa using this
        · rw [← hmr, ← WithTop.coe_add]
          refine hr3 _ ?_
          have := Int.floor_le r
          have : r ≤ r3 - mr := min_le_right _ _
          linarith
        · exact (Int.floor_le r).trans ((min_le_left _ _).trans (min_le_left _ _))
        · exact (Int.floor_le r).trans ((min_le_left _ _).trans (min_le_right _ _))
      · obtain ⟨ar, har⟩ := WithTop.ne_top_iff_exists.1 hA
        replace har := har.symm
        have hmG : mr ∈ G := valIn_sum hv1 hv2 hmr.symm
        have haG : ar ∈ G := valIn_sum hv1 hv2 har
        refine ⟨mr - ar, G.sub_mem hmG haG, ?_, ?_, ?_, ?_⟩
        · rw [← hmr, har, ← WithTop.coe_add, WithTop.coe_le_coe]; linarith
        · rw [← hmr, ← WithTop.coe_add]
          have := h2m
          rw [← hmr, har, ← WithTop.coe_add] at this
          rcases wt_cases (dd U2) with hw | ⟨w, hw⟩ <;> rw [hw] at this ⊢
          · exact le_top
          ·
            rw [← WithTop.coe_add, WithTop.coe_le_coe] at this
            rw [WithTop.coe_le_coe]; linarith
        · have := hb1
          rw [← hmr, har] at this
          rcases wt_cases (ρ1 {e}) with hw | ⟨w, hw⟩ <;> rw [hw] at this ⊢
          · exact le_top
          ·
            rw [← WithTop.coe_add, WithTop.coe_le_coe] at this
            rw [WithTop.coe_le_coe]; linarith
        · have := hb2
          rw [← hmr, har] at this
          rcases wt_cases (ρ2 {e}) with hw | ⟨w, hw⟩ <;> rw [hw] at this ⊢
          · exact le_top
          ·
            rw [← WithTop.coe_add, WithTop.coe_le_coe] at this
            rw [WithTop.coe_le_coe]; linarith
    -- the contracted problem
    have hcon0 : ∀ ρ : Finset V → WithTop ℝ, ρ ∅ = 0 → (α : WithTop ℝ) ≤ ρ {e} →
        con ρ e α ∅ = 0 := by
      intro ρ h0 hα
      unfold con
      rw [h0, insert_empty]
      refine min_eq_left ?_
      rcases wt_cases (ρ {e}) with hw | ⟨w, hw⟩ <;> rw [hw] at hα ⊢
      · simp
      ·
        rw [WithTop.coe_le_coe] at hα
        norm_cast
        linarith
    have hconv : ∀ ρ : Finset V → WithTop ℝ, ValIn G ρ → ValIn G (con ρ e α) := by
      intro ρ hv Y
      unfold con
      rcases min_choice (ρ Y) (ρ (insert e Y) + ((-α : ℝ) : WithTop ℝ)) with h | h <;> rw [h]
      · exact hv Y
      · rcases hv (insert e Y) with h' | ⟨g, hg, h'⟩
        · left; rw [h', top_add]
        · right; exact ⟨g + -α, G.add_mem hg (G.neg_mem hαG), by rw [h', WithTop.coe_add]⟩
    have hconS : con ρ1 e α S ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (min_le_right _ _)
      rw [← hT]
      exact WithTop.add_ne_top.2 ⟨hS, WithTop.coe_ne_top⟩
    obtain ⟨x', hx'G, hx'f, U', hU'S, hU'⟩ := ih (con ρ1 e α) (con ρ2 e α) (hcon0 ρ1 h1 He1)
      (hcon0 ρ2 h2 He2) hconS (subOn_con he hs1 α) (subOn_con he hs2 α) (hconv ρ1 hv1)
      (hconv ρ2 hv2)
    -- the extension `x`
    set x := Function.update x' e α with hx
    have sum_of : ∀ X : Finset V, e ∉ X → ∑ v ∈ X, x v = ∑ v ∈ X, x' v := by
      intro X hX
      refine sum_congr rfl fun v hv => ?_
      rw [hx, Function.update_of_ne (by rintro rfl; exact hX hv)]
    have sum_ins : ∀ X : Finset V, e ∉ X → ∑ v ∈ insert e X, x v = α + ∑ v ∈ X, x' v := by
      intro X hX
      rw [sum_insert hX, sum_of X hX, hx, Function.update_self]
    have hU'e : e ∉ U' := fun h => he (hU'S h)
    refine ⟨x, fun v => ?_, fun X hX => ?_, X0, mem_powerset.1 hX0, ?_⟩
    · by_cases hv : v = e
      · subst hv; rw [hx, Function.update_self]; exact hαG
      · rw [hx, Function.update_of_ne hv]; exact hx'G v
    · by_cases heX : e ∈ X
      · have hY : X.erase e ⊆ S := by
          intro y hy
          have := hX (mem_of_mem_erase hy)
          rw [mem_insert] at this
          exact this.resolve_left (ne_of_mem_erase hy)
        have hXY : X = insert e (X.erase e) := (insert_erase heX).symm
        have hs : ∑ v ∈ X, x v = α + ∑ v ∈ X.erase e, x' v := by
          conv_lhs => rw [hXY]
          exact sum_ins _ (notMem_erase e X)
        obtain ⟨k1, k2⟩ := hx'f _ hY
        rw [hs]
        constructor
        · refine coe_le_add_neg (k1.trans (min_le_right _ _) |>.trans ?_)
          rw [← hXY]
        · refine coe_le_add_neg (k2.trans (min_le_right _ _) |>.trans ?_)
          rw [← hXY]
      · have hXS : X ⊆ S := fun y hy => by
          have := hX hy
          rw [mem_insert] at this
          exact this.resolve_left (fun h => heX (h ▸ hy))
        obtain ⟨k1, k2⟩ := hx'f _ hXS
        rw [sum_of X heX]
        exact ⟨k1.trans (min_le_left _ _), k2.trans (min_le_left _ _)⟩
    · -- optimality: `m ≤ x(T)`
      rw [hT, sum_ins S he, WithTop.coe_add, add_comm (α : WithTop ℝ)]
      refine le_trans ?_ (add_le_add_left hU' _)
      have hins : insert e (S \ U') = T \ U' := (insert_sdiff_of_notMem _ hU'e).symm
      have hins2 : T \ insert e U' = S \ U' := by
        rw [hT, insert_sdiff_insert, sdiff_insert_of_notMem he]
      unfold con
      rw [hins]
      rcases min_choice (ρ1 U') (ρ1 (insert e U') + ((-α : ℝ) : WithTop ℝ)) with k1 | k1 <;>
      rcases min_choice (ρ2 (S \ U')) (ρ2 (T \ U') + ((-α : ℝ) : WithTop ℝ)) with k2 | k2 <;>
      rw [k1, k2]
      · -- (a)
        exact Ha.trans (add_le_add_left (ha U' (mem_powerset.2 hU'S)) _)
      · -- (c): `X = U'`
        rw [add_neg_add']
        exact hmin U' (hU'S.trans hST)
      · -- (b): `X = U' + e`
        rw [add_neg_add, ← hins2]
        exact hmin _ (insert_subset_insert _ hU'S)
      · -- (d): `e` counted on both sides
        rw [add_neg_add', add_right_comm]
        have := (Hd.trans (hd U' (mem_powerset.2 hU'S)))
        calc f X0 = f X0 + (α : WithTop ℝ) + ((-α : ℝ) : WithTop ℝ) := by
              rw [add_assoc, ← WithTop.coe_add, add_neg_cancel, WithTop.coe_zero, add_zero]
          _ ≤ _ := add_le_add_left this _

/-! ### Frank's separation theorem from the max–min induction -/

open DiscreteConvex.MConvexSets

/-- the integers, as an additive subgroup of `ℝ` -/
def Zs : AddSubgroup ℝ := (Int.castAddHom ℝ).range

lemma mem_Zs {r : ℝ} : r ∈ Zs ↔ ∃ k : ℤ, r = k := by
  simp only [Zs, AddMonoidHom.mem_range, Int.coe_castAddHom]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

lemma one_mem_Zs : (1 : ℝ) ∈ Zs := mem_Zs.2 ⟨1, by simp⟩

lemma wb_cases (w : WithBot ℝ) : w = ⊥ ∨ ∃ r : ℝ, w = r := by
  induction w using WithBot.recBotCoe <;> simp

/-- negation `R ∪ {-∞} → R ∪ {+∞}` -/
def ng (w : WithBot ℝ) : WithTop ℝ := Option.elim w ⊤ (fun r => ((-r : ℝ) : WithTop ℝ))

lemma ng_bot : ng ⊥ = ⊤ := rfl

lemma ng_coe (r : ℝ) : ng (r : WithBot ℝ) = ((-r : ℝ) : WithTop ℝ) := rfl

lemma ng_add (a b : WithBot ℝ) : ng (a + b) = ng a + ng b := by
  rcases wb_cases a with rfl | ⟨r, rfl⟩
  · rw [WithBot.bot_add, ng_bot, top_add]
  rcases wb_cases b with rfl | ⟨s, rfl⟩
  · rw [WithBot.add_bot, ng_bot, add_top]
  rw [← WithBot.coe_add, ng_coe, ng_coe, ng_coe, ← WithTop.coe_add, neg_add]

lemma ng_anti {a b : WithBot ℝ} (h : a ≤ b) : ng b ≤ ng a := by
  rcases wb_cases a with rfl | ⟨r, rfl⟩
  · rw [ng_bot]; exact le_top
  rcases wb_cases b with rfl | ⟨s, rfl⟩
  · exact absurd h (by simp)
  rw [ng_coe, ng_coe, WithTop.coe_le_coe]
  exact neg_le_neg (WithBot.coe_le_coe.1 h)

lemma toEB_le {r s : ℝ} : ToERealOfBot (r : WithBot ℝ) ≤ ToEReal (s : WithTop ℝ) ↔ r ≤ s :=
  WithBot.coe_le_coe.trans WithTop.coe_le_coe

lemma toE_le {a b : WithTop ℝ} : ToEReal a ≤ ToEReal b ↔ a ≤ b := WithBot.coe_le_coe

/-- The separation statement with values of `x` in a subgroup `G ∋ 1` containing all finite
values of `ρ` and `μ`. -/
theorem sep_core (G : AddSubgroup ℝ) (hG : (1 : ℝ) ∈ G)
    (ρ : Finset V → WithTop ℝ) (μ : Finset V → WithBot ℝ)
    (hρ : SubmodularSetFunction ρ) (hμ : SupermodularSetFunction μ)
    (hsep : ∀ X : Finset V, ToERealOfBot (μ X) ≤ ToEReal (ρ X))
    (hvρ : ValIn G ρ) (hvμ : ∀ X, μ X = ⊥ ∨ ∃ g ∈ G, μ X = (g : WithBot ℝ)) :
    ∃ x : V → ℝ, (∀ v, x v ∈ G) ∧ ∀ X : Finset V,
        ToERealOfBot (μ X) ≤ ToEReal (((∑ v ∈ X, x v : ℝ) : WithTop ℝ)) ∧
        ToEReal (((∑ v ∈ X, x v : ℝ) : WithTop ℝ)) ≤ ToEReal (ρ X) := by
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.1 hμ.2.1
  obtain ⟨ρ2, hρ2⟩ : ∃ f : Finset V → WithTop ℝ, ∀ X, f X = ng (μ Xᶜ) + (m : WithTop ℝ) :=
    ⟨_, fun _ => rfl⟩
  have h20 : ρ2 ∅ = 0 := by
    simp only [hρ2, compl_empty, ← hm, ng_coe, ← WithTop.coe_add, neg_add_cancel,
      WithTop.coe_zero]
  have hs2 : SubOn univ ρ2 := by
    intro X _ Y _
    have h := ng_anti (hμ.2.2 Xᶜ Yᶜ)
    rw [ng_add, ng_add, ← compl_inter, ← compl_union] at h
    simp only [hρ2]
    calc ng (μ (X ∪ Y)ᶜ) + (m : WithTop ℝ) + (ng (μ (X ∩ Y)ᶜ) + (m : WithTop ℝ))
        = (ng (μ (X ∩ Y)ᶜ) + ng (μ (X ∪ Y)ᶜ)) + ((m : WithTop ℝ) + (m : WithTop ℝ)) := by
          ac_rfl
      _ ≤ (ng (μ Xᶜ) + ng (μ Yᶜ)) + ((m : WithTop ℝ) + (m : WithTop ℝ)) := by gcongr
      _ = _ := by ac_rfl
  have hmG : m ∈ G := by
    rcases hvμ univ with h | ⟨g, hg, h⟩
    · exact absurd h hμ.2.1
    · rw [← hm, WithBot.coe_inj] at h; rw [h]; exact hg
  have hv2 : ValIn G ρ2 := by
    intro X
    rcases hvμ Xᶜ with h | ⟨g, hg, h⟩
    · left; simp only [hρ2, h, ng_bot, top_add]
    · right
      refine ⟨-g + m, G.add_mem (G.neg_mem hg) hmG, ?_⟩
      simp only [hρ2, h, ng_coe, WithTop.coe_add]
  obtain ⟨x, hxG, hxf, U, -, hU⟩ :=
    exists_opt G hG univ ρ ρ2 hρ.1 h20 hρ.2.1 (fun X _ Y _ => hρ.2.2 X Y) hs2 hvρ hv2
  -- `x(V) = μ(V)`
  have hsum : ∑ v, x v = m := by
    apply le_antisymm
    · have := (hxf univ (subset_refl _)).2
      simp only [hρ2, compl_univ, hμ.1] at this
      rw [show ng 0 = ((-0 : ℝ) : WithTop ℝ) from rfl, ← WithTop.coe_add,
        WithTop.coe_le_coe] at this
      linarith
    · rw [← compl_eq_univ_sdiff] at hU
      simp only [hρ2, compl_compl] at hU
      have hsU := hsep U
      rcases wb_cases (μ U) with h | ⟨r, h⟩
      · rw [h, ng_bot, top_add, add_top] at hU
        exact absurd hU (by simp)
      rcases wt_cases (ρ U) with h' | ⟨s, h'⟩
      · rw [h', top_add] at hU
        exact absurd hU (by simp)
      rw [h, h', toEB_le] at hsU
      rw [h, h', ng_coe, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe] at hU
      linarith
  refine ⟨x, hxG, fun X => ⟨?_, toE_le.2 (hxf X (subset_univ _)).1⟩⟩
  rcases wb_cases (μ X) with h | ⟨r, h⟩
  · rw [h]; exact bot_le
  have hc := (hxf Xᶜ (subset_univ _)).2
  simp only [hρ2, compl_compl, h, ng_coe, ← WithTop.coe_add, WithTop.coe_le_coe] at hc
  have hsplit := sum_add_sum_compl X x
  rw [h, toEB_le]
  linarith

end FrankSep

open DiscreteConvex.MConvexSets FrankSep Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (μ : Finset V → WithBot ℝ)
    (hρ : SubmodularSetFunction ρ) (hμ : SupermodularSetFunction μ)
    (hsep : ∀ X : Finset V, ToERealOfBot (μ X) ≤ ToEReal (ρ X)) :
    (∃ x : V → ℝ, ∀ X : Finset V,
        ToERealOfBot (μ X) ≤ ToEReal (((∑ v ∈ X, x v : ℝ) : WithTop ℝ)) ∧
        ToEReal (((∑ v ∈ X, x v : ℝ) : WithTop ℝ)) ≤ ToEReal (ρ X)) ∧
    (IsIntegerValued ρ → IsIntegerValuedBot μ →
      ∃ x : V → ℤ, ∀ X : Finset V,
        ToERealOfBot (μ X) ≤ ToEReal (((∑ v ∈ X, (x v : ℝ) : ℝ) : WithTop ℝ)) ∧
        ToEReal (((∑ v ∈ X, (x v : ℝ) : ℝ) : WithTop ℝ)) ≤ ToEReal (ρ X)) := by
  refine ⟨?_, fun hI hJ => ?_⟩
  · obtain ⟨x, -, hx⟩ := sep_core ⊤ (AddSubgroup.mem_top 1) ρ μ hρ hμ hsep
      (fun X => (wt_cases (ρ X)).imp id fun ⟨r, h⟩ => ⟨r, AddSubgroup.mem_top r, h⟩)
      (fun X => (wb_cases (μ X)).imp id fun ⟨r, h⟩ => ⟨r, AddSubgroup.mem_top r, h⟩)
    exact ⟨x, hx⟩
  · obtain ⟨x, hxG, hx⟩ := sep_core Zs one_mem_Zs ρ μ hρ hμ hsep
      (fun X => (hI X).imp id fun ⟨k, h⟩ => ⟨k, mem_Zs.2 ⟨k, rfl⟩, h⟩)
      (fun X => (hJ X).imp id fun ⟨k, h⟩ => ⟨k, mem_Zs.2 ⟨k, rfl⟩, h⟩)
    choose k hk using fun v => mem_Zs.1 (hxG v)
    refine ⟨k, fun X => ?_⟩
    simp_rw [← hk]
    exact hx X
