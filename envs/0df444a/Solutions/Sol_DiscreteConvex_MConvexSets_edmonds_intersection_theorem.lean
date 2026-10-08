-- Prove2me | solution 1 for DiscreteConvex.MConvexSets.edmonds_intersection_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Tim
-- created : 2026-10-05T17:14:17.269624+00:00
-- url     : https://prove2.me/submissions/b55c8152-e400-4d2e-942b-5896e17615a1

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSets_SubmodularPolyhedron
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegerValued
import Definitions.Def_DiscreteConvex_MConvexSets_IsIntegralPolyhedron
import Definitions.Def_DiscreteConvex_MConvexSets_ToEReal

set_option linter.unusedSectionVars false

namespace EdmondsInt

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



/-! ### Lattices of sets and their classes -/

section Lat

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- a family of sets closed under union and intersection, containing `∅` -/
structure IsLat (T : Finset (Finset V)) : Prop where
  empty : ∅ ∈ T
  union : ∀ X ∈ T, ∀ Y ∈ T, X ∪ Y ∈ T
  inter : ∀ X ∈ T, ∀ Y ∈ T, X ∩ Y ∈ T

variable {T : Finset (Finset V)}

lemma IsLat.sup_mem (hT : IsLat T) (𝒜 : Finset (Finset V)) (h : 𝒜 ⊆ T) : 𝒜.sup id ∈ T := by
  induction 𝒜 using Finset.induction_on with
  | empty => simpa using hT.empty
  | @insert a s ha ih =>
    rw [sup_insert]
    exact hT.union _ (h (mem_insert_self _ _)) _ (ih ((subset_insert _ _).trans h))

lemma IsLat.inf_mem (hT : IsLat T) (𝒜 : Finset (Finset V)) (h : 𝒜 ⊆ T) (hne : 𝒜.Nonempty) :
    𝒜.inf id ∈ T := by
  induction 𝒜 using Finset.induction_on with
  | empty => exact absurd hne (by simp)
  | @insert a s ha ih =>
    rw [inf_insert]
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs; simpa using h (mem_insert_self _ _)
    · exact hT.inter _ (h (mem_insert_self _ _)) _ (ih ((subset_insert _ _).trans h) hs)

/-- the largest member -/
def top (T : Finset (Finset V)) : Finset V := T.sup id
/-- the smallest member containing `v` -/
def Mv (T : Finset (Finset V)) (v : V) : Finset V := (T.filter (fun X => v ∈ X)).inf id
/-- the largest member inside `Mv T v` avoiding `v` -/
def Nv (T : Finset (Finset V)) (v : V) : Finset V :=
  (T.filter (fun X => X ⊆ Mv T v ∧ v ∉ X)).sup id
/-- the class of `v` -/
def Kv (T : Finset (Finset V)) (v : V) : Finset V := Mv T v \ Nv T v
/-- all classes -/
def cls (T : Finset (Finset V)) : Finset (Finset V) := (top T).image (Kv T)

lemma sub_top {X : Finset V} (hX : X ∈ T) : X ⊆ top T := le_sup (f := id) hX

lemma mem_top {v : V} : v ∈ top T ↔ ∃ X ∈ T, v ∈ X := by
  rw [top, sup_eq_biUnion, mem_biUnion]; rfl

lemma Mv_mem (hT : IsLat T) {v : V} (hv : v ∈ top T) : Mv T v ∈ T := by
  obtain ⟨X, hX, hvX⟩ := mem_top.1 hv
  exact hT.inf_mem _ (filter_subset _ _) ⟨X, mem_filter.2 ⟨hX, hvX⟩⟩

lemma mem_Mv (v : V) : v ∈ Mv T v :=
  singleton_subset_iff.1 (Finset.le_inf fun _ hX => singleton_subset_iff.2 (mem_filter.1 hX).2)

lemma Mv_sub {X : Finset V} {v : V} (hX : X ∈ T) (hvX : v ∈ X) : Mv T v ⊆ X :=
  inf_le (f := id) (mem_filter.2 ⟨hX, hvX⟩)

lemma Nv_mem (hT : IsLat T) (v : V) : Nv T v ∈ T := hT.sup_mem _ (filter_subset _ _)

lemma not_mem_Nv (v : V) : v ∉ Nv T v := by
  intro h
  rw [Nv, sup_eq_biUnion, mem_biUnion] at h
  obtain ⟨X, hX, hvX⟩ := h
  exact (mem_filter.1 hX).2.2 hvX

lemma sub_Nv {X : Finset V} {v : V} (hX : X ∈ T) (h1 : X ⊆ Mv T v) (h2 : v ∉ X) : X ⊆ Nv T v :=
  le_sup (f := id) (mem_filter.2 ⟨hX, h1, h2⟩)

lemma sep (hT : IsLat T) {X : Finset V} {v : V} (hX : X ∈ T) (hv : v ∈ top T) :
    Kv T v ⊆ X ∨ ∀ u ∈ Kv T v, u ∉ X := by
  by_cases hvX : v ∈ X
  · exact Or.inl (sdiff_subset.trans (Mv_sub hX hvX))
  · right
    intro u hu huX
    have : X ∩ Mv T v ⊆ Nv T v := sub_Nv (hT.inter _ hX _ (Mv_mem hT hv)) inter_subset_right
      (fun h => hvX (mem_inter.1 h).1)
    rw [Kv, mem_sdiff] at hu
    exact hu.2 (this (mem_inter.2 ⟨huX, hu.1⟩))

lemma mem_Kv (v : V) : v ∈ Kv T v := mem_sdiff.2 ⟨mem_Mv v, not_mem_Nv v⟩

lemma Kv_sub_top (hT : IsLat T) {v : V} (hv : v ∈ top T) : Kv T v ⊆ top T :=
  sdiff_subset.trans (sub_top (Mv_mem hT hv))

lemma Kv_sub (hT : IsLat T) {u v w : V} (hv : v ∈ top T) (hw : w ∈ top T) (hu1 : u ∈ Kv T v)
    (hu2 : u ∈ Kv T w) : Kv T v ⊆ Kv T w := by
  intro y hy
  rcases sep hT (Mv_mem hT hw) hv with h | h
  · rcases sep hT (Nv_mem hT w) hv with h' | h'
    · exact absurd (h' hu1) (mem_sdiff.1 hu2).2
    · exact mem_sdiff.2 ⟨h hy, h' y hy⟩
  · exact absurd (mem_sdiff.1 hu2).1 (h u hu1)

lemma cls_disj (hT : IsLat T) {c1 c2 : Finset V} (h1 : c1 ∈ cls T) (h2 : c2 ∈ cls T)
    (hne : c1 ≠ c2) : Disjoint c1 c2 := by
  obtain ⟨v, hv, rfl⟩ := mem_image.1 h1
  obtain ⟨w, hw, rfl⟩ := mem_image.1 h2
  rw [disjoint_left]
  intro u hu1 hu2
  exact hne (subset_antisymm (Kv_sub hT hv hw hu1 hu2) (Kv_sub hT hw hv hu2 hu1))

lemma cls_sub_top (hT : IsLat T) {c : Finset V} (hc : c ∈ cls T) : c ⊆ top T := by
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
  exact Kv_sub_top hT hv

lemma sum_eq_cls (hT : IsLat T) {X : Finset V} (hX : X ∈ T) (d : V → ℝ) :
    ∑ u ∈ X, d u = ∑ c ∈ (cls T).filter (· ⊆ X), ∑ u ∈ c, d u := by
  have hXeq : X = ((cls T).filter (· ⊆ X)).biUnion id := by
    ext u
    simp only [mem_biUnion, mem_filter, id]
    constructor
    · intro hu
      have hut := sub_top hX hu
      refine ⟨Kv T u, ⟨mem_image_of_mem _ hut, ?_⟩, mem_Kv u⟩
      rcases sep hT hX hut with h | h
      · exact h
      · exact absurd hu (h u (mem_Kv u))
    · rintro ⟨c, ⟨_, hc⟩, huc⟩
      exact hc huc
  conv_lhs => rw [hXeq]
  rw [sum_biUnion]
  · rfl
  · intro c1 hc1 c2 hc2 hne
    exact cls_disj hT (mem_filter.1 hc1).1 (mem_filter.1 hc2).1 hne

lemma sum_zero_of_cls (hT : IsLat T) (d : V → ℝ) (h : ∀ c ∈ cls T, ∑ u ∈ c, d u = 0)
    {X : Finset V} (hX : X ∈ T) : ∑ u ∈ X, d u = 0 := by
  rw [sum_eq_cls hT hX]
  exact sum_eq_zero fun c hc => h c (mem_filter.1 hc).1

lemma sum_top (hT : IsLat T) (d : V → ℝ) :
    ∑ u ∈ top T, d u = ∑ c ∈ cls T, ∑ u ∈ c, d u := by
  rw [sum_eq_cls hT (X := top T) (hT.sup_mem T subset_rfl), filter_true_of_mem fun c hc => cls_sub_top hT hc]

lemma cls_mem_G {G : AddSubgroup ℝ} (hT : IsLat T) {y : V → ℝ}
    (hi : ∀ X ∈ T, ∑ u ∈ X, y u ∈ G) {c : Finset V} (hc : c ∈ cls T) : ∑ u ∈ c, y u ∈ G := by
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hc
  have hsub : Nv T v ⊆ Mv T v := Finset.sup_le fun X hX => (mem_filter.1 hX).2.1
  rw [Kv, sum_sdiff_eq_sub hsub]
  exact G.sub_mem (hi _ (Mv_mem hT hv)) (hi _ (Nv_mem hT v))

/-- classes meeting `F` -/
def cls' (T : Finset (Finset V)) (F : Finset V) : Finset (Finset V) :=
  (cls T).filter (fun c => (c ∩ F).Nonempty)

lemma two_le {G : AddSubgroup ℝ} (hT : IsLat T) {y : V → ℝ} (hi : ∀ X ∈ T, ∑ u ∈ X, y u ∈ G)
    {F : Finset V} (hF : ∀ u, u ∈ F ↔ y u ∉ G) {c : Finset V} (hc : c ∈ cls T)
    (hne : (c ∩ F).Nonempty) : 2 ≤ (c ∩ F).card := by
  by_contra h
  have h1 : (c ∩ F).card = 1 := by have := hne.card_pos; omega
  obtain ⟨u, hu⟩ := card_eq_one.1 h1
  have hrest : ∑ v ∈ c \ F, y v ∈ G :=
    G.sum_mem fun v hv => by
      by_contra hv'
      exact (mem_sdiff.1 hv).2 ((hF v).2 hv')
  have hsplit := sum_inter_add_sum_sdiff c F y
  have hin : ∑ v ∈ c ∩ F, y v ∈ G := by
    have : ∑ v ∈ c ∩ F, y v = ∑ v ∈ c, y v - ∑ v ∈ c \ F, y v := by linarith
    rw [this]
    exact G.sub_mem (cls_mem_G hT hi hc) hrest
  rw [hu, sum_singleton] at hin
  have : u ∈ F := (mem_inter.1 (hu ▸ mem_singleton_self u)).2
  exact (hF u).1 this hin

lemma card_cls' {G : AddSubgroup ℝ} (hT : IsLat T) {y : V → ℝ}
    (hi : ∀ X ∈ T, ∑ u ∈ X, y u ∈ G) {F : Finset V} (hF : ∀ u, u ∈ F ↔ y u ∉ G) :
    2 * (cls' T F).card ≤ (top T ∩ F).card := by
  calc 2 * (cls' T F).card = ∑ c ∈ cls' T F, 2 := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ c ∈ cls' T F, (c ∩ F).card :=
        sum_le_sum fun c hc => two_le hT hi hF (mem_filter.1 hc).1 (mem_filter.1 hc).2
    _ = ((cls' T F).biUnion (· ∩ F)).card := by
        rw [card_biUnion]
        intro c1 hc1 c2 hc2 hne
        exact (cls_disj hT (mem_filter.1 hc1).1 (mem_filter.1 hc2).1 hne).mono
          inter_subset_left inter_subset_left
    _ ≤ (top T ∩ F).card := by
        refine card_le_card (biUnion_subset.2 fun c hc => ?_)
        exact inter_subset_inter_right (cls_sub_top hT (mem_filter.1 hc).1)

end Lat

/-! ### A nonzero vector orthogonal to few rows -/

lemma exists_orth {V : Type*} [Fintype V] (R : Finset (V → ℝ)) (h : R.card < Fintype.card V) :
    ∃ d : V → ℝ, d ≠ 0 ∧ ∀ r ∈ R, ∑ v, r v * d v = 0 := by
  let L : (V → ℝ) →ₗ[ℝ] (R → ℝ) :=
    { toFun := fun d r => ∑ v, r.1 v * d v
      map_add' := by
        intro a b
        ext r
        simp [mul_add, sum_add_distrib]
      map_smul' := by
        intro c a
        ext r
        simp [mul_sum, mul_left_comm] }
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨d, hd, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨d, hne, fun r hr => congrFun (LinearMap.mem_ker.1 hd) ⟨r, hr⟩⟩


/-! ### The key lemma: a non-integral point admits a direction preserving all tight sets -/

section Key

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- incidence vector -/
def ind (c : Finset V) : V → ℝ := fun v => if v ∈ c then 1 else 0

lemma dot_ind (c : Finset V) (d : V → ℝ) : ∑ v, ind c v * d v = ∑ v ∈ c, d v := by
  simp [ind, ite_mul, Finset.sum_ite_mem]

theorem key (G : AddSubgroup ℝ) (y : V → ℝ) {T1 T2 : Finset (Finset V)} (h1 : IsLat T1)
    (h2 : IsLat T2) (hi1 : ∀ X ∈ T1, ∑ u ∈ X, y u ∈ G) (hi2 : ∀ X ∈ T2, ∑ u ∈ X, y u ∈ G)
    (hnot : ∃ v, y v ∉ G) :
    ∃ d : V → ℝ, d ≠ 0 ∧ (∀ v, y v ∈ G → d v = 0) ∧ (∀ X ∈ T1, ∑ u ∈ X, d u = 0) ∧
      (∀ X ∈ T2, ∑ u ∈ X, d u = 0) := by
  classical
  set F := univ.filter (fun u => y u ∉ G) with hFdef
  have hF : ∀ u, u ∈ F ↔ y u ∉ G := fun u => by simp [F]
  have hFne : F.Nonempty := let ⟨v, hv⟩ := hnot; ⟨v, (hF v).2 hv⟩
  let unit : V → V → ℝ := fun u v => if v = u then 1 else 0
  have dot_unit : ∀ u (d : V → ℝ), ∑ v, unit u v * d v = d u := by
    intro u d; simp [unit, ite_mul]
  have fin1 : ∀ T : Finset (Finset V), ∀ d : V → ℝ, (∀ v ∉ F, d v = 0) →
      (∀ c ∈ cls' T F, ∑ u ∈ c, d u = 0) → ∀ c ∈ cls T, ∑ u ∈ c, d u = 0 := by
    intro T d hdF hc c hcT
    by_cases hne : (c ∩ F).Nonempty
    · exact hc c (mem_filter.2 ⟨hcT, hne⟩)
    · exact sum_eq_zero fun u hu => hdF u (fun huF => hne ⟨u, mem_inter.2 ⟨hu, huF⟩⟩)
  have hFV : (univ \ F).card + F.card = Fintype.card V := by
    rw [card_sdiff_add_card_eq_card (subset_univ _), card_univ]
  have hdF_of : ∀ (R : Finset (V → ℝ)) (d : V → ℝ), (univ \ F).image unit ⊆ R →
      (∀ r ∈ R, ∑ v, r v * d v = 0) → ∀ v ∉ F, d v = 0 := by
    intro R d hR hd v hv
    have := hd (unit v) (hR (mem_image_of_mem _ (by simpa using hv)))
    rwa [dot_unit] at this
  have hc_of : ∀ (R : Finset (V → ℝ)) (C : Finset (Finset V)) (d : V → ℝ), C.image ind ⊆ R →
      (∀ r ∈ R, ∑ v, r v * d v = 0) → ∀ c ∈ C, ∑ u ∈ c, d u = 0 := by
    intro R C d hR hd c hc
    have := hd (ind c) (hR (mem_image_of_mem _ hc))
    rwa [dot_ind] at this
  have hint : ∀ d : V → ℝ, (∀ v ∉ F, d v = 0) → ∀ v, y v ∈ G → d v = 0 :=
    fun d hdF v hv => hdF v (fun h => (hF v).1 h hv)
  by_cases hlt : (cls' T1 F).card + (cls' T2 F).card < F.card
  · set R := (cls' T1 F).image ind ∪ (cls' T2 F).image ind ∪ (univ \ F).image unit
    have hR : R.card < Fintype.card V := by
      have := card_union_le ((cls' T1 F).image ind ∪ (cls' T2 F).image ind) ((univ \ F).image unit)
      have := card_union_le ((cls' T1 F).image ind) ((cls' T2 F).image ind)
      have := card_image_le (s := cls' T1 F) (f := ind)
      have := card_image_le (s := cls' T2 F) (f := ind)
      have := card_image_le (s := univ \ F) (f := unit)
      have : R.card = ((cls' T1 F).image ind ∪ (cls' T2 F).image ind ∪ (univ \ F).image unit).card := rfl
      omega
    obtain ⟨d, hd0, hdR⟩ := exists_orth R hR
    have hdF := hdF_of R d subset_union_right hdR
    have hc1 := hc_of R _ d (subset_union_left.trans subset_union_left) hdR
    have hc2 := hc_of R _ d (subset_union_right.trans subset_union_left) hdR
    exact ⟨d, hd0, hint d hdF, fun X hX => sum_zero_of_cls h1 d (fin1 T1 d hdF hc1) hX,
      fun X hX => sum_zero_of_cls h2 d (fin1 T2 d hdF hc2) hX⟩
  · push Not at hlt
    have k1 := card_cls' h1 hi1 hF
    have k2 := card_cls' h2 hi2 hF
    have l1 : (top T1 ∩ F).card ≤ F.card := card_le_card inter_subset_right
    have l2 : (top T2 ∩ F).card ≤ F.card := card_le_card inter_subset_right
    have hsubF : ∀ T : Finset (Finset V), (top T ∩ F).card = F.card → F ⊆ top T := by
      intro T hT u hu
      have := eq_of_subset_of_card_le (inter_subset_right (s₁ := top T) (s₂ := F)) hT.ge
      rw [← this] at hu
      exact (mem_inter.1 hu).1
    have hF1 := hsubF T1 (by omega)
    have hF2 := hsubF T2 (by omega)
    have hFc : 0 < F.card := hFne.card_pos
    obtain ⟨c0, hc0⟩ : (cls' T2 F).Nonempty := by rw [← card_pos]; omega
    set R := (cls' T1 F).image ind ∪ ((cls' T2 F).erase c0).image ind ∪ (univ \ F).image unit
    have hR : R.card < Fintype.card V := by
      have := card_union_le ((cls' T1 F).image ind ∪ ((cls' T2 F).erase c0).image ind)
        ((univ \ F).image unit)
      have := card_union_le ((cls' T1 F).image ind) (((cls' T2 F).erase c0).image ind)
      have := card_image_le (s := cls' T1 F) (f := ind)
      have := card_image_le (s := (cls' T2 F).erase c0) (f := ind)
      have := card_image_le (s := univ \ F) (f := unit)
      have := card_erase_of_mem hc0
      have : R.card = ((cls' T1 F).image ind ∪ ((cls' T2 F).erase c0).image ind ∪
        (univ \ F).image unit).card := rfl
      omega
    obtain ⟨d, hd0, hdR⟩ := exists_orth R hR
    have hdF := hdF_of R d subset_union_right hdR
    have hc1 := hc_of R _ d (subset_union_left.trans subset_union_left) hdR
    have hc2' := hc_of R _ d (subset_union_right.trans subset_union_left) hdR
    have all1 := fin1 T1 d hdF hc1
    have z1 : ∑ u ∈ top T1, d u = 0 := by rw [sum_top h1]; exact sum_eq_zero all1
    have sF : ∀ T : Finset (Finset V), F ⊆ top T → ∑ u ∈ top T, d u = ∑ u ∈ F, d u :=
      fun T hT => (sum_subset hT (fun u _ hu => hdF u hu)).symm
    have z2 : ∑ u ∈ top T2, d u = 0 := by rw [sF T2 hF2, ← sF T1 hF1, z1]
    have hc0z : ∑ u ∈ c0, d u = 0 := by
      rw [sum_top h2, sum_eq_single c0] at z2
      · exact z2
      · intro c hc hne
        by_cases hcF : (c ∩ F).Nonempty
        · exact hc2' c (mem_erase.2 ⟨hne, mem_filter.2 ⟨hc, hcF⟩⟩)
        · exact sum_eq_zero fun u hu => hdF u (fun huF => hcF ⟨u, mem_inter.2 ⟨hu, huF⟩⟩)
      · intro h; exact absurd (mem_filter.1 hc0).1 h
    have hc2 : ∀ c ∈ cls' T2 F, ∑ u ∈ c, d u = 0 := by
      intro c hc
      by_cases hcc : c = c0
      · rw [hcc]; exact hc0z
      · exact hc2' c (mem_erase.2 ⟨hcc, hc⟩)
    exact ⟨d, hd0, hint d hdF, fun X hX => sum_zero_of_cls h1 d (fin1 T1 d hdF hc1) hX,
      fun X hX => sum_zero_of_cls h2 d (fin1 T2 d hdF hc2) hX⟩

end Key

/-! ### Moving along a line inside a polytope given by finitely many inequalities -/

section Line

variable {V : Type*} [Fintype V] {ι : Type*} [Fintype ι]

def dot (a x : V → ℝ) : ℝ := ∑ v, a v * x v

lemma dot_add_smul (a y d : V → ℝ) (t : ℝ) : dot a (y + t • d) = dot a y + t * dot a d := by
  simp only [dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, sum_add_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun v _ => by ring

lemma dot_neg (a d : V → ℝ) : dot a (-d) = - dot a d := by
  simp [dot, sum_neg_distrib]

def Feas (w : ι → V → ℝ) (b : ι → ℝ) (y : V → ℝ) : Prop := ∀ i, dot (w i) y ≤ b i

open Classical in
/-- the non-tight constraints -/
noncomputable def nt (w : ι → V → ℝ) (b : ι → ℝ) (y : V → ℝ) : Finset ι :=
  univ.filter (fun i => dot (w i) y < b i)

lemma mem_nt {w : ι → V → ℝ} {b : ι → ℝ} {y : V → ℝ} {i : ι} :
    i ∈ nt w b y ↔ dot (w i) y < b i := by
  classical
  simp [nt]

lemma line {w : ι → V → ℝ} {b : ι → ℝ} {y d : V → ℝ} (hy : Feas w b y)
    (hd0 : ∀ i, dot (w i) y = b i → dot (w i) d = 0) (hpos : ∃ i, 0 < dot (w i) d) :
    ∃ t : ℝ, 0 < t ∧ Feas w b (y + t • d) ∧ (nt w b (y + t • d)).card < (nt w b y).card := by
  classical
  set S := univ.filter (fun i => 0 < dot (w i) d)
  have hS' : ∀ i ∈ S, 0 < dot (w i) d := fun i hi => (mem_filter.1 hi).2
  have hS : S.Nonempty := let ⟨i, hi⟩ := hpos; ⟨i, mem_filter.2 ⟨mem_univ _, hi⟩⟩
  obtain ⟨i0, hi0, hmin⟩ := S.exists_min_image (fun i => (b i - dot (w i) y) / dot (w i) d) hS
  have slack : ∀ i ∈ S, dot (w i) y < b i :=
    fun i hi => lt_of_le_of_ne (hy i) (fun h => (hS' i hi).ne' (hd0 i h))
  set t := (b i0 - dot (w i0) y) / dot (w i0) d with ht_def
  have ht : 0 < t := div_pos (by linarith [slack i0 hi0]) (hS' i0 hi0)
  refine ⟨t, ht, fun i => ?_, ?_⟩
  · rw [dot_add_smul]
    by_cases hi : i ∈ S
    · have h' := (le_div_iff₀ (hS' i hi)).1 (hmin i hi)
      linarith
    · have : dot (w i) d ≤ 0 := by
        by_contra hc
        exact hi (mem_filter.2 ⟨mem_univ _, lt_of_not_ge hc⟩)
      have := mul_nonpos_of_nonneg_of_nonpos ht.le this
      linarith [hy i]
  · apply card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨i0, mem_nt.2 (slack i0 hi0), ?_⟩
      rw [mem_nt, dot_add_smul, ht_def, div_mul_cancel₀ _ (hS' i0 hi0).ne']
      linarith
    · intro i hi
      rw [mem_nt] at hi ⊢
      by_contra hc
      have htight : dot (w i) y = b i := le_antisymm (hy i) (not_lt.1 hc)
      rw [dot_add_smul, hd0 i htight, htight] at hi
      simp at hi

end Line


/-! ### Integrality of the truncated intersection -/

section Integral

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- the two functions indexed by `Bool` -/
def rho (ρ1 ρ2 : Finset V → WithTop ℝ) : Bool → Finset V → WithTop ℝ
  | true => ρ1
  | false => ρ2

/-- constraint rows: `x(X) ≤ ρ_b(X)` (vacuous `0 ≤ 0` if `ρ_b(X) = ⊤`) and `-x(v) ≤ -N` -/
noncomputable def Wc (ρ1 ρ2 : Finset V → WithTop ℝ) : (Bool × Finset V) ⊕ V → V → ℝ
  | .inl p => if rho ρ1 ρ2 p.1 p.2 = ⊤ then 0 else ind p.2
  | .inr v => fun u => if u = v then -1 else 0

/-- right-hand sides -/
noncomputable def Bc (ρ1 ρ2 : Finset V → WithTop ℝ) (N : ℝ) : (Bool × Finset V) ⊕ V → ℝ
  | .inl p => (rho ρ1 ρ2 p.1 p.2).untopD 0
  | .inr _ => -N

variable {ρ1 ρ2 : Finset V → WithTop ℝ}

lemma dot_Wc_inl_top {b : Bool} {X : Finset V} (h : rho ρ1 ρ2 b X = ⊤) (y : V → ℝ) :
    dot (Wc ρ1 ρ2 (.inl (b, X))) y = 0 := by
  simp [Wc, h, dot]

lemma dot_Wc_inl {b : Bool} {X : Finset V} (h : rho ρ1 ρ2 b X ≠ ⊤) (y : V → ℝ) :
    dot (Wc ρ1 ρ2 (.inl (b, X))) y = ∑ v ∈ X, y v := by
  simp only [Wc, if_neg h]
  exact dot_ind X y

lemma dot_Wc_inr (v : V) (y : V → ℝ) : dot (Wc ρ1 ρ2 (.inr v)) y = - y v := by
  simp [Wc, dot, ite_mul]

lemma Bc_inl {N : ℝ} {b : Bool} {X : Finset V} {r : ℝ} (h : rho ρ1 ρ2 b X = r) :
    Bc ρ1 ρ2 N (.inl (b, X)) = r := by
  simp [Bc, h]

lemma feas_iff {N : ℝ} {y : V → ℝ} : Feas (Wc ρ1 ρ2) (Bc ρ1 ρ2 N) y ↔
    (∀ b X, ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) ≤ rho ρ1 ρ2 b X) ∧ ∀ v, N ≤ y v := by
  constructor
  · intro h
    refine ⟨fun b X => ?_, fun v => ?_⟩
    · have := h (.inl (b, X))
      rcases wt_cases (rho ρ1 ρ2 b X) with hX | ⟨r, hX⟩
      · rw [hX]; exact le_top
      · rw [dot_Wc_inl (by rw [hX]; exact WithTop.coe_ne_top), Bc_inl hX] at this
        rw [hX]; exact WithTop.coe_le_coe.2 this
    · have := h (.inr v)
      rw [dot_Wc_inr] at this
      simp only [Bc] at this
      linarith
  · rintro ⟨h1, h2⟩ (⟨b, X⟩ | v)
    · rcases wt_cases (rho ρ1 ρ2 b X) with hX | ⟨r, hX⟩
      · rw [dot_Wc_inl_top hX]; simp [Bc, hX]
      · rw [dot_Wc_inl (by rw [hX]; exact WithTop.coe_ne_top), Bc_inl hX]
        have := h1 b X
        rw [hX] at this
        exact WithTop.coe_le_coe.1 this
    · rw [dot_Wc_inr]
      simp only [Bc]
      linarith [h2 v]

lemma tight_aux {p q : WithTop ℝ} {s t : ℝ} (hp : (s : WithTop ℝ) ≤ p) (hq : (t : WithTop ℝ) ≤ q)
    (h : p + q ≤ ((s + t : ℝ) : WithTop ℝ)) : p = s ∧ q = t := by
  rcases wt_cases p with rfl | ⟨a, rfl⟩
  · rw [top_add] at h; exact absurd h (WithTop.not_top_le_coe _)
  rcases wt_cases q with rfl | ⟨b, rfl⟩
  · rw [add_top] at h; exact absurd h (WithTop.not_top_le_coe _)
  rw [WithTop.coe_le_coe] at hp hq
  rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
  exact ⟨WithTop.coe_inj.2 (by linarith), WithTop.coe_inj.2 (by linarith)⟩

theorem integral_trunc (G : AddSubgroup ℝ) (hs1 : SubOn univ ρ1) (hs2 : SubOn univ ρ2)
    (h01 : ρ1 ∅ = 0) (h02 : ρ2 ∅ = 0) (hT : ρ1 univ ≠ ⊤) (hv1 : ValIn G ρ1) (hv2 : ValIn G ρ2)
    {N : ℝ} (hN : N ∈ G) :
    ∀ n : ℕ, ∀ y : V → ℝ, Feas (Wc ρ1 ρ2) (Bc ρ1 ρ2 N) y →
      (nt (Wc ρ1 ρ2) (Bc ρ1 ρ2 N) y).card ≤ n →
      y ∈ convexHull ℝ {z | Feas (Wc ρ1 ρ2) (Bc ρ1 ρ2 N) z ∧ ∀ v, z v ∈ G} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hy hn
  by_cases hint : ∀ v, y v ∈ G
  · exact subset_convexHull ℝ _ ⟨hy, hint⟩
  push Not at hint
  obtain ⟨hP, -⟩ := feas_iff.1 hy
  classical
  have hsub : ∀ b, SubOn univ (rho ρ1 ρ2 b) := by intro b; cases b; exacts [hs2, hs1]
  have h0 : ∀ b, rho ρ1 ρ2 b ∅ = 0 := by intro b; cases b; exacts [h02, h01]
  have hv : ∀ b, ValIn G (rho ρ1 ρ2 b) := by intro b; cases b; exacts [hv2, hv1]
  let Tb : Bool → Finset (Finset V) := fun b =>
    univ.filter (fun X => rho ρ1 ρ2 b X = ((∑ v ∈ X, y v : ℝ) : WithTop ℝ))
  have hTb : ∀ b X, X ∈ Tb b ↔ rho ρ1 ρ2 b X = ((∑ v ∈ X, y v : ℝ) : WithTop ℝ) := by
    intro b X; simp [Tb]
  have hL : ∀ b, IsLat (Tb b) := by
    intro b
    refine ⟨(hTb b ∅).2 (by rw [h0 b, sum_empty, WithTop.coe_zero]), fun X hX Y hY => ?_,
      fun X hX Y hY => ?_⟩
    · rw [hTb] at hX hY ⊢
      have hs := hsub b X (subset_univ _) Y (subset_univ _)
      rw [hX, hY, ← WithTop.coe_add, ← sum_union_inter] at hs
      exact (tight_aux (hP b _) (hP b _) hs).1
    · rw [hTb] at hX hY ⊢
      have hs := hsub b X (subset_univ _) Y (subset_univ _)
      rw [hX, hY, ← WithTop.coe_add, ← sum_union_inter] at hs
      exact (tight_aux (hP b _) (hP b _) hs).2
  have hI : ∀ b, ∀ X ∈ Tb b, ∑ u ∈ X, y u ∈ G := by
    intro b X hX
    rw [hTb] at hX
    rcases hv b X with h | ⟨g, hg, h⟩
    · rw [h] at hX; exact absurd hX.symm WithTop.coe_ne_top
    · rw [h, WithTop.coe_inj] at hX; rw [← hX]; exact hg
  obtain ⟨d, hd0, hdi, hd1, hd2⟩ := key G y (hL true) (hL false) (hI true) (hI false) hint
  have hdT : ∀ b, ∀ X ∈ Tb b, ∑ u ∈ X, d u = 0 := by intro b; cases b; exacts [hd2, hd1]
  have htight : ∀ i, dot (Wc ρ1 ρ2 i) y = Bc ρ1 ρ2 N i → dot (Wc ρ1 ρ2 i) d = 0 := by
    rintro (⟨b, X⟩ | v) h
    · rcases wt_cases (rho ρ1 ρ2 b X) with hX | ⟨r, hX⟩
      · exact dot_Wc_inl_top hX d
      · have hne : rho ρ1 ρ2 b X ≠ ⊤ := by rw [hX]; exact WithTop.coe_ne_top
        rw [dot_Wc_inl hne, Bc_inl hX] at h
        rw [dot_Wc_inl hne]
        exact hdT b X ((hTb b X).2 (by rw [hX, h]))
    · rw [dot_Wc_inr] at h ⊢
      simp only [Bc] at h
      have : y v = N := by linarith
      rw [hdi v (this ▸ hN), neg_zero]
  have htight' : ∀ i, dot (Wc ρ1 ρ2 i) y = Bc ρ1 ρ2 N i → dot (Wc ρ1 ρ2 i) (-d) = 0 := by
    intro i h; rw [dot_neg, htight i h, neg_zero]
  have hpos : ∀ e : V → ℝ, e ≠ 0 → ∃ i, 0 < dot (Wc ρ1 ρ2 i) e := by
    intro e he
    by_cases hneg : ∃ v, e v < 0
    · obtain ⟨v, hv⟩ := hneg
      exact ⟨.inr v, by rw [dot_Wc_inr]; linarith⟩
    · push Not at hneg
      obtain ⟨v, hv⟩ : ∃ v, e v ≠ 0 := by
        by_contra hc
        push Not at hc
        exact he (funext hc)
      refine ⟨.inl (true, univ), ?_⟩
      rw [dot_Wc_inl (by simpa [rho] using hT)]
      exact sum_pos' (fun u _ => hneg u) ⟨v, mem_univ _, lt_of_le_of_ne (hneg v) (Ne.symm hv)⟩
  obtain ⟨t1, ht1, hy1, hc1⟩ := line hy htight (hpos d hd0)
  obtain ⟨t2, ht2, hy2, hc2⟩ := line hy htight' (hpos (-d) (neg_ne_zero.2 hd0))
  have m1 := ih _ (lt_of_lt_of_le hc1 hn) _ hy1 le_rfl
  have m2 := ih _ (lt_of_lt_of_le hc2 hn) _ hy2 le_rfl
  have hsum : 0 < t1 + t2 := by linarith
  have := (convex_convexHull ℝ _) m1 m2 (div_pos ht2 hsum).le (div_pos ht1 hsum).le
    (by field_simp; ring)
  convert this using 1
  ext v
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  field_simp
  ring

end Integral

end EdmondsInt

/-! ### The theorem -/

namespace EdmondsInt

open DiscreteConvex.MConvexSets Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- the integers, as an additive subgroup of `ℝ` -/
def Zs : AddSubgroup ℝ := (Int.castAddHom ℝ).range

lemma mem_Zs {r : ℝ} : r ∈ Zs ↔ ∃ k : ℤ, r = k := by
  simp only [Zs, AddMonoidHom.mem_range, Int.coe_castAddHom]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

lemma one_mem_Zs : (1 : ℝ) ∈ Zs := mem_Zs.2 ⟨1, by simp⟩

lemma valIn_top (ρ : Finset V → WithTop ℝ) : ValIn ⊤ ρ := by
  intro X
  rcases wt_cases (ρ X) with h | ⟨r, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨r, AddSubgroup.mem_top r, h⟩

lemma valIn_Zs {ρ : Finset V → WithTop ℝ} (h : IsIntegerValued ρ) : ValIn Zs ρ := by
  intro X
  rcases h X with h | ⟨k, hk⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, mem_Zs.2 ⟨k, rfl⟩, hk⟩

lemma subOn_univ {ρ : Finset V → WithTop ℝ} (h : SubmodularSetFunction ρ) : SubOn univ ρ :=
  fun X _ Y _ => h.2.2 X Y

lemma toE_le {a b : WithTop ℝ} : ToEReal a ≤ ToEReal b ↔ a ≤ b := WithBot.coe_le_coe

lemma toE_add (a b : WithTop ℝ) : ToEReal (a + b) = ToEReal a + ToEReal b := by
  rcases wt_cases a with rfl | ⟨r, rfl⟩
  · rw [top_add]
    rcases wt_cases b with rfl | ⟨s, rfl⟩
    · rfl
    · exact (EReal.top_add_coe s).symm
  rcases wt_cases b with rfl | ⟨s, rfl⟩
  · rw [add_top]; exact (EReal.coe_add_top r).symm
  · rw [← WithTop.coe_add]; exact EReal.coe_add r s

lemma convex_poly (ρ : Finset V → WithTop ℝ) : Convex ℝ (SubmodularPolyhedron ρ) := by
  intro x hx y hy a b ha hb hab X
  have e : ∑ v ∈ X, (a • x + b • y) v = a * ∑ v ∈ X, x v + b * ∑ v ∈ X, y v := by
    simp [sum_add_distrib, mul_sum]
  rw [e]
  have h1 := hx X
  have h2 := hy X
  rcases wt_cases (ρ X) with h | ⟨r, h⟩
  · rw [h]; exact le_top
  · rw [h, WithTop.coe_le_coe] at h1 h2 ⊢
    have : r = a * r + b * r := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma weak {x : V → ℝ} {ρ1 ρ2 : Finset V → WithTop ℝ}
    (hx : x ∈ SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2) (X : Finset V) :
    ((∑ v, x v : ℝ) : WithTop ℝ) ≤ ρ1 X + ρ2 Xᶜ := by
  rw [← sum_add_sum_compl X, WithTop.coe_add]
  exact add_le_add (hx.1 X) (hx.2 Xᶜ)

end EdmondsInt

open DiscreteConvex.MConvexSets EdmondsInt Finset in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ1 ρ2 : Finset V → WithTop ℝ) (hρ1 : SubmodularSetFunction ρ1)
    (hρ2 : SubmodularSetFunction ρ2) :
    (∃ m : EReal,
        IsGreatest ((fun x : V → ℝ => ToEReal ((∑ v, x v : ℝ) : WithTop ℝ)) ''
          (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2)) m ∧
        IsLeast ((fun X : Finset V => ToEReal (ρ1 X) + ToEReal (ρ2 Xᶜ)) ''
          (Set.univ : Set (Finset V))) m) ∧
    (IsIntegerValued ρ1 → IsIntegerValued ρ2 →
      IsIntegralPolyhedron (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2) ∧
      ∃ x ∈ SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2, (∀ v, ∃ k : ℤ, x v = (k : ℝ)) ∧
        IsGreatest ((fun y : V → ℝ => ToEReal ((∑ v, y v : ℝ) : WithTop ℝ)) ''
          (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2))
          (ToEReal ((∑ v, x v : ℝ) : WithTop ℝ))) := by
  classical
  have hS1 := subOn_univ hρ1
  have hS2 := subOn_univ hρ2
  -- an optimal vector from the induction, in a given subgroup
  have opt : ∀ G : AddSubgroup ℝ, (1 : ℝ) ∈ G → ValIn G ρ1 → ValIn G ρ2 →
      ∃ x ∈ SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2, (∀ v, x v ∈ G) ∧
        ∃ U : Finset V, ρ1 U + ρ2 Uᶜ ≤ ((∑ v, x v : ℝ) : WithTop ℝ) := by
    intro G hG hv1 hv2
    obtain ⟨x, hxG, hxf, U, -, hU⟩ :=
      exists_opt G hG univ ρ1 ρ2 hρ1.1 hρ2.1 hρ1.2.1 hS1 hS2 hv1 hv2
    refine ⟨x, ⟨fun X => (hxf X (subset_univ _)).1, fun X => (hxf X (subset_univ _)).2⟩, hxG,
      U, ?_⟩
    rwa [compl_eq_univ_sdiff]
  -- greatest element of the image, given an optimal vector
  have great : ∀ x ∈ SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2, ∀ U : Finset V,
      ρ1 U + ρ2 Uᶜ ≤ ((∑ v, x v : ℝ) : WithTop ℝ) →
      IsGreatest ((fun y : V → ℝ => ToEReal ((∑ v, y v : ℝ) : WithTop ℝ)) ''
        (SubmodularPolyhedron ρ1 ∩ SubmodularPolyhedron ρ2)) (ToEReal ((∑ v, x v : ℝ) : WithTop ℝ)) := by
    intro x hx U hU
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact toE_le.2 ((weak hz U).trans hU)
  refine ⟨?_, fun hI1 hI2 => ⟨?_, ?_⟩⟩
  · obtain ⟨X0, -, hmin⟩ := (univ : Finset (Finset V)).exists_min_image
      (fun X => ρ1 X + ρ2 Xᶜ) univ_nonempty
    obtain ⟨x, hx, -, U, hU⟩ := opt ⊤ (AddSubgroup.mem_top 1) (valIn_top ρ1) (valIn_top ρ2)
    have hle : ((∑ v, x v : ℝ) : WithTop ℝ) ≤ ρ1 X0 + ρ2 X0ᶜ := weak hx X0
    have heq : ((∑ v, x v : ℝ) : WithTop ℝ) = ρ1 X0 + ρ2 X0ᶜ :=
      le_antisymm hle ((hmin U (mem_univ _)).trans hU)
    refine ⟨ToEReal ((∑ v, x v : ℝ) : WithTop ℝ), great x hx U hU, ⟨X0, Set.mem_univ _, ?_⟩, ?_⟩
    · simp only; rw [heq, toE_add]
    · rintro _ ⟨X, -, rfl⟩
      simp only
      rw [← toE_add, heq]
      exact toE_le.2 (hmin X (mem_univ _))
  · -- integrality
    unfold IsIntegralPolyhedron
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ v, (N : ℝ) ≤ x v := by
        refine ⟨-⌈∑ v, |x v|⌉, fun v => ?_⟩
        push_cast
        have h1 := Int.le_ceil (∑ v, |x v|)
        have h2 : |x v| ≤ ∑ u, |x u| := single_le_sum (fun u _ => abs_nonneg (x u)) (mem_univ v)
        have h3 := neg_abs_le (x v)
        linarith
      have hfe : Feas (Wc ρ1 ρ2) (Bc ρ1 ρ2 N) x := by
        refine feas_iff.2 ⟨fun b X => ?_, hN⟩
        cases b
        · exact hx.2 X
        · exact hx.1 X
      have := integral_trunc Zs hS1 hS2 hρ1.1 hρ2.1 hρ1.2.1 (valIn_Zs hI1) (valIn_Zs hI2)
        (mem_Zs.2 ⟨N, rfl⟩) _ x hfe le_rfl
      refine convexHull_mono ?_ this
      rintro z ⟨hz, hzi⟩
      obtain ⟨hz1, -⟩ := feas_iff.1 hz
      exact ⟨⟨fun X => hz1 true X, fun X => hz1 false X⟩, fun v => mem_Zs.1 (hzi v)⟩
    · exact convexHull_min Set.inter_subset_left ((convex_poly ρ1).inter (convex_poly ρ2))
  · obtain ⟨x, hx, hxi, U, hU⟩ := opt Zs one_mem_Zs (valIn_Zs hI1) (valIn_Zs hI2)
    exact ⟨x, hx, fun v => mem_Zs.1 (hxi v), great x hx U hU⟩
