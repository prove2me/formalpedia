-- Prove2me | solution 1 for BSLambda.LLL.pr_avoid_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:24:21.485817+00:00
-- url     : https://prove2.me/submissions/af2e200d-f5c3-4872-96ce-cc3d7f8780ad

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_mem_nbr
public import Theorems.Thm_BSLambda_LLL_disjoint_supp_sup_sdiff_nbr
public import Theorems.Thm_BSLambda_LLL_mem_avoid
public import Theorems.Thm_BSLambda_LLL_avoid_empty
public import Theorems.Thm_BSLambda_LLL_avoid_univ
public import Theorems.Thm_BSLambda_LLL_avoid_anti
public import Theorems.Thm_BSLambda_LLL_avoid_insert
public import Theorems.Thm_BSLambda_LLL_determined_avoid
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_mem
public import Theorems.Thm_BSLambda_LLL_glue_apply_of_notMem
public import Theorems.Thm_BSLambda_LLL_pr_compl_inter
public import Theorems.Thm_BSLambda_LLL_pr_empty
public import Theorems.Thm_BSLambda_LLL_pr_inter_of_disjoint_support
public import Theorems.Thm_BSLambda_LLL_pr_mono
public import Theorems.Thm_BSLambda_LLL_pr_nonneg
public import Theorems.Thm_BSLambda_LLL_pr_univ
attribute [local simp] BSLambda.LLL.glue_apply_of_mem
attribute [local simp] BSLambda.LLL.glue_apply_of_notMem
attribute [local simp] BSLambda.LLL.pr_empty
attribute [local simp] BSLambda.LLL.pr_univ


attribute [local simp] BSLambda.LLL.mem_nbr
attribute [local simp] BSLambda.LLL.mem_avoid
attribute [local simp] BSLambda.LLL.avoid_empty
section
@[expose] public section
namespace BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
section AvoidBasic
end AvoidBasic
section Telescope
omit [∀ (a : A), Nonempty (β a)] in
/-- **Peeling one event.**  If `Ev j` is conditionally bounded by `x j` given that the events
indexed by `S` are avoided, then also avoiding `Ev j` costs at most the factor `1 - x j`. -/
private theorem mul_pr_avoid_le_pr_avoid_insert {Ev : I → Finset (Cfg β)} {x : I → ℝ} {j : I}
    {S : Finset I} (h : pr (Ev j ∩ avoid Ev S) ≤ x j * pr (avoid Ev S)) :
    (1 - x j) * pr (avoid Ev S) ≤ pr (avoid Ev (insert j S)) := by
  rw [avoid_insert, pr_compl_inter, sub_mul, one_mul]
  exact sub_le_sub_left h _
omit [∀ (a : A), Nonempty (β a)] in
/-- **Telescoping step.**  If, along the way, every single event can be bounded by its
weight `x j` conditionally on the events avoided so far, then avoiding all of `T` on top of
`U` costs at most the factor `∏ j ∈ T, (1 - x j)`. -/
private theorem le_pr_avoid_union (Ev : I → Finset (Cfg β)) (x : I → ℝ) (hx1 : ∀ j, x j ≤ 1)
    (U T : Finset I) (hstep : ∀ T' ⊆ T, ∀ j ∈ T, j ∉ T' →
      pr (Ev j ∩ avoid Ev (U ∪ T')) ≤ x j * pr (avoid Ev (U ∪ T'))) :
    (∏ j ∈ T, (1 - x j)) * pr (avoid Ev U) ≤ pr (avoid Ev (U ∪ T)) := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hIH : (∏ j ∈ T, (1 - x j)) * pr (avoid Ev U) ≤ pr (avoid Ev (U ∪ T)) :=
      ih fun T' hT' j hj hj' ↦
        hstep T' (hT'.trans (Finset.subset_insert a T)) j (Finset.mem_insert_of_mem hj) hj'
    have hge : (1 - x a) * pr (avoid Ev (U ∪ T)) ≤ pr (avoid Ev (U ∪ insert a T)) := by
      rw [Finset.union_insert]
      exact mul_pr_avoid_le_pr_avoid_insert
        (hstep T (Finset.subset_insert a T) a (Finset.mem_insert_self a T) ha)
    rw [Finset.prod_insert ha, mul_assoc]
    exact (mul_le_mul_of_nonneg_left hIH (sub_nonneg.mpr (hx1 a))).trans hge
end Telescope
section Main
variable (Ev : I → Finset (Cfg β)) (supp : I → Finset A) (x : I → ℝ)
private theorem pr_avoid_pos_of_forall_card_lt (hx1 : ∀ i, x i < 1) (S : Finset I)
    (IH : ∀ T : Finset I, T.card < S.card →
      0 < pr (avoid Ev T) ∧ ∀ i ∉ T, pr (Ev i ∩ avoid Ev T) ≤ x i * pr (avoid Ev T)) :
    0 < pr (avoid Ev S) := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨j, hj⟩
  · simp
  obtain ⟨hpos, hbnd⟩ := IH (S.erase j) (Finset.card_erase_lt_of_mem hj)
  have h1 : (1 - x j) * pr (avoid Ev (S.erase j)) ≤ pr (avoid Ev S) := by
    conv_rhs => rw [← Finset.insert_erase hj]
    exact mul_pr_avoid_le_pr_avoid_insert (hbnd j (Finset.notMem_erase j S))
  exact (mul_pos (sub_pos.mpr (hx1 j)) hpos).trans_le h1
private theorem pr_inter_avoid_le_of_forall_card_lt (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) (S : Finset I)
    (IH : ∀ T : Finset I, T.card < S.card →
      ∀ i ∉ T, pr (Ev i ∩ avoid Ev T) ≤ x i * pr (avoid Ev T))
    {i : I} (hi : i ∉ S) :
    pr (Ev i ∩ avoid Ev S) ≤ x i * pr (avoid Ev S) := by
  -- the events indexed outside `nbr supp i` are independent of `Ev i`
  have hind : pr (Ev i ∩ avoid Ev (S \ nbr supp i))
      = pr (Ev i) * pr (avoid Ev (S \ nbr supp i)) :=
    pr_inter_of_disjoint_support (hdet i) (determined_avoid hdet _)
      (disjoint_supp_sup_sdiff_nbr hi)
  -- the neighbourhood product only shrinks when restricted to `S`
  have hkey : pr (Ev i) ≤ x i * ∏ j ∈ S ∩ nbr supp i, (1 - x j) :=
    (hcond i).trans <| mul_le_mul_of_nonneg_left
      (by
        rw [← Finset.prod_sdiff Finset.inter_subset_right]
        exact mul_le_of_le_one_left
          (Finset.prod_nonneg fun j _ ↦ sub_nonneg.mpr (hx1 j).le)
          (Finset.prod_le_one (fun j _ ↦ sub_nonneg.mpr (hx1 j).le)
            fun j _ ↦ sub_le_self _ (hx0 j).le)) (hx0 i).le
  -- the telescoping lower bound on `pr (avoid Ev S)`
  have htel : (∏ j ∈ S ∩ nbr supp i, (1 - x j)) * pr (avoid Ev (S \ nbr supp i))
      ≤ pr (avoid Ev S) := by
    conv_rhs => rw [← Finset.sdiff_union_inter S (nbr supp i)]
    refine le_pr_avoid_union Ev x (fun j ↦ (hx1 j).le) _ _ fun T' hT' j hjS₁ hjT' ↦ ?_
    obtain ⟨hjS, hjnbr⟩ := Finset.mem_inter.mp hjS₁
    have hjmem : j ∉ S \ nbr supp i ∪ T' := fun h ↦
      (Finset.mem_union.mp h).elim (fun h' ↦ (Finset.mem_sdiff.mp h').2 hjnbr) hjT'
    refine IH _ ((Finset.card_le_card (Finset.subset_erase.mpr ⟨Finset.union_subset
      Finset.sdiff_subset (hT'.trans Finset.inter_subset_left), hjmem⟩)).trans_lt
      (Finset.card_erase_lt_of_mem hjS)) j hjmem
  calc pr (Ev i ∩ avoid Ev S)
      ≤ pr (Ev i ∩ avoid Ev (S \ nbr supp i)) :=
        pr_mono (Finset.inter_subset_inter_left (avoid_anti Finset.sdiff_subset))
    _ = pr (Ev i) * pr (avoid Ev (S \ nbr supp i)) := hind
    _ ≤ (x i * ∏ j ∈ S ∩ nbr supp i, (1 - x j)) * pr (avoid Ev (S \ nbr supp i)) :=
        mul_le_mul_of_nonneg_right hkey (pr_nonneg _)
    _ = x i * ((∏ j ∈ S ∩ nbr supp i, (1 - x j)) * pr (avoid Ev (S \ nbr supp i))) :=
        mul_assoc _ _ _
    _ ≤ x i * pr (avoid Ev S) := mul_le_mul_of_nonneg_left htel (hx0 i).le
private theorem pr_avoid_pos_and_inter_le (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) (S : Finset I) :
    0 < pr (avoid Ev S) ∧ ∀ i ∉ S, pr (Ev i ∩ avoid Ev S) ≤ x i * pr (avoid Ev S) := by
  generalize hn : S.card = n
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    have IH : ∀ T : Finset I, T.card < S.card →
        0 < pr (avoid Ev T) ∧ ∀ i ∉ T, pr (Ev i ∩ avoid Ev T) ≤ x i * pr (avoid Ev T) :=
      fun T hT ↦ ih T.card (hn ▸ hT) T rfl
    exact ⟨pr_avoid_pos_of_forall_card_lt Ev x hx1 S IH, fun i hi ↦
      pr_inter_avoid_le_of_forall_card_lt Ev supp x hdet hx0 hx1 hcond S
        (fun T hT ↦ (IH T hT).2) hi⟩
end Main
section TwoType
end TwoType
section Fibre
variable {G : Finset A}
end Fibre
section Pinned
end Pinned
end BSLambda.LLL
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (Ev : I → Finset (Cfg β)) (supp : I → Finset A) (x : I → ℝ)
namespace BSLambda.LLL
theorem _root_.solution (hdet : ∀ i, Determined (supp i) (Ev i))
    (hx0 : ∀ i, 0 < x i) (hx1 : ∀ i, x i < 1)
    (hcond : ∀ i, pr (Ev i) ≤ x i * ∏ j ∈ nbr supp i, (1 - x j)) :
    0 < pr (Finset.univ.filter fun ω ↦ ∀ i, ω ∉ Ev i) := by
  rw [← avoid_univ]
  exact (pr_avoid_pos_and_inter_le Ev supp x hdet hx0 hx1 hcond Finset.univ).1
end BSLambda.LLL
