-- Prove2me | solution 1 for Finset.prod_one_sub_le_weightProb_forall_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:02:37.418028+00:00
-- url     : https://prove2.me/submissions/56ba1070-a052-4034-8534-7033ed865073

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
public import Theorems.Thm_Finset_bernoulliProb_true
public import Theorems.Thm_Finset_weightProb_nonneg
public import Theorems.Thm_Finset_weightProb_mono
public import Theorems.Thm_Finset_weightProb_eq_add
public import Theorems.Thm_Finset_avoids_insert
attribute [local simp] Finset.bernoulliProb_true
section
@[expose] public section
open Finset Real
namespace Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
section Basic
variable (U p)
variable {U p}
end Basic
section Weights
variable {β : Type*}
variable {Ω : Finset β} {w : β → ℝ}
end Weights
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
private theorem prod_le_one_of_mem_Icc {s : Finset ι} {f : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) : ∏ i ∈ s, f i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha]
    have hs0 : 0 ≤ ∏ i ∈ s, f i := prod_nonneg fun i hi => h0 i (mem_insert_of_mem hi)
    have hs1 := ih (fun i hi => h0 i (mem_insert_of_mem hi)) fun i hi => h1 i (mem_insert_of_mem hi)
    nlinarith [h0 a (mem_insert_self a s), h1 a (mem_insert_self a s)]
private theorem prod_le_prod_of_superset_of_le_one {s t : Finset ι} (hst : s ⊆ t) (f : ι → ℝ)
    (h0 : ∀ i ∈ t, 0 ≤ f i) (h1 : ∀ i ∈ t, f i ≤ 1) : ∏ i ∈ t, f i ≤ ∏ i ∈ s, f i := by
  classical
  rw [← prod_sdiff hst]
  refine mul_le_of_le_one_left (prod_nonneg fun i hi => h0 i (hst hi)) ?_
  exact prod_le_one_of_mem_Icc (fun i hi => h0 i (mem_sdiff.mp hi).1)
    fun i hi => h1 i (mem_sdiff.mp hi).1
section Weights
variable {Ω : Finset β} {w : β → ℝ}
private theorem weightProb_avoids_insert [DecidableEq ι] (i : ι) (S : Finset ι) :
    Ω.weightProb w (Avoids E (insert i S)) =
      Ω.weightProb w (Avoids E S) - Ω.weightProb w (fun a => E i a ∧ Avoids E S a) := by
  have := weightProb_eq_add Ω w (Avoids E S) (E i)
  have heq : Ω.weightProb w (Avoids E (insert i S)) =
      Ω.weightProb w (fun a => Avoids E S a ∧ ¬E i a) := by
    unfold weightProb
    congr 1
    ext a
    simp [avoids_insert, and_comm]
  have heq2 : Ω.weightProb w (fun a => E i a ∧ Avoids E S a) =
      Ω.weightProb w (fun a => Avoids E S a ∧ E i a) := by
    unfold weightProb
    congr 1
    ext a
    simp [and_comm]
  linarith
private theorem weightProb_and_avoids_le (hw0 : ∀ a ∈ Ω, 0 ≤ w a) {I : Finset ι}
    {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ) {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i)
    (hx1 : ∀ i, x i ≤ 1) (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j))
    (n : ℕ) : ∀ S ⊆ I, #S = n → ∀ i ∈ I, i ∉ S →
      Ω.weightProb w (fun a => E i a ∧ Avoids E S a) ≤ x i * Ω.weightProb w (Avoids E S) := by
  classical
  set μ := Ω.weightProb w
  have hμ0 : ∀ (P : β → Prop) [DecidablePred P], 0 ≤ Ω.weightProb w P :=
    fun P _ => weightProb_nonneg hw0 P
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hS hn i hi hiS
    -- adding an index to a smaller set keeps a fraction `1 - x j`
    have step : ∀ T ⊆ I, #T < n → ∀ j ∈ I, j ∉ T →
        (1 - x j) * μ (Avoids E T) ≤ μ (Avoids E (insert j T)) := by
      intro T hT hTn j hj hjT
      have hs : μ (Avoids E (insert j T)) =
          μ (Avoids E T) - μ (fun a => E j a ∧ Avoids E T a) := weightProb_avoids_insert j T
      rw [hs]
      have := ih _ hTn T hT rfl j hj hjT
      nlinarith
    set S₂ := S.filter (· ∉ Γ i)
    set S₁ := S.filter (· ∈ Γ i)
    have hS₂ : S₂ ⊆ S := filter_subset _ _
    -- avoiding `S` costs at most the product over `S₁`
    have hgrow : ∀ T ⊆ S₁, (∏ j ∈ T, (1 - x j)) * μ (Avoids E S₂) ≤ μ (Avoids E (S₂ ∪ T)) := by
      intro T hT
      induction T using Finset.induction_on with
      | empty => simp
      | insert j T hjT ihT =>
        have hT' := (insert_subset_iff.mp hT).2
        have hj := (insert_subset_iff.mp hT).1
        have hjS : j ∈ S := (mem_filter.mp hj).1
        have hjS₂ : j ∉ S₂ := fun h => (mem_filter.mp h).2 (mem_filter.mp hj).2
        have hsub : S₂ ∪ T ⊆ S.erase j := fun y hy => by
          rcases mem_union.mp hy with hy | hy
          · exact mem_erase.mpr ⟨fun h => hjS₂ (h ▸ hy), hS₂ hy⟩
          · exact mem_erase.mpr ⟨fun h => hjT (h ▸ hy), (mem_filter.mp (hT' hy)).1⟩
        have hlt : #(S₂ ∪ T) < n := by
          rw [← hn]
          exact (card_le_card hsub).trans_lt (card_erase_lt_of_mem hjS)
        have := step (S₂ ∪ T) (hsub.trans ((erase_subset _ _).trans hS)) hlt j (hS hjS)
          fun h => (mem_union.mp h).elim hjS₂ hjT
        rw [prod_insert hjT, union_insert]
        calc (1 - x j) * (∏ k ∈ T, (1 - x k)) * μ (Avoids E S₂)
            = (1 - x j) * ((∏ k ∈ T, (1 - x k)) * μ (Avoids E S₂)) := by ring
          _ ≤ (1 - x j) * μ (Avoids E (S₂ ∪ T)) :=
              mul_le_mul_of_nonneg_left (ihT hT') (by linarith [hx1 j])
          _ ≤ _ := this
    have hS12 : S₂ ∪ S₁ = S := by
      ext j
      simp only [S₂, S₁, mem_union, mem_filter]
      tauto
    have hgrowS := hgrow S₁ Subset.rfl
    rw [hS12] at hgrowS
    have hprod : ∏ j ∈ Γ i, (1 - x j) ≤ ∏ j ∈ S₁, (1 - x j) := by
      refine prod_le_prod_of_superset_of_le_one (fun j hj => (mem_filter.mp hj).2) _
        (fun j _ => ?_)
        (fun j _ => ?_)
      · linarith [hx1 j]
      · linarith [hx0 j]
    calc μ (fun a => E i a ∧ Avoids E S a)
        ≤ μ (fun a => E i a ∧ Avoids E S₂ a) := weightProb_mono hw0 fun a ha =>
          ⟨ha.1, fun j hj => ha.2 j (hS₂ hj)⟩
      _ ≤ μ (E i) * μ (Avoids E S₂) := hL i hi S₂ (hS₂.trans hS)
          (disjoint_left.mpr fun j hj hjΓ => (mem_filter.mp hj).2 hjΓ)
          fun h => hiS (hS₂ h)
      _ ≤ x i * (∏ j ∈ Γ i, (1 - x j)) * μ (Avoids E S₂) :=
          mul_le_mul_of_nonneg_right (hp i hi) (hμ0 _)
      _ ≤ x i * (∏ j ∈ S₁, (1 - x j)) * μ (Avoids E S₂) := by
          gcongr
          · exact hμ0 _
          · exact hx0 i
      _ = x i * ((∏ j ∈ S₁, (1 - x j)) * μ (Avoids E S₂)) := by ring
      _ ≤ x i * μ (Avoids E S) := mul_le_mul_of_nonneg_left hgrowS (hx0 i)
end Weights
variable {E : ι → Finset α → Prop} [∀ i, DecidablePred (E i)]
end Finset
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable {β : Type*} (E : ι → β → Prop) [∀ i, DecidablePred (E i)]
variable {E}
variable {Ω : Finset β} {w : β → ℝ}
namespace Finset
theorem _root_.solution (hw0 : ∀ a ∈ Ω, 0 ≤ w a)
    (hw1 : ∑ a ∈ Ω, w a = 1) {I : Finset ι} {Γ : ι → Finset ι} (hL : LopsidedWeights Ω w I E Γ)
    {x : ι → ℝ} (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hp : ∀ i ∈ I, Ω.weightProb w (E i) ≤ x i * ∏ j ∈ Γ i, (1 - x j)) :
    ∏ i ∈ I, (1 - x i) ≤ Ω.weightProb w (Avoids E I) := by
  classical
  -- multiply up over `I`
  have hall : ∀ T ⊆ I, ∏ i ∈ T, (1 - x i) ≤ Ω.weightProb w (Avoids E T) := by
    intro T hT
    induction T using Finset.induction_on with
    | empty =>
      rw [prod_empty]
      refine le_of_eq ?_
      unfold weightProb
      rw [filter_true_of_mem fun a _ j hj => absurd hj (notMem_empty j), hw1]
    | insert j T hjT ihT =>
      have hT' := (insert_subset_iff.mp hT).2
      have hj := (insert_subset_iff.mp hT).1
      rw [prod_insert hjT, weightProb_avoids_insert]
      have := weightProb_and_avoids_le hw0 hL hx0 hx1 hp _ T hT' rfl j hj hjT
      have h1j : 0 ≤ 1 - x j := by linarith [hx1 j]
      nlinarith [ihT hT', mul_le_mul_of_nonneg_left (ihT hT') h1j]
  exact hall I Subset.rfl
end Finset
