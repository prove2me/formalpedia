-- Prove2me | solution 1 for BSLambda.LLL.pr_le_prod_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:25:20.98505+00:00
-- url     : https://prove2.me/submissions/8922703d-8597-44a6-b2b8-cbd501ac3f61

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Theorems.Thm_BSLambda_LLL_mem_fibre_restrict
public import Theorems.Thm_BSLambda_LLL_determined_fibre
public import Theorems.Thm_BSLambda_LLL_sum_pr_fibre
public import Theorems.Thm_BSLambda_LLL_determined_pin
public import Theorems.Thm_BSLambda_LLL_pr_inter_of_disjoint_support
public import Theorems.Thm_BSLambda_LLL_pr_le_of_subset_biUnion
public import Theorems.Thm_BSLambda_LLL_pr_nonneg
public import Theorems.Thm_BSLambda_LLL_pr_pin_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [∀ a, DecidableEq (β a)]
namespace BSLambda.LLL
theorem _root_.solution {G T : Finset A} (hGT : Disjoint G T)
    (tgt : ((a : A) → a ∈ G → β a) → (a : A) → Finset (β a)) (m : ℕ)
    (hm : ∀ c, ∀ a ∈ T, (tgt c a).card ≤ m) {E : Finset (Cfg β)}
    (hE : ∀ ω ∈ E, ∀ a ∈ T, ω a ∈ tgt (fun b _ ↦ ω b) a) :
    pr E ≤ ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
  classical
  set C : Finset ((a : A) → a ∈ G → β a) := G.pi fun a ↦ (Finset.univ : Finset (β a))
  set P : ((a : A) → a ∈ G → β a) → Finset (Cfg β) :=
    fun c ↦ Finset.univ.filter fun ω : Cfg β ↦ ∀ a ∈ T, ω a ∈ tgt c a
  have hsub : E ⊆ C.biUnion fun c ↦ fibre G c ∩ P c := fun ω hω ↦
    Finset.mem_biUnion.mpr ⟨fun a _ ↦ ω a, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _,
      Finset.mem_inter.mpr ⟨mem_fibre_restrict ω, (Finset.mem_filter_univ ω).mpr (hE ω hω)⟩⟩
  calc pr E ≤ ∑ c ∈ C, pr (fibre G c ∩ P c) := pr_le_of_subset_biUnion C _ hsub
    _ = ∑ c ∈ C, pr (fibre G c) * pr (P c) := Finset.sum_congr rfl fun c _ ↦
        pr_inter_of_disjoint_support (determined_fibre c) (determined_pin T (tgt c)) hGT
    _ ≤ ∑ c ∈ C, pr (fibre G c) * ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) :=
        Finset.sum_le_sum fun c _ ↦
          mul_le_mul_of_nonneg_left (pr_pin_le T (tgt c) m (hm c)) (pr_nonneg _)
    _ = ∏ a ∈ T, (m : ℝ) / (Fintype.card (β a) : ℝ) := by
        rw [← Finset.sum_mul, sum_pr_fibre, one_mul]
end BSLambda.LLL
