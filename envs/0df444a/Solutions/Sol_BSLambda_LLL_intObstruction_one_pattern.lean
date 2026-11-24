-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_one_pattern
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:04.782681+00:00
-- url     : https://prove2.me/submissions/54b51fe1-0a3c-4cc6-a646-71f42594789c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_of_owner_arc
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_of_arc_to_owner
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_card_beats_le_one
public import Theorems.Thm_BSLambda_IsTournament_arc_of_not_arc
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    (∀ j ∈ S, j ≠ h → Arc h j = true) ∨
      ∃ a ∈ S, a ≠ h ∧ Arc a h = true ∧
        ∀ j ∈ S, j ≠ h → j ≠ a → Arc h j = true ∧ Arc a j = true := by
  classical
  have hU := intObstruction_one_card_beats_le_one hT hh hobs
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  by_cases hempty : (S.filter fun j ↦ Arc j h = true) = ∅
  · rw [Finset.eq_empty_iff_forall_notMem] at hempty
    exact Or.inl fun j hj hjh ↦ hT.arc_of_not_arc (Ne.symm hjh)
      (Bool.eq_false_iff.2 fun hx ↦ hempty j (Finset.mem_filter.mpr ⟨hj, hx⟩))
  · obtain ⟨a, hamem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨haS, hah⟩ := Finset.mem_filter.1 hamem
    have hahne : a ≠ h := hT.ne_of_arc hah
    refine Or.inr ⟨a, haS, hahne, hah, fun j hj hjh hja ↦ ?_⟩
    -- `j` does not beat `h`, since `a` is the unique such vertex
    have hjf : Arc j h = false := Bool.eq_false_iff.2 fun hx ↦
      hja (Finset.card_le_one.mp hU j (Finset.mem_filter.mpr ⟨hj, hx⟩) a hamem)
    have hhj : Arc h j = true := hT.arc_of_not_arc (Ne.symm hjh) hjf
    refine ⟨hhj, ?_⟩
    -- if `j` beat `a` it would be a second miss for `j`, whose budget is already spent
    by_contra hx
    rw [Bool.not_eq_true] at hx
    obtain ⟨hZa, -⟩ := intObstruction_one_of_arc_to_owner hh hZh hbud haS hahne hah
    obtain ⟨-, hnomiss⟩ := intObstruction_one_of_owner_arc hgate hbud hj hjh hhj
    exact absurd (hZa ▸ hnomiss a haS (hT.arc_of_not_arc hja hx)) (Finset.notMem_empty _)
end BSLambda.LLL
