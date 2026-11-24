-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_one_card_beats_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:15.459596+00:00
-- url     : https://prove2.me/submissions/fbc117af-56e2-49b6-b2e3-554897141c4a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_of_arc_to_owner
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
    (S.filter fun j => Arc j h = true).card ≤ 1 := by
  classical
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  rw [Finset.card_le_one]
  intro a hamem b hbmem
  rw [Finset.mem_filter] at hamem hbmem
  obtain ⟨haS, ha⟩ := hamem
  obtain ⟨hbS, hb⟩ := hbmem
  have hah : a ≠ h := hT.ne_of_arc ha
  have hbh : b ≠ h := hT.ne_of_arc hb
  by_contra hne
  obtain ⟨hZa, hmissa⟩ := intObstruction_one_of_arc_to_owner hh hZh hbud haS hah ha
  obtain ⟨hZb, hmissb⟩ := intObstruction_one_of_arc_to_owner hh hZh hbud hbS hbh hb
  cases hab : Arc a b with
  | true => exact absurd (hZb ▸ hmissa b hbS hbh hab) (Finset.notMem_empty _)
  | false =>
    have hba : Arc b a = true := hT.arc_of_not_arc (Ne.symm hne) hab
    exact absurd (hZa ▸ hmissb a haS hah hba) (Finset.notMem_empty _)
end BSLambda.LLL
