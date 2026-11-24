-- Prove2me | solution 1 for BSLambda.LLL.exists_active_flag_of_intObstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:55.588059+00:00
-- url     : https://prove2.me/submissions/57423619-a281-4a4e-adeb-8b212cd098bf

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_pattern
public import Theorems.Thm_BSLambda_LLL_active_flag_typeA
public import Theorems.Thm_BSLambda_LLL_active_flag_typeB
public import Theorems.Thm_BSLambda_LLL_gate_eq_of_active_of_intObstruction

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} (hS : S.card = 5) {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    ∃ F : Flag1 ι, F.Active Arc ∧ F.supp = S ∧ F.owner = h ∧
      ∀ p ∈ arcSet Arc F.nonOwners, γ p.1 p.2 = γ h p.2 := by
  rcases intObstruction_one_pattern hT hh hobs with hA | ⟨a, haS, hah, harc, hdom⟩
  · obtain ⟨hact, hsupp⟩ := active_flag_typeA hS hh hA
    exact ⟨_, hact, hsupp, rfl,
      gate_eq_of_active_of_intObstruction hT hh hobs hact hsupp rfl⟩
  · obtain ⟨hact, hsupp⟩ := active_flag_typeB hS hh haS hah harc hdom
    exact ⟨_, hact, hsupp, rfl,
      gate_eq_of_active_of_intObstruction hT hh hobs hact hsupp rfl⟩
end BSLambda.LLL
