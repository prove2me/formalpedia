-- Prove2me | solution 1 for BSLambda.LLL.exists_gate_labelling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:16.270884+00:00
-- url     : https://prove2.me/submissions/f3bf4011-5ccb-4e27-8368-3d6601b8f888

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_exists_good_config
public import Theorems.Thm_BSLambda_LLL_card_le_three_of_good
public import Theorems.Thm_BSLambda_LLL_card_le_seven_of_good

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] (hk : Fintype.card ι = 14011)
    (hT : IsDRTournamentWith Arc 7005 3502) (hr : r = 144) :
    ∃ γ : ι → ι → Fin r,
      (∀ h x, (cert Arc γ h).Sat x →
        (Finset.univ.filter fun j => j ≠ h ∧ (cert Arc γ j).dist x = 1).card ≤ 3) ∧
      (∀ h x, (cert Arc γ h).Sat x →
        (Finset.univ.filter fun j => j ≠ h ∧ (cert Arc γ j).dist x ≤ 2).card ≤ 7) := by
  obtain ⟨ω, hgood⟩ := exists_good_config hk hT hr
  exact ⟨toGamma ω, fun h x hx ↦ card_le_three_of_good hT.toIsTournament hgood h x hx,
    fun h x hx ↦ card_le_seven_of_good hT.toIsTournament hgood h x hx⟩
end BSLambda.LLL
