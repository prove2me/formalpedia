-- Prove2me | solution 1 for BSLambda.LLL.card_miss_add_card_disc_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:24.70995+00:00
-- url     : https://prove2.me/submissions/8ad2a0b2-3b07-480b-982b-118a993d6142

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_card_discSet_eq_sum
public import Theorems.Thm_BSLambda_LLL_card_missArcs_eq_sum
public import Theorems.Thm_BSLambda_LLL_intObstruction_two_nonowner

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι]
namespace BSLambda.LLL
theorem _root_.solution [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S)
    {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 2) :
    (missArcs Arc γ Z (S.erase h)).card + (discSet γ Z (S.erase h) h).card ≤ 8 := by
  have hEcard : (S.erase h).card = 8 := by rw [Finset.card_erase_of_mem hh, hS]
  rw [card_missArcs_eq_sum hT, card_discSet_eq_sum, ← Finset.sum_add_distrib]
  calc ∑ j ∈ S.erase h, ((missSet Arc γ Z (S.erase h) j).card
          + if Z j ⊆ {γ h j} then 0 else 1)
      ≤ ∑ _j ∈ S.erase h, 1 := Finset.sum_le_sum fun j hjE ↦
        (intObstruction_two_nonowner hT hh hZh hgate hjE
          (hbud j (Finset.mem_of_mem_erase hjE) (Finset.ne_of_mem_erase hjE))).2
    _ = 8 := by rw [Finset.sum_const, hEcard, smul_eq_mul, mul_one]
end BSLambda.LLL
