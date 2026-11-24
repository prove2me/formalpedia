-- Prove2me | solution 1 for Formalism.NG.blockChiCFull_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:43:52.800088+00:00
-- url     : https://prove2.me/submissions/dc975dc2-dd3f-4d36-8cf9-b34fc22f1fc1

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Theorems.Thm_Formalism_NG_IdempotentColumnIndexImages_sum_image_colIdx
import Theorems.Thm_Formalism_NG_IdempotentColumnIndexImages_card_image_colIdx
import Theorems.Thm_Formalism_NG_blockRhoAbs
import Theorems.Thm_Formalism_NG_cobColumn
import Theorems.Thm_Formalism_NG_colPsiKer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
universe u₁ u₂ u₃ u₄ u₅ u₆
namespace Formalism.NG
theorem _root_.solution (hK : StatColKerChiC.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiCFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j Kc k0 ℓ cB sE tE
    hd hE hEE he₁ hEM hk0 hδ hτ ρM Ψ lrows qs F deg vζ Q Sha H0 cols eO vδ hH0 hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    he₁ hEM hk0 (fun m => by rw [algebraMap_smul]; exact hδ m)
  have hsumH : ∑ l : ι, Module.length O
      (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l)))) ≤ ∑ w ∈ cols, H0 := by
    calc ∑ l : ι, Module.length O
          (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l))))
        ≤ ∑ l : ι, H0 :=
          Finset.sum_le_sum fun l _ => hH0 (colIdx l) (Finset.mem_image_of_mem _ (Finset.mem_univ l))
      _ = ∑ w ∈ cols, H0 := (IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun _ => H0)).symm
  have hker' : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) *
        (eO * (((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) + vδ) + (fun _ => H0 : ι' → ℕ∞) w) +
        (cols.card : ℕ∞) * (Fintype.card d : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans ?_
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [show (cols.card : ℕ∞) = (Fintype.card ι : ℕ∞) from IdempotentColumnIndexImages.card_image_colIdx colIdx hinj]
    exact add_le_add hsumH le_rfl
  have hcob : ∀ (h : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
      (d → KO O)) (v : d → KO O), (Ψ h : G → (d → KO O)) = coD0 ρM v → (δO * δO) • v = 0 :=
    fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEM hδ hτ h v hv
  have h := blockRhoAbs O G d ρM _ Ψ δO hcob ι' (lrows ∪ qs) cols D F lenRow Q Sha ℓ
    (fun _ => 0) (fun _ => 0) (fun _ => H0) hrows hcols hQ hsel hker'
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul, hd, Nat.cast_one,
    mul_one]
  rw [hsum]
  ring
end Formalism.NG
