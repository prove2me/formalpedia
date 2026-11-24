-- Prove2me | solution 1 for Formalism.NG.TrivialCharacterBlockLength.blockTrivAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:08:23.807188+00:00
-- url     : https://prove2.me/submissions/c7cc1a6a-1253-40e9-afcd-55dbd6d15543

import Definitions.Def_Formalism_CharacterColumnKernels_StatBlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
import Theorems.Thm_Formalism_NG_TrivialCharacterBlockLength_length_mid_zero
import Theorems.Thm_Formalism_NG_lenChain
import Theorems.Thm_Formalism_NG_selRelax


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.TrivialCharacterBlockLength
namespace Formalism.NG.TrivialCharacterBlockLength
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
    {H : Type*} [AddCommGroup H] [Module O H]
    (ρM : Representation O G M) (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM)
    {ι : Type*} [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
    (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
    (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞)
    (hrows : ∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))),
      F w ≤ A ∧ Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A)
    (hcols : ∀ w ∈ cols, ∀ h : H,
      resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w)
    (hQ : ∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q)
    (hsel : Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols,
      (F w).comap (resH1 ρM (D w))) ≤ s) :
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) + (s + ∑ w ∈ what₂, lenRow w) := by
  classical
  let A : ∀ w, Submodule O (H1z (resRep ρM (D w))) := fun w =>
    if hw : w ∈ what₂ then Classical.choose (hrows w hw) else F w
  have hA : ∀ w (hw : w ∈ what₂), A w = Classical.choose (hrows w hw) := fun w hw => dif_pos hw
  have hA' : ∀ w, w ∉ what₂ → A w = F w := fun w hw => dif_neg hw
  have hFA : ∀ w, F w ≤ A w := by
    intro w
    by_cases hw : w ∈ what₂
    · rw [hA w hw]; exact (Classical.choose_spec (hrows w hw)).1
    · rw [hA' w hw]
  let S : Submodule O (H1z ρM) := Q ⊓ ⨅ w ∈ what₂ ∪ cols, (A w).comap (resH1 ρM (D w))
  have hS : LinearMap.range ((Submodule.mkQ ((coB1 ρM).comap (coZ1s ρM).subtype)) ∘ₗ Ψ) ≤ S := by
    rintro _ ⟨h, rfl⟩
    refine (IdempotentNormalFormsRhoFacts.mem_sel (what₂ ∪ cols) (fun w => resH1 ρM (D w)) A Q _).mpr
      ⟨hQ h, fun w hw => ?_⟩
    by_cases hwr : w ∈ what₂
    · rw [hA w hwr]; exact (Classical.choose_spec (hrows w hwr)).2.2 h
    · rw [hA' w hwr]
      exact hcols w ((Finset.mem_union.mp hw).resolve_left hwr) h
  have hchain := lenChain O H (coZ1s ρM) (H1z ρM) Ψ _ S hS
  rw [length_mid_zero ρM hB Ψ, add_zero] at hchain
  have hSel : Module.length O S ≤ s + ∑ w ∈ what₂, lenRow w := by
    have h2 := selRelax O (H1z ρM) ι (what₂ ∪ cols) (fun w => H1z (resRep ρM (D w)))
      (fun w => resH1 ρM (D w)) F A Q hFA
    have hterm : ∀ w ∈ what₂ ∪ cols, Module.length O (A w ⧸ (F w).comap (A w).subtype) ≤
        if w ∈ what₂ then lenRow w else 0 := by
      intro w _
      by_cases hwr : w ∈ what₂
      · rw [if_pos hwr, hA w hwr]
        exact (Classical.choose_spec (hrows w hwr)).2.1
      · rw [if_neg hwr, hA' w hwr, Submodule.comap_subtype_self, Module.length_eq_zero]
    calc Module.length O S ≤ _ := h2
      _ ≤ s + ∑ w ∈ what₂ ∪ cols, (if w ∈ what₂ then lenRow w else 0) :=
          add_le_add hsel (Finset.sum_le_sum hterm)
      _ = s + ∑ w ∈ what₂, lenRow w := by
          rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  exact hchain.trans (add_le_add le_rfl hSel)
end Formalism.NG.TrivialCharacterBlockLength
