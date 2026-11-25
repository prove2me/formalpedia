-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.generation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:04.206259+00:00
-- url     : https://prove2.me/submissions/900f452c-bbe0-4b75-8a92-676f0b185b4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_tenV_update
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_bigDiv_tenV_update
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution : Gen := by
  intro ι _ _ n lam M hM hT
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  have key : ∀ s : Finset ι, ∀ f : ι → MvPolynomial (Fin n × Fin n) ℂ,
      (∀ τ ∈ s, f τ ∈ delSq ℂ n (lam τ)) → (∀ τ ∉ s, f τ = extremal ℂ n (lam τ)) → tenV f ∈ M := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro f _ h0
      have : f = fun τ => extremal ℂ n (lam τ) := funext fun τ => h0 τ (Finset.notMem_empty τ)
      rw [this]
      exact hT
    · intro τ₀ s hτ ih f h1 h0
      have hword : ∀ wd : List (Fin n × Fin n × ℕ),
          tenV (Function.update f τ₀ (applyWord ℂ wd (hw ℂ le_rfl (lam τ₀).natW))) ∈ M := by
        intro wd
        induction wd with
        | nil =>
          apply ih
          · intro τ hτs
            rw [Function.update_of_ne (fun e => hτ (by rw [← e]; exact hτs))]
            exact h1 τ (Finset.mem_insert_of_mem hτs)
          · intro τ hτs
            by_cases e : τ = τ₀
            · rw [e, Function.update_self]
              rfl
            · rw [Function.update_of_ne e]
              exact h0 τ (by simp [e, hτs])
        | cons y wd ihw =>
          show tenV (Function.update f τ₀ (rowDiv ℂ y.1 y.2.1 y.2.2 (applyWord ℂ wd _))) ∈ M
          rw [← bigDiv_tenV_update]
          exact hM τ₀ _ _ _ _ ihw
      have hspan : f τ₀ ∈ Submodule.span ℂ
          (Set.range fun wd : List (Fin n × Fin n × ℕ) => applyWord ℂ wd (hw ℂ le_rfl (lam τ₀).natW)) :=
        h1 τ₀ (Finset.mem_insert_self _ _)
      have hmem : tenV (Function.update f τ₀ (f τ₀)) ∈ M := by
        refine Submodule.span_induction (p := fun p _ => tenV (Function.update f τ₀ p) ∈ M)
          ?_ ?_ ?_ ?_ hspan
        · rintro _ ⟨wd, rfl⟩
          exact hword wd
        · rw [tenV_update, map_zero, zero_mul]
          exact M.zero_mem
        · intro p q _ _ hp hq
          rw [tenV_update] at hp hq ⊢
          rw [map_add, add_mul]
          exact M.add_mem hp hq
        · intro c p _ hp
          rw [tenV_update] at hp ⊢
          rw [map_smul, smul_mul_assoc]
          exact M.smul_mem c hp
      rwa [Function.update_eq_self] at hmem
  exact key Finset.univ f (fun τ _ => hf τ) (fun τ h => absurd (Finset.mem_univ τ) h)
end Formalism.L2.SG.Pf.ColDictValCPf
