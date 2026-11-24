-- Prove2me | solution 1 for Formalism.L2.LamCM.Dx.idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:04.572436+00:00
-- url     : https://prove2.me/submissions/c31c391c-1a16-4118-9956-ca13ca03af17

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_AbsNormEqRelIndexMul
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_castSucc
import Theorems.Thm_Formalism_L2_LamCM_Dx_snocL_last
import Theorems.Thm_Formalism_L2_LamCM_Dx_lastL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_castSucc
attribute [local simp] Formalism.L2.LamCM.Dx.snocL_last
attribute [local simp] Formalism.L2.LamCM.Dx.lastL_apply

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.Dx
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.Dx
theorem _root_.solution {G H : Type*} [AddCommGroup G] [AddCommGroup H] (A' A : AddSubgroup G) (hA : A' ≤ A) (f : G →+ H) :
    A'.relIndex A = (A' ⊓ f.ker).relIndex (A ⊓ f.ker) * (A'.map f).relIndex (A.map f) := by
  set Z := f.ker
  have hmod : (A' ⊔ Z) ⊓ A = A' ⊔ (A ⊓ Z) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      exact ⟨y, hy, z, ⟨by simpa using A.sub_mem hx (hA hy), hz⟩, rfl⟩
    · rintro ⟨y, hy, z, ⟨hzA, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, A.add_mem (hA hy) hzA⟩
  have h1 : A'.relIndex (A' ⊔ (A ⊓ Z)) = (A' ⊓ Z).relIndex (A ⊓ Z) := by
    rw [sup_comm, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A' (A ⊓ Z),
      ← AddSubgroup.inf_relIndex_right (A' ⊓ Z) (A ⊓ Z)]
    congr 1
    ext x; simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨h, h2, h3⟩; exact ⟨⟨h, h3⟩, h2, h3⟩
    · rintro ⟨⟨h, h3⟩, h2, _⟩; exact ⟨h, h2, h3⟩
  have h2 : (A' ⊔ (A ⊓ Z)).relIndex A = (A'.map f).relIndex (A.map f) := by
    rw [AddSubgroup.relIndex_map_map]
    have e : A ⊔ f.ker = A ⊔ (A' ⊔ f.ker) := by
      apply le_antisymm
      · exact sup_le le_sup_left (le_trans le_sup_right le_sup_right)
      · exact sup_le le_sup_left (sup_le (le_trans hA le_sup_left) le_sup_right)
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (A' ⊔ f.ker) A]
    show _ = ((A' ⊔ Z) ⊓ A).relIndex A
    rw [hmod]
  rw [← AddSubgroup.relIndex_mul_relIndex A' (A' ⊔ (A ⊓ Z)) A le_sup_left (sup_le hA inf_le_left), h1, h2]
end Formalism.L2.LamCM.Dx
