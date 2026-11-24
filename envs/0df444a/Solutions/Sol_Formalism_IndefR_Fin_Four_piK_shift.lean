-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.piK_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:54:42.261917+00:00
-- url     : https://prove2.me/submissions/3f62fb3a-7ee4-4f8d-bd6b-1ef36bb5733c

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_Yk
import Theorems.Thm_Formalism_IndefR_Fin_Four_Ik_out_mk
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y') {k : ℕ} [Finite (Ik L Y k)]
    {u : W} (hu : u ∈ Yk L Y k) {G : V} (hG : ∀ v ∈ L ⊓ Y, ρ (k • v) G = G) :
    piK ρ L X Y k (ρ u G) = piK ρ L X Y k G := by
  classical
  letI := Fintype.ofFinite (Ik L Y k)
  unfold piK
  congr 1
  funext b
  congr 1
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let m : Ik L Y k := QuotientAddGroup.mk ⟨u, hu⟩
  have huY : u ∈ Y := (mem_Yk.1 hu).1
  have key : ∀ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) (ρ u G) = ρ (((y + m).out : ↥(Yk L Y k)) : W) G := by
    intro y
    have hyY : ((y.out : ↥(Yk L Y k)) : W) ∈ Y := (mem_Yk.1 (y.out : ↥(Yk L Y k)).2).1
    have h1 : y + m = QuotientAddGroup.mk (y.out + ⟨u, hu⟩) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    obtain ⟨v, hv, hout⟩ := Ik_out_mk (L := L) (Y := Y) (k := k) (y.out + ⟨u, hu⟩)
    rw [h1]
    have hoY : ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) ∈ Y :=
      (mem_Yk.1 ((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out.2).1
    have hkvY : k • v ∈ Y := Y.nsmul_mem (AddSubgroup.mem_inf.1 hv).2 k
    rw [← Module.End.mul_apply, ← hY _ hyY _ huY]
    have h2 : ((y.out : ↥(Yk L Y k)) : W) + u =
        ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v := by
      rw [hout]
      push_cast
      rfl
    rw [h2, hY _ hoY _ hkvY, Module.End.mul_apply, hG v hv]
  rw [Finset.sum_congr rfl fun y _ => key y]
  exact Fintype.sum_equiv (Equiv.addRight m) _ _ (fun _ => rfl)
end Formalism.IndefR.Fin.Four
