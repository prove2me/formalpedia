-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.piK_vac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:46.843867+00:00
-- url     : https://prove2.me/submissions/4a2372c8-eece-4f92-89aa-75b2ad14fda5

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourUniq
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourVac
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_Yk
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_sum_X
import Theorems.Thm_Formalism_IndefR_Fin_Four_mem_smulSub


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
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
include hXY hχl hχr hχ0 hLL hdY
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] {w : V} (hwX : ∀ u ∈ L ⊓ X, ρ u w = w)
    (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w) : ∃ c : ℂ, c ≠ 0 ∧ piK ρ L X Y k w = c • w := by
  classical
  letI := Fintype.ofFinite (Qt k (L ⊓ X))
  letI := Fintype.ofFinite (Ik L Y k)
  have hyk : ∀ y : Ik L Y k, ((y.out : ↥(Yk L Y k)) : W) ∈ Yk L Y k := fun y => (y.out : ↥(Yk L Y k)).2
  have hterm : ∀ (b : Qt k (L ⊓ X)) (y : Ik L Y k), ρ ((b.out : ↥(L ⊓ X)) : W) (ρ ((y.out : ↥(Yk L Y k)) : W) w) =
      χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W) • ρ ((y.out : ↥(Yk L Y k)) : W) w := by
    intro b y
    have := congrArg (fun T : Module.End ℂ V => T w)
      (hXY _ (AddSubgroup.mem_inf.1 (b.out : ↥(L ⊓ X)).2).2 _ (mem_Yk.1 (hyk y)).1)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hwX _ (b.out : ↥(L ⊓ X)).2]
  have e1 : piK ρ L X Y k w = ∑ y : Ik L Y k,
      (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W)) •
        ρ ((y.out : ↥(Yk L Y k)) : W) w := by
    unfold piK
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [map_sum, hterm, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  simp only [chi_sum_X hχl hχr hχ0 hLL hdY (hyk _)]
  have e2 : ∀ y : Ik L Y k, (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) •
      ρ ((y.out : ↥(Yk L Y k)) : W) w =
      (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) • w := by
    intro y
    split_ifs with h
    · rw [hwY _ (AddSubgroup.mem_inf.2 ⟨h, (mem_Yk.1 (hyk y)).1⟩)]
    · rw [zero_smul, zero_smul]
  simp only [e2, ← Finset.sum_smul]
  refine ⟨_, ?_, rfl⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ (by exact_mod_cast Fintype.card_ne_zero)
  have h0 : (0 : Ik L Y k) ∈ Finset.univ.filter (fun y : Ik L Y k => ((y.out : ↥(Yk L Y k)) : W) ∈ L) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' (0 : Ik L Y k))
    rw [AddSubgroup.mem_addSubgroupOf] at this
    obtain ⟨v, hv, hvx⟩ := mem_smulSub.1 this
    rw [← hvx]
    exact L.nsmul_mem (AddSubgroup.mem_inf.1 hv).1 k
  exact_mod_cast (Finset.card_pos.2 ⟨_, h0⟩).ne'
end Formalism.IndefR.Fin.Four
