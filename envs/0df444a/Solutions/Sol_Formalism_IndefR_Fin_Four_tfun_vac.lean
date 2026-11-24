-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.tfun_vac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:34.598793+00:00
-- url     : https://prove2.me/submissions/971d0f6d-9b85-47c2-97d0-d3bd04d4b117

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_nsmul_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_nsmul_right
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_zero_right
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_congr
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_one
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_twist
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_zero_of
import Theorems.Thm_Formalism_IndefR_Fin_Four_isSB_ind
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_add_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_add_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
  (hoX : ∀ x ∈ X, ∃ k : ℕ, 0 < k ∧ k • x ∈ L) (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L)
  (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀) (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀)
include hX hY hXY hfX hfY hχl hχr hχ0 hLL hdY hoY hfinX
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution : tfun ρ χ L X Y f₀ (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
  have hsupp := (isSB_ind (L := L) (X := X)).1
  have hval : ∀ a ∈ L ⊓ X, ∀ y ∈ L ⊓ Y,
      term ρ χ L X f₀ (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) a y = f₀ := by
    intro a ha y hy
    have e1 := term_add_left hχl hχ0 hfinX hX hXY hfX _ hsupp 0 (AddSubgroup.mem_inf.1 hy).2 ha
    have e2 := term_add_right hfinX hχr hLL hY hfY (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) 0
      Y.zero_mem hy
    rw [zero_add] at e1 e2
    rw [e1, e2]
    have hc : coef χ L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) 0 0 = 1 := by
      have hpt : ∀ t ∈ L ⊓ X, (if 0 + t ∈ L ∧ 0 + t ∈ X then (1 : ℂ) else 0) * (χ t 0)⁻¹ = 1 := by
        intro t ht
        rw [zero_add, if_pos (AddSubgroup.mem_inf.1 ht), chi_zero_right hχr hχ0, inv_one, mul_one]
      unfold coef
      exact (integ_congr hfinX (g' := fun _ => (1 : ℂ)) hpt).trans (integ_one hfinX)
    rw [term, hc, one_smul, neg_zero, hfX 0 (L ⊓ X).zero_mem, hfX 0 (L ⊓ X).zero_mem]
  unfold tfun
  have h0X : (0 : QX L X).out ∈ L ⊓ X := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
  have h0Y : (0 : QY L Y).out ∈ L ⊓ Y := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' 0)
  rw [finsum_eq_single _ ((0 : QX L X), (0 : QY L Y))]
  · show (if (0 : QY L Y).out ∈ Y then _ else _) = f₀
    rw [if_pos (AddSubgroup.mem_inf.1 h0Y).2]
    exact hval _ h0X _ h0Y
  · rintro ⟨q1, q2⟩ hq
    by_cases hy : q2.out ∈ Y
    · show (if q2.out ∈ Y then _ else _) = 0
      rw [if_pos hy, term]
      suffices hc : coef χ L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) q1.out q2.out = 0 by
        rw [hc, zero_smul]
      by_cases h1 : q1 = 0
      · have hq2 : q2 ≠ 0 := fun h2 => hq (by rw [h1, h2])
        have h1X : q1.out ∈ L ⊓ X :=
          (QuotientAddGroup.eq_zero_iff _).1 ((QuotientAddGroup.out_eq' q1).trans h1)
        have hyL : q2.out ∉ L := fun hL => hq2 ((QuotientAddGroup.out_eq' q2).symm.trans
          ((QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_inf.2 ⟨hL, hy⟩)))
        have hne : ¬ ∀ x ∈ L ⊓ X, χ x q2.out = 1 := fun hall => hyL (hdY _ hy hall)
        push_neg at hne
        obtain ⟨u, hu, hχu⟩ := hne
        obtain ⟨m, hm, hmy⟩ := hoY _ hy
        unfold coef
        rw [integ_congr hfinX (g' := fun t => (χ t q2.out)⁻¹) fun t ht => by
          show (if q1.out + t ∈ L ∧ q1.out + t ∈ X then (1 : ℂ) else 0) * _ = _
          rw [if_pos (AddSubgroup.mem_inf.1 ((L ⊓ X).add_mem h1X ht)), one_mul]]
        refine integ_twist hfinX hm (fun t _ u' hu' => ?_) hu (ζ := (χ u q2.out)⁻¹) (by rwa [Ne, inv_eq_one]) ?_
        · rw [hχl, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0,
            hLL _ hu' _ (AddSubgroup.mem_inf.2 ⟨hmy, Y.nsmul_mem hy m⟩), mul_one]
        · intro t _
          rw [hχl, mul_inv, mul_comm]
      · have h1X : q1.out ∉ L ⊓ X := fun hm => h1 ((QuotientAddGroup.out_eq' q1).symm.trans
          ((QuotientAddGroup.eq_zero_iff _).2 hm))
        unfold coef
        refine integ_zero_of hfinX fun t ht => ?_
        show (if q1.out + t ∈ L ∧ q1.out + t ∈ X then (1 : ℂ) else 0) * _ = 0
        rw [if_neg, zero_mul]
        intro hh
        exact h1X (by simpa using (L ⊓ X).sub_mem (AddSubgroup.mem_inf.2 hh) ht)
    · show (if q2.out ∈ Y then _ else _) = 0
      rw [if_neg hy]
end Formalism.IndefR.Fin.Four
