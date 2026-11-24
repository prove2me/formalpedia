-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.tfun_modul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:33.2706+00:00
-- url     : https://prove2.me/submissions/d0892b7d-371d-4324-9fe0-24ae8b699f8b

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_QY_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_neg_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_eq_zero
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_add_right
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_support_finite
import Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_integ_cmul__b92e15a955ec


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
include hY hXY hfY hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {Φ : W → ℂ} (h : IsSB L X Φ) {y₀ : W} (hy₀ : y₀ ∈ Y) :
    tfun ρ χ L X Y f₀ (fun t => χ t y₀ * Φ t) = ρ y₀ (tfun ρ χ L X Y f₀ Φ) := by
  have hs := h.1
  unfold tfun
  rw [map_finsum' _ (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine Eq.trans ?_ (finsum_comp_equiv
    (Equiv.prodCongr (Equiv.refl (QX L X)) (Equiv.addRight (QuotientAddGroup.mk (-y₀) : QY L Y))))
  refine finsum_congr fun q => ?_
  show _ = ρ y₀ (if (q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y)).out ∈ Y then
    term ρ χ L X f₀ Φ q.1.out (q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y)).out else 0)
  obtain ⟨μ, hμ, hout⟩ := QY_out (L := L) (Y := Y) (q.2.out + -y₀)
  have hq : q.2 + (QuotientAddGroup.mk (-y₀) : QY L Y) = QuotientAddGroup.mk (q.2.out + -y₀) := by
    rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
  rw [hq, hout]
  have hμY := (AddSubgroup.mem_inf.1 hμ).2
  by_cases hy : q.2.out ∈ Y
  · have hy1 : q.2.out + -y₀ ∈ Y := Y.add_mem hy (Y.neg_mem hy₀)
    rw [if_pos hy, if_pos (Y.add_mem hy1 hμY), term_add_right hfinX hχr hLL hY hfY Φ _ hy1 hμ]
    unfold term
    have hc : coef χ L X (fun t => χ t y₀ * Φ t) q.1.out q.2.out =
        χ q.1.out y₀ * coef χ L X Φ q.1.out (q.2.out + -y₀) := by
      unfold coef
      rw [← integ_cmul' hfinX]
      congr 1
      funext t
      have e1 : χ t q.2.out = χ t (q.2.out + -y₀) * χ t y₀ := by rw [← hχr, neg_add_cancel_right]
      show χ (q.1.out + t) y₀ * Φ (q.1.out + t) * (χ t q.2.out)⁻¹ = _
      rw [hχl, e1, mul_inv]
      linear_combination (χ q.1.out y₀ * Φ (q.1.out + t) * (χ t (q.2.out + -y₀))⁻¹) *
        mul_inv_cancel₀ (hχ0 t y₀)
    rw [hc]
    by_cases ha : q.1.out ∈ X
    · have hc2 := congrArg (fun T : Module.End ℂ V => T (ρ (q.2.out + -y₀) f₀)) (hXY _ (X.neg_mem ha) y₀ hy₀)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at hc2
      have hρy : ρ y₀ (ρ (q.2.out + -y₀) f₀) = ρ q.2.out f₀ := by
        rw [← Module.End.mul_apply, ← hY _ hy₀ _ hy1, show y₀ + (q.2.out + -y₀) = q.2.out by abel]
      have hswap : ρ y₀ (ρ (-q.1.out) (ρ (q.2.out + -y₀) f₀)) = χ q.1.out y₀ • ρ (-q.1.out) (ρ q.2.out f₀) := by
        have h3 : ρ y₀ (ρ (-q.1.out) (ρ (q.2.out + -y₀) f₀)) =
            (χ (-q.1.out) y₀)⁻¹ • ρ (-q.1.out) (ρ y₀ (ρ (q.2.out + -y₀) f₀)) := by
          rw [hc2, smul_smul, inv_mul_cancel₀ (hχ0 _ _), one_smul]
        rw [h3, hρy, chi_neg_left hχl hχ0, inv_inv]
      rw [map_smul, hswap, smul_smul, mul_comm]
    · simp [coef_eq_zero hfinX Φ hs ha]
  · have hy' : q.2.out + -y₀ + μ ∉ Y := fun h' => hy (by
      have := Y.add_mem (Y.sub_mem h' hμY) hy₀
      simpa using this)
    rw [if_neg hy, if_neg hy', map_zero]
end Formalism.IndefR.Fin.Four
