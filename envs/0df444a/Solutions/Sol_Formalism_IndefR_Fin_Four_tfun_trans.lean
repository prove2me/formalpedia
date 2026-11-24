-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.tfun_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:33.901371+00:00
-- url     : https://prove2.me/submissions/b5ff1232-5fc3-4968-be9f-28ad57f7d516

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Theorems.Thm_P2M_Formalism_IndefR_Fin_Four_map_finsum__3c600d0ebc52
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_congr
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_QX_out
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_eq_zero
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_add_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_term_support_finite


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
include hX hXY hfX hχl hχr hχ0 hLL hdY hoY hfinX hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution {Φ : W → ℂ} (h : IsSB L X Φ) {x : W} (hx : x ∈ X) :
    tfun ρ χ L X Y f₀ (fun t => Φ (t + x)) = ρ x (tfun ρ χ L X Y f₀ Φ) := by
  have hs := h.1
  unfold tfun
  rw [map_finsum' _ (term_support_finite hχl hχr hχ0 hLL hdY hfinX hfinY htf hoY h)]
  refine Eq.trans ?_ (finsum_comp_equiv
    (Equiv.prodCongr (Equiv.addRight (QuotientAddGroup.mk x : QX L X)) (Equiv.refl (QY L Y))))
  refine finsum_congr fun q => ?_
  show _ = ρ x (if q.2.out ∈ Y then
    term ρ χ L X f₀ Φ (q.1 + (QuotientAddGroup.mk x : QX L X)).out q.2.out else 0)
  by_cases hy : q.2.out ∈ Y
  · simp only [if_pos hy]
    obtain ⟨l, hl, hout⟩ := QX_out (L := L) (X := X) (q.1.out + x)
    have hq : q.1 + (QuotientAddGroup.mk x : QX L X) = QuotientAddGroup.mk (q.1.out + x) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    rw [hq, hout, term_add_left hχl hχ0 hfinX hX hXY hfX Φ hs _ hy hl]
    unfold term
    have hc : coef χ L X (fun t => Φ (t + x)) q.1.out q.2.out = coef χ L X Φ (q.1.out + x) q.2.out := by
      unfold coef
      congr 1
      funext t
      rw [add_right_comm]
    rw [hc, map_smul]
    by_cases ha : q.1.out + x ∈ X
    · have hρ : ρ x (ρ (-(q.1.out + x)) (ρ q.2.out f₀)) = ρ (-q.1.out) (ρ q.2.out f₀) := by
        rw [← Module.End.mul_apply, ← hX _ hx _ (X.neg_mem ha), show x + -(q.1.out + x) = -q.1.out by abel]
      rw [hρ]
    · simp [coef_eq_zero hfinX Φ hs ha]
  · simp only [if_neg hy, map_zero]
end Formalism.IndefR.Fin.Four
