-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.exists_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:57.097336+00:00
-- url     : https://prove2.me/submissions/5c7e0bb9-c881-4a0c-b79e-fad527af82fe

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulFinsum
import Theorems.Thm_Formalism_IndefR_Fin_Four_tfun_add
import Theorems.Thm_Formalism_IndefR_Fin_Four_tfun_smul
import Theorems.Thm_Formalism_IndefR_Fin_Four_tfun_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_tfun_modul
import Theorems.Thm_Formalism_IndefR_Fin_Four_tfun_vac
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsInv_add
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_add
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_modul
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_smul
import Theorems.Thm_Formalism_IndefR_Fin_Four_IsSB_trans
import Theorems.Thm_Formalism_IndefR_Fin_Four_isSB_ind
import Theorems.Thm_Formalism_IndefR_Fin_Four_isSB_zero


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
include hX hY hXY hfX hfY hχl hχr hχ0 hLL hdY hoX hoY hfinX hfinY htf
open Classical
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution : ∃ T : (W → ℂ) →ₗ[ℂ] V,
    (∀ Φ, IsSB L X Φ → T Φ = tfun ρ χ L X Y f₀ Φ) ∧
    (∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ)) ∧
    (∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ)) ∧
    T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀ := by
  let S : Submodule ℂ (W → ℂ) :=
    { carrier := {Φ | IsSB L X Φ}
      add_mem' := fun h h' => IsSB.add h h'
      zero_mem' := isSB_zero
      smul_mem' := fun c _ h => IsSB.smul h c }
  let tL : S →ₗ[ℂ] V :=
    { toFun := fun Φ => tfun ρ χ L X Y f₀ Φ.1
      map_add' := fun Φ Φ' => tfun_add (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY)
        (hfinX := hfinX) (hfinY := hfinY) (htf := htf) (hoY := hoY) Φ.2 Φ'.2
      map_smul' := fun c Φ => tfun_smul (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL) (hdY := hdY)
        (hfinX := hfinX) (hfinY := hfinY) (htf := htf) (hoY := hoY) Φ.2 c }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend tL
  have hTe : ∀ Φ, IsSB L X Φ → T Φ = tfun ρ χ L X Y f₀ Φ := fun Φ h => LinearMap.congr_fun hT ⟨Φ, h⟩
  refine ⟨T, hTe, fun Φ h x hx => ?_, fun Φ h y hy => ?_, ?_⟩
  · rw [hTe _ (h.trans hoX hx), hTe _ h]
    exact tfun_trans (hX := hX) (hXY := hXY) (hfX := hfX) (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) (hfinY := hfinY) (htf := htf) h hx
  · rw [hTe _ (h.modul hχl hχr hχ0 hLL hoY hy), hTe _ h]
    exact tfun_modul (hY := hY) (hXY := hXY) (hfY := hfY) (hχl := hχl) (hχr := hχr) (hχ0 := hχ0) (hLL := hLL)
      (hdY := hdY) (hoY := hoY) (hfinX := hfinX) (hfinY := hfinY) (htf := htf) h hy
  · rw [hTe _ isSB_ind]
    exact tfun_vac (hX := hX) (hY := hY) (hXY := hXY) (hfX := hfX) (hfY := hfY) (hχl := hχl) (hχr := hχr)
      (hχ0 := hχ0) (hLL := hLL) (hdY := hdY) (hoY := hoY) (hfinX := hfinX)
end Formalism.IndefR.Fin.Four
