-- Prove2me | solution 1 for Formalism.UG.P.psiK_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:35.40909+00:00
-- url     : https://prove2.me/submissions/9b3e3e37-28e6-4c47-addf-67ef12eb1b3a

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Heckebasic
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActionLevelMemHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G₁ G₂ : Type} [Group G₁] [Group G₂]
namespace Formalism.UG.P
theorem _root_.solution {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    {Γ : Subgroup (G₁ × G₂)} {K₁ : Subgroup G₁} {K₂ : Subgroup G₂}
    {ρK : Representation k (K₁.prod K₂) W}
    (hρ : ∀ κ : K₁.prod K₂, (κ : G₁ × G₂).2 = 1 → ρK κ = 1)
    {φ : G₁ × G₂ → W} (hφ : φ ∈ AMFK k Γ (K₁.prod K₂) ρK) (g : G₁ × G₂) :
    psiK φ g ∈ AMF k (⊥ : Subgroup G₁) K₁ (1 : Representation k (⊥ : Subgroup G₁) W) := by
  intro γ h c
  have hγ : (γ : G₁) = 1 := Subgroup.mem_bot.1 γ.2
  let d : K₁.prod K₂ := ⟨((c : G₁), (1 : G₂)), Subgroup.mem_prod.2 ⟨c.2, K₂.one_mem⟩⟩
  have e := hφ 1 (g * (h, 1)) d
  have hd : ρK d⁻¹ = 1 := hρ d⁻¹ (by simp [d])
  rw [hd] at e
  simp only [OneMemClass.coe_one, one_mul, Module.End.one_apply] at e
  have e' : g * (h * (c : G₁), (1 : G₂)) = g * (h, 1) * (d : G₁ × G₂) := by
    ext <;> simp [d, mul_assoc]
  unfold psiK
  rw [hγ, one_mul, e', e]
  simp
end Formalism.UG.P
