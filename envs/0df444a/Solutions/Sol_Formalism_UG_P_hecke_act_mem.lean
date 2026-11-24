-- Prove2me | solution 1 for Formalism.UG.P.hecke_act_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:58.728878+00:00
-- url     : https://prove2.me/submissions/92179cd5-5335-4336-814f-936b141db1ea

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Theorems.Thm_Formalism_UG_P_out_smul
import Theorems.Thm_Formalism_UG_P_finite_supp

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
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.HeckeActMem := by
  intro G _ Γ K k _ W _ _ ρ hK f hf φ hφ
  have hf' : IsBiInv K f ∧ FinDosetSupp K f := hf
  have hbi : ∀ (a b : K) (g : G), f (↑a * g * ↑b) = f g := hf'.1
  have hφ' : ∀ (γ : Γ) (g : G) (κ : K), φ (↑γ * g * ↑κ) = ρ γ (φ g) := hφ
  have hfin := finite_supp K hK f hf
  show ∀ (γ : Γ) (g : G) (κ : K), hAct K f φ (↑γ * g * ↑κ) = ρ γ (hAct K f φ g)
  intro γ g κ
  simp only [hAct]
  have step1 : ∀ x : G ⧸ K, f x.out • φ (↑γ * g * ↑κ * x.out) =
      ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) := by
    intro x
    obtain ⟨κ', hκ'⟩ := out_smul K (κ : G) x
    have h1 : x.out = (κ : G)⁻¹ * ((κ : G) • x).out * (κ' : G)⁻¹ := by rw [hκ']; group
    have e1 : f x.out = f ((κ : G) • x).out := by
      rw [h1]
      have := hbi κ⁻¹ κ'⁻¹ ((κ : G) • x).out
      simpa using this
    have e2 : φ (↑γ * g * ↑κ * x.out) = ρ γ (φ (g * ((κ : G) • x).out)) := by
      have : (↑γ : G) * g * ↑κ * x.out = ↑γ * (g * ((κ : G) • x).out) * ↑(κ'⁻¹) := by
        rw [h1, Subgroup.coe_inv]
        group
      rw [this, hφ']
    rw [e1, e2, map_smul]
  rw [finsum_congr step1]
  have hre : ∑ᶠ x : G ⧸ K, ρ γ (f ((κ : G) • x).out • φ (g * ((κ : G) • x).out)) =
      ∑ᶠ y : G ⧸ K, ρ γ (f y.out • φ (g * y.out)) :=
    finsum_comp_equiv (MulAction.toPerm (κ : G) : Equiv.Perm (G ⧸ K))
      (f := fun y => ρ γ (f y.out • φ (g * y.out)))
  rw [hre]
  have hsupp : (Function.support fun y : G ⧸ K => f y.out • φ (g * y.out)).Finite :=
    hfin.subset fun y hy => by
      intro h0
      exact hy (by simp [h0])
  exact (map_finsum (ρ γ) hsupp).symm
end Formalism.UG.P
