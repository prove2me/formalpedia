-- Prove2me | solution 1 for Formalism.UG.P.satake_transform_multiplicative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:55:29.377124+00:00
-- url     : https://prove2.me/submissions/3d533e8f-565c-4cb5-b2ad-8383685c5d06

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake
import Theorems.Thm_Formalism_UG_P_fSatake_chiDelta_one
import Theorems.Thm_Formalism_UG_P_satake_transform_inert_prime
import Theorems.Thm_Formalism_UG_P_conv_biInv
import Theorems.Thm_Formalism_UG_P_conv_finDosetSupp
import Theorems.Thm_Formalism_UG_P_hecke_act_mul
import Theorems.Thm_Formalism_UG_P_isCommensurated_integral_unitary_of_unramified


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatMul := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h₁ hh₁ h₂ hh₂
  obtain ⟨φ0, hφ0, hφ01, -⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hSI := satake_transform_inert_prime hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have hh₁' := hh₁
  have hh₂' := hh₂
  obtain ⟨hb₁, hs₁⟩ := hh₁'
  obtain ⟨hb₂, hs₂⟩ := hh₂'
  have hconv : conv (KU σ n) h₁ h₂ ∈ Hecke ℂ (KU σ n) := by
    show _ ∧ _
    exact ⟨conv_biInv _ _ _ hb₁ hb₂, conv_finDosetSupp (isCommensurated_integral_unitary_of_unramified hU n) _ _ hs₁ hs₂⟩
  have hb1 : IsBorelU (1 : GU σ n) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_lt hij).symm]
  have hamf : φ0 ∈ AMF ℂ (⊥ : Subgroup (GU σ n)) (KU σ n)
      (1 : Representation ℂ (⊥ : Subgroup (GU σ n)) ℂ) := by
    intro γ g κ
    have hγ : (γ : GU σ n) = 1 := Subgroup.mem_bot.mp γ.2
    rw [hγ, one_mul]
    have := hφ0 1 g κ hb1 κ.2
    simpa [fSatake_chiDelta_one] using this
  have hmul := hecke_act_mul (GU σ n) ⊥ (KU σ n) ℂ ℂ 1 (isCommensurated_integral_unitary_of_unramified hU n) h₁ hh₁ h₂ hh₂ φ0 hamf
  have hs2 : IsSphericalU q α (SatU ϖ q h₂ α • φ0) := fun b g k hb hk => by
    simp only [Pi.smul_apply, smul_eq_mul, hφ0 b g k hb hk]
    ring
  rw [hSI _ hconv _ hφ0, hSI _ hh₂ _ hφ0, hSI _ hh₁ _ hs2] at hmul
  have := congrFun hmul 1
  simp only [Pi.smul_apply, smul_eq_mul, hφ01, mul_one] at this
  rw [this]
end Formalism.UG.P
