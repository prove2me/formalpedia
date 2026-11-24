-- Prove2me | solution 1 for Formalism.LIFT.uChase_proof
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:57.312349+00:00
-- url     : https://prove2.me/submissions/82775361-3241-45a6-87bf-ddb05e9f02d0

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_LIFT_uc_qinv_add
import Theorems.Thm_Formalism_LIFT_uc_qinv_sub
import Theorems.Thm_Formalism_LIFT_uc_qinv_smul
import Theorems.Thm_Formalism_LIFT_uc_qinv_phi_sub
import Theorems.Thm_Formalism_LIFT_d1_sub_sub
import Theorems.Thm_Formalism_LIFT_uc_smul
import Theorems.Thm_Formalism_LIFT_uc_gamma
import Theorems.Thm_Formalism_LIFT_uc_phi
import Theorems.Thm_Formalism_LIFT_uc_xn_sub
import Theorems.Thm_Formalism_LIFT_uc_xn_smul
import Theorems.Thm_Formalism_LIFT_uc_hom_tsmul
import Theorems.Thm_Formalism_LIFT_uc_hom
import Theorems.Thm_Formalism_LIFT_uc_hom_qinv
import Theorems.Thm_Formalism_LIFT_uc_hom_xn
import Theorems.Thm_Formalism_LIFT_uc_pi_iota
import Theorems.Thm_Formalism_LIFT_uc_lift_qinv
import Theorems.Thm_Formalism_LIFT_uc_pull_qinv
import Theorems.Thm_Formalism_LIFT_uc_pull_xn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution : UChase := by
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e c hK hR hT y z hyz
  obtain ⟨⟨hy, n, hn, rfl⟩, hd⟩ := hyz
  set L : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ e with hL
  obtain ⟨y₁, hy₁, hπy⟩ := uc_lift_qinv S hK hy
  obtain ⟨n₁, hn₁, hπn⟩ := hK n hn
  rw [← hL] at hπy hπn
  have hπz : S.π.f (B.X • n₁) = L • (B.X • n) := by rw [map_smul, hπn, smul_comm]
  obtain ⟨a, ha, hga⟩ := uc_gamma W₁ hy₁
  obtain ⟨hq, hph⟩ := uc_phi W₁ hn₁
  have hω : W₁.d1 y₁ (B.X • n₁) = B.X • (a - (B.Q • W₁.φ n₁ - n₁)) := by
    rw [WD.d1, hga, hph]; exact (smul_sub _ _ _).symm
  have hπω : S.π.f (W₁.d1 y₁ (B.X • n₁)) = 0 := by
    rw [uc_hom, hπy, hπz, uc_smul, hd, smul_zero]
  obtain ⟨y₀, hy₀, hιy₀⟩ : ∃ y₀, W₀.QInv y₀ ∧ S.ι.f y₀ = a - (B.Q • W₁.φ n₁ - n₁) := by
    apply uc_pull_qinv S (uc_qinv_sub W₁ ha hq)
    rw [hω, map_smul] at hπω
    exact W₂.X_inj _ hπω
  have hιω : S.ι.f (B.X • y₀) = W₁.d1 y₁ (B.X • n₁) := by rw [map_smul, hιy₀, hω]
  obtain ⟨k, y', z', ⟨⟨hy', nz, hnz, rfl⟩, hd'⟩, x, hx, hπy', hπz'⟩ :=
    hR y (B.X • n) ⟨⟨hy, n, hn, rfl⟩, hd⟩
  obtain ⟨x₁, hx₁, hπx⟩ := hK x hx
  rw [← hL] at hπx
  obtain ⟨x', hx', hγx⟩ := W₁.γ_N x₁ hx₁
  set K : ℤ_[ℓ] := (ℓ : ℤ_[ℓ]) ^ k with hKk
  set Y := K • y₁ - L • y' + (W₁.φ x₁ - x₁) with hY
  set m := K • n₁ - L • nz + x' with hm
  have hZ : K • (B.X • n₁) - L • (B.X • nz) + (W₁.γ x₁ - x₁) = B.X • m := by
    rw [hγx, hm, smul_add, smul_sub, smul_comm K, smul_comm L]
  have hmN : m ∈ W₁.N := W₁.N.add_mem (W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hn₁)
    (W₁.N.smul_of_tower_mem _ hnz)) hx'
  have hYq : W₁.QInv Y := uc_qinv_add W₁ (uc_qinv_sub W₁ (uc_qinv_smul W₁ _ hy₁)
    (uc_qinv_smul W₁ _ hy')) (uc_qinv_phi_sub W₁ hx₁)
  have hπY : S.π.f Y = 0 := by
    simp only [hY, map_add, map_sub, uc_hom_tsmul, S.π.φ_comm, hπy, hπy', hπx]
    rw [map_smul W₂.φ]
    module
  have hπZ : S.π.f (B.X • m) = 0 := by
    rw [← hZ]
    simp only [map_add, map_sub, uc_hom_tsmul, S.π.γ_comm, hπz, hπz', hπx]
    rw [map_smul W₂.γ]
    module
  obtain ⟨Y₀, hY₀, hιY⟩ := uc_pull_qinv S hYq hπY
  obtain ⟨m₀, hm₀, hιm⟩ := uc_pull_xn S hmN hπZ
  have hdYZ : W₁.d1 Y (B.X • m) = K • W₁.d1 y₁ (B.X • n₁) := by
    rw [← hZ, hY]
    unfold WD.d1 at hd' ⊢
    simp only [map_add, map_sub, map_smul]
    have hc := W₁.comm x₁
    linear_combination (norm := module) (-L) • hd' - hc
  have hcob : W₀.IsCob2 (K • (B.X • y₀)) := by
    refine ⟨Y₀, B.X • m₀, ⟨hY₀, m₀, hm₀, rfl⟩, ?_⟩
    apply S.ι_inj
    rw [uc_hom, hιY, hιm, hdYZ, uc_hom_tsmul, hιω]
  obtain ⟨y₀', z₀', ⟨hy₀', hz₀'⟩, hc⟩ := hT _ ⟨y₀, hy₀, rfl⟩ ⟨k, hcob⟩
  refine ⟨c • y₁ - S.ι.f y₀', c • (B.X • n₁) - S.ι.f z₀', ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · exact uc_qinv_sub W₁ (uc_qinv_smul W₁ c hy₁) (uc_hom_qinv S.ι hy₀')
  · exact uc_xn_sub W₁ (uc_xn_smul W₁ c ⟨n₁, hn₁, rfl⟩) (uc_hom_xn S.ι hz₀')
  · rw [d1_sub_sub, uc_smul, ← uc_hom, ← hc, uc_hom_tsmul, hιω, sub_self]
  · rw [map_sub, uc_hom_tsmul, hπy, uc_pi_iota, sub_zero, mul_smul, smul_comm]
  · rw [map_sub, uc_hom_tsmul, hπz, uc_pi_iota, sub_zero, mul_smul, smul_comm]
end Formalism.LIFT
