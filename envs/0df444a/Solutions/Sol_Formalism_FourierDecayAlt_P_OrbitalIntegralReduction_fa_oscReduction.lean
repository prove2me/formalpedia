-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_oscReduction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:15:22.663621+00:00
-- url     : https://prove2.me/submissions/89464947-d7f1-41fa-9008-e31ef3ff7261

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_adic_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_GG_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_levelA
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_lat
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_inv_y
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_amp
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_crit
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_main
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_inv_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_I_nhds
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_adic_of_datum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution : OscReduction := by
  intro K _ _ _ R ψ hD hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  obtain ⟨ϖ, hA⟩ := adic_of_datum hD hn
  obtain ⟨a1, ha1⟩ := adic_bounded hA hL₀.2
  obtain ⟨a2, ha2⟩ := adic_bounded hA hQc
  obtain ⟨a3, ha3⟩ := hA.inv_bounded hQc hQu
  obtain ⟨b, hb⟩ := hA.basis (Λ₀ : Set K) (hΛ₀.1.mem_nhds Λ₀.zero_mem)
  have hC : Cst R ϖ L₀ Λ₀ Q (a1 + a2 + a3) b :=
    { adic := hA
      L0 := fun x hx => Bd.mono hA.mem (by omega) (ha1 x hx)
      Qb := fun d hd => Bd.mono hA.mem (by omega) (ha2 d hd)
      Qi := fun d hd d' e => Bd.mono hA.mem (by omega) (show Bd R ϖ a3 d' from ha3 d hd d' e)
      abelian₂ := by
        rintro x ⟨r, hr, rfl⟩
        exact hb r hr }
  obtain ⟨b₁, hInv⟩ := GG_inv hD hC m
  obtain ⟨M, hLA⟩ := levelA hD hC hL₀ m hm
  refine ⟨mulR R ((ϖ⁻¹ ^ ((m + 1) * (a1 + a2 + a3)) : Kˣ) : K), mulR R ((ϖ ^ b₁ : Kˣ) : K),
    fa_lat hA _, fa_lat hA _, {x | Sm R ϖ M x}, ?_, ?_⟩
  · have h1 := I_nhds hA.isOpen (ϖ ^ M)
    refine Filter.mem_of_superset h1 ?_
    rintro x ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp⟩
  intro Φ hΦ D hDQ
  have hD'Q : (((-1) ^ m * D : Kˣ) : K) ∈ Q ∨ -(((-1) ^ m * D : Kˣ) : K) ∈ Q := by
    rcases neg_one_pow_eq_or Kˣ m with h | h
    · left; rw [h]; simpa using hDQ
    · right; rw [h]; simpa using hDQ
  have hI : InvP R ψ ϖ Φ m (((-1) ^ m * D : Kˣ) : K) b₁ := hInv Φ hΦ _ hD'Q
  refine ⟨fun x => bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1))
    (GG R ψ Φ (((-1) ^ m * D : Kˣ) : K) x), fa_amp hC Φ hΦ _ hD'Q hI, ?_, ?_⟩
  · intro z hz
    exact fa_crit hD hC hm Φ hΦ _ z hz hI
  · intro t c ht hct Λ hΛ hΛinv
    refine fa_main hD hC hL₀ Φ hΦ t c _ hD'Q hI (Sm.mem hA.mem ht) ?_ Λ hΛ hΛinv
    refine hLA Φ hΦ t c _ ht ?_ hD'Q _ (fa_lat hA _) (fun x => fa_inv_y hI x)
    rw [← hct]
    push_cast
    ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
