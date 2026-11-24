-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.exists_solve_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:06:01.347932+00:00
-- url     : https://prove2.me/submissions/7e9aa7eb-83c1-45b0-bdaf-55561f1a17d9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_exists_solve_herm
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_lift
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_of_map_eq_zero
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_exists_lift
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_map_conjTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]
variable [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k : ℕ}
    (hk : 1 ≤ k) {H P Q S : Matrix c c (𝓞 K ⧸ extP K 𝔭 ^ k)} (hHh : Hᴴ = H)
    (hH : ∀ i j, H i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hPQ : ∀ i j, (Pᴴ * Q - 1) i j ∈ (extP K 𝔭).map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))
    (hS : Sᴴ = S) : ∃ Z, S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z = 0 := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨H', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k H
  obtain ⟨P', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k P
  obtain ⟨Q', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k Q
  obtain ⟨S', rfl⟩ := reductionMapsOfForms.exists_lift 𝔭 k S
  have hmap : ∀ A : Matrix c c (𝓞 K), A.map (reductionMapsOfForms.mkk K 𝔭 k) = 0 → Ent (extP K 𝔭 ^ k) A :=
    fun A hA => ent_of_map_eq_zero hA
  have hH' : Ent (extP K 𝔭) H' := ent_lift hk hH
  have hPQ' : Ent (extP K 𝔭) (P'ᴴ * Q' - 1) := by
    apply ent_lift hk
    intro i j
    have e : (P'ᴴ * Q' - 1).map (reductionMapsOfForms.mkk K 𝔭 k) = (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Q'.map (reductionMapsOfForms.mkk K 𝔭 k) - 1 := by
      rw [reductionMapsOfForms.map_conjTranspose, Matrix.map_sub, Matrix.map_mul, Matrix.map_one] <;> simp
    have := hPQ i j
    rw [← e] at this
    exact this
  have hHh' : Ent (extP K 𝔭 ^ k) (H'ᴴ - H') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hHh, sub_self]
    simp
  have hS' : Ent (extP K 𝔭 ^ k) (S'ᴴ - S') := by
    apply hmap
    rw [Matrix.map_sub, ← reductionMapsOfForms.map_conjTranspose, hS, sub_self]
    simp
  obtain ⟨Z', hZ'⟩ := exists_solve_herm hK hF h𝔭 hH' hPQ' hHh' hS' k le_rfl
  refine ⟨Z'.map (reductionMapsOfForms.mkk K 𝔭 k), ?_⟩
  have e : (S' + P'ᴴ * Z' + Z'ᴴ * P' + Z'ᴴ * H' * Z').map (reductionMapsOfForms.mkk K 𝔭 k) =
      S'.map (reductionMapsOfForms.mkk K 𝔭 k) + (P'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * P'.map (reductionMapsOfForms.mkk K 𝔭 k) +
        (Z'.map (reductionMapsOfForms.mkk K 𝔭 k))ᴴ * H'.map (reductionMapsOfForms.mkk K 𝔭 k) * Z'.map (reductionMapsOfForms.mkk K 𝔭 k) := by
    simp only [reductionMapsOfForms.map_conjTranspose]
    simp only [← RingHom.mapMatrix_apply, map_add, map_mul]
  rw [← e]
  ext i j
  show Ideal.Quotient.mk (extP K 𝔭 ^ k) _ = 0
  exact Ideal.Quotient.eq_zero_iff_mem.2 (hZ' i j)
end Formalism.L2.SG.Pf.discriminantNormShapes
