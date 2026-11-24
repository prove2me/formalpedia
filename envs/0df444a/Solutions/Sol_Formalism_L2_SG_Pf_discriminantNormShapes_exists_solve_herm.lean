-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantNormShapes.exists_solve_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:46:22.926744+00:00
-- url     : https://prove2.me/submissions/bda07393-a673-4326-83a1-1513281aec3a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_EntOfMapEqZero
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_mul
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_mul_left
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_mul_right
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_add
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_sub
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_neg
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_smul
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_mono
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantNormShapes_ent_conjTranspose
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_mem_of_unram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Matrix
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]
private theorem exists_add_conj_sub_one_mem_extP (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ t : 𝓞 K, t + conjO K t - 1 ∈ extP K 𝔭 := by
  by_cases h : ∃ t : 𝓞 K, t + conjO K t ∉ extP K 𝔭
  · obtain ⟨t0, ht0⟩ := h
    obtain ⟨a, ha⟩ := exists_tr hF t0
    have haP : a ∉ 𝔭 := by
      intro haP
      apply ht0
      rw [← ha]
      exact Ideal.mem_map_of_mem _ haP
    obtain ⟨b, c, hc, hbc⟩ := h𝔭.exists_inv haP
    refine ⟨algebraMap (𝓞 F) (𝓞 K) b * t0, ?_⟩
    have e1 : algebraMap (𝓞 F) (𝓞 K) b * t0 + conjO K (algebraMap (𝓞 F) (𝓞 K) b * t0) - 1 = algebraMap (𝓞 F) (𝓞 K) (b * a - 1) := by
      rw [map_mul, conjO_map hF, map_sub, map_mul, map_one, ha]; ring
    have e2 : b * a - 1 = -c := by linear_combination hbc
    rw [e1, e2, map_neg]
    exact (extP K 𝔭).neg_mem (Ideal.mem_map_of_mem _ hc)
  · push_neg at h
    have h1 : (1 : 𝓞 K) ∈ extP K 𝔭 := by
      apply BallB.mem_of_unram hK
      intro θ
      have e : (θ - conjO K θ) * 1 = θ * (1 + conjO K 1) - (θ + conjO K θ) := by
        rw [map_one]; ring
      rw [e]
      exact (extP K 𝔭).sub_mem ((extP K 𝔭).mul_mem_left _ (h 1)) (h θ)
    refine ⟨0, ?_⟩
    simpa using (extP K 𝔭).neg_mem h1
variable [Fact (IsFixF K F)]
end Formalism.L2.SG.Pf.discriminantNormShapes
end
end

set_option autoImplicit false
open NumberField Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {c : Type} [Fintype c] [DecidableEq c]
namespace Formalism.L2.SG.Pf.discriminantNormShapes
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {H P Q S : Matrix c c (𝓞 K)} (hH : Ent (extP K 𝔭) H)
    (hPQ : Ent (extP K 𝔭) (Pᴴ * Q - 1)) {N : ℕ} (hHh : Ent (extP K 𝔭 ^ N) (Hᴴ - H))
    (hS : Ent (extP K 𝔭 ^ N) (Sᴴ - S)) :
    ∀ j, j ≤ N → ∃ Z : Matrix c c (𝓞 K),
      Ent (extP K 𝔭 ^ j) (S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z) := by
  obtain ⟨t, ht⟩ := exists_add_conj_sub_one_mem_extP hK hF h𝔭
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, fun _ _ => ?_⟩
    rw [pow_zero, Ideal.one_eq_top]
    exact Submodule.mem_top
  | succ j ih =>
    intro hj
    obtain ⟨Z, hZ⟩ := ih (by omega)
    set E := S + Pᴴ * Z + Zᴴ * P + Zᴴ * H * Z with hE
    set Y : Matrix c c (𝓞 K) := -(t • E) with hYdef
    set W := Q * Y with hW
    refine ⟨Z + W, ?_⟩
    have hJ : extP K 𝔭 ^ (j + 1) = extP K 𝔭 * extP K 𝔭 ^ j := pow_succ' _ _
    have hJ' : extP K 𝔭 ^ (j + 1) = extP K 𝔭 ^ j * extP K 𝔭 := pow_succ _ _
    have hY : Ent (extP K 𝔭 ^ j) Y := ent_neg (ent_smul t hZ)
    have hYh : Ent (extP K 𝔭 ^ j) Yᴴ := ent_conjTranspose hF 𝔭 j hY
    have hWj : Ent (extP K 𝔭 ^ j) W := ent_mul_left Q hY
    have hWh : Ent (extP K 𝔭 ^ j) Wᴴ := ent_conjTranspose hF 𝔭 j hWj
    have hPQh : Ent (extP K 𝔭) (Pᴴ * Q - 1)ᴴ := by
      have := ent_conjTranspose hF 𝔭 1 (A := Pᴴ * Q - 1) (by rw [pow_one]; exact hPQ)
      rwa [pow_one] at this
    have hEh : Ent (extP K 𝔭 ^ (j + 1)) (Eᴴ - E) := by
      have e : Eᴴ - E = (Sᴴ - S) + Zᴴ * (Hᴴ - H) * Z := by
        simp only [hE, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
        abel
      rw [e]
      have hN : extP K 𝔭 ^ N ≤ extP K 𝔭 ^ (j + 1) := Ideal.pow_le_pow_right hj
      exact ent_mono hN (ent_add hS (ent_mul_right (ent_mul_left _ hHh) _))
    have eq1 : S + Pᴴ * (Z + W) + (Z + W)ᴴ * P + (Z + W)ᴴ * H * (Z + W) =
        E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      simp only [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      rw [hE]
      abel
    have eq2 : Pᴴ * W = (Pᴴ * Q - 1) * Y + Y := by
      rw [hW, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul]
      abel
    have eq3 : Wᴴ * P = Yᴴ * (Pᴴ * Q - 1)ᴴ + Yᴴ := by
      rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.mul_sub,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    have eq4 : E + Y + Yᴴ = (1 - t - star t) • E - star t • (Eᴴ - E) := by
      rw [hYdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul]
      simp only [sub_smul, one_smul, smul_sub]
      abel
    have hx : (1 - t - star t) ∈ extP K 𝔭 := by
      have := (extP K 𝔭).neg_mem ht
      convert this using 1
      show 1 - t - conjO K t = -(t + conjO K t - 1)
      ring
    have T1 : Ent (extP K 𝔭 ^ (j + 1)) ((1 - t - star t) • E) := fun a b => by
      rw [hJ]; exact Ideal.mul_mem_mul hx (hZ a b)
    have T2 : Ent (extP K 𝔭 ^ (j + 1)) (star t • (Eᴴ - E)) := ent_smul _ hEh
    have T3 : Ent (extP K 𝔭 ^ (j + 1)) ((Pᴴ * Q - 1) * Y) := by
      rw [hJ]; exact ent_mul hPQ hY
    have T4 : Ent (extP K 𝔭 ^ (j + 1)) (Yᴴ * (Pᴴ * Q - 1)ᴴ) := by
      rw [hJ']; exact ent_mul hYh hPQh
    have T5 : Ent (extP K 𝔭 ^ (j + 1)) (Zᴴ * H * W) := by
      rw [hJ]; exact ent_mul (ent_mul_left Zᴴ hH) hWj
    have FreeQuotientRank : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * Z) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) Z
    have T7 : Ent (extP K 𝔭 ^ (j + 1)) (Wᴴ * H * W) := by
      rw [hJ']; exact ent_mul_right (ent_mul hWh hH) W
    have eq5 : E + Pᴴ * W + Wᴴ * P + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W =
        ((1 - t - star t) • E - star t • (Eᴴ - E)) + (Pᴴ * Q - 1) * Y + Yᴴ * (Pᴴ * Q - 1)ᴴ
          + Zᴴ * H * W + Wᴴ * H * Z + Wᴴ * H * W := by
      rw [eq2, eq3, ← eq4]
      abel
    rw [eq1, eq5]
    exact ent_add (ent_add (ent_add (ent_add (ent_add (ent_sub T1 T2) T3) T4) T5) FreeQuotientRank) T7
end Formalism.L2.SG.Pf.discriminantNormShapes
