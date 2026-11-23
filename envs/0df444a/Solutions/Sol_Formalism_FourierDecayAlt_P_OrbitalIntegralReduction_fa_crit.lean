-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.fa_crit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:27.424731+00:00
-- url     : https://prove2.me/submissions/e0da360a-2967-4db5-98f6-1767c701deab

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_ringInverse_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_psi_R
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_mul_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_sumU
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_omPhi_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fin_single
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_card_Pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_sub_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_sUp_EE
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_smul_EE
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_lat
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_mem_mulR
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_modK_pow
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_fa_inv_y
import Theorems.Thm_Formalism_DoubleCosetMeasures_Final_simpleAdd
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_sUp_mem
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_simpleAdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_modK_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) (hC : Cst R ϖ L₀ Λ₀ Q a b) {m : ℕ} (hm : 1 ≤ m)
    (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (hΦ : PhiHyp R (m + 1) L₀ Λ₀ Q Φ) (D' z : Kˣ) (hz : z ^ (m + 1) = D') {b₁ : ℕ}
    (hI : InvP R ψ ϖ Φ m (D' : K) b₁) :
    bx R (mulR R ((ϖ ^ b₁ : Kˣ) : K)) (Pr (m + 1)) (GG R ψ Φ (D' : K) (fun _ => (z : K))) =
      ((modK R (z : K) ^ (m * (m - 1) / 2) : ℝ) : ℂ) * omPhi R ψ (addBlock h0 (m + 1) z) Φ := by
  have hA := hC.adic
  have hzz : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := by simp
  have hprod : ∏ _k : Fin m, (z : K) = (z : K) ^ m := by simp
  have hinvz : Ring.inverse (z : K) = ((z⁻¹ : Kˣ) : K) := ringInverse_eq hzz
  have hx0 : x0 (D' : K) (fun _ : Fin m => (z : K)) = (z : K) := by
    unfold x0
    rw [hprod, ringInverse_eq (y := ((z⁻¹ : Kˣ) : K) ^ m) (by rw [← mul_pow, hzz, one_pow]), ← hz]
    push_cast
    have h : (z : K) ^ m * ((z⁻¹ : Kˣ) : K) ^ m = 1 := by rw [← mul_pow, hzz, one_pow]
    linear_combination (z : K) * h
  have hxt : xt (D' : K) (fun _ : Fin m => (z : K)) = fun _ => (z : K) := by
    funext i
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp [xt, hx0]
    · simp [xt]
  have hg1 : ∀ N : Pr (m + 1) → K, g1 (D' : K) (fun _ : Fin m => (z : K)) ((z : K) • N) =
      ∑ i : Fin m, N (sd i) := by
    intro N
    unfold g1
    rw [hx0, hxt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hinvz, Pi.smul_apply, smul_eq_mul]
    linear_combination ((z : K) * ((z⁻¹ : Kˣ) : K) * N (sd i) + N (sd i)) * hzz
  set f : Matrix (Fin (m + 1)) (Fin (m + 1)) K → ℂ := fun u =>
    Φ (m + 1) (((z : K) • u).submatrix Fin.rev id) * ψ (sUp u) with hf
  have hP : 0 < modK R (z : K) := modK_pos hA.isOpen hA.isCompact z
  have key : ∀ N : Pr (m + 1) → K, f (1 + EE N) =
      ((modK R (z : K) ^ m : ℝ) : ℂ) * GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • N) := by
    intro N
    have hu : ∀ _k : Fin m, IsUnit (z : K) := fun _ => z.isUnit
    simp only [hf, GG, if_pos hu, hprod, fa_modK_pow hA, hxt, hg1, fa_sUp_EE, fa_smul_EE, ZZ]
    have : ((modK R (z : K) ^ m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (pow_pos hP m).ne'
    push_cast
    push_cast at this
    field_simp
  set Λ' : AddSubgroup K := mulR R ((z⁻¹ * ϖ ^ b₁ : Kˣ) : K) with hΛ'
  have hinv' : BInv Λ' (fun N : Pr (m + 1) → K =>
      GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • N)) := by
    intro N l hl
    show GG R ψ Φ (D' : K) (fun _ => (z : K)) ((z : K) • (N + l)) = _
    rw [smul_add]
    refine fa_inv_y hI _ _ _ fun p => ?_
    obtain ⟨r, hr, e⟩ := fa_mem_mulR.1 (hl p)
    refine fa_mem_mulR.2 ⟨r, hr, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, e]
    push_cast
    linear_combination ((ϖ : K) ^ b₁ * r) * hzz
  have hsc := bx_scale hD z (fa_lat hA (ϖ ^ b₁)) (fa_lat hA (z⁻¹ * ϖ ^ b₁))
    (GG R ψ Φ (D' : K) (fun _ => (z : K))) (fa_inv_y hI _) hinv'
  have hU := sumU hD (m + 1) f (by
      intro u r hu hr hrI
      simp only [hf]
      rw [← Matrix.smul_mul, fa_sub_mul, hΦ.1 _ 1 r (isLowUni_one K) (by
        intro i j; rw [Matrix.one_apply]; split_ifs; exacts [R.one_mem, R.zero_mem]) hr hrI,
        (Formalism.DoubleCosetMeasures.P.simpleAdd K (m + 1) u r).2 hu hr, AddChar.map_add_eq_mul,
        psi_R hD (Formalism.DoubleCosetMeasures.P.sUp_mem R _ hrI), mul_one]) (by
      refine (fin_single hD (m + 1) (ϖ ^ a * z)).subset ?_
      intro q hq
      have h1 : Φ (m + 1) (((z : K) • sec_m (Quotient.out q)).submatrix Fin.rev id) ≠ 0 :=
        left_ne_zero_of_mul hq
      intro i j
      have h2 := hC.L0 _ (hΦ.2.1 _ h1 (Fin.rev i) j)
      simp only [Matrix.submatrix_apply, Fin.rev_rev, id, Matrix.smul_apply, smul_eq_mul] at h2
      show ((ϖ ^ a * z : Kˣ) : K) • sec_m (Quotient.out q) i j ∈ R
      have h3 : ((ϖ ^ a * z : Kˣ) : K) • sec_m (Quotient.out q) i j =
          (ϖ : K) ^ a * ((z : K) * sec_m (Quotient.out q) i j) := by
        push_cast; rw [smul_eq_mul, mul_assoc]
      rw [h3]; exact h2) (fa_lat hA (z⁻¹ * ϖ ^ b₁)) (by
      intro N l hl
      show f (1 + EE (N + l)) = f (1 + EE N)
      rw [key, key]
      exact congrArg _ (hinv' N l hl))
  rw [omPhi_single, hU, bx_congr _ key, bx_mul_left, ← hsc, fa_card_Pr]
  have hcard : (m + 1) * (m + 1 - 1) / 2 = m * (m - 1) / 2 + m := by
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have e : (k + 1 + 1) * (k + 1 + 1 - 1) = (k + 1) * (k + 1 - 1) + 2 * (k + 1) := by
      simp only [Nat.add_sub_cancel]; ring
    rw [e, Nat.add_mul_div_left _ _ (by norm_num)]
  rw [hcard, pow_add]
  push_cast
  ring
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
