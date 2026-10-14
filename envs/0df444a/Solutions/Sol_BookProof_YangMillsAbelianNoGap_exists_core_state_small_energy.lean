-- Prove2me | solution 1 for BookProof.YangMillsAbelianNoGap.exists_core_state_small_energy
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T12:18:00.047867+00:00
-- url     : https://prove2.me/submissions/b202b88f-cbc0-40b5-8d8e-cff3b8d6d01a

-- Generated from ChapterYangMillsAbelianNoGap.lean — solution of BookProof.YangMillsAbelianNoGap.exists_core_state_small_energy
import Mathlib
import Definitions.Def_ChapterYangMillsAbelianNoGap
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_bigP_pos
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_norm_op_bigP_le
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_abs_levi_le_one
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_magPoly_abelian
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_vsel_idxA
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_Msel_idxA
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_vsel_idxD
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_Msel_idxD
import Theorems.Thm_BookProof_YangMillsAbelianNoGap_le_of_sq_le
import Theorems.Thm_BookProof_SqueezedGaussStates_exists_momentum_small
import Theorems.Thm_BookProof_SqueezedGaussStates_exists_position_small
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op
import Theorems.Thm_BookProof_YangMillsHermite_momOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_mulOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_ymHamiltonian_quadForm
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGaussCoordCombo
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsAbelianNoGap




open MvPolynomial MeasureTheory
open BookProof.HermiteProductCore BookProof.GaussCoordCombo BookProof.SqueezedGaussStates
open BookProof.YangMillsHermite BookProof.FarisLavine BookProof.HermiteGalerkin

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable (vf : Fin d → ℝ) (Mf : Fin d → ℕ)

set_option maxHeartbeats 1000000 in
theorem solution (e : ℕ ≃ (Fin 99 →₀ ℕ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : finiteModeDomain (coreBasis e), ((x : L2d 99) ≠ 0) ∧
      quadForm (ymHamiltonian (coreRepBasis e) (fun _ _ _ => (0 : ℝ))) x
        ≤ ε * ‖(x : L2d 99)‖ ^ 2 := by

  classical
  obtain ⟨v₁, M₁, -, h₁⟩ := exists_momentum_small (ε := ε / 24) (by positivity)
  obtain ⟨v₂, M₂, -, h₂⟩ := exists_position_small (ε := ε / 2000) (by positivity)
  set vf : Fin 99 → ℝ := vsel v₁ v₂ with hvf
  set Mf : Fin 99 → ℕ := Msel M₁ M₂ with hMf
  set P : MvPolynomial (Fin 99) ℂ := bigP vf Mf with hP
  set x : finiteModeDomain (coreBasis e) := (coreRepBasis e).equiv P with hx
  have hxc : ((x : finiteModeDomain (coreBasis e)) : L2d 99) = pgLp P :=
    (coreRepBasis e).coe_equiv P
  have hxs : (coreRepBasis e).equiv.symm x = P := LinearEquiv.symm_apply_apply _ _
  have hPpos : 0 < ‖pgLp P‖ ^ 2 := norm_bigP_pos vf Mf
  -- the momentum terms
  have hpi : ∀ m : Fin 24,
      ‖((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2
        ≤ (ε / 24) * ‖pgLp P‖ ^ 2 := by
    intro m
    set c : Fin 99 := idxA (decodeSpace m) (decodeColor m) with hc
    have hcoe : ((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) : L2d 99)
        = pgLp (momOp c P) := by
      rw [piOps, CoreRep.coe_op, hxs]
    have hmom : momOp c P
        = (-Complex.I) • ((((-(1 / 2) : ℝ)) : ℂ) • (X c * P) + (((1 : ℝ)) : ℂ) • pderiv c P) := by
      rw [momOp_apply]
      push_cast
      module
    have hnorm : ‖pgLp (momOp c P)‖
        = ‖pgLp ((((-(1 / 2) : ℝ)) : ℂ) • (X c * P) + (((1 : ℝ)) : ℂ) • pderiv c P)‖ := by
      rw [hmom, ← pgMap_apply, map_smul, pgMap_apply, norm_smul]
      simp
    rw [hcoe, hnorm]
    refine norm_op_bigP_le vf Mf c (-(1 / 2)) 1 (ε / 24) ?_
    have hv : vf c = v₁ := by rw [hvf, hc, vsel_idxA]
    have hM : Mf c = M₁ := by rw [hMf, hc, Msel_idxA]
    rw [facS, hv, hM]
    exact h₁
  -- the magnetic terms
  set t : ℝ := Real.sqrt (ε / 2000) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = ε / 2000 := Real.sq_sqrt (by positivity)
  have hXD : ∀ (j k : Fin 3) (a : Fin 8),
      ‖pgLp (X (idxD j k a) * P)‖ ≤ t * ‖pgLp P‖ := by
    intro j k a
    set c : Fin 99 := idxD j k a with hc
    have hbound : ‖pgLp ((((1 : ℝ)) : ℂ) • (X c * P) + (((0 : ℝ)) : ℂ) • pderiv c P)‖ ^ 2
        ≤ (ε / 2000) * ‖pgLp P‖ ^ 2 := by
      refine norm_op_bigP_le vf Mf c 1 0 (ε / 2000) ?_
      have hv : vf c = v₂ := by rw [hvf, hc, vsel_idxD]
      have hM : Mf c = M₂ := by rw [hMf, hc, Msel_idxD]
      rw [facS, hv, hM]
      exact h₂
    have hsimp : (((1 : ℝ)) : ℂ) • (X c * P) + (((0 : ℝ)) : ℂ) • pderiv c P = X c * P := by
      push_cast
      module
    rw [hsimp] at hbound
    refine le_of_sq_le ht0 (norm_nonneg _) ?_
    rw [ht2]
    exact hbound
  have hB : ∀ m : Fin 24,
      ‖((magOps (coreRepBasis e) (fun _ _ _ => (0 : ℝ)) m x :
          finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2
        ≤ 81 * (ε / 2000) * ‖pgLp P‖ ^ 2 := by
    intro m
    set i : Fin 3 := decodeSpace m with hi
    set a : Fin 8 := decodeColor m with ha
    have hcoe : ((magOps (coreRepBasis e) (fun _ _ _ => (0 : ℝ)) m x :
        finiteModeDomain (coreBasis e)) : L2d 99)
        = pgLp (magPoly (fun _ _ _ => (0 : ℝ)) i a * P) := by
      rw [magOps, CoreRep.coe_op, hxs, mulOp_apply]
    have hexp : magPoly (fun _ _ _ => (0 : ℝ)) i a * P
        = ∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • (X (idxD j k a) * P) := by
      rw [magPoly_abelian, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc]
    have hsum : pgLp (∑ j : Fin 3, ∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • (X (idxD j k a) * P))
        = ∑ j : Fin 3, ∑ k : Fin 3,
            ((levi i j k : ℝ) : ℂ) • pgLp (X (idxD j k a) * P) := by
      rw [← pgMap_apply, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, pgMap_apply]
    have hnorm : ‖pgLp (magPoly (fun _ _ _ => (0 : ℝ)) i a * P)‖ ≤ 9 * (t * ‖pgLp P‖) := by
      rw [hexp, hsum]
      have hstep : ∀ j : Fin 3,
          ‖∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • pgLp (X (idxD j k a) * P)‖
            ≤ 3 * (t * ‖pgLp P‖) := by
        intro j
        refine le_trans (norm_sum_le _ _) ?_
        have hterm : ∀ k : Fin 3, ‖((levi i j k : ℝ) : ℂ) • pgLp (X (idxD j k a) * P)‖
            ≤ t * ‖pgLp P‖ := by
          intro k
          rw [norm_smul]
          have h1 : ‖((levi i j k : ℝ) : ℂ)‖ ≤ 1 := by
            simpa [Complex.norm_real] using abs_levi_le_one i j k
          have h2 : ‖pgLp (X (idxD j k a) * P)‖ ≤ t * ‖pgLp P‖ := hXD j k a
          have h3 : (0 : ℝ) ≤ ‖pgLp (X (idxD j k a) * P)‖ := norm_nonneg _
          nlinarith [norm_nonneg ((((levi i j k : ℝ) : ℂ))), h3]
        calc ∑ k : Fin 3, ‖((levi i j k : ℝ) : ℂ) • pgLp (X (idxD j k a) * P)‖
            ≤ ∑ _k : Fin 3, t * ‖pgLp P‖ := Finset.sum_le_sum fun k _ => hterm k
          _ = 3 * (t * ‖pgLp P‖) := by simp
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ j : Fin 3, ‖∑ k : Fin 3, ((levi i j k : ℝ) : ℂ) • pgLp (X (idxD j k a) * P)‖
          ≤ ∑ _j : Fin 3, 3 * (t * ‖pgLp P‖) := Finset.sum_le_sum fun j _ => hstep j
        _ = 9 * (t * ‖pgLp P‖) := by simp; ring
    rw [hcoe]
    have hnn : 0 ≤ ‖pgLp (magPoly (fun _ _ _ => (0 : ℝ)) i a * P)‖ := norm_nonneg _
    have hrhs : 0 ≤ 9 * (t * ‖pgLp P‖) :=
      mul_nonneg (by norm_num) (mul_nonneg ht0 (norm_nonneg _))
    nlinarith [hnorm, hnn, ht2, norm_nonneg (pgLp P)]
  -- assemble
  refine ⟨x, ?_, ?_⟩
  · rw [hxc]
    intro hzero
    rw [hzero] at hPpos
    simp at hPpos
  · rw [ymHamiltonian_quadForm, hxc]
    have hs1 : (∑ m : Fin 24,
        ‖((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2)
          ≤ 24 * ((ε / 24) * ‖pgLp P‖ ^ 2) := by
      calc (∑ m : Fin 24,
          ‖((piOps (coreRepBasis e) m x : finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2)
          ≤ ∑ _m : Fin 24, (ε / 24) * ‖pgLp P‖ ^ 2 := Finset.sum_le_sum fun m _ => hpi m
        _ = 24 * ((ε / 24) * ‖pgLp P‖ ^ 2) := by simp
    have hs2 : (∑ m : Fin 24,
        ‖((magOps (coreRepBasis e) (fun _ _ _ => (0 : ℝ)) m x :
            finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2)
          ≤ 24 * (81 * (ε / 2000) * ‖pgLp P‖ ^ 2) := by
      calc (∑ m : Fin 24,
          ‖((magOps (coreRepBasis e) (fun _ _ _ => (0 : ℝ)) m x :
              finiteModeDomain (coreBasis e)) : L2d 99)‖ ^ 2)
          ≤ ∑ _m : Fin 24, 81 * (ε / 2000) * ‖pgLp P‖ ^ 2 := Finset.sum_le_sum fun m _ => hB m
        _ = 24 * (81 * (ε / 2000) * ‖pgLp P‖ ^ 2) := by simp
    nlinarith [hs1, hs2, hPpos]
