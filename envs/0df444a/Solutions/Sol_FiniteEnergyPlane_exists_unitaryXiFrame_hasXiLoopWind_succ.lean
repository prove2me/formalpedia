-- Prove2me | solution 1 for FiniteEnergyPlane.exists_unitaryXiFrame_hasXiLoopWind_succ
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-15T16:10:12.57585+00:00
-- url     : https://prove2.me/submissions/99a85d54-5499-4e08-86e5-852165310313

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_exists_unitaryXiFrame_hasXiLoopWind_iff
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_conj
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



/-!
# A unitary frame of `ξ` of winding one along a Reeb orbit

Standalone version of the rotated frame of `Scratch/NF_M.lean` (`nf_frame_rot` with `θ = 1`),
built on any winding-zero unitary frame (`exists_unitaryXiFrame_hasXiLoopWind_iff`).
-/

namespace FiniteEnergyPlane

open Filter Topology Metric
open scoped ContDiff Real

lemma nfw_vecToC_J₀ (a : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, CauchyRiemannIndex.J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec,
      dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]

lemma nfw_vecToC_injective : Function.Injective vecToC := fun a b h => by
  ext i
  rcases i with i | i <;> fin_cases i
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

lemma nfw_vecToC_add (a b : CauchyRiemannIndex.Vec 1) :
    vecToC (a + b) = vecToC a + vecToC b := by
  apply Complex.ext <;> simp [vecToC]

lemma nfw_vecToC_smul (r : ℝ) (a : CauchyRiemannIndex.Vec 1) :
    vecToC (r • a) = (r : ℂ) * vecToC a := by
  apply Complex.ext <;> simp [vecToC]

lemma nfw_vecToC_zero : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
  apply Complex.ext <;> simp [vecToC]

/-- `e^{2πit}`. -/
noncomputable def nfwE (t : ℝ) : ℂ := Complex.exp (((2 * π * t : ℝ) : ℂ) * Complex.I)

lemma nfwE_contDiff : ContDiff ℝ ∞ nfwE := by
  unfold nfwE
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul contDiff_const)

lemma nfwE_per (t : ℝ) : nfwE (t + 1) = nfwE t := by
  unfold nfwE
  rw [show (((2 * π * (t + 1) : ℝ)) : ℂ) * Complex.I =
    (((2 * π * t : ℝ)) : ℂ) * Complex.I + 2 * π * Complex.I by push_cast; ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

lemma nfwE_norm (t : ℝ) : ‖nfwE t‖ = 1 := by
  unfold nfwE
  rw [Complex.norm_exp_ofReal_mul_I]

lemma nfwE_conj_mul (t : ℝ) : starRingEnd ℂ (nfwE t) * nfwE t = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, nfwE_norm]; simp

lemma nfwE_hasLoopWind : HasLoopWind nfwE 1 := by
  refine ⟨nfwE_contDiff.continuous, nfwE_per, fun t => ?_, ?_⟩
  · unfold nfwE; exact Complex.exp_ne_zero _
  refine ⟨fun t => 2 * π * t, by fun_prop, fun t => ?_, by ring⟩
  rw [nfwE_norm]
  unfold nfwE
  push_cast
  ring_nf

/-- Multiplication by `w` on `ℝ² ≅ ℂ`. -/
noncomputable def nfwRot (w : ℂ) : CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  w.re • ContinuousLinearMap.id ℝ _ +
    w.im • (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1)).toContinuousLinearMap

lemma vecToC_nfwRot (w : ℂ) (a : CauchyRiemannIndex.Vec 1) :
    vecToC (nfwRot w a) = w * vecToC a := by
  simp only [nfwRot, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, LinearMap.coe_toContinuousLinearMap']
  rw [nfw_vecToC_add, nfw_vecToC_smul, nfw_vecToC_smul, nfw_vecToC_J₀]
  conv_rhs => rw [← Complex.re_add_im w]
  ring

lemma nfwRot_contDiff {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ fun t => nfwRot (w t) := by
  unfold nfwRot
  exact ((Complex.reCLM.contDiff.comp hw).smul contDiff_const).add
    ((Complex.imCLM.contDiff.comp hw).smul contDiff_const)

lemma nfw_inner_eq (a b : CauchyRiemannIndex.Vec 1) :
    inner ℝ a b = (starRingEnd ℂ (vecToC a) * vecToC b).re := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_one, RCLike.inner_apply,
    conj_trivial, vecToC, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- A unitary frame of `ξ` along `P` whose winding is shifted by one relative to the frame
coordinates. -/
theorem exists_unitaryXiFrame_hasXiLoopWind_succ_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P M ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => M t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k) := by
  obtain ⟨Z, ⟨hZc, hZp, hZt⟩, hwind⟩ := exists_unitaryXiFrame_hasXiLoopWind_iff H hH J hJ P
  have hR := nfwRot_contDiff nfwE_contDiff
  have hvinj := nfw_vecToC_injective
  refine ⟨fun t => (Z t).comp (nfwRot (nfwE t)),
    ⟨hZc.clm_comp hR, fun t => ?_, fun t => ⟨fun a => (hZt t).1 _, fun w hw => ?_,
      fun a => ?_, fun a b => ?_⟩⟩, ?_⟩
  · simp only [nfwE_per, hZp t]
  · obtain ⟨a, ha⟩ := (hZt t).2.1 w hw
    refine ⟨nfwRot (starRingEnd ℂ (nfwE t)) a, ?_⟩
    simp only [ContinuousLinearMap.comp_apply]
    rw [← ha]
    congr 1
    apply hvinj
    rw [vecToC_nfwRot, vecToC_nfwRot, ← mul_assoc, mul_comm (nfwE t), nfwE_conj_mul, one_mul]
  · simp only [ContinuousLinearMap.comp_apply]
    rw [(hZt t).2.2.1]
    congr 1
    apply hvinj
    rw [nfw_vecToC_J₀, vecToC_nfwRot, vecToC_nfwRot, nfw_vecToC_J₀]
    ring
  · simp only [ContinuousLinearMap.comp_apply]
    rw [(hZt t).2.2.2, nfw_inner_eq, nfw_inner_eq, nfw_vecToC_J₀, nfw_vecToC_J₀, vecToC_nfwRot,
      vecToC_nfwRot]
    have := nfwE_conj_mul t
    congr 1
    simp only [map_mul]
    linear_combination (starRingEnd ℂ Complex.I * starRingEnd ℂ (vecToC a) * vecToC b) * this
  · intro ζ hζ hζp hζ0 k
    set ζ' : ℝ → CauchyRiemannIndex.Vec 1 := fun t => nfwRot (nfwE t) (ζ t) with hζ'
    have hc : Continuous ζ' := hR.continuous.clm_apply hζ
    have hp : Function.Periodic ζ' 1 := fun t => by simp only [hζ', nfwE_per, hζp t]
    have h0 : ∀ t, ζ' t ≠ 0 := by
      intro t h
      have := congrArg vecToC h
      rw [vecToC_nfwRot, nfw_vecToC_zero] at this
      rcases mul_eq_zero.1 this with h1 | h1
      · have := nfwE_norm t; rw [h1] at this; simp at this
      · exact hζ0 t (hvinj (h1.trans nfw_vecToC_zero.symm))
    have e1 := hwind ζ' hc hp h0 (k + 1)
    have e2 : (fun t => ((Z t).comp (nfwRot (nfwE t))) (ζ t)) = fun t => Z t (ζ' t) := rfl
    have e3 : (fun t => vecToC (ζ' t)) = fun t => nfwE t * vecToC (ζ t) :=
      funext fun t => vecToC_nfwRot _ _
    rw [e2, e1, e3]
    constructor
    · intro h
      have := hasLoopWind_mul (hasLoopWind_conj nfwE_hasLoopWind) h
      have e4 : (fun t => starRingEnd ℂ (nfwE t) * (nfwE t * vecToC (ζ t))) =
          fun t => vecToC (ζ t) := funext fun t => by
        rw [← mul_assoc, nfwE_conj_mul, one_mul]
      rw [e4, show -(1 : ℤ) + (k + 1) = k by ring] at this
      exact this
    · intro h
      have := hasLoopWind_mul nfwE_hasLoopWind h
      rwa [add_comm] at this

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P M ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => M t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k) :=
  exists_unitaryXiFrame_hasXiLoopWind_succ_aux H hH J hJ P
