-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.MpG.curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:16:51.132059+00:00
-- url     : https://prove2.me/submissions/44fe1e63-5d84-44cd-b552-7907d5574a1b

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MpFOne
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_HasFDerivAtOfCurves
import Theorems.Thm_CompanionTheory_ThKR_Mp_MpG_hasDerivAt_det_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inl_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inl_inr_one
import Theorems.Thm_CompanionTheory_ThKR_LL_block_inr_inl_one
import Theorems.Thm_CompanionTheory_ThKR_LL_det_bl
import Theorems.Thm_CompanionTheory_ThKR_LL_ld_big


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL
open scoped Real ContDiff
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp CompanionTheory.ThKR.Mp.MpG
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp.MpG
theorem _root_.solution {g : ℝ → (l ⊕ l) → (l ⊕ l) → ℝ} {X : (l ⊕ l) → (l ⊕ l) → ℝ} (g0 : Matrix.of (g 0) = 1)
    (hg : HasDerivAt g X 0) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (sec (Matrix.of (g t)) f)) (schwartzToL2 l (Qd (Matrix.of X) f)) 0 := by
  have hd : ∀ i j : l → l ⊕ l, HasDerivAt (fun t => bl i j (Matrix.of (g t))) (bl i j (Matrix.of X)) 0 := fun i j =>
    (LinearMap.toContinuousLinearMap
      ((bl i j).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)).hasFDerivAt.comp_hasDerivAt 0 hg
  let A : ℝ → Eu l →L[ℝ] Eu l := fun t => bl Sum.inl Sum.inl (Matrix.of (g t))
  let c : ℝ → ℝ := fun t => (√|(Matrix.of (g t)).toBlocks₁₁.det|)⁻¹
  have eA : ∀ t, (A t).det = (Matrix.of (g t)).toBlocks₁₁.det := fun t => det_bl _ _ _
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  have hopen : ∀ᶠ u in 𝓝 0, IsUnit (A u) := (hd _ _).continuousAt.eventually (Units.isOpen.mem_nhds h0)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _), eA]
  have d0 : (Matrix.of (g 0)).toBlocks₁₁.det = 1 := by
    rw [← eA, A0]
    simp [ContinuousLinearMap.det]
  have c0 : c 0 = 1 := by simp only [c, d0]; simp
  have hD : HasDerivAt (fun t => (Matrix.of (g t)).toBlocks₁₁.det) (Matrix.of X).toBlocks₁₁.trace 0 :=
    hasDerivAt_det_one (M := fun t a b => g t (.inl a) (.inl b)) (X := fun a b => X (.inl a) (.inl b))
      (hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hasDerivAt_pi.1 (hasDerivAt_pi.1 hg _) _)
      (by
        ext a b
        have := congrFun (congrFun g0 (.inl a)) (.inl b)
        simpa [Matrix.one_apply] using this)
  have hcd : HasDerivAt c (-((Matrix.of X).toBlocks₁₁.trace / 2)) 0 := by
    have hp : 0 < (Matrix.of (g 0)).toBlocks₁₁.det := by rw [d0]; exact one_pos
    have h1 := (hD.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv (by simp only [d0]; simp)
    filter_upwards [hD.continuousAt.eventually (lt_mem_nhds hp)] with t ht
    simp only [c, abs_of_pos ht]
    rfl
  have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-bl Sum.inl Sum.inl (Matrix.of X)) 0 := by
    have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Eu l →L[ℝ] Eu l)ˣ)).comp_hasDerivAt_of_eq 0
      (hd Sum.inl Sum.inl) A0.symm
    exact h2.congr_deriv (by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
        one_mul, mul_one])
  obtain ⟨Q, hQ, hQ'⟩ := ld_big h1 (hd Sum.inl Sum.inr) (hd Sum.inr Sum.inl) hcd
    (hopen.mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [g0, block_inl_inr_one]) (by rw [g0, block_inr_inl_one]) c0 f
  refine (hQ f).congr_deriv (congrArg _ ?_)
  rw [h3, Qd, ofReal_neg, neg_smul, sub_eq_add_neg]
end CompanionTheory.ThKR.Mp.MpG
