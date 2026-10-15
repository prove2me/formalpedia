-- Prove2me | solution 1 for CauchyRiemannIndex.plane_cauchyRiemann_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T07:28:42.840921+00:00
-- url     : https://prove2.me/submissions/c7026150-491d-47ab-a5ad-2fbad7dcbdd4

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_euclidean
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- ===== Scratch/CRLocPhi.lean =====
namespace CauchyRiemannIndex

open Matrix

noncomputable section

variable {n : ℕ}

/-- `ℝ²ⁿ → ℂⁿ`, `(x, y) ↦ x + i y`, as a real-linear map. -/
def crlPhiL (n : ℕ) : Vec n →ₗ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun w := (WithLp.equiv 2 (Fin n → ℂ)).symm
    (fun i => (w (Sum.inl i) : ℂ) + Complex.I * (w (Sum.inr i) : ℂ))
  map_add' a b := by
    ext i; simp; ring
  map_smul' c a := by
    ext i; simp; ring

lemma crlPhiL_apply (w : Vec n) (i : Fin n) :
    crlPhiL n w i = (w (Sum.inl i) : ℂ) + Complex.I * (w (Sum.inr i) : ℂ) := rfl

lemma crlPhiL_J (w : Vec n) :
    crlPhiL n (Matrix.toEuclideanLin (J₀ n) w) = Complex.I • crlPhiL n w := by
  ext i
  simp only [crlPhiL_apply, PiLp.smul_apply, smul_eq_mul]
  simp [Matrix.toEuclideanLin, Matrix.J, Matrix.mulVec, dotProduct, Matrix.fromBlocks,
    Fintype.sum_sum_type, Matrix.one_apply]
  ring_nf
  simp [Complex.I_sq]

lemma crlPhiL_injective : Function.Injective (crlPhiL n) := by
  intro a b h
  ext j
  rcases j with i | i
  · have := congrArg (fun w => (w i).re) h
    simpa [crlPhiL_apply] using this
  · have := congrArg (fun w => (w i).im) h
    simpa [crlPhiL_apply] using this

end

end CauchyRiemannIndex

-- ===== Scratch/CRLocPlane.lean =====
namespace CauchyRiemannIndex

open MeasureTheory Matrix
open scoped ENNReal NNReal

noncomputable section

variable {n : ℕ}

/-- `(x, y) ↦ x + i y` as a real-linear equivalence `ℝ²ⁿ ≃ ℂⁿ`. -/
def crlPhiE (n : ℕ) : Vec n ≃ₗ[ℝ] EuclideanSpace ℂ (Fin n) :=
  { crlPhiL n with
    invFun := fun w => (WithLp.equiv 2 (Fin n ⊕ Fin n → ℝ)).symm
      (Sum.elim (fun i => (w i).re) (fun i => (w i).im))
    left_inv := fun a => by
      ext j; rcases j with i | i <;> simp [crlPhiL_apply]
    right_inv := fun w => by
      show crlPhiL n _ = w
      ext i
      rw [crlPhiL_apply]
      apply Complex.ext <;> simp }

/-- The continuous version of `crlPhiE`. -/
def crlPhiC (n : ℕ) : Vec n ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (crlPhiE n).toContinuousLinearEquiv

lemma crlPhiC_apply (w : Vec n) : crlPhiC n w = crlPhiL n w := rfl

lemma crl_enorm_le (w : Vec n) :
    ‖w‖ₑ ≤ ‖((crlPhiC n).symm : EuclideanSpace ℂ (Fin n) →L[ℝ] Vec n)‖₊ * ‖crlPhiC n w‖ₑ := by
  have h := ((crlPhiC n).symm : EuclideanSpace ℂ (Fin n) →L[ℝ] Vec n).le_opNNNorm (crlPhiC n w)
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at h
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h

lemma crl_enorm_le' (w : Vec n) :
    ‖crlPhiC n w‖ₑ ≤ ‖((crlPhiC n) : Vec n →L[ℝ] EuclideanSpace ℂ (Fin n))‖₊ * ‖w‖ₑ := by
  have h := ((crlPhiC n) : Vec n →L[ℝ] EuclideanSpace ℂ (Fin n)).le_opNNNorm w
  simp only [ContinuousLinearEquiv.coe_coe] at h
  simp only [enorm_eq_nnnorm]
  exact_mod_cast h

/-- The complex model `φ = Φ ∘ v ∘ (z ↦ (re z, im z))`. -/
def crlModel (v : ℝ × ℝ → Vec n) : ℂ → EuclideanSpace ℂ (Fin n) :=
  fun z => crlPhiC n (v (Complex.equivRealProdCLM z))

lemma crlModel_fderiv {v : ℝ × ℝ → Vec n} (hv : ContDiff ℝ 1 v) (z w : ℂ) :
    fderiv ℝ (crlModel v) z w =
      crlPhiC n (fderiv ℝ v (Complex.equivRealProdCLM z) (Complex.equivRealProdCLM w)) := by
  have hd : DifferentiableAt ℝ v (Complex.equivRealProdCLM z) :=
    (hv.differentiable one_ne_zero) _
  have h1 : HasFDerivAt (fun z => v (Complex.equivRealProdCLM z))
      ((fderiv ℝ v (Complex.equivRealProdCLM z)).comp
        (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ)) z :=
    hd.hasFDerivAt.comp z (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).hasFDerivAt
  have h2 := ((crlPhiC n : Vec n →L[ℝ] EuclideanSpace ℂ (Fin n)).hasFDerivAt).comp z h1
  rw [show crlModel v = (crlPhiC n : Vec n →L[ℝ] EuclideanSpace ℂ (Fin n)) ∘
      (fun z => v (Complex.equivRealProdCLM z)) from rfl, h2.fderiv]
  rfl

lemma crl_e_one : Complex.equivRealProdCLM (1 : ℂ) = ((1 : ℝ), (0 : ℝ)) := by
  show ((1 : ℂ).re, (1 : ℂ).im) = _
  simp

lemma crl_e_I : Complex.equivRealProdCLM Complex.I = ((0 : ℝ), (1 : ℝ)) := by
  show (Complex.I.re, Complex.I.im) = _
  simp

lemma crl_e_mp : MeasurePreserving (fun z : ℂ => Complex.equivRealProdCLM z) volume volume :=
  Complex.volume_preserving_equiv_real_prod

lemma crl_eLpNorm_model (g : ℝ × ℝ → Vec n) (hg : Continuous g) (p : ℝ≥0∞) :
    eLpNorm (fun z : ℂ => crlPhiC n (g (Complex.equivRealProdCLM z))) p volume =
      eLpNorm (fun x => crlPhiC n (g x)) p volume := by
  have := eLpNorm_comp_measurePreserving (p := p)
    ((crlPhiC n).continuous.comp hg).aestronglyMeasurable crl_e_mp
  exact this

lemma crl_plane (n : ℕ) (p : ℝ≥0∞) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ A : ℝ≥0, ∀ v : ℝ × ℝ → Vec n, ContDiff ℝ 1 v → HasCompactSupport v →
      eLpNorm (partialS v) p volume + eLpNorm (partialT v) p volume ≤
        A * eLpNorm (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x))
          p volume := by
  have hpr : 1 < p.toReal := by
    have := ENNReal.toReal_strict_mono hp' hp
    simpa using this
  obtain ⟨A, hA⟩ := DbarRegularity.cauchyRiemann_lp_euclidean n p.toReal hpr
  rw [ENNReal.ofReal_toReal hp'] at hA
  set K := ‖((crlPhiC n).symm : EuclideanSpace ℂ (Fin n) →L[ℝ] Vec n)‖₊
  set L := ‖((crlPhiC n) : Vec n →L[ℝ] EuclideanSpace ℂ (Fin n))‖₊
  refine ⟨K * A * L, fun v hv hsupp => ?_⟩
  have hcd : Continuous (fun x => fderiv ℝ v x) := hv.continuous_fderiv one_ne_zero
  have hcS : Continuous (partialS v) := hcd.clm_apply continuous_const
  have hcT : Continuous (partialT v) := hcd.clm_apply continuous_const
  have hφ : ContDiff ℝ 1 (crlModel v) :=
    (crlPhiC n : Vec n →L[ℝ] EuclideanSpace ℂ (Fin n)).contDiff.comp
      (hv.comp (Complex.equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ).contDiff)
  have hφs : HasCompactSupport (crlModel v) := by
    have h1 : HasCompactSupport (fun z => v (Complex.equivRealProdCLM z)) :=
      hsupp.comp_homeomorph Complex.equivRealProdCLM.toHomeomorph
    exact h1.comp_left (map_zero (crlPhiC n))
  have key := hA (crlModel v) hφ hφs
  have eS : (fun z => fderiv ℝ (crlModel v) z 1) =
      fun z => crlPhiC n (partialS v (Complex.equivRealProdCLM z)) := by
    funext z; rw [crlModel_fderiv hv, crl_e_one]; rfl
  have eT : (fun z => fderiv ℝ (crlModel v) z Complex.I) =
      fun z => crlPhiC n (partialT v (Complex.equivRealProdCLM z)) := by
    funext z; rw [crlModel_fderiv hv, crl_e_I]; rfl
  have eD : DbarRegularity.dbar (crlModel v) =
      fun z => crlPhiC n ((fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x))
        (Complex.equivRealProdCLM z)) := by
    funext z
    simp only [DbarRegularity.dbar]
    rw [crlModel_fderiv hv, crlModel_fderiv hv, crl_e_one, crl_e_I]
    simp only [map_add, crlPhiC_apply, crlPhiL_J]
    rfl
  rw [eS, eT, eD] at key
  rw [crl_eLpNorm_model _ hcS p, crl_eLpNorm_model _ hcT p,
    crl_eLpNorm_model (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x))
      (hcS.add (((Matrix.toEuclideanLin (J₀ n)).toContinuousLinearMap).continuous.comp hcT)) p]
    at key
  have bS : eLpNorm (partialS v) p volume ≤ K * eLpNorm (fun x => crlPhiC n (partialS v x)) p volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (Filter.Eventually.of_forall fun x => crl_enorm_le _) p
  have bT : eLpNorm (partialT v) p volume ≤ K * eLpNorm (fun x => crlPhiC n (partialT v x)) p volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (Filter.Eventually.of_forall fun x => crl_enorm_le _) p
  have bD : eLpNorm (fun x => crlPhiC n (partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x)))
      p volume ≤ L * eLpNorm (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x))
        p volume :=
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul' (Filter.Eventually.of_forall fun x => crl_enorm_le' _) p
  calc eLpNorm (partialS v) p volume + eLpNorm (partialT v) p volume
      ≤ K * eLpNorm (fun x => crlPhiC n (partialS v x)) p volume +
          K * eLpNorm (fun x => crlPhiC n (partialT v x)) p volume := add_le_add bS bT
    _ = K * (eLpNorm (fun x => crlPhiC n (partialS v x)) p volume +
          eLpNorm (fun x => crlPhiC n (partialT v x)) p volume) := by rw [mul_add]
    _ ≤ K * (A * eLpNorm (fun x => crlPhiC n
          (partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x))) p volume) := by gcongr
    _ ≤ K * (A * (L * eLpNorm (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n)
          (partialT v x)) p volume)) := by gcongr
    _ = ((K * A * L : ℝ≥0) : ℝ≥0∞) * eLpNorm (fun x => partialS v x +
          Matrix.toEuclideanLin (J₀ n) (partialT v x)) p volume := by
        push_cast; ring

end

end CauchyRiemannIndex

-- ===== Scratch/CRLocPlaneSol.lean =====
open CauchyRiemannIndex in
theorem solution (n : ℕ) (p : ENNReal) (hp : 1 < p) (hp' : p ≠ ⊤) :
    ∃ A : NNReal, ∀ v : ℝ × ℝ → Vec n, ContDiff ℝ 1 v → HasCompactSupport v →
      MeasureTheory.eLpNorm (partialS v) p MeasureTheory.volume +
          MeasureTheory.eLpNorm (partialT v) p MeasureTheory.volume ≤
        A * MeasureTheory.eLpNorm
          (fun x => partialS v x + Matrix.toEuclideanLin (J₀ n) (partialT v x)) p
          MeasureTheory.volume :=
  crl_plane n p hp hp'
