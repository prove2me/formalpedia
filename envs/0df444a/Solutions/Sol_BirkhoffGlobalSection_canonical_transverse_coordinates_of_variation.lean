-- Prove2me | solution 1 for BirkhoffGlobalSection.canonical_transverse_coordinates_of_variation
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-29T19:41:47.740557+00:00
-- url     : https://prove2.me/submissions/7188567f-48d1-465c-a803-24dfbe8589dc

import Definitions.Def_BirkhoffGlobalSection_CanonicalPositiveFrame
import Definitions.Def_BirkhoffGlobalSection_MovingFrameAlgebra
import Definitions.Def_BirkhoffGlobalSection_RegularizationModel
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_HryniewiczCriterion_local_C2_variational_transport



-- Generic Hamiltonian/frame matrix calculations adapted with credit to Mazecto,
-- accepted homogeneous_frame_flow_split and submission 893234ef-5ec2-4f4b-b415-f79ec1030002.
-- The C2 local completion and projected-flow assembly are derived for this contribution.

namespace HryniewiczCriterion.CanonicalMatrix
open HryniewiczCriterion Matrix

def col (F : Matrix (Fin 4) (Fin 4) ℝ) (i : Fin 4) : R4 := fun k => F k i

lemma transpose_omega_mul_apply (F : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) :
    (F.transpose * omegaMat * F) i j = omega0 (col F i) (col F j) := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, omegaMat, omega0, col]; ring

lemma inverse_identities (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) :
    F⁻¹ * F = 1 ∧ F * F⁻¹ = 1 ∧ F⁻¹ * symplJ4 = symplJ4 * F.transpose := by
  have hJΩ : symplJ4 * omegaMat = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  have hΩJ : omegaMat * symplJ4 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [symplJ4, omegaMat, Matrix.mul_apply, Fin.sum_univ_four]
  let G := symplJ4 * F.transpose * omegaMat
  have hGF : G * F = 1 := by
    dsimp [G]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc F.transpose, hF, hJΩ]
  have hInv : F⁻¹ = G := Matrix.inv_eq_left_inv hGF
  refine ⟨by rw [hInv, hGF], ?_, ?_⟩
  · rw [hInv]; exact mul_eq_one_comm.mp hGF
  · rw [hInv]
    dsimp [G]
    rw [Matrix.mul_assoc, hΩJ, Matrix.mul_one]

lemma omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma mulVec_eq_cols (F : Matrix (Fin 4) (Fin 4) ℝ) (c : R4) :
    F.mulVec c = c 0 • col F 0 + c 1 • col F 1 + c 2 • col F 2 + c 3 • col F 3 := by
  ext i; simp [mulVec, dotProduct, Fin.sum_univ_four, col]; ring

lemma frame_coordinates_pairing (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (v : R4) :
    omega0 (col F 0) v = (F⁻¹.mulVec v) 1 ∧
      omega0 (col F 1) v = -(F⁻¹.mulVec v) 0 := by
  let c := F⁻¹.mulVec v
  have hc : F.mulVec c = v := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec, (inverse_identities F hF).2.1, Matrix.one_mulVec]
  have hp : ∀ i j, omega0 (col F i) (col F j) = omegaMat i j := by
    intro i j
    rw [← transpose_omega_mul_apply, hF]
  have h0 : omega0 (col F 0) v = c 1 := by
    calc _ = omega0 (col F 0) (F.mulVec c) := congrArg (omega0 (col F 0)) hc.symm
         _ = c 1 := by rw [mulVec_eq_cols, omega0_lin_right]; simp [hp, omegaMat]
  have h1 : omega0 (col F 1) v = -c 0 := by
    calc _ = omega0 (col F 1) (F.mulVec c) := congrArg (omega0 (col F 1)) hc.symm
         _ = -c 0 := by rw [mulVec_eq_cols, omega0_lin_right]; simp [hp, omegaMat]
  exact ⟨h0, h1⟩

lemma inverse_mulVec_col (F : Matrix (Fin 4) (Fin 4) ℝ)
    (hF : F.transpose * omegaMat * F = omegaMat) (j : Fin 4) :
    F⁻¹.mulVec (col F j) = Pi.single j 1 := by
  change col (F⁻¹ * F) j = _
  rw [(inverse_identities F hF).1]
  ext i; simp [col, Matrix.one_apply, Pi.single_apply, eq_comm]


end HryniewiczCriterion.CanonicalMatrix


set_option backward.isDefEq.respectTransparency false

namespace BirkhoffGlobalSection.CanonicalCoordinates
open BirkhoffGlobalSection HryniewiczCriterion
open scoped ContDiff
noncomputable section
def toHrynCLM : Phase →L[ℝ] R4 :=
  ContinuousLinearMap.pi fun i =>
    ![ContinuousLinearMap.proj 0, -ContinuousLinearMap.proj 2,
      ContinuousLinearMap.proj 1, -ContinuousLinearMap.proj 3] i

def fromHrynCLM : R4 →L[ℝ] Phase :=
  ContinuousLinearMap.pi fun i =>
    ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 2,
      -ContinuousLinearMap.proj 1, -ContinuousLinearMap.proj 3] i

lemma toHrynCLM_apply (v : Phase) : toHrynCLM v = toHryn v := by
  ext i; fin_cases i <;> simp [toHrynCLM, toHryn]
lemma fromHrynCLM_apply (v : R4) : fromHrynCLM v = fromHryn v := by
  ext i; fin_cases i <;> simp [fromHrynCLM, fromHryn]

lemma from_to (v : Phase) : fromHryn (toHryn v) = v := by
  ext i; fin_cases i <;> simp [fromHryn, toHryn]
lemma to_from (v : R4) : toHryn (fromHryn v) = v := by
  ext i; fin_cases i <;> simp [fromHryn, toHryn]


def coordinateEquiv : Phase ≃L[ℝ] R4 where
  toLinearEquiv := { toHrynCLM.toLinearMap with
    invFun := fromHrynCLM
    left_inv := by
      intro v
      change fromHrynCLM (toHrynCLM v) = v
      rw [toHrynCLM_apply, fromHrynCLM_apply, from_to]
    right_inv := by
      intro v
      change toHrynCLM (fromHrynCLM v) = v
      rw [fromHrynCLM_apply, toHrynCLM_apply, to_from] }
  continuous_toFun := toHrynCLM.continuous
  continuous_invFun := fromHrynCLM.continuous

lemma coordinateEquiv_apply (v : Phase) : coordinateEquiv v = toHryn v := toHrynCLM_apply v
lemma coordinateEquiv_symm_apply (v : R4) : coordinateEquiv.symm v = fromHryn v :=
  fromHrynCLM_apply v

lemma coordinateEquiv_coe : (coordinateEquiv : Phase →L[ℝ] R4) = toHrynCLM := by
  ext v i; rfl
lemma coordinateEquiv_symm_coe : (coordinateEquiv.symm : R4 →L[ℝ] Phase) = fromHrynCLM := by
  ext v i; rfl

lemma pullback_fderiv (G : Phase → ℝ) (y : R4) :
    fderiv ℝ (fun z => G (fromHryn z)) y =
      (fderiv ℝ G (fromHryn y)).comp fromHrynCLM := by
  have h := coordinateEquiv.symm.comp_right_fderiv (f := G) (x := y)
  simpa only [Function.comp_def, coordinateEquiv_symm_apply, coordinateEquiv_symm_coe] using h

lemma fromHrynCLM_single (i : Fin 4) :
    fromHrynCLM (Pi.single i 1) =
      ![Pi.single 0 1, -Pi.single 2 1, Pi.single 1 1, -Pi.single 3 1] i := by
  ext j; fin_cases i <;> fin_cases j <;> simp [fromHrynCLM, Pi.single_apply]

lemma vector_field_conjugacy (G : Phase → ℝ) (y : R4) :
    HryniewiczCriterion.hamiltonianVectorField (fun z => G (fromHryn z)) y =
      toHrynCLM (BirkhoffGlobalSection.hamiltonianVectorField G (fromHryn y)) := by
  have hbasis : ∀ i : Fin 4, coordinateVector i = Pi.single i 1 := by
    intro i; ext j; simp [coordinateVector, Pi.single_apply, eq_comm]
  ext i; fin_cases i <;>
    simp [HryniewiczCriterion.hamiltonianVectorField, HryniewiczCriterion.partialDeriv,
      BirkhoffGlobalSection.hamiltonianVectorField, BirkhoffGlobalSection.partialDerivative,
      pullback_fderiv, fromHrynCLM_single, toHrynCLM, hbasis]

lemma fderiv_vector_field_conjugacy (G : Phase → ℝ) (y : R4) :
    fderiv ℝ (HryniewiczCriterion.hamiltonianVectorField (fun z => G (fromHryn z))) y =
      toHrynCLM.comp ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G)
        (fromHryn y)).comp fromHrynCLM) := by
  have heq : HryniewiczCriterion.hamiltonianVectorField (fun z => G (fromHryn z)) =
      coordinateEquiv ∘ BirkhoffGlobalSection.hamiltonianVectorField G ∘ coordinateEquiv.symm := by
    funext z
    simpa only [Function.comp_apply, coordinateEquiv_apply, coordinateEquiv_symm_apply,
      toHrynCLM_apply] using vector_field_conjugacy G z
  rw [heq, coordinateEquiv.comp_fderiv, coordinateEquiv.symm.comp_right_fderiv]
  simp only [coordinateEquiv_coe, coordinateEquiv_symm_coe, coordinateEquiv_symm_apply]


noncomputable def transformedFlow (Y : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) : R4 →L[ℝ] R4 :=
  toHrynCLM.comp ((Y t).comp fromHrynCLM)

lemma transformed_trajectory (G : Phase → ℝ) (x : ℝ → Phase)
    (hx : ∀ t, HasDerivAt x (BirkhoffGlobalSection.hamiltonianVectorField G (x t)) t) :
    ∀ t, HasDerivAt (fun s => toHryn (x s))
      (HryniewiczCriterion.hamiltonianVectorField (fun y => G (fromHryn y)) (toHryn (x t))) t := by
  intro t
  have h := toHrynCLM.hasFDerivAt.comp_hasDerivAt t (hx t)
  simpa only [Function.comp_def, vector_field_conjugacy, toHrynCLM_apply, from_to] using h

lemma transformed_linearized_flow (G : Phase → ℝ) (x : ℝ → Phase)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t) :
    IsLinearizedFlow (fun y => G (fromHryn y)) (fun t => toHryn (x t)) (transformedFlow Y) := by
  have hid : fromHrynCLM.comp toHrynCLM = ContinuousLinearMap.id ℝ Phase := by
    ext v i
    change fromHrynCLM (toHrynCLM v) i = v i
    simp only [toHrynCLM_apply, fromHrynCLM_apply, from_to]
  have hid' : toHrynCLM.comp fromHrynCLM = ContinuousLinearMap.id ℝ R4 := by
    ext v i
    change toHrynCLM (fromHrynCLM v) i = v i
    simp only [fromHrynCLM_apply, toHrynCLM_apply, to_from]
  refine ⟨?_, ?_⟩
  · simp only [transformedFlow, hY0, ContinuousLinearMap.id_comp, hid']
  · intro t
    change HasDerivAt (fun s => transformedFlow Y s) _ t
    have h := (hasDerivAt_const t toHrynCLM).clm_comp
      ((hY t).clm_comp (hasDerivAt_const t fromHrynCLM))
    simpa only [transformedFlow, fderiv_vector_field_conjugacy, from_to,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, zero_add, add_zero,
      ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc fromHrynCLM toHrynCLM,
      hid, ContinuousLinearMap.id_comp] using h

lemma transformedFlow_matrix (Y : ℝ → (Phase →L[ℝ] Phase)) (t : ℝ) :
    LinearMap.toMatrix' (transformedFlow Y t : R4 →ₗ[ℝ] R4) = hrynFlowMatrix Y t := by
  ext i j
  change toHrynCLM (Y t (fromHrynCLM (Pi.single j 1))) i =
    toHryn (Y t (fromHryn (Pi.single j 1))) i
  rw [toHrynCLM_apply, fromHrynCLM_apply]


end
end BirkhoffGlobalSection.CanonicalCoordinates

namespace HryniewiczCriterion.FrameTransition
open HryniewiczCriterion Matrix
lemma lower_coordinates_transport
    (F₀ F R : Matrix (Fin 4) (Fin 4) ℝ)
    (hF₀ : F₀.transpose * omegaMat * F₀ = omegaMat)
    (hF : F.transpose * omegaMat * F = omegaMat)
    (v : R4) (hv : omega0 (CanonicalMatrix.col F₀ 1) v = 0)
    (c : ℝ) (hR : R.mulVec (CanonicalMatrix.col F₀ 1) = c • CanonicalMatrix.col F 1) :
    (fun i : Fin 2 => (F⁻¹.mulVec (R.mulVec v)) i.succ.succ) =
      Matrix.mulVec (fun i j : Fin 2 => (F⁻¹ * R * F₀) i.succ.succ j.succ.succ)
        (fun i : Fin 2 => (F₀⁻¹.mulVec v) i.succ.succ) := by
  let η := F⁻¹ * R * F₀
  let z := F₀⁻¹.mulVec v
  have hz0 : z 0 = 0 := by
    have h := (CanonicalMatrix.frame_coordinates_pairing F₀ hF₀ v).2
    dsimp [z]; linarith
  have hη : η.mulVec z = F⁻¹.mulVec (R.mulVec v) := by
    dsimp [η, z]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc,
      (CanonicalMatrix.inverse_identities F₀ hF₀).2.1, Matrix.mul_one]
  have hcol : CanonicalMatrix.col η 1 = c • Pi.single 1 1 := by
    change (F⁻¹ * R).mulVec (CanonicalMatrix.col F₀ 1) = _
    rw [← Matrix.mulVec_mulVec, hR, Matrix.mulVec_smul, CanonicalMatrix.inverse_mulVec_col F hF]
  have hη2 : η 2 1 = 0 := by simpa [CanonicalMatrix.col] using congrFun hcol 2
  have hη3 : η 3 1 = 0 := by simpa [CanonicalMatrix.col] using congrFun hcol 3
  change (fun i : Fin 2 => (F⁻¹.mulVec (R.mulVec v)) i.succ.succ) =
    Matrix.mulVec (fun i j : Fin 2 => η i.succ.succ j.succ.succ) (fun i : Fin 2 => z i.succ.succ)
  ext i
  rw [← hη]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_two]
  fin_cases i
  · change η 2 0 * z 0 + η 2 1 * z 1 + η 2 2 * z 2 + η 2 3 * z 3 = _
    simp [hz0, hη2]
  · change η 3 0 * z 0 + η 3 1 * z 1 + η 3 2 * z 2 + η 3 3 * z 3 = _
    simp [hz0, hη3]


end HryniewiczCriterion.FrameTransition

namespace BirkhoffGlobalSection.RadialAngle
open BirkhoffGlobalSection HryniewiczCriterion Matrix
open scoped ContDiff
noncomputable section

lemma covector_decomp (L : R4 →L[ℝ] ℝ) (w : R4) :
    L w = ∑ i, L (Pi.single i 1) * w i := by
  have hw : w = ∑ i, w i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp [map_smul, mul_comm]

lemma omega_hamiltonian_left (H : R4 → ℝ) (y w : R4) :
    omega0 (HryniewiczCriterion.hamiltonianVectorField H y) w = - fderiv ℝ H y w := by
  rw [covector_decomp]
  simp [omega0, HryniewiczCriterion.hamiltonianVectorField, partialDeriv, Fin.sum_univ_four]
  ring

lemma omega_hamiltonian_right (H : R4 → ℝ) (y w : R4) :
    omega0 w (HryniewiczCriterion.hamiltonianVectorField H y) = fderiv ℝ H y w := by
  have he := omega_hamiltonian_left H y w
  simp only [omega0] at *
  linarith

lemma frame_col1 (H : R4 → ℝ) (y : R4) :
    CanonicalMatrix.col (homogFrame H y) 1 =
      (omega0 y (HryniewiczCriterion.hamiltonianVectorField H y))⁻¹ •
        HryniewiczCriterion.hamiltonianVectorField H y := rfl

lemma quotient_flow_coordinates
    (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t)
    (v : Phase) (hv : fderiv ℝ G (x 0) v = 0)
    (hsp : ∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat) (τ : ℝ) :
    fderiv ℝ G (x (τ * T)) (Y (τ * T) v) = 0 ∧
    (fun i : Fin 2 => ((canonicalRadialFrame G x (τ * T))⁻¹.mulVec
      (toHryn (Y (τ * T) v))) i.succ.succ) =
    (canonicalTransversePath G x T Y τ).mulVec
      (fun i : Fin 2 => ((canonicalRadialFrame G x 0)⁻¹.mulVec (toHryn v)) i.succ.succ) := by
  let H : R4 → ℝ := fun y => G (fromHryn y)
  let y : ℝ → R4 := fun t => toHryn (x t)
  let Z := CanonicalCoordinates.transformedFlow Y
  have hH : ∀ t, ContDiffAt ℝ 2 H (y t) := by
    intro t
    have hGc : ContDiffAt ℝ 2 G (CanonicalCoordinates.fromHrynCLM (y t)) := by
      simpa only [y, CanonicalCoordinates.fromHrynCLM_apply, CanonicalCoordinates.from_to] using
        (hx.2.1 t).1.1 (x t) (by simp)
    have hh := hGc.comp (y t) CanonicalCoordinates.fromHrynCLM.contDiff.contDiffAt
    simpa only [H, Function.comp_def, CanonicalCoordinates.fromHrynCLM_apply] using hh
  have hy := CanonicalCoordinates.transformed_trajectory G x hx.2.2.1
  have hZ := CanonicalCoordinates.transformed_linearized_flow G x Y hY0 hY
  have htr := HryniewiczCriterion.local_C2_variational_transport H y hH hy Z hZ
  have hrad : ∀ t, 0 < fderiv ℝ H (y t) (y t) := by
    intro t
    simpa only [H, y, CanonicalCoordinates.pullback_fderiv, CanonicalCoordinates.from_to,
      ContinuousLinearMap.comp_apply, CanonicalCoordinates.fromHrynCLM_apply] using (hx.2.1 t).2
  have hv0 : fderiv ℝ H (y 0) (toHryn v) = 0 := by
    simpa only [H, y, CanonicalCoordinates.pullback_fderiv, CanonicalCoordinates.from_to,
      ContinuousLinearMap.comp_apply, CanonicalCoordinates.fromHrynCLM_apply] using hv
  have hvω : omega0 (CanonicalMatrix.col (canonicalRadialFrame G x 0) 1) (toHryn v) = 0 := by
    change omega0 (CanonicalMatrix.col (homogFrame H (y 0)) 1) (toHryn v) = 0
    rw [frame_col1]
    have hsmul : ∀ (c : ℝ) (u : R4), omega0 (c • u) (toHryn v) = c * omega0 u (toHryn v) := by
      intros; simp [omega0]; ring
    rw [hsmul, omega_hamiltonian_left, hv0]; simp
  let r : ℝ → ℝ := fun t => omega0 (y t) (HryniewiczCriterion.hamiltonianVectorField H (y t))
  have hrne : ∀ t, r t ≠ 0 := by
    intro t
    simpa only [r, omega_hamiltonian_right] using (hrad t).ne'
  have hR : (hrynFlowMatrix Y (τ * T)).mulVec
      (CanonicalMatrix.col (canonicalRadialFrame G x 0) 1) =
      (r (τ * T) / r 0) • CanonicalMatrix.col (canonicalRadialFrame G x (τ * T)) 1 := by
    rw [← CanonicalCoordinates.transformedFlow_matrix]
    rw [LinearMap.toMatrix'_mulVec]
    change Z (τ * T) (CanonicalMatrix.col (homogFrame H (y 0)) 1) =
      (r (τ * T) / r 0) • CanonicalMatrix.col (homogFrame H (y (τ * T))) 1
    rw [frame_col1, frame_col1, map_smul, htr.2]
    change (r 0)⁻¹ • HryniewiczCriterion.hamiltonianVectorField H (y (τ * T)) =
      (r (τ * T) / r 0) • ((r (τ * T))⁻¹ • HryniewiczCriterion.hamiltonianVectorField H (y (τ * T)))
    rw [smul_smul]
    congr 1
    field_simp [hrne 0, hrne (τ * T)]
  have he := FrameTransition.lower_coordinates_transport
    (canonicalRadialFrame G x 0) (canonicalRadialFrame G x (τ * T))
    (hrynFlowMatrix Y (τ * T)) (hsp 0) (hsp (τ * T)) (toHryn v) hvω _ hR
  have hRv : (hrynFlowMatrix Y (τ * T)).mulVec (toHryn v) = toHryn (Y (τ * T) v) := by
    rw [← CanonicalCoordinates.transformedFlow_matrix, LinearMap.toMatrix'_mulVec]
    change CanonicalCoordinates.toHrynCLM (Y (τ * T)
      (CanonicalCoordinates.fromHrynCLM (toHryn v))) = _
    rw [CanonicalCoordinates.fromHrynCLM_apply, CanonicalCoordinates.from_to,
      CanonicalCoordinates.toHrynCLM_apply]
  rw [hRv] at he
  refine ⟨?_, he⟩
  have hve : fderiv ℝ H (y (τ * T)) (Z (τ * T) (toHryn v)) = 0 := by
    rw [htr.1, hv0]
  change fderiv ℝ H (y (τ * T))
    (CanonicalCoordinates.toHrynCLM (Y (τ * T)
      (CanonicalCoordinates.fromHrynCLM (toHryn v)))) = 0 at hve
  simpa only [H, y, CanonicalCoordinates.fromHrynCLM_apply, CanonicalCoordinates.toHrynCLM_apply,
    CanonicalCoordinates.pullback_fderiv, CanonicalCoordinates.from_to,
    ContinuousLinearMap.comp_apply] using hve

end
end BirkhoffGlobalSection.RadialAngle

open BirkhoffGlobalSection HryniewiczCriterion
theorem solution
    (G : Phase → ℝ) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn G {y | IsStrictlyConvexStarShapedAt G y} x T)
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY0 : Y 0 = ContinuousLinearMap.id ℝ Phase)
    (hY : ∀ t : ℝ, HasDerivAt Y
      ((fderiv ℝ (BirkhoffGlobalSection.hamiltonianVectorField G) (x t)).comp (Y t)) t)
    (v : Phase) (hv : fderiv ℝ G (x 0) v = 0)
    (hsp : ∀ t, (canonicalRadialFrame G x t).transpose * omegaMat *
      canonicalRadialFrame G x t = omegaMat) (τ : ℝ) :
    fderiv ℝ G (x (τ * T)) (Y (τ * T) v) = 0 ∧
    (fun i : Fin 2 => ((canonicalRadialFrame G x (τ * T))⁻¹.mulVec
      (toHryn (Y (τ * T) v))) i.succ.succ) =
    (canonicalTransversePath G x T Y τ).mulVec
      (fun i : Fin 2 => ((canonicalRadialFrame G x 0)⁻¹.mulVec (toHryn v)) i.succ.succ) := by
  exact BirkhoffGlobalSection.RadialAngle.quotient_flow_coordinates G x T hx Y hY0 hY v hv hsp τ