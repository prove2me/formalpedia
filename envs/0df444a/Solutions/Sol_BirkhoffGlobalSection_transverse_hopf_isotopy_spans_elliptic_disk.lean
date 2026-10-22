-- Prove2me | solution 1 for BirkhoffGlobalSection.transverse_hopf_isotopy_spans_elliptic_disk
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-07T03:07:44.96139+00:00
-- url     : https://prove2.me/submissions/1f4f0c10-da19-49f6-92d9-6e1992c84208
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BirkhoffGlobalSection_equivariant_transverse_isotopy_extension
import Theorems.Thm_BirkhoffGlobalSection_standard_hopf_elliptic_rational_disk
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

/-!
# A transverse Hopf isotopy spans an elliptic disk

The child `equivariant_transverse_isotopy_extension` extends the transverse isotopy to an
equivariant contactomorphism `F` of the sphere with `F (standard Hopf circle) = K`. The
standard Hopf circle bounds a positive elliptic rational disk `D`
(`standard_hopf_elliptic_rational_disk`). We show here that `F ∘ D` is a positive elliptic
rational disk for `K`.

* `D` takes values in the sphere on the closed disk, so its derivative is tangent to the
  sphere, boundary points included (`PositiveEllipticRationalDisk.tangent`). The derivative
  of the identity `|D|² = 1` is computed from one-sided difference quotients along segments
  into the disk.
* On tangent vectors `F` multiplies the radial contact form by `contactFactor F y > 0`.
  The factor is read off on the tangent direction `reebDir y`, where the form equals `1/2`.
  It is smooth near the sphere because `F` is.
* The characteristic field of `F ∘ D` is therefore `(contactFactor F ∘ D) • W`, where `W` is
  the characteristic field of `D`. Since `W 0 = 0`, its derivative at `0` is
  `contactFactor F (D 0) • κ • id`.
* `F⁻¹ ∘ (F ∘ D) = D` on the closed disk gives the immersion property. Injectivity, the
  antipodal fibers and the boundary follow from `F⁻¹ ∘ F = id` on the sphere and the
  equivariance of `F`.
-/

open scoped ContDiff Topology
open Filter

namespace BirkhoffGlobalSection

/-- Segments between points of the closed unit disk stay in it. -/
lemma disk_segment_mem {u p : Plane} (hu : u ∈ closedUnitDisk) (hp : p ∈ closedUnitDisk)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : u + t • (p - u) ∈ closedUnitDisk := by
  simp only [closedUnitDisk, planeNormSq, Set.mem_ofPred_eq] at hu hp ⊢
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  obtain ⟨h0, h1⟩ := ht
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.2 h1))
      (add_nonneg (sq_nonneg (u 0 - p 0)) (sq_nonneg (u 1 - p 1))),
    mul_le_mul_of_nonneg_left hu (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left hp h0]

/-- Two curves agreeing on `[0,1]` have the same derivative at `0`. -/
lemma hasDerivAt_unique_of_eqOn_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ ψ : ℝ → E} {a b : E} (hφ : HasDerivAt φ a 0) (hψ : HasDerivAt ψ b 0)
    (h : Set.EqOn φ ψ (Set.Icc 0 1)) : a = b := by
  have h2 : HasDerivWithinAt φ b (Set.Ici 0) 0 := by
    refine hψ.hasDerivWithinAt.congr_of_eventuallyEq ?_ (h ⟨le_rfl, zero_le_one⟩)
    filter_upwards [Icc_mem_nhdsGE (zero_lt_one' ℝ)] with t ht using h ht
  exact (uniqueDiffWithinAt_Ici 0).eq_deriv _ hφ.hasDerivWithinAt h2

/-- Maps agreeing on the closed unit disk have the same derivative at each of its points,
boundary points included. -/
lemma fderiv_eq_of_eqOn_closedUnitDisk {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : Plane → E} {u : Plane} (hu : u ∈ closedUnitDisk)
    (hf : DifferentiableAt ℝ f u) (hg : DifferentiableAt ℝ g u)
    (h : Set.EqOn f g closedUnitDisk) : fderiv ℝ f u = fderiv ℝ g u := by
  have key : ∀ p ∈ closedUnitDisk, fderiv ℝ f u (p - u) = fderiv ℝ g u (p - u) := by
    intro p hp
    have hl : HasDerivAt (fun t : ℝ => u + t • (p - u)) (p - u) 0 := by
      simpa using HasDerivAt.smul_const (hasDerivAt_id' (x := (0 : ℝ))) (p - u)
    have h1 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    have h2 := hg.hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
    exact hasDerivAt_unique_of_eqOn_Icc h1 h2 (fun t ht => h (disk_segment_mem hu hp ht))
  have k0 := key 0 (by simp [closedUnitDisk, planeNormSq])
  have k1 := key ![1 / 2, 0] (by norm_num [closedUnitDisk, planeNormSq])
  have k2 := key ![0, 1 / 2] (by norm_num [closedUnitDisk, planeNormSq])
  refine ContinuousLinearMap.ext fun w => ?_
  have hw : w = (2 * w 0) • ((![1 / 2, 0] - u) - (0 - u)) +
      (2 * w 1) • ((![0, 1 / 2] - u) - (0 - u)) := by
    ext i; fin_cases i <;> simp <;> ring
  rw [hw]
  simp only [map_add, map_smul, map_sub, k0, k1, k2]

/-- The derivative of the disk map is tangent to the sphere on the closed disk. -/
lemma PositiveEllipticRationalDisk.tangent {L : Set Phase} (D : PositiveEllipticRationalDisk L)
    {u : Plane} (hu : u ∈ closedUnitDisk) (w : Plane) :
    phaseDot (D.disk u) (fderiv ℝ D.disk u w) = 0 := by
  have hp := fun i : Fin 4 =>
    (hasFDerivAt_apply (𝕜 := ℝ) i (D.disk u)).mul (hasFDerivAt_apply (𝕜 := ℝ) i (D.disk u))
  have hN := ((hp 0).add (hp 1)).add ((hp 2).add (hp 3))
  have hND := (hN.comp u ((D.smooth u hu).differentiableAt (by simp)).hasFDerivAt
    ).congr_of_eventuallyEq (f₁ := fun v => zNormSq (D.disk v) + wNormSq (D.disk v))
    (Filter.Eventually.of_forall fun v => by simp [zNormSq, wNormSq]; ring)
  have hc : Set.EqOn (fun v => zNormSq (D.disk v) + wNormSq (D.disk v)) (fun _ => (1 : ℝ))
      closedUnitDisk := fun v hv => D.sphere v hv
  have hzero := fderiv_eq_of_eqOn_closedUnitDisk hu hND.differentiableAt
    (differentiableAt_const _) hc
  rw [hND.fderiv, fderiv_const_apply] at hzero
  have h := congrArg (fun T => T w) hzero
  simp at h
  simp only [phaseDot]
  linarith

/-- A tangent direction on which the radial contact form equals half the squared radius. -/
def reebDir (y : Phase) : Phase := ![y 2, y 3, -y 0, -y 1]

/-- The conformal factor of `F` at `y`, read off on `reebDir y`. -/
noncomputable def contactFactor (F : EquivariantSphereContactomorphism) (y : Phase) : ℝ :=
  2 * phaseRadialContact (F.toFun y) (fderiv ℝ F.toFun y (reebDir y))

lemma contactFactor_spec (F : EquivariantSphereContactomorphism) {y : Phase}
    (hy : y ∈ unitThreeSphere) :
    0 < contactFactor F y ∧ ∀ v : Phase, phaseDot y v = 0 →
      phaseRadialContact (F.toFun y) (fderiv ℝ F.toFun y v) =
        contactFactor F y * phaseRadialContact y v := by
  obtain ⟨a, ha, hc⟩ := F.contact y hy
  have hR : phaseDot y (reebDir y) = 0 := by
    simp [phaseDot, reebDir]; ring
  have hlam : phaseRadialContact y (reebDir y) = 1 / 2 := by
    have h1 : zNormSq y + wNormSq y = 1 := hy
    simp only [zNormSq, wNormSq] at h1
    simp [phaseRadialContact, phaseSymplecticForm, reebDir]
    linear_combination (1 / 2 : ℝ) * h1
  have hA : contactFactor F y = a := by
    rw [contactFactor, hc _ hR, hlam]; ring
  rw [hA]
  exact ⟨ha, hc⟩

lemma contactFactor_differentiableAt (F : EquivariantSphereContactomorphism) {y : Phase}
    (hy : y ∈ unitThreeSphere) : DifferentiableAt ℝ (contactFactor F) y := by
  have hF := F.smooth y hy
  have h1 : DifferentiableAt ℝ F.toFun y := hF.differentiableAt (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ F.toFun) y :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have h3 : DifferentiableAt ℝ reebDir y := by
    rw [differentiableAt_pi]
    intro i; fin_cases i <;> simp [reebDir] <;> fun_prop
  have h4 := h2.clm_apply h3
  have a0 : DifferentiableAt ℝ (fun x => F.toFun x 0) y := differentiableAt_pi.1 h1 0
  have a1 : DifferentiableAt ℝ (fun x => F.toFun x 1) y := differentiableAt_pi.1 h1 1
  have a2 : DifferentiableAt ℝ (fun x => F.toFun x 2) y := differentiableAt_pi.1 h1 2
  have a3 : DifferentiableAt ℝ (fun x => F.toFun x 3) y := differentiableAt_pi.1 h1 3
  have b0 : DifferentiableAt ℝ (fun x => fderiv ℝ F.toFun x (reebDir x) 0) y :=
    differentiableAt_pi.1 h4 0
  have b1 : DifferentiableAt ℝ (fun x => fderiv ℝ F.toFun x (reebDir x) 1) y :=
    differentiableAt_pi.1 h4 1
  have b2 : DifferentiableAt ℝ (fun x => fderiv ℝ F.toFun x (reebDir x) 2) y :=
    differentiableAt_pi.1 h4 2
  have b3 : DifferentiableAt ℝ (fun x => fderiv ℝ F.toFun x (reebDir x) 3) y :=
    differentiableAt_pi.1 h4 3
  unfold contactFactor phaseRadialContact phaseSymplecticForm
  fun_prop

/-- The characteristic field of `F ∘ D` is the contact factor times that of `D`. -/
lemma diskCharacteristic_comp (F : EquivariantSphereContactomorphism) {L : Set Phase}
    (D : PositiveEllipticRationalDisk L) {u : Plane} (hu : u ∈ closedUnitDisk) :
    diskCharacteristic (F.toFun ∘ D.disk) u =
      contactFactor F (D.disk u) • diskCharacteristic D.disk u := by
  have hy := D.sphere u hu
  have hcomp : fderiv ℝ (F.toFun ∘ D.disk) u =
      (fderiv ℝ F.toFun (D.disk u)).comp (fderiv ℝ D.disk u) :=
    fderiv_comp u ((F.smooth _ hy).differentiableAt (by simp))
      ((D.smooth u hu).differentiableAt (by simp))
  have hc := (contactFactor_spec F hy).2
  ext i
  fin_cases i
  · simp only [diskCharacteristic, Function.comp_apply, hcomp, ContinuousLinearMap.comp_apply,
      hc _ (D.tangent hu _), Pi.smul_apply, smul_eq_mul]
    simp
  · simp only [diskCharacteristic, Function.comp_apply, hcomp, ContinuousLinearMap.comp_apply,
      hc _ (D.tangent hu _), Pi.smul_apply, smul_eq_mul]
    simp

/-- Transport of a positive elliptic rational disk by an equivariant contactomorphism. -/
noncomputable def transportDisk (F : EquivariantSphereContactomorphism) {L : Set Phase}
    (D : PositiveEllipticRationalDisk L) : PositiveEllipticRationalDisk (F.toFun '' L) where
  disk := F.toFun ∘ D.disk
  sphere u hu := F.maps_sphere (D.sphere u hu)
  smooth u hu := (F.smooth _ (D.sphere u hu)).comp u (D.smooth u hu)
  injective u hu v hv huv := by
    apply D.injective hu hv
    have h := congrArg F.invFun huv
    simp only [Function.comp_apply] at h
    rwa [F.left_inv _ (D.sphere u hu), F.left_inv _ (D.sphere v hv)] at h
  immersion u hu := by
    have hy := D.sphere u hu
    have hFd : DifferentiableAt ℝ F.toFun (D.disk u) :=
      (F.smooth _ hy).differentiableAt (by simp)
    have hDd : DifferentiableAt ℝ D.disk u := (D.smooth u hu).differentiableAt (by simp)
    have hId : DifferentiableAt ℝ F.invFun (F.toFun (D.disk u)) :=
      (F.inv_smooth _ (F.maps_sphere hy)).differentiableAt (by simp)
    have hFD : DifferentiableAt ℝ (F.toFun ∘ D.disk) u := hFd.comp u hDd
    have heq : fderiv ℝ (F.invFun ∘ (F.toFun ∘ D.disk)) u = fderiv ℝ D.disk u :=
      fderiv_eq_of_eqOn_closedUnitDisk hu (hId.comp u hFD) hDd
        (fun v hv => F.left_inv _ (D.sphere v hv))
    rw [fderiv_comp u hId hFD] at heq
    intro a b hab
    apply D.immersion u hu
    rw [← heq, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hab]
  boundary := by rw [Set.image_comp, D.boundary]
  antipodal_fibers u hu v hv := by
    rw [← D.antipodal_fibers u hu v hv]
    have hu' := D.sphere u hu
    have hv' := D.sphere v hv
    have hnv : -D.disk v ∈ unitThreeSphere := by
      simpa [unitThreeSphere, zNormSq, wNormSq] using hv'
    simp only [Function.comp_apply]
    rw [← F.antipodal _ hv']
    constructor
    · intro h
      have h' := congrArg F.invFun h
      rwa [F.left_inv _ hu', F.left_inv _ hnv] at h'
    · intro h
      rw [h]
  positive_boundary u hu := by
    have hu' : u ∈ closedUnitDisk := by
      simp only [closedUnitDisk, unitCircle, Set.mem_ofPred_eq] at hu ⊢
      exact hu.le
    have hy := D.sphere u hu'
    have hcomp : fderiv ℝ (F.toFun ∘ D.disk) u =
        (fderiv ℝ F.toFun (D.disk u)).comp (fderiv ℝ D.disk u) :=
      fderiv_comp u ((F.smooth _ hy).differentiableAt (by simp))
        ((D.smooth u hu').differentiableAt (by simp))
    obtain ⟨hpos, hc⟩ := contactFactor_spec F hy
    rw [Function.comp_apply, hcomp, ContinuousLinearMap.comp_apply, hc _ (D.tangent hu' _)]
    exact mul_pos hpos (D.positive_boundary u hu)
  characteristic_zero u hu := by
    have hu' : u ∈ closedUnitDisk := by
      simp only [closedUnitDisk, openUnitDisk, Set.mem_ofPred_eq] at hu ⊢
      exact hu.le
    rw [diskCharacteristic_comp F D hu', smul_eq_zero, ← D.characteristic_zero u hu]
    have hpos := (contactFactor_spec F (D.sphere u hu')).1
    constructor
    · rintro (h | h)
      · exact absurd h hpos.ne'
      · exact h
    · exact Or.inr
  elliptic := by
    obtain ⟨κ, hκ, hW⟩ := D.elliptic
    have h0 : (0 : Plane) ∈ openUnitDisk := by simp [openUnitDisk, planeNormSq]
    have h0' : (0 : Plane) ∈ closedUnitDisk := by simp [closedUnitDisk, planeNormSq]
    have hnhds : closedUnitDisk ∈ 𝓝 (0 : Plane) := by
      have hopen : IsOpen openUnitDisk :=
        isOpen_lt (by unfold planeNormSq; fun_prop) continuous_const
      refine Filter.mem_of_superset (hopen.mem_nhds h0) (fun v hv => ?_)
      simp only [openUnitDisk, closedUnitDisk, Set.mem_ofPred_eq] at hv ⊢
      exact hv.le
    have hcd : DifferentiableAt ℝ (fun u => contactFactor F (D.disk u)) 0 :=
      (contactFactor_differentiableAt F (D.sphere 0 h0')).comp (0 : Plane)
        ((D.smooth 0 h0').differentiableAt (by simp))
    have hWd : DifferentiableAt ℝ (diskCharacteristic D.disk) 0 := by
      by_contra hnd
      have h1 := hW ![1, 0]
      rw [fderiv_zero_of_not_differentiableAt hnd] at h1
      have h2 := congrFun h1 0
      simp at h2
      linarith
    have hW0 : diskCharacteristic D.disk 0 = 0 := (D.characteristic_zero 0 h0).2 rfl
    have hev : diskCharacteristic (F.toFun ∘ D.disk) =ᶠ[𝓝 0]
        (fun u => contactFactor F (D.disk u)) • diskCharacteristic D.disk := by
      filter_upwards [hnhds] with u hu
      exact diskCharacteristic_comp F D hu
    have hder := hcd.hasFDerivAt.smul hWd.hasFDerivAt
    refine ⟨contactFactor F (D.disk 0) * κ,
      mul_pos (contactFactor_spec F (D.sphere 0 h0')).1 hκ, fun v => ?_⟩
    rw [hev.fderiv_eq, hder.fderiv]
    simp [hW0, hW v, smul_smul]

end BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (K : Set Phase) (I : EquivariantTransverseHopfIsotopy K) :
    Nonempty (PositiveEllipticRationalDisk K) := by
  obtain ⟨F, hF⟩ := equivariant_transverse_isotopy_extension K I
  obtain ⟨D⟩ := standard_hopf_elliptic_rational_disk
  exact hF ▸ ⟨transportDisk F D⟩
