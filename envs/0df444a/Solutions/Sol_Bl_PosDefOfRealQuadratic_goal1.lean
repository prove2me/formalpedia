-- Prove2me | solution 1 for Bl.PosDefOfRealQuadratic.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:27.257328+00:00
-- url     : https://prove2.me/submissions/ec22d6d2-fa23-400b-b55e-2ee832e4cdb8

import Mathlib
import Definitions.Def_Lemmata_PosDefOfRealQuadratic_QuadFormRealSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u_1
namespace Bl.PosDefOfRealQuadratic
private lemma quadForm_real_smul {m : Nat} (M : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (r : ℝ) :
    star ((r : ℂ) • v) ⬝ᵥ (Matrix.mulVec (M) ((r : ℂ) • v)) = ((r ^ 2 : ℝ) : ℂ) * (star v ⬝ᵥ (Matrix.mulVec (M) v)) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct]
  simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring
open scoped ComplexOrder in
private lemma re_quad_pos {m : Nat} {M : Matrix (Fin m) (Fin m) ℂ} (h : M.PosDef) {y : Fin m → ℂ}
    (hy : y ≠ 0) : 0 < (star y ⬝ᵥ (Matrix.mulVec M y)).re :=
  (Complex.pos_iff.mp (h.dotProduct_mulVec_pos hy)).1
open scoped ComplexOrder in
private lemma posDef_of_re {m : Nat} {M : Matrix (Fin m) (Fin m) ℂ} (hH : M.IsHermitian)
    (h : ∀ v : Fin m → ℂ, v ≠ 0 → 0 < (star v ⬝ᵥ (Matrix.mulVec M v)).re) : M.PosDef :=
  Matrix.PosDef.of_dotProduct_mulVec_pos hH fun v hv =>
    Complex.pos_iff.mpr ⟨h v hv, (hH.im_star_dotProduct_mulVec_self v).symm⟩
end Bl.PosDefOfRealQuadratic
end

set_option autoImplicit false
universe u_1
open Bl Bl.PosDefOfRealQuadratic
namespace Bl.PosDefOfRealQuadratic
theorem _root_.solution :
  ∀ {X : Type u_1} [inst : TopologicalSpace.{u_1} X] {m : Nat} (A : X → Matrix.{0, 0, 0} (Fin m) (Fin m) Complex),
  (∀ (i j : Fin m),
      @Continuous.{u_1, 0} X Complex inst
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        fun (x : X) ↦ A x i j) →
    (∀ (x : X),
        @Matrix.IsHermitian.{0, 0} Complex (Fin m)
          (@InvolutiveStar.toStar.{0} Complex
            (@StarAddMonoid.toInvolutiveStar.{0} Complex
              (@AddCommMonoid.toAddMonoid.{0} Complex
                (@NonUnitalNonAssocSemiring.toAddCommMonoid.{0} Complex
                  (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                    (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                      (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))))
              (@StarRing.toStarAddMonoid.{0} Complex
                (@NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} Complex
                  (@NonUnitalNonAssocCommRing.toNonUnitalNonAssocRing.{0} Complex
                    (@NonUnitalCommRing.toNonUnitalNonAssocCommRing.{0} Complex Complex.instNonUnitalCommRing)))
                Complex.instStarRing)))
          (A x)) →
      ∀ (x0 : X),
        @Matrix.PosDef.{0, 0} (Fin m) Complex Complex.instRing Complex.partialOrder Complex.instStarRing (A x0) →
          @Filter.Eventually.{u_1} X
            (fun (x : X) ↦
              @Matrix.PosDef.{0, 0} (Fin m) Complex Complex.instRing Complex.partialOrder Complex.instStarRing (A x))
            (@nhds.{u_1} X inst x0) := by
  intro X inst m A hA hH x0 h0
  have hAc : Continuous A := continuous_pi fun i => continuous_pi fun j => hA i j
  set K : Set (Fin m → ℂ) := Metric.sphere 0 1 with hK
  have hKc : IsCompact K := isCompact_sphere 0 1
  have hq : Continuous fun p : X × (Fin m → ℂ) => star p.2 ⬝ᵥ (Matrix.mulVec (A p.1) p.2) :=
    (continuous_snd.star).dotProduct ((hAc.comp continuous_fst).matrix_mulVec continuous_snd)
  have key : ∀ᶠ x in nhds x0, ∀ y ∈ K, 0 < (star y ⬝ᵥ (Matrix.mulVec (A x) y)).re := by
    refine hKc.eventually_forall_of_forall_eventually fun y hy => ?_
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp [hK] at hy
    have hpos : 0 < (star y ⬝ᵥ (Matrix.mulVec (A x0) y)).re :=
      re_quad_pos h0 hy0
    have hev := (continuousAt_const (x := (x0, y))).eventually_lt
      ((Complex.continuous_re.comp hq).continuousAt (x := (x0, y))) hpos
    filter_upwards [hev] with z hz using hz
  filter_upwards [key] with x hx
  refine posDef_of_re (hH x) fun v hv => ?_
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw : ((‖v‖⁻¹ : ℝ) : ℂ) • v ∈ K := by
    rw [hK, mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne']
  have h1 := hx _ hw
  rw [quadForm_real_smul, Complex.re_ofReal_mul] at h1
  exact pos_of_mul_pos_right h1 (by positivity)
end Bl.PosDefOfRealQuadratic
