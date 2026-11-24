-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.charpoly_smul_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:43.138192+00:00
-- url     : https://prove2.me/submissions/62646784-e073-4dd2-8f53-b7e5e40b4427

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
private theorem separable_comp_C_mul_X_of_ne_zero {K : Type*} [Field K] {p : Polynomial K} (hp : p.Separable) {a : K}
    (ha : a ≠ 0) : (p.comp (Polynomial.C a * Polynomial.X)).Separable := by
  rw [Polynomial.separable_def] at hp ⊢
  obtain ⟨u, v, e⟩ := hp
  set q := Polynomial.C a * Polynomial.X with hqdef
  have hcomp : (u * p + v * Polynomial.derivative p).comp q = 1 := by rw [e, Polynomial.one_comp]
  rw [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.mul_comp] at hcomp
  have hq : Polynomial.derivative q = Polynomial.C a := by simp [hqdef]
  have hC : Polynomial.C a⁻¹ * Polynomial.C a = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ ha, Polynomial.C_1]
  refine ⟨u.comp q, v.comp q * Polynomial.C a⁻¹, ?_⟩
  rw [Polynomial.derivative_comp, hq]
  linear_combination hcomp + (v.comp q * (Polynomial.derivative p).comp q) * hC
section Pts
variable {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
  [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))
end Pts
end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {K : Type*} [Field K] {S : Type*} [Fintype S] [DecidableEq S] (B : Matrix S S K)
    (c : K) (hc : c ≠ 0) (h : B.charpoly.Separable) : (c • B).charpoly.Separable := by
  classical
  have key : Matrix.charmatrix (c • B) = Polynomial.C c •
      (Matrix.charmatrix B).map (Polynomial.compRingHom (Polynomial.C c⁻¹ * Polynomial.X)) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.map_apply,
        Polynomial.coe_compRingHom_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
        smul_eq_mul]
      rw [mul_sub, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, mul_inv_cancel₀ hc,
        Polynomial.C_1, one_mul]
    · simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply_ne _ hij, zero_sub, Matrix.smul_apply,
        Matrix.map_apply, Polynomial.coe_compRingHom_apply, Polynomial.neg_comp, Polynomial.C_comp,
        smul_eq_mul, mul_neg]
      rw [Polynomial.C_mul]
  have hcp : (c • B).charpoly =
      Polynomial.C (c ^ Fintype.card S) * B.charpoly.comp (Polynomial.C c⁻¹ * Polynomial.X) := by
    rw [Matrix.charpoly, key, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Polynomial.coe_compRingHom_apply, Polynomial.C_pow, Matrix.charpoly]
  rw [hcp]
  exact Polynomial.Separable.unit_mul
    (Polynomial.isUnit_C.mpr ((isUnit_iff_ne_zero.mpr hc).pow _)) (separable_comp_C_mul_X_of_ne_zero h (inv_ne_zero hc))
end Formalism.RepresentationBoundsCohomology.ringDataObjects
