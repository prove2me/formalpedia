-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hj_caseB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:46.441591+00:00
-- url     : https://prove2.me/submissions/522f9225-e763-4684-948d-9a16596601cd

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_hj_norm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_rmulE
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_lmulE
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_det_eq_of_agree
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hs : ∀ c : F, star (algebraMap F E c) = algebraMap F E c)
    (ε : E) (β : Module.Basis (Fin 2) F E) (h0 : β 0 = 1) (h1 : β 1 = ε)
    (hε : ε * ε = 0) (hstar : star ε = -ε) (htwo : (2 : F) ≠ 0) (m : ℕ)
    (A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (congrHerm F E hs m A) = Algebra.norm F A.det ^ m := by
  classical
  have : Module.Finite F E := Module.Finite.of_basis β
  let π0 := dualNumberReal β ε h0 h1 hε
  have hπ0 : ∀ e, π0 e = β.repr e 0 := fun e => rfl
  have hrep0 : ∀ a b : F, π0 (algebraMap F E a + algebraMap F E b * ε) = a := fun a b =>
    (hj_repr β ε h0 h1 a b).1
  have hrep1 : ∀ a b : F, β.repr (algebraMap F E a + algebraMap F E b * ε) 1 = b := fun a b =>
    (hj_repr β ε h0 h1 a b).2
  have hdec : ∀ e, e = algebraMap F E (π0 e) + algebraMap F E (β.repr e 1) * ε :=
    hj_decomp β ε h0 h1
  have hst : ∀ e, star e = algebraMap F E (π0 e) + algebraMap F E (-(β.repr e 1)) * ε := by
    intro e
    conv_lhs => rw [hdec e]
    rw [star_add, star_mul', hs, hs, hstar, map_neg]; ring
  have hπ0st : ∀ e, π0 (star e) = π0 e := fun e => by rw [hst e, hrep0]
  have hπ1st : ∀ e, β.repr (star e) 1 = -(β.repr e 1) := fun e => by rw [hst e, hrep1]
  have hεe : ∀ e, ε * e = ε * algebraMap F E (π0 e) := by
    intro e
    conv_lhs => rw [hdec e]
    linear_combination (algebraMap F E (β.repr e 1)) * hε
  let A0 : Matrix (Fin m) (Fin m) F := π0.mapMatrix A

  let Φ0 : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) E :=
    { toFun := fun Y => Matrix.of fun i j =>
        algebraMap F E (Y i j + Y j i) + algebraMap F E (Y i j - Y j i) * ε
      map_add' := fun Y Z => by
        ext i j
        simp only [Matrix.of_apply, Matrix.add_apply, map_add, map_sub]; ring
      map_smul' := fun c Y => by
        ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, map_add,
          map_sub, map_mul, Algebra.smul_def]
        ring }
  have hΦ0 : ∀ Y i j, Φ0 Y i j
      = algebraMap F E (Y i j + Y j i) + algebraMap F E (Y i j - Y j i) * ε := fun Y i j => rfl
  have hΦH : ∀ Y, Φ0 Y ∈ hermSub F E hs m := by
    intro Y
    change (Φ0 Y).conjTranspose = Φ0 Y
    ext i j
    rw [Matrix.conjTranspose_apply, hΦ0, hΦ0, star_add, star_mul', hs, hs, hstar]
    simp only [map_add, map_sub]; ring
  let Φl : Matrix (Fin m) (Fin m) F →ₗ[F] hermSub F E hs m := LinearMap.codRestrict _ Φ0 hΦH
  have hinj : Function.Injective Φl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Y hY
    have hY0 : Φ0 Y = 0 := congrArg Subtype.val hY
    ext i j
    have e := congrFun (congrFun hY0 i) j
    rw [hΦ0] at e
    have e0 := hrep0 (Y i j + Y j i) (Y i j - Y j i)
    have e1 := hrep1 (Y i j + Y j i) (Y i j - Y j i)
    rw [e] at e0 e1
    simp only [Matrix.zero_apply, map_zero, Finsupp.coe_zero, Pi.zero_apply] at e0 e1
    have : (2 : F) * Y i j = 0 := by linear_combination -e0 - e1
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h htwo
    · simpa using h
  have hsurj : Function.Surjective Φl := by
    intro X
    have hX : ∀ i j, (X : Matrix (Fin m) (Fin m) E) j i = star ((X : Matrix (Fin m) (Fin m) E) i j) := by
      intro i j
      have := congrFun (congrFun X.2 j) i
      rw [Matrix.conjTranspose_apply] at this
      exact this.symm
    refine ⟨Matrix.of fun i j => (π0 ((X : Matrix (Fin m) (Fin m) E) i j)
      + β.repr ((X : Matrix (Fin m) (Fin m) E) i j) 1) / 2, Subtype.ext ?_⟩
    ext i j
    change Φ0 _ i j = _
    rw [hΦ0]
    simp only [Matrix.of_apply]
    rw [hX i j, hπ0st, hπ1st]
    conv_rhs => rw [hdec ((X : Matrix (Fin m) (Fin m) E) i j)]
    have ea : ∀ a b : F, (a + b) / 2 + (a + -b) / 2 = a := fun a b => by field_simp; ring
    have eb : ∀ a b : F, (a + b) / 2 - (a + -b) / 2 = b := fun a b => by field_simp; ring
    rw [ea, eb]
  let Φ : Matrix (Fin m) (Fin m) F ≃ₗ[F] hermSub F E hs m := LinearEquiv.ofBijective Φl ⟨hinj, hsurj⟩
  have hΦ : ∀ Y, ((Φ Y : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = Φ0 Y := fun Y => rfl
  have hP0Φ : ∀ Y, π0.mapMatrix (Φ0 Y) = Y + Y.transpose := by
    intro Y
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, hΦ0, hrep0]
    rfl
  have hP0H : π0.mapMatrix A.conjTranspose = A0.transpose := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
      Matrix.transpose_apply, A0, hπ0st]
  let c0 : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) F :=
    rmulE m A0 ∘ₗ lmulE m A0.transpose
  have hc0 : ∀ Y, c0 Y = A0.transpose * Y * A0 := fun Y => rfl
  have hc0T : ∀ Y, c0 Y + (c0 Y).transpose = A0.transpose * (Y + Y.transpose) * A0 := by
    intro Y
    rw [hc0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc A0.transpose Y.transpose]
  let f' : Matrix (Fin m) (Fin m) F →ₗ[F] Matrix (Fin m) (Fin m) F :=
    (Φ.symm : _ →ₗ[F] _) ∘ₗ congrHerm F E hs m A ∘ₗ (Φ.symm.symm : _ →ₗ[F] _)
  have hf' : ∀ Y, Φ0 (f' Y) = A.conjTranspose * Φ0 Y * A := by
    intro Y
    rw [← hΦ]
    change ((Φ (Φ.symm (congrHerm F E hs m A (Φ Y))) : hermSub F E hs m) : Matrix (Fin m) (Fin m) E) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hdet1 : LinearMap.det f' = LinearMap.det (congrHerm F E hs m A) := LinearMap.det_conj _ _
  let W : Submodule F (Matrix (Fin m) (Fin m) F) :=
    { carrier := {Y | Y + Y.transpose = 0}
      add_mem' := fun {a b} ha hb => by
        change a + b + (a + b).transpose = 0
        have ha' : a + a.transpose = 0 := ha
        have hb' : b + b.transpose = 0 := hb
        rw [Matrix.transpose_add, add_add_add_comm, ha', hb', add_zero]
      zero_mem' := by
        change (0 : Matrix (Fin m) (Fin m) F) + (0 : Matrix (Fin m) (Fin m) F).transpose = 0
        simp
      smul_mem' := fun c a ha => by
        change c • a + (c • a).transpose = 0
        have ha' : a + a.transpose = 0 := ha
        rw [Matrix.transpose_smul, ← smul_add, ha', smul_zero] }
  have hdet2 : LinearMap.det f' = LinearMap.det c0 := by
    apply det_eq_of_agree W f' c0
    · intro Y hY
      change c0 Y + (c0 Y).transpose = 0
      have hY' : Y + Y.transpose = 0 := hY
      rw [hc0T, hY', Matrix.mul_zero, Matrix.zero_mul]
    · intro Y hY
      have hY' : Y + Y.transpose = 0 := hY
      have hinj0 : Function.Injective Φ0 := fun a b hab => hinj (Subtype.ext hab)
      apply hinj0
      rw [hf']
      have eform : ∀ Z : Matrix (Fin m) (Fin m) F, Z + Z.transpose = 0 →
          Φ0 Z = ε • (algebraMap F E).mapMatrix (Z - Z.transpose) := by
        intro Z hZ
        ext i j
        have hz : Z i j + Z j i = 0 := congrFun (congrFun hZ i) j
        rw [hΦ0, hz, map_zero, zero_add, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
          smul_eq_mul, mul_comm]
        rfl
      have hεX : ∀ X : Matrix (Fin m) (Fin m) E,
          ε • X = ε • (algebraMap F E).mapMatrix (π0.mapMatrix X) := by
        intro X
        ext i j
        simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
        exact hεe _
      have hc0W : c0 Y + (c0 Y).transpose = 0 := by
        rw [hc0T, hY', Matrix.mul_zero, Matrix.zero_mul]
      rw [eform Y hY', eform (c0 Y) hc0W, Matrix.mul_smul, Matrix.smul_mul, hεX]
      congr 2
      rw [map_mul, map_mul, hP0H]
      have e3 : π0.mapMatrix ((algebraMap F E).mapMatrix (Y - Y.transpose)) = Y - Y.transpose := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
        have := hrep0 ((Y - Y.transpose) i j) 0
        simpa using this
      rw [e3, hc0, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc A0.transpose Y.transpose]
    · intro Y
      change (f' Y - c0 Y) + (f' Y - c0 Y).transpose = 0
      have e1 : f' Y + (f' Y).transpose = A0.transpose * (Y + Y.transpose) * A0 := by
        rw [← hP0Φ, hf', map_mul, map_mul, hP0H, hP0Φ]
      rw [Matrix.transpose_sub, sub_add_sub_comm, e1, hc0T, sub_self]
  have hdet3 : LinearMap.det c0 = (A0.det ^ 2) ^ m := by
    rw [LinearMap.det_comp, det_rmulE, det_lmulE, Matrix.det_transpose, ← mul_pow, sq]
  have hnorm : Algebra.norm F A.det = A0.det ^ 2 := by
    have e1 : A0.det = π0 A.det := (RingHom.map_det π0 A).symm
    rw [hdec A.det, hj_norm β ε h0 h1 0 0 (by rw [hε]; simp), ← e1]
    ring
  rw [← hdet1, hdet2, hdet3, hnorm]
end Formalism.HermitianLatticeCounting.P.S4aux
