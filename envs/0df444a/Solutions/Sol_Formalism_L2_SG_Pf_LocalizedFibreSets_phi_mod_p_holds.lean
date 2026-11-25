-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LocalizedFibreSets.phi_mod_p_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:20:18.00244+00:00
-- url     : https://prove2.me/submissions/18f6d6b4-f8a9-445c-8d2f-f4510110e681

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CardPhiSucc
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_DetMulEqSumProdMulDetSubmatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsoCountOneInert
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_PhiCountingHolds
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_vF_ne_zero_iff
import Theorems.Thm_Formalism_L2_SG_Pf_LocalizedFibreSets_card_U_diag
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_hermSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_star_inv_eq_neg
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormResidues_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_inv
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_card_ker_piQ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_finite_quot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_card_hermSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_exists_unit_quot
import Theorems.Thm_P2M_Formalism_L2_SG_Pf_LocalizedFibreSets_starO___c01796a1051a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


section
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]
private theorem fromBlocks_cayley_eq_zero_iff {A : Type*} [CommRing A] [StarRing A] {u z : Type*} [Fintype u] [Fintype z]
    [DecidableEq u] [DecidableEq z] (Du : Matrix u u A) (hDu : Duᴴ = Du) (P : Matrix u u A)
    (Q : Matrix u z A) (R : Matrix z u A) (S : Matrix z z A) :
    Matrix.fromBlocks P Q R S + (Matrix.fromBlocks P Q R S)ᴴ +
        (Matrix.fromBlocks P Q R S)ᴴ * Matrix.fromBlocks Du 0 0 0 * Matrix.fromBlocks P Q R S = 0 ↔
      P + Pᴴ + Pᴴ * Du * P = 0 ∧ R = -(Q + Pᴴ * Du * Q)ᴴ ∧ S + Sᴴ + Qᴴ * Du * Q = 0 := by
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_add, Matrix.fromBlocks_add, ← Matrix.fromBlocks_zero, Matrix.fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    refine ⟨h1, ?_, h4⟩
    have hR : Rᴴ = -(Q + Pᴴ * Du * Q) := by
      rw [eq_neg_iff_add_eq_zero, ← h2]; abel
    rw [← Matrix.conjTranspose_conjTranspose R, hR, Matrix.conjTranspose_neg]
  · rintro ⟨h1, rfl, h4⟩
    refine ⟨h1, ?_, ?_, h4⟩
    · rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_conjTranspose]; abel
    · rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDu,
        Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]
      abel
private theorem card_fromBlocks_cayley_eq_mul {A : Type*} [CommRing A] [StarRing A] [Finite A] {u z : Type*} [Fintype u]
    [Fintype z] [DecidableEq u] [DecidableEq z] (Du : Matrix u u A) (hDu : Duᴴ = Du) {θ e : A}
    (he : (θ - star θ) * e = 1) :
    Nat.card {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} =
      Nat.card {P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} * Nat.card (Matrix u z A) *
        Nat.card {S : Matrix z z A // S + Sᴴ = 0} := by
  have hse : star e = -e := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he
  have hte : θ * e + star θ * -e = 1 := by rw [← he]; ring

  have hS0 : ∀ Q : Matrix u z A, (θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ =
      -(Qᴴ * Du * Q) := by
    intro Q
    have hM : (-(Qᴴ * Du * Q))ᴴ = -(Qᴴ * Du * Q) := by
      rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose, hDu, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_smul, hM, star_mul', hse, ← add_smul, hte, one_smul]
  have key : ∀ (Q : Matrix u z A) (S : Matrix z z A),
      (S - (θ * e) • (-(Qᴴ * Du * Q))) + (S - (θ * e) • (-(Qᴴ * Du * Q)))ᴴ =
        S + Sᴴ + Qᴴ * Du * Q := by
    intro Q S
    rw [Matrix.conjTranspose_sub]
    rw [show S - (θ * e) • (-(Qᴴ * Du * Q)) + (Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) =
      S + Sᴴ - ((θ * e) • (-(Qᴴ * Du * Q)) + ((θ * e) • (-(Qᴴ * Du * Q)))ᴴ) by abel, hS0 Q,
      sub_neg_eq_add]
  let eqv : {Y : Matrix (u ⊕ z) (u ⊕ z) A // Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} ≃
      ({P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} × Matrix u z A) ×
        {S : Matrix z z A // S + Sᴴ = 0} :=
    { toFun := fun Y =>
        have h := (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)
        ((⟨Y.1.toBlocks₁₁, h.1⟩, Y.1.toBlocks₁₂),
          ⟨Y.1.toBlocks₂₂ - (θ * e) • (-(Y.1.toBlocks₁₂ᴴ * Du * Y.1.toBlocks₁₂)),
            by rw [key]; exact h.2.2⟩)
      invFun := fun x =>
        ⟨Matrix.fromBlocks x.1.1.1 x.1.2 (-(x.1.2 + x.1.1.1ᴴ * Du * x.1.2)ᴴ)
            (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2))),
          (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mpr ⟨x.1.1.2, rfl, by
            have h := key x.1.2 (x.2.1 + (θ * e) • (-(x.1.2ᴴ * Du * x.1.2)))
            rw [add_sub_cancel_right] at h
            rw [← h]; exact x.2.2⟩⟩
      left_inv := fun Y => by
        have h := (fromBlocks_cayley_eq_zero_iff Du hDu _ _ _ _).mp (by rw [Matrix.fromBlocks_toBlocks]; exact Y.2)
        apply Subtype.ext
        simp only [sub_add_cancel]
        rw [← h.2.1, Matrix.fromBlocks_toBlocks]
      right_inv := fun x => by
        ext
        · simp
        · simp
        · simp }
  rw [Nat.card_congr eqv, Nat.card_prod, Nat.card_prod]
private theorem card_skewHermitian_eq_card_hermitian {A : Type*} [CommRing A] [StarRing A] {z : Type*} {θ e : A}
    (he : (θ - star θ) * e = 1) :
    Nat.card {S : Matrix z z A // S + Sᴴ = 0} = Nat.card {M : Matrix z z A // Mᴴ = M} := by
  have hse : star e = -e := Formalism.HermitianLattices.Ext.L3.HermitianSublattices.star_inv_eq_neg he
  have hst : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star]; ring
  have he' : e * (θ - star θ) = 1 := by rw [mul_comm]; exact he
  exact Nat.card_congr
    { toFun := fun S => ⟨(θ - star θ) • S.1, by
        have hS : S.1ᴴ = -S.1 := eq_neg_of_add_eq_zero_right S.2
        rw [Matrix.conjTranspose_smul, hst, hS, neg_smul, smul_neg, neg_neg]⟩
      invFun := fun M => ⟨e • M.1, by
        rw [Matrix.conjTranspose_smul, hse, M.2, neg_smul, add_neg_cancel]⟩
      left_inv := fun S => Subtype.ext (by simp only [smul_smul, he', one_smul])
      right_inv := fun M => Subtype.ext (by simp only [smul_smul, he, one_smul]) }
private theorem exists_UJ_umat_eq_of_inUJ {A : Type*} [CommRing A] [StarRing A] {u : Type*} [Fintype u] [DecidableEq u]
    (Du Dv : Matrix u u A) (hDu : Duᴴ = Du) (huv : Du * Dv = 1) (hvu : Dv * Du = 1) :
    Nat.card {P : Matrix u u A // P + Pᴴ + Pᴴ * Du * P = 0} =
      Nat.card {γ : Matrix u u A // γᴴ * Du * γ = Du} := by
  have iden : ∀ P : Matrix u u A, (1 + P * Du)ᴴ * Du * (1 + P * Du) =
      Du + Du * (P + Pᴴ + Pᴴ * Du * P) * Du := by
    intro P
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul, hDu]
    noncomm_ring
  have cancel : ∀ X : Matrix u u A, Dv * (Du * X * Du) * Dv = X := by
    intro X
    rw [← Matrix.mul_assoc Dv (Du * X) Du, ← Matrix.mul_assoc Dv Du X, hvu, Matrix.one_mul,
      Matrix.mul_assoc X Du Dv, huv, Matrix.mul_one]
  exact Nat.card_congr
    { toFun := fun P => ⟨1 + P.1 * Du, by rw [iden, P.2, Matrix.mul_zero, Matrix.zero_mul, add_zero]⟩
      invFun := fun γ => ⟨(γ.1 - 1) * Dv, by
        have h1 : 1 + (γ.1 - 1) * Dv * Du = γ.1 := by
          rw [Matrix.mul_assoc, hvu, Matrix.mul_one]; abel
        have h2 := iden ((γ.1 - 1) * Dv)
        rw [h1, γ.2] at h2
        have h3 : Du * ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv)) * Du = 0 := by
          have := congrArg (fun X => X - Du) h2
          simp only [sub_self, add_sub_cancel_left] at this
          exact this.symm
        have h4 := cancel ((γ.1 - 1) * Dv + ((γ.1 - 1) * Dv)ᴴ + ((γ.1 - 1) * Dv)ᴴ * Du * ((γ.1 - 1) * Dv))
        rw [h3, Matrix.mul_zero, Matrix.zero_mul] at h4
        exact h4.symm⟩
      left_inv := fun P => Subtype.ext (by
        simp only [add_sub_cancel_left, Matrix.mul_assoc, huv, Matrix.mul_one])
      right_inv := fun γ => Subtype.ext (by
        simp only
        rw [Matrix.mul_assoc, hvu, Matrix.mul_one]; abel) }
end Formalism.L2.SG.Pf.LocalizedFibreSets
end
end

set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LocalizedFibreSets
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HermitianSublattices Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)]
namespace Formalism.L2.SG.Pf.LocalizedFibreSets
theorem _root_.solution : PhiModP := by
  intro K F _ _ _ _ _ _ _ hK 𝔭 h𝔭 m a ha
  classical
  haveI := finite_quot (K := K) h𝔭 1
  haveI : Subsingleton (𝓞 K ⧸ extP K 𝔭 ^ 0) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  obtain ⟨θ, e, he⟩ := exists_unit_quot hK h𝔭 1

  have hzero : ∀ i, a i ∈ 𝔭 →
      Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i)) = 0 := by
    intro i hi
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact Ideal.mem_map_of_mem _ hi
  have hinv : ∀ i : {i : Fin m // a i ∉ 𝔭}, ∃ v : (𝓞 K ⧸ extP K 𝔭 ^ 1),
      Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1)) * v = 1 := by
    intro i
    obtain ⟨y, j, hj, hy⟩ := h𝔭.exists_inv i.2
    refine ⟨Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) y), ?_⟩
    have h1 := congrArg (fun x => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) x)) hy
    simp only [map_add, map_mul, map_one] at h1
    have h2 : Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) j) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.mem_map_of_mem _ hj
    rw [h2, add_zero] at h1
    exact (mul_comm _ _).trans h1
  choose dv hdv using hinv
  obtain ⟨Du, hDu_def⟩ : ∃ Du : Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1),
      Du = Matrix.diagonal (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (algebraMap (𝓞 F) (𝓞 K) (a i.1))) :=
    ⟨_, rfl⟩
  have hDuh : Duᴴ = Du := by
    rw [hDu_def, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    rw [Pi.star_apply, star_mk, starO_ι]
  have huv : Du * Matrix.diagonal dv = 1 := by
    rw [hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdv i
  have hvu : Matrix.diagonal dv * Du = 1 := by
    rw [hDu_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hdv i

  let e' : Fin m ≃ {i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭} := (Equiv.sumCompl (fun i => a i ∉ 𝔭)).symm
  have hHD : Matrix.fromBlocks Du 0 0 0 = Matrix.reindex e' e' (diagQ K 𝔭 1 a) := by
    rw [hDu_def]
    ext (i | i) (j | j)
    · simp [e', diagQ, Matrix.diagonal_apply, Subtype.ext_iff]
    · have hij : i.1 ≠ j.1 := fun h => j.2 (h ▸ i.2)
      simp [e', diagQ, Matrix.diagonal_apply, hij]
    · have hij : i.1 ≠ j.1 := fun h => i.2 (h ▸ j.2)
      simp [e', diagQ, Matrix.diagonal_apply, hij]
    · have hi : a i.1 ∈ 𝔭 := not_not.mp i.2
      simp [e', diagQ, Matrix.diagonal_apply, hzero _ hi]
      first
      | exact fun _ => (hzero _ hi).symm
      | (intro _; rw [IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) (𝓞 K ⧸ extP K 𝔭 ^ 1)]; exact (hzero _ hi).symm)
  have h6 : Nat.card {Y : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ 1) // phiQ K 𝔭 1 a Y = 0} =
      Nat.card {Y : Matrix ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) ({i : Fin m // a i ∉ 𝔭} ⊕ {i : Fin m // ¬ a i ∉ 𝔭}) (𝓞 K ⧸ extP K 𝔭 ^ 1) //
        Y + Yᴴ + Yᴴ * Matrix.fromBlocks Du 0 0 0 * Y = 0} := by
    refine Nat.card_congr (Equiv.subtypeEquiv (Matrix.reindex e' e') fun Y => ?_)
    have hre : Matrix.reindex e' e' Y + (Matrix.reindex e' e' Y)ᴴ +
        (Matrix.reindex e' e' Y)ᴴ * Matrix.reindex e' e' (diagQ K 𝔭 1 a) * Matrix.reindex e' e' Y =
        Matrix.reindex e' e' (phiQ K 𝔭 1 a Y) := by
      unfold phiQ
      simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
      rfl
    rw [hHD, hre]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      apply (Matrix.reindex e' e').injective
      rw [h]
      simp

  have hU := card_U_diag hK h𝔭 (ι := {i : Fin m // a i ∉ 𝔭}) (fun i => a i.1) (fun i => i.2)
  rw [← hDu_def] at hU
  have hR1 : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ 1) = Ideal.absNorm 𝔭 ^ 2 := by
    have h := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.card_ker_piQ hK (Fact.out) h𝔭 0
    have htop : RingHom.ker (piQ K 𝔭 0) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [RingHom.mem_ker]
      exact Subsingleton.elim _ _
    rw [htop] at h
    rw [← h]
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun x => Submodule.mem_top))).symm
  have hMat : Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) =
      ((Ideal.absNorm 𝔭 ^ 2) ^ Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ Fintype.card {i : Fin m // a i ∉ 𝔭} := by
    rw [show Nat.card (Matrix {i : Fin m // a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1)) = Nat.card ({i : Fin m // a i ∉ 𝔭} → {i : Fin m // ¬ a i ∉ 𝔭} → (𝓞 K ⧸ extP K 𝔭 ^ 1)) from rfl,
      Nat.card_fun, Nat.card_fun, hR1, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hherm : Nat.card {M : Matrix {i : Fin m // ¬ a i ∉ 𝔭} {i : Fin m // ¬ a i ∉ 𝔭} (𝓞 K ⧸ extP K 𝔭 ^ 1) // Mᴴ = M} =
      Ideal.absNorm 𝔭 ^ (Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} * Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) := by
    rw [← Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.card_hermSub (r := {i : Fin m // ¬ a i ∉ 𝔭}) hK h𝔭 0]
    exact Nat.card_congr
      { toFun := fun M => ⟨M.1, Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mpr ⟨M.2, fun _ _ => by
            rw [RingHom.mem_ker]; exact Subsingleton.elim _ _⟩⟩
        invFun := fun S => ⟨S.1, (Formalism.HermitianLattices.Ext.L3.HermitianSublattices.mem_hermSub.mp S.2).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hc : cJof 𝔭 a = Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} := by
    unfold cJof
    rw [Fintype.card_subtype]
    exact congrArg Finset.card (Finset.filter_congr (fun i _ => by
      rw [not_not]; exact vF_ne_zero_iff h𝔭 (ha i)))
  have hm : Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = m := by
    rw [← Fintype.card_sum, Fintype.card_congr e'.symm, Fintype.card_fin]
  rw [h6, card_fromBlocks_cayley_eq_mul Du hDuh he, exists_UJ_umat_eq_of_inUJ Du (Matrix.diagonal dv) hDuh huv hvu, card_skewHermitian_eq_card_hermitian he, hherm, hMat]
  push_cast
  rw [hU, hc, show m - Fintype.card {i : Fin m // ¬ a i ∉ 𝔭} = Fintype.card {i : Fin m // a i ∉ 𝔭} by omega,
    show m ^ 2 = (Fintype.card {i : Fin m // a i ∉ 𝔭} + Fintype.card {i : Fin m // ¬ a i ∉ 𝔭}) ^ 2 by rw [hm]]
  ring
end Formalism.L2.SG.Pf.LocalizedFibreSets
