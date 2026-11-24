-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x9.countId
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:23.025115+00:00
-- url     : https://prove2.me/submissions/a161a5c1-e27b-4d97-970d-b89242e5b01a

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lift_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_desc_abs
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_equiv_of_birel
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_isD_mulVec_msk
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_colSpan_le_latZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_colSpan
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_mem_colSpan_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_Lam_latZ_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_exists_latZ_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_inTT_iff_base
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_Lam_coord
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_msk_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_msk_Lam
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_msk_D
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_nrm_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_nrm_unique
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_det_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_cnt_bad_iff
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamLin_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_lamTil_eLast
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_mk_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ} (k : ℕ)
namespace Formalism.FourierDecayAlt.P.A5x9
theorem _root_.solution (ψ : AddChar K ℂ) (hsd : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R)
    (hk : k + 2 ≤ n) (Z₀ Z₀' : Matrix (Fin n) (Fin n) K) (hd : IsUnit Z₀.det)
    (hd' : IsUnit Z₀'.det)
    (he : ∀ a b : Fin n, k < a.val → b.val + 1 = n → Z₀⁻¹ a b = 0)
    (he' : ∀ a b : Fin n, k < a.val → b.val + 1 = n → Z₀'⁻¹ a b = 0)
    (p p' : Matrix (Fin n) (Fin n) K) (hp : IsPP R k p) (hp' : IsPP R k p')
    (hZ : IsInt R (Z₀ * p)) (hZ' : IsInt R (Z₀' * p')) (hfin : Finite (coker R (Z₀ * p))) :
    Nonempty ({φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p') //
        φ ∈ isoZZ R (Z₀ * p) (Z₀' * p') ∧ InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ∧
          ¬ InTT R k (Z₀ * p) (Z₀' * p') φ} ≃
      {Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀' // GB R k Z₀ Z₀' Ψ ∧
        Rel R Ψ (latZ R (Z₀ * p)) (latZ R (Z₀' * p'))}) := by
  have hdZ := cnt_det_mul R k Z₀ p hd hp
  have hdZ' := cnt_det_mul R k Z₀' p' hd' hp'
  have hn : 0 < n := by omega
  have hLe : abelian₂ R k Z₀ (eLast R) = 0 := by
    ext j
    rw [cnt_Lam_coord]
    split_ifs with hj
    · rw [A5x2.lamTil_eLast R Z₀ j ⟨n - 1, by omega⟩ (by simp only; omega)]
      exact he j _ hj (by simp only; omega)
    · rfl
  have hLe' : abelian₂ R k Z₀' (eLast R) = 0 := by
    ext j
    rw [cnt_Lam_coord]
    split_ifs with hj
    · rw [A5x2.lamTil_eLast R Z₀' j ⟨n - 1, by omega⟩ (by simp only; omega)]
      exact he' j _ hj (by simp only; omega)
    · rfl
  apply equiv_of_birel
    (fun φ : coker R (Z₀ * p) ≃ₗ[R] coker R (Z₀' * p') =>
      φ ∈ isoZZ R (Z₀ * p) (Z₀' * p') ∧ InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ ∧
          ¬ InTT R k (Z₀ * p) (Z₀' * p') φ)
    (fun Ψ : MM R k Z₀ ≃ₗ[R] MM R k Z₀' => GB R k Z₀ Z₀' Ψ ∧
        Rel R Ψ (latZ R (Z₀ * p)) (latZ R (Z₀' * p')))
    (fun Ψ φ => ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
      φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y)
  ·
    rintro φ ⟨hiso, hT, hnT⟩
    obtain ⟨D₁, hD₁, hD₁r⟩ := (inTT_iff_base R k Z₀ Z₀' p p' hp hp' φ).1 hT
    obtain ⟨D, hN, hDD⟩ := cnt_nrm_exists R k Z₀ ⟨D₁, hD₁⟩
    have hDr : ∀ v v' : Fin n → R, φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' →
        ∀ j, (abelian₂ R k Z₀' v' - D.1 *ᵥ abelian₂ R k Z₀ v) j ∈ R := by
      intro v v' h j
      have h1 := hD₁r v v' h j
      have h2 := hDD v j
      have e : (abelian₂ R k Z₀' v' - D.1 *ᵥ abelian₂ R k Z₀ v) j =
          (abelian₂ R k Z₀' v' - D₁ *ᵥ abelian₂ R k Z₀ v) j - ((D.1 - D₁) *ᵥ abelian₂ R k Z₀ v) j := by
        rw [Matrix.sub_mulVec]; simp only [Pi.sub_apply]; ring
      rw [e]; exact R.sub_mem h1 h2
    have hDdet : IsUnit D.1.det := by rw [isUpUni_det K D.2.1]; exact isUnit_one
    have hDi := isD_inv R k D.2
    have h1 : ∀ x ∈ latZ R (Z₀ * p),
        (D.1.mulVecLin.restrictScalars R) (abelian₂ R k Z₀ x) = 0 → x ∈ colSpan R k Z₀ := by
      intro x hx h0
      have h0' : D.1 *ᵥ abelian₂ R k Z₀ x = 0 := h0
      have h00 : abelian₂ R k Z₀ x = 0 := by
        have := congrArg (fun y => D.1⁻¹ *ᵥ y) h0'
        simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hDdet] using this
      exact mem_colSpan_of R k Z₀ p hd hp x hx h00
    have h2 : ∀ x : Fin n → R, ∃ y : Fin n → R,
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
          abelian₂ R k Z₀' y = (D.1.mulVecLin.restrictScalars R) (abelian₂ R k Z₀ x) := by
      intro x
      obtain ⟨y0, hy0⟩ := Submodule.Quotient.mk_surjective _ (φ (Submodule.Quotient.mk x))
      have hr := hDr x y0 hy0.symm
      have hm : msk k (abelian₂ R k Z₀' y0 - D.1 *ᵥ abelian₂ R k Z₀ x) =
          abelian₂ R k Z₀' y0 - D.1 *ᵥ abelian₂ R k Z₀ x := by
        rw [cnt_msk_sub, cnt_msk_Lam, cnt_msk_D R k D.2]
      obtain ⟨z, hz, hzL⟩ := exists_latZ_Lam R k Z₀' p' hd' hp' hZ' _ hr hm
      refine ⟨y0 - z, ?_, ?_⟩
      · rw [Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hz, sub_zero, hy0]
      · rw [map_sub, hzL, sub_sub_cancel]; rfl
    have h3 : ∀ y : Fin n → R, ∃ x : Fin n → R,
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧
          abelian₂ R k Z₀' y = (D.1.mulVecLin.restrictScalars R) (abelian₂ R k Z₀ x) := by
      intro y
      obtain ⟨x0, hx0⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (Submodule.Quotient.mk y))
      have hx0' : φ (Submodule.Quotient.mk x0) = Submodule.Quotient.mk y := by
        rw [hx0, φ.apply_symm_apply]
      have hr := hDr x0 y hx0'
      have hm : msk k (abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0) =
          abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0 := by
        rw [cnt_msk_sub, cnt_msk_Lam, cnt_msk_D R k D.2]
      have hr1 := isD_mulVec_int R k hDi hr
      have hm1 : msk k (D.1⁻¹ *ᵥ (abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0)) =
          D.1⁻¹ *ᵥ (abelian₂ R k Z₀' y - D.1 *ᵥ abelian₂ R k Z₀ x0) := by
        rw [← isD_mulVec_msk R k hDi, hm]
      obtain ⟨z, hz, hzL⟩ := exists_latZ_Lam R k Z₀ p hd hp hZ _ hr1 hm1
      refine ⟨x0 + z, ?_, ?_⟩
      · rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).2 hz, add_zero, hx0']
      · show _ = D.1 *ᵥ abelian₂ R k Z₀ (x0 + z)
        rw [map_add, hzL, Matrix.mulVec_add, Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _ hDdet, Matrix.one_mulVec, add_sub_cancel]
    obtain ⟨Ψ, hΨ⟩ := lift_abs (latZ R (Z₀ * p)) (colSpan R k Z₀) (latZ R (Z₀' * p'))
      (colSpan R k Z₀') (abelian₂ R k Z₀) (abelian₂ R k Z₀') (D.1.mulVecLin.restrictScalars R) φ
      (colSpan_le_latZ R k Z₀ p hp) (colSpan_le_latZ R k Z₀' p' hp') (Lam_colSpan R k Z₀ hd)
      (Lam_colSpan R k Z₀' hd') h1 (mem_colSpan_of R k Z₀' p' hd' hp') h2 h3
    have hC : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := fun x y h => ((hΨ x y).1 h).1
    have hL : ∀ x y : Fin n → R, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y →
        abelian₂ R k Z₀' y = D.1 *ᵥ abelian₂ R k Z₀ x := fun x y h => ((hΨ x y).1 h).2
    refine ⟨Ψ, ⟨⟨?_, ⟨D, hN, hL⟩, ?_⟩, ?_⟩, hC⟩
    · exact (hΨ _ _).2 ⟨hiso.1, by rw [hLe', hLe, map_zero]⟩
    · exact (cnt_bad_iff R k ψ hsd hk Z₀ Z₀' hd hd' p p' hp hp' hZ hfin φ Ψ hC hT D.1 hL).1 hnT
    · intro x y h
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.Quotient.mk_eq_zero (latZ R (Z₀' * p')),
        ← hC x y h]
      exact (LinearEquiv.map_eq_zero_iff φ).symm
  ·
    rintro Ψ ⟨hG, hR⟩
    obtain ⟨φ, hφ⟩ := desc_abs (latZ R (Z₀ * p)) (colSpan R k Z₀) (latZ R (Z₀' * p'))
      (colSpan R k Z₀') Ψ (colSpan_le_latZ R k Z₀ p hp) (colSpan_le_latZ R k Z₀' p' hp') hR
    obtain ⟨D, hN, hL⟩ := hG.lift
    have hT : InTT R (k + 1) (Z₀ * p) (Z₀' * p') φ := by
      refine (inTT_iff_base R k Z₀ Z₀' p p' hp hp' φ).2 ⟨D.1, D.2, fun v v' h j => ?_⟩
      obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk v))
      have h1 := hφ v y hy.symm
      rw [h] at h1
      have h2 : v' - y ∈ latZ R (Z₀' * p') := (Submodule.Quotient.eq _).1 h1
      have h3 := Lam_latZ_int R k Z₀' p' hd' hp' _ h2 j
      rw [map_sub, hL v y hy.symm] at h3
      exact h3
    refine ⟨φ, ⟨⟨hφ _ _ hG.e, ?_⟩, hT,
      (cnt_bad_iff R k ψ hsd hk Z₀ Z₀' hd hd' p p' hp hp' hZ hfin φ Ψ hφ hT D.1 hL).2 hG.bad⟩, hφ⟩
    intro v v' h
    rw [A5x2.lamLin_eq R _ hn, A5x2.lamLin_eq R _ hn]
    obtain ⟨a, ha⟩ := hT (n - 1) (by omega) (by omega)
    rw [ha v v' h]
    have hE : Finset.Ioo (n - 1) n = ∅ := by
      ext l; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega
    rw [hE, Finset.sum_empty, add_zero]
  · intro Ψ φ₁ φ₂ h₁ h₂
    apply LinearEquiv.ext
    intro c
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (Ψ (Submodule.Quotient.mk v))
    rw [h₁ v y hy.symm, h₂ v y hy.symm]
  · rintro φ Ψ₁ Ψ₂ ⟨hG₁, -⟩ ⟨hG₂, -⟩ h₁ h₂
    obtain ⟨D₁, hN₁, hL₁⟩ := hG₁.lift
    obtain ⟨D₂, hN₂, hL₂⟩ := hG₂.lift
    have key : ∀ x y₁ y₂ : Fin n → R, Ψ₁ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y₁ →
        Ψ₂ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y₂ →
        y₁ - y₂ ∈ latZ R (Z₀' * p') := by
      intro x y₁ y₂ e₁ e₂
      rw [← Submodule.Quotient.eq, ← h₁ x y₁ e₁, ← h₂ x y₂ e₂]
    have hDeq : D₁ = D₂ := by
      refine cnt_nrm_unique R k Z₀ D₁ D₂ hN₁ hN₂ (fun x j => ?_)
      obtain ⟨y₁, e₁⟩ := Submodule.Quotient.mk_surjective _ (Ψ₁ (Submodule.Quotient.mk x))
      obtain ⟨y₂, e₂⟩ := Submodule.Quotient.mk_surjective _ (Ψ₂ (Submodule.Quotient.mk x))
      have h3 := Lam_latZ_int R k Z₀' p' hd' hp' _ (key x y₁ y₂ e₁.symm e₂.symm) j
      rw [map_sub, hL₁ x y₁ e₁.symm, hL₂ x y₂ e₂.symm, ← Matrix.sub_mulVec] at h3
      exact h3
    apply LinearEquiv.ext
    intro c
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨y₁, e₁⟩ := Submodule.Quotient.mk_surjective _ (Ψ₁ (Submodule.Quotient.mk x))
    obtain ⟨y₂, e₂⟩ := Submodule.Quotient.mk_surjective _ (Ψ₂ (Submodule.Quotient.mk x))
    rw [← e₁, ← e₂, Submodule.Quotient.eq]
    apply mem_colSpan_of R k Z₀' p' hd' hp' _ (key x y₁ y₂ e₁.symm e₂.symm)
    rw [map_sub, hL₁ x y₁ e₁.symm, hL₂ x y₂ e₂.symm, hDeq, sub_self]
end Formalism.FourierDecayAlt.P.A5x9
