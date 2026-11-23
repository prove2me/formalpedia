-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.exists_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:08.791091+00:00
-- url     : https://prove2.me/submissions/877391ad-8101-40fa-afab-8095aa835994

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_star_vecMul_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Matrix
variable {K : Type} [Field K] [Fintype K] [StarRing K]
omit [Fintype K]
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (a : ℕ) (T : Matrix (Fin a) (Fin a) K) (hT : Tᴴ = T) :
    ∃ B : Matrix (Fin a) (Fin (a - T.rank)) K,
      ∀ D : Matrix (Fin (a - T.rank)) (Fin (a - T.rank)) K,
        IsUnit (Matrix.fromBlocks T B Bᴴ D).det := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range T.mulVecLin)
  have hfin : Module.finrank K C = a - T.rank := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hC
    rw [Module.finrank_fin_fun] at h1
    have h2 : Module.finrank K (LinearMap.range T.mulVecLin) = T.rank := rfl
    omega
  let b := Module.finBasisOfFinrankEq K C hfin
  let B : Matrix (Fin a) (Fin (a - T.rank)) K := Matrix.of fun i j => (b j : Fin a → K) i
  have hBv : ∀ w : Fin (a - T.rank) → K, B *ᵥ w = ((∑ j, w j • b j : C) : Fin a → K) := by
    intro w
    ext i
    simp [B, Matrix.mulVec, dotProduct, mul_comm]
  refine ⟨B, fun D => ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ x, (Matrix.fromBlocks T B Bᴴ D) *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.fromBlocks_mulVec] at hx
    set u : Fin a → K := x ∘ Sum.inl with hu
    set w : Fin (a - T.rank) → K := x ∘ Sum.inr with hw
    have h1 : T *ᵥ u + B *ᵥ w = 0 := by
      funext i
      have := congrFun hx (Sum.inl i)
      simpa using this
    have h2 : Bᴴ *ᵥ u + D *ᵥ w = 0 := by
      funext i
      have := congrFun hx (Sum.inr i)
      simpa using this
    have hTR : T *ᵥ u ∈ LinearMap.range T.mulVecLin := ⟨u, by simp⟩
    have hBC : B *ᵥ w ∈ C := by rw [hBv]; exact Submodule.coe_mem _
    have hTC : T *ᵥ u ∈ C := by
      have : T *ᵥ u = -(B *ᵥ w) := eq_neg_of_add_eq_zero_left h1
      rw [this]; exact C.neg_mem hBC
    have hTu : T *ᵥ u = 0 := Submodule.disjoint_def.1 hC.disjoint _ hTR hTC
    have hBw : B *ᵥ w = 0 := by rw [hTu, zero_add] at h1; exact h1
    have hw0 : w = 0 := by
      rw [hBv] at hBw
      have h3 : (∑ j, w j • b j : C) = 0 := Subtype.ext hBw
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent w h3 j
    have hBu : Bᴴ *ᵥ u = 0 := by rw [hw0, Matrix.mulVec_zero, add_zero] at h2; exact h2
    have k1 : star u ᵥ* T = 0 := star_vecMul_zero T u (by rw [hT]; exact hTu)
    have k2 : star u ᵥ* B = 0 := star_vecMul_zero B u hBu
    have hsu : star u = 0 := by
      apply _root_.dotProduct_eq_zero
      intro y
      have hy : y ∈ LinearMap.range T.mulVecLin ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨r, ⟨x', rfl⟩, c', hc', rfl⟩ := Submodule.mem_sup.1 hy
      have hc2 : c' = B *ᵥ (fun j => b.repr ⟨c', hc'⟩ j) := by
        rw [hBv, b.sum_repr]
      rw [dotProduct_add, Matrix.mulVecLin_apply, Matrix.dotProduct_mulVec, k1, hc2,
        Matrix.dotProduct_mulVec, k2]
      simp
    have hu0 : u = 0 := by simpa using congrArg star hsu
    funext i
    rcases i with i | i
    · exact congrFun hu0 i
    · exact congrFun hw0 i
  intro x y hxy
  have := hker (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.1 this
end Formalism.FourierDecayAlt.P.S3x5
