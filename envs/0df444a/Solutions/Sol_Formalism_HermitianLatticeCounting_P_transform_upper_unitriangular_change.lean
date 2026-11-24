-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.transform_upper_unitriangular_change
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:19.03088+00:00
-- url     : https://prove2.me/submissions/02264655-41fe-4c3d-99c3-b4fa8404b5a1

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hL_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_sum_left
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_herm_sum_right
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_adj_last
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gh_det_upper
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate TensorProduct
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Formalism.QuantumDeterminants
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (H η : Matrix ι ι ℂ) (hη : η ∈ UH H)
    (hηu : IsUnit η.det) {r : ℕ} (y f' : Fin (r + 1) → ι → ℂ) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (hA : IsUpperUnitriangular A) (hA' : IsUpperUnitriangular A') (hf : ∀ b, η *ᵥ f' b = ∑ c, A' c b • f' c) :
    formalDeterminantVector (hermitianSesquilinearForm H) (fun a => η⁻¹ *ᵥ ∑ e, A e a • y e) f' = η⁻¹ *ᵥ formalDeterminantVector (hermitianSesquilinearForm H) y f' := by
  set M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hermitianSesquilinearForm H (y a) (f' b) with hM
  set B : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := A'.map star with hB
  have hBu : IsUpperUnitriangular B :=
    ⟨fun i => by simp [hB, hA'.1], fun i j hij => by simp [hB, hA'.2 i j hij]⟩
  have hM' : (Matrix.of fun a b => hermitianSesquilinearForm H ((fun a => η⁻¹ *ᵥ ∑ e, A e a • y e) a) (f' b)) = Aᵀ * M * B := by
    ext a b
    simp only [Matrix.of_apply, s1c2_hL_apply]
    rw [← ggHerm_unitary H η hη, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv η hηu, Matrix.one_mulVec, hf,
      s1c2_herm_sum_left]
    simp only [s1c2_herm_sum_right, Matrix.mul_apply, Matrix.transpose_apply, hM, hB, Matrix.of_apply,
      Matrix.map_apply, s1c2_hL_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => by ring
  have hAt : (Aᵀ).det = 1 := by rw [Matrix.det_transpose]; exact gh_det_upper hA.1 hA.2
  have hadj : (Aᵀ * M * B).adjugate * Aᵀ = B.adjugate * M.adjugate := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.adjugate_mul, hAt, one_smul, Matrix.mul_one]
  have hrow : ∀ e, ∑ a, (Aᵀ * M * B).adjugate (Fin.last r) a * A e a = M.adjugate (Fin.last r) e := by
    intro e
    have h1 := congrFun (congrFun hadj (Fin.last r)) e
    have h2 : ∑ j, B.adjugate (Fin.last r) j * M.adjugate j e = M.adjugate (Fin.last r) e := by
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [s1c2_adj_last B hBu, if_pos rfl, one_mul]
      · intro d _ hd; rw [s1c2_adj_last B hBu, if_neg hd, zero_mul]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    rw [Matrix.mul_apply, Matrix.mul_apply, h2] at h1
    exact h1
  unfold formalDeterminantVector
  rw [hM', ← hM]
  simp only [← Matrix.mulVec_smul, ← Matrix.mulVec_sum]
  congr 1
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_smul, hrow]
end Formalism.HermitianLatticeCounting.P
