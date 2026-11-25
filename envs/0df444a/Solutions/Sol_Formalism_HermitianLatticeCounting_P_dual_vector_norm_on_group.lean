-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.dual_vector_norm_on_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:39.928085+00:00
-- url     : https://prove2.me/submissions/2cc0f0eb-a180-4411-a82f-ff196ee4ae34

import Definitions.Def_Formalism_FlagUnipotentLattices_StabiliserComplementDecomposition
import Definitions.Def_Formalism_FlagUnipotentLattices_AlgebraicIdentityHigherDegree
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorAbsoluteOfExplicit
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gauge_le_determinant
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minimal_degree_comparison
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_hL_apply
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_Hh
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_gram_f
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_omega_decomposition
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_s1c2_det_map_star
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_dual_vector_norm_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_swap
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
open Formalism.QuantumDeterminants.WeylGroupFacts
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DualVectorNormOnGroup := by
  intro k r z z' hz hz' hT' g hg
  have hgu : IsUnit g.det := isUnit_of_uh hg
  have hgi : g⁻¹ ∈ UH (Hpk k r) := uh_inv hg
  obtain ⟨hW, horth, co, hco⟩ := omega_decomposition k r z z' hz hz' hT'.ne' g hg
  have hM : (Matrix.of fun a b => hermitianSesquilinearForm (Hpk k r) (g⁻¹ *ᵥ fvec k r z a) (fvec k r z' b)) =
      (Zhat k r z z' g).map star := by
    ext a b
    simp only [Matrix.of_apply, Matrix.map_apply, s1c2_hL_apply, Zhat]
    rw [← ggHerm_unitary _ g hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv g hgu, Matrix.one_mulVec,
      ggHerm_swap _ (s1c2_Hh k r)]
  have key := dual_vector_norm_sq _ (hermitianSesquilinearForm (Hpk k r))
    (fun x y => by simp only [s1c2_hL_apply]; exact ggHerm_swap _ (s1c2_Hh k r) y x) r
    (fun a => g⁻¹ *ᵥ fvec k r z a) (fvec k r z') (Tz k r z) (Tz k r z') hT'.ne'
    (fun a b => by simp only [s1c2_hL_apply]; rw [ggHerm_unitary _ _ hgi, s1c2_gram_f k r z hz])
    (fun a b => by simp only [s1c2_hL_apply]; rw [s1c2_gram_f k r z' hz'])
    (∑ b ∈ univ.erase (Fin.last r), co b • fvec k r z' b) (N3om k r z z' g) (co (Fin.last r))
    (Submodule.sum_mem _ fun b hb => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨b, (Finset.mem_erase.mp hb).1, rfl⟩))
    horth
    (by
      have : (∑ a, (Matrix.of fun a b => hermitianSesquilinearForm (Hpk k r) (g⁻¹ *ᵥ fvec k r z a) (fvec k r z' b)).adjugate
          (Fin.last r) a • (g⁻¹ *ᵥ fvec k r z a)) = formalDeterminantVectorOnGroup k r z z' g := rfl
      rw [this, hco, ← Finset.sum_erase_add _ _ (Finset.mem_univ (Fin.last r))])
  have hfirst : herm (Hpk k r) (N3om k r z z' g) (N3om k r z z' g) =
      ((Gf k r z z' g / Tz k r z' : ℝ) : ℂ) := by
    rw [s1c2_hL_apply, hM] at key
    rw [key, s1c2_det_map_star]
    have h2 : leadingPrincipalMinor ((Zhat k r z z' g).map star) r = star (leadingPrincipalMinor (Zhat k r z z' g) r) := by
      unfold leadingPrincipalMinor
      rw [← s1c2_det_map_star]; rfl
    rw [h2]
    have h3 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := by
      unfold Dmin
      congr 1
    have h4 : Dmin k r z z' g ⟨r, by omega⟩ = leadingPrincipalMinor (Zhat k r z z' g) r := minimal_degree_comparison k r z z' g ⟨r, by omega⟩
    unfold Gf
    rw [h3, h4]
    simp only [Complex.star_def, Complex.normSq_conj]
    push_cast
    ring
  refine ⟨hfirst, fun hT => ?_⟩
  rw [hfirst, Complex.ofReal_re]
  exact div_le_div_of_nonneg_right (gauge_le_determinant k r z z' g hT hT'.le) hT'.le
end Formalism.HermitianLatticeCounting.P
