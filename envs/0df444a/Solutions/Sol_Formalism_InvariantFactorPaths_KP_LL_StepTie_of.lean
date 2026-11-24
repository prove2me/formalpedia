-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.StepTie_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:57:00.727721+00:00
-- url     : https://prove2.me/submissions/4ade9578-3371-45dc-9cc8-deb84d8d23da

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_StepTie
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_st_gen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution : PairStep → LatTie → PLLin → CommPL → ParamPL → JoinCondition := by
  intro hPS hLT hLin hC hPar p _ N r _ D a u hB hr hdeg hzz hH hu k hk
  have hc : ∀ v : MvPolynomial (BVar N r D.T.t) ℚ_[p], (p : ℚ_[p]) ^ u • v = ((p : ℤ_[p]) ^ u) • v := by
    intro v
    rw [← algebraMap_smul ℚ_[p] ((p : ℤ_[p]) ^ u) v, map_pow, map_natCast]
  have key : ∀ k₁ k₂ : ℕ, (∀ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp → ∀ x ∈ Lat p D (r := r) j jp,
      (p : ℚ_[p]) ^ u • midGen p D k₁ j jp x ∈ Mid p (r := r) D k₂) →
      ∀ v ∈ Mid p (r := r) D k₁, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k₂ := by
    intro k₁ k₂ hg v hv
    rw [hc]
    have hle : Mid p (r := r) D k₁ ≤ (Mid p (r := r) D k₂).comap
        (((p : ℤ_[p]) ^ u) • LinearMap.id :
          MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℤ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p]) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨j, jp, hOK, x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hc]
      exact hg j jp hOK x hx
    have h2 := Submodule.mem_comap.1 (hle hv)
    rwa [LinearMap.smul_apply, LinearMap.id_apply] at h2
  exact ⟨key (k + 1) k (fun j jp hOK x hx =>
      (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).1),
    key k (k + 1) (fun j jp hOK x hx =>
      (st_gen p hPS hLT hLin hC hPar a u hB hr hdeg hzz hH hu k hk j jp hOK x hx).2)⟩
end Formalism.InvariantFactorPaths.KP.LL
