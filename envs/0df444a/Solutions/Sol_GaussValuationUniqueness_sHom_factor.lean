-- Prove2me | solution 1 for GaussValuationUniqueness.sHom_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:29.103413+00:00
-- url     : https://prove2.me/submissions/aaf13449-b506-4685-8aad-84f48dbf6e85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ImgRSuccAbove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_SHomFactor
import Theorems.Thm_GaussValuationUniqueness_sub_apply
import Theorems.Thm_GaussValuationUniqueness_sac_same
import Theorems.Thm_GaussValuationUniqueness_sac_succAbove


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] {D N : ℕ}
  (v : AddValuation Ω (WithTop ℤ))
namespace GaussValuationUniqueness
theorem _root_.solution (hv : IsTrivOn K v) (jc j0 : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → Ω) (ha : ∀ j, a j ∈ vRing v) (ha0 : a j0 = 1)
    (hrel : ∀ i : Fin (D + 1), i ≠ 0 →
      ∑ j, sImg jc x (i, j) * algebraMap Ω (OmS Ω D N) (a j) = 0) (f : MvPolynomial (TVar D N) K) :
    sHom (K := K) jc x f = MvPolynomial.eval₂ ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
      (eS jc j0 x) (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩) f) := by
  have key : ((sHom (K := K) jc x : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N) :
      MvPolynomial (TVar D N) K →+* OmS Ω D N) =
      (MvPolynomial.eval₂Hom ((algebraMap Ω (OmS Ω D N)).comp (vRing v).subtype)
        (eS jc j0 x)).comp (psiT v hv j0 (fun k => ⟨a (j0.succAbove k), ha _⟩)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom, sHom,
        MvPolynomial.aeval_C, psiT, MvPolynomial.eval₂Hom_C, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_C]
      rw [IsScalarTower.algebraMap_apply K (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
        MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
      rfl
    · rintro ⟨i, j⟩
      rcases Fin.eq_self_or_eq_succAbove j0 j with rfl | ⟨k, rfl⟩
      · by_cases hi : i = 0
        · subst hi
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same]
        · have h := hrel i hi
          rw [Fin.sum_univ_succAbove _ j, ha0, map_one, mul_one] at h
          simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_same, hi, GaussValuationUniqueness.sub_apply]
          linear_combination h
      · simp [sHom, psiT, imgR, eS, GaussValuationUniqueness.sac_succAbove]
  exact RingHom.congr_fun key f
end GaussValuationUniqueness
