-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x6.d_wittHerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:36.175975+00:00
-- url     : https://prove2.me/submissions/aa4f9906-4446-4896-b905-7e0afea87f02

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictOrthogonalComplementNondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_witt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_exists_sigma
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_gram_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_fconj_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_herm
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_nondeg
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x6_d_li_of_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x6
open Module
variable {K : Type} [Field K] {σ : K →+* K}
open Matrix Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x6
theorem _root_.solution : WittHerm := by
  intro K _ _ q n a J X Y hq hJh hJu hX hY hXY
  obtain ⟨σ, hσ, hi⟩ := exists_sigma K q hq
  obtain ⟨g, hg, hgx⟩ := witt hi (hJ σ J) (d_herm hσ hi J hJh) (d_nondeg J hJu)
    (fun (i : Fin a) (k : Fin n) => X k i) (fun (i : Fin a) (k : Fin n) => Y k i)
    (d_li_of_rank X hX) (d_li_of_rank Y hY) (by
      intro i j
      rw [← d_gram_entry hσ, ← d_gram_entry hσ, hXY])
  have hcol : ∀ (α : Type) [Fintype α] (Z : Matrix (Fin n) α K) (i : α),
      (fun k => (LinearMap.toMatrix' g.toLinearMap * Z) k i) = g (fun k => Z k i) := by
    intro α _ Z i
    have : g (fun k => Z k i) = LinearMap.toMatrix' g.toLinearMap *ᵥ (fun k => Z k i) := by
      rw [LinearMap.toMatrix'_mulVec]; rfl
    rw [this]
    ext k
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  refine ⟨LinearMap.toMatrix' g.toLinearMap, ?_, ?_⟩
  · ext i j
    have h1 := d_gram_entry hσ J (LinearMap.toMatrix' g.toLinearMap * 1)
      (LinearMap.toMatrix' g.toLinearMap * 1) i j
    rw [hcol, hcol, hg, ← d_gram_entry hσ, d_fconj_one hσ] at h1
    simpa using h1
  · ext k i
    have := congrFun (hcol _ X i) k
    rw [hgx] at this
    exact this
end Formalism.FourierDecayAlt.P.S3x6
