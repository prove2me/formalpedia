-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.ycond_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:57:15.831621+00:00
-- url     : https://prove2.me/submissions/0bd11459-7c6f-4447-887d-608bfbee696f

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_weight_mapDomain
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_compat
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
omit hS
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (J : ℕ) (M : WithTop ℤ) (F : MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p])
    (h : rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) F ∈ YCond p LL J M) :
    F ∈ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
  classical
  have hK := hK_of_adm LL T hadm i
  have hι := inclusion_prodMap_injective (N := N) (r := r) hK
  set S : Submodule ℚ_[p] (MvPolynomial (Fin (T.pos i + 1 + 1) × Fin r) ℚ_[p]) := (YCond p LL J M).comap
    (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2))).toLinearMap with hSd
  have hle : S ≤ YCond p (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) J M := by
    refine le_sSup ⟨?_, ?_⟩
    · intro G hG
      rw [mem_restrictSupport_iff]
      intro m hm
      have h1 := Formalism.CountingSumsFrames.ycond_le_supp LL J M (Submodule.mem_comap.mp hG)
      rw [mem_restrictSupport_iff] at h1
      have h2 : Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) m ∈
          (rename (fun x : Fin (T.pos i + 1 + 1) × Fin r => (ιF N (T.pos i + 1) x.1, x.2)) G).support := by
        rw [support_rename_of_injective hι]; exact Finset.mem_image_of_mem _ hm
      have h3 : ((wt LL J 0 (Finsupp.mapDomain (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
          (ιF N (T.pos i + 1) x.1, x.2)) m) : ℤ) : WithTop ℤ) ≤ M := h1 (Finset.mem_coe.mpr h2)
      rw [← weight_wv, weight_mapDomain, wv_compat LL T hadm i n (n i), weight_wv] at h3
      exact h3
    · intro c d G hG
      rw [hSd, Submodule.mem_comap, AlgHom.toLinearMap_apply,
        glAct_rename (((LL.setTies T n).takeD (T.pos i + 1)).snoc (n i)) LL (ιF N (T.pos i + 1)) (ιF_val hK)
          (fun a => vec_compat LL T hadm i n (n i) a) J c d G]
      exact Formalism.CountingSumsFrames.ycond_glStable LL J M c d _ (Submodule.mem_comap.mp hG)
  exact hle (Submodule.mem_comap.mpr h)
end Formalism.CountingSumsFrames.TO
