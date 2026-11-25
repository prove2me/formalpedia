-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.Ffull_hw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:05.249858+00:00
-- url     : https://prove2.me/submissions/fa174fa3-1a44-4d83-b978-3c1612cbee9e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_isWH_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_freeze_gen
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freeze_wh
import Theorems.Thm_P2M_Formalism_GM_DimensionMonotonicity__F_val_6b0203f3e58f
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_inclusion_prodMap_injective
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_vec_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_wv_compat
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_freeze_zero
import Theorems.Thm_Formalism_GM_extendMapsTo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
    (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) :
    (GA p LL (T.pos i + 1 + 1)).IsHW (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) (T.Ffull p (LL.setTies T n) i ρ (n i) f) := by
  classical
  have hK := hK_of_adm LL T hadm i
  set LLK := (LL.setTies T n).takeD (T.pos i + 1) with hLLK
  obtain ⟨⟨hY, hH⟩, hW⟩ := Submodule.mem_inf.mp hf |>.imp_left Submodule.mem_inf.mp
  have hP : f ∈ Pol p r LLK := (Submodule.mem_inf.mp hY).1
  refine ⟨?_, fun a b hab => ?_⟩
  · have hwh := freeze_wh LLK ρ (n i) hS w f hP hW
    rw [← wv_compat LL T hadm i n (n i) (T.pos i + 1 + 1)] at hwh
    have := isWH_rename (K := ℚ_[p]) (wv LL (T.pos i + 1 + 1)) _ (inclusion_prodMap_injective (r := r) hK) hwh
    show weightedHomogeneousComponent _ _ _ = _
    rw [Ffull_eq, weightedHomogeneousComponent_of_mem this, if_pos rfl]
  · show glAct p LL (T.pos i + 1 + 1) a b (T.Ffull p (LL.setTies T n) i ρ (n i) f) = 0
    rw [Ffull_eq, ← glAct_rename (LA := LLK.snoc (n i)) (LB := LL) (ιF N (T.pos i + 1)) (ιF_val hK)
      (fun a => vec_compat LL T hadm i n (n i) a)]
    have h0 : glAct p (LLK.snoc (n i)) (T.pos i + 1 + 1) a b (freeze p LLK ρ (n i) f) = 0 := by
      by_cases hb : b = ρ
      · subst hb
        have := (Formalism.GM.extendMapsTo p (T.pos i + 1) r LLK b (n i) hS f hP).2.1
        exact this a (ne_of_lt hab)
      · have hbr : (b : ℕ) ≤ r - 1 := by have := b.isLt; omega
        have ha : a ≠ ρ := by
          intro h; subst h
          have : (a : ℕ) < b := hab
          omega
        rw [glAct_freeze_gen LLK (n i) ρ a b ha hb]
        have hk : glAct p LLK (T.pos i + 1) a b f = 0 := by
          have := (Submodule.mem_inf.mp hH).2
          rw [Submodule.mem_iInf] at this
          have := this a
          rw [Submodule.mem_iInf] at this
          have := this b
          rw [Submodule.mem_iInf] at this
          exact this ⟨Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩, hab⟩
        rw [hk, freeze_zero]
    rw [h0, map_zero]
end Formalism.GM.DimensionMonotonicity
