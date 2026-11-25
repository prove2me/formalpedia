-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ptFB_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:01.950109+00:00
-- url     : https://prove2.me/submissions/909fce58-5212-4e41-9c76-eca6fe4a7146

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartTop
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePPTFBSt
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_chart_log_constantCoeff
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_axis0
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_FBChart_raw_lin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_add_mem
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_const_mem_type_set_of_nonneg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RawChart_val_nonneg_leading_coeff_of_mem_tySet
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_neg
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_addCvFB_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution (hEx : PTExFBSt) (hAvg : PTAvgFBSt) (hG : GermIAllSt) (hStab : HStabFBSt) : PTFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g a w hw hty
  obtain ⟨x, hx, hx0⟩ := hEx C V O dd Y d I p g a w hw hty

  have hint : ∀ n, V.Ge 0 (x 0 n) :=
    (Y.raw p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.raw_lin p) (Y.raw_axis0 p) (p.u_sat g) (hStab C V O dd Y d I p g) x hx 0
      (fun i hi => absurd hi (Nat.not_lt_zero i))
  set ζ : JJ I g → C := fun q => -x 0 (Sum.inr q) with hζ
  have hζi : ∀ q, V.Ge 0 (ζ q) := fun q => VF.Ge.neg (hint _)
  have h3 := (Y.raw p).const_mem_type_set_of_nonneg (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g ζ hζi
  have hx1 := (Y.raw p).add_mem V g (addCvFB_of hG C V O dd Y d I p) p.u_int x _ hx h3
  have e0 : (x + const0 (Sum.elim 0 ζ) : ℕ → I g ⊕ JJ I g → C) 0 = Sum.elim w 0 := by
    funext n
    cases n with
    | inl c => simp [const0, hx0 c]
    | inr q => simp [const0, hζ]
  obtain ⟨x', hx', hx'0, hpure⟩ := hAvg C V O dd Y d I p g a _ hx1 (by
    intro n hn
    rw [e0]
    cases n with
    | inl c => exact hty c hn
    | inr q => rfl)
  exact ⟨x', hx', hx'0.trans e0, hpure⟩
end Formalism.L2.FormalSeriesBounds
