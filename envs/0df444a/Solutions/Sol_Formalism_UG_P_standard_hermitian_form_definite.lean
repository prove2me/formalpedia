-- Prove2me | solution 1 for Formalism.UG.P.standard_hermitian_form_definite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:42:27.677822+00:00
-- url     : https://prove2.me/submissions/8fe81c11-0e40-4c13-be4b-5c87357d0329

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_ext
import Theorems.Thm_Formalism_UG_P_stdform_sig_one
import Theorems.Thm_Formalism_UG_P_stdform_sig_neg_one
import Theorems.Thm_Formalism_UG_P_definite_form_signature

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.StdFormDef := by
  intro F E _ _ _ _ _ n _ _ σ hσ hfix hF
  have hH1 : IsHerm (σ : E →+* E) (1 : Matrix n n E) := cT_one _
  have hHm : IsHerm (σ : E →+* E) (-1 : Matrix n n E) := by
    unfold IsHerm cT
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply, h, Ne.symm h]
  refine ⟨hH1, ⟨hF, fun ι => ?_⟩, ⟨hF, fun ι => ?_⟩⟩
  · obtain ⟨τ, hτ⟩ := stdform_ext (E := E) ι
    refine (definite_form_signature F E n σ 1 ι τ (hσ τ) hτ hfix hH1 (by simp)).mpr (Or.inl ?_)
    rw [Matrix.map_one _ (map_zero τ) (map_one τ)]
    exact stdform_sig_one
  · obtain ⟨τ, hτ⟩ := stdform_ext (E := E) ι
    refine (definite_form_signature F E n σ (-1) ι τ (hσ τ) hτ hfix hHm
      ((Matrix.isUnit_iff_isUnit_det _).mp isUnit_one.neg)).mpr (Or.inr ?_)
    have : (-1 : Matrix n n E).map τ = -1 := by
      rw [Matrix.map_neg _ (map_neg τ), Matrix.map_one _ (map_zero τ) (map_one τ)]
    rw [this]
    exact stdform_sig_neg_one
end Formalism.UG.P
