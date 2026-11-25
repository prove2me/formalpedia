-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.thGrid_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:15:28.521494+00:00
-- url     : https://prove2.me/submissions/53046e1c-6cc3-4a22-af97-333b6bd2b005

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_lagCo_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hinj : ∀ b, Function.Injective (grid b)) :
    ∑ j, F7.thGrid grid j = 1 := by
  unfold F7.thGrid
  have h := Finset.prod_univ_sum (fun _ : Fin K => (Finset.univ : Finset (Fin (d + 1))))
    (fun a i => |F7.lagCo (grid a) i| / ∑ i, |F7.lagCo (grid a) i|)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  refine Finset.prod_eq_one fun b _ => ?_
  rw [← Finset.sum_div, div_self]
  have h0 : 0 < |F7.lagCo (grid b) 0| := abs_pos.2 (lagCo_ne_zero _ (hinj b) 0)
  exact (Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨0, Finset.mem_univ _, h0⟩).ne'
end Formalism.FourierDecayAlt.P.PBD
