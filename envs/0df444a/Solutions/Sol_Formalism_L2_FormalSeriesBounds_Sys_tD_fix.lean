-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Sys.tD_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:11:51.811212+00:00
-- url     : https://prove2.me/submissions/b7e4f85d-4f8d-432d-857a-b4b4ce6a2d55

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_coeff_tD
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_noConst_tD
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_Psi


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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
  {Xc : Cart V d I J} (S : Sys Xc)
variable {τ : Type} [Fintype τ]
namespace Formalism.L2.FormalSeriesBounds
namespace Sys
theorem _root_.solution {N1 : ℕ} (D : Formalism.BaseCaseIdentities.Data C (Fin N1) I) (hl : D.l = V.l)
    (hal : ∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, D.al c k b * S.al b 0 x)
    {t : I → MvPowerSeries I C} (ht : S.IsT t) :
    NoConst (fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c)) ∧
      D.Psi (fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c)) =
        fun c => subst (linS fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) (t c) := by
  refine ⟨S.noConst_tD _ ht, ?_⟩
  funext b
  ext A
  rw [Formalism.BaseCaseIdentities.Data.coeff_Psi, hl,
    S.coeff_tD (fun (δ : Fin N1) x => S.al (D.ι δ) 0 x) ht D.al
      (fun δ b => if D.ι δ = b then 1 else 0) hal (fun β x => by simp) b A]
  congr 2
  unfold Formalism.BaseCaseIdentities.Data.zvec
  refine Finset.sum_congr rfl fun δ _ => ?_
  split_ifs <;> simp
end Sys
end Formalism.L2.FormalSeriesBounds
