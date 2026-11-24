-- Prove2me | solution 1 for Formalism.UG.P.stdform_hform_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:52:56.417422+00:00
-- url     : https://prove2.me/submissions/85f0c8ff-9e20-4578-9f7e-8dbf3252fa41

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
import Theorems.Thm_Formalism_UG_P_stdform_invol

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
variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]
namespace Formalism.UG.P
theorem _root_.solution (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E)
    (hJ : IsHerm (σ : E →+* E) J) (x : n → E) :
    σ (hform (σ : E →+* E) J x x) = hform (σ : E →+* E) J x x := by
  unfold IsHerm at hJ
  have hJ' : ∀ i j, σ (J i j) = J j i := fun i j => by
    have h := congrFun (congrFun hJ j) i
    simpa [cT] using h
  simp only [hform, map_sum, map_mul, AlgHom.coe_toRingHom, stdform_invol σ τ hσ, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
end Formalism.UG.P
