-- Prove2me | solution 1 for Formalism.UG.P.satake_chiDelta_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:09.300674+00:00
-- url     : https://prove2.me/submissions/91a61f45-7f1e-4b56-ad8a-8808d25c23e7

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satakeGL_diag
import Theorems.Thm_Formalism_UG_P_satake_ordV_one
import Theorems.Thm_Formalism_UG_P_satake_ordV_unif
import Theorems.Thm_Formalism_UG_P_satake_unif_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)
namespace Formalism.UG.P
theorem _root_.solution (α : Fin n → ℂ) {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) :
    chiDelta F v α (satakeB v hϖ hu i) =
      ∏ a ∈ i.1.1, (α a * (qV F v : ℂ) ^ (-(((n : ℂ) - 1 - 2 * (a : ℂ)) / 2))) := by
  unfold chiDelta
  rw [← Finset.univ_inter i.1.1, ← Finset.prod_ite_mem]
  refine Finset.prod_congr rfl fun a _ => ?_
  have hd := satakeGL_diag (Ov F v) (satake_unif_ne_zero v hu) i.1.1
    (fun p => satakeSec (Ov F v) ⟨ϖ, hϖ⟩ (i.2 p)) a
  have e : ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) a a = if a ∈ i.1.1 then ϖ else 1 := hd
  rw [e]
  by_cases h : a ∈ i.1.1
  · simp [h, satake_ordV_unif v hu]
  · simp [h, satake_ordV_one v]
end Formalism.UG.P
