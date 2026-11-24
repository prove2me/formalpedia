-- Prove2me | solution 1 for Formalism.UG.P.satake_value_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:17:14.72555+00:00
-- url     : https://prove2.me/submissions/54f109d2-ddef-45f2-b494-845db37e42ed

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_Tset_right
import Theorems.Thm_Formalism_UG_P_satake_Tj_eq
import Theorems.Thm_Formalism_UG_P_satake_Tj_ne_zero_iff
import Theorems.Thm_Formalism_UG_P_satakeB_mem
import Theorems.Thm_Formalism_UG_P_satakeB_upper
import Theorems.Thm_Formalism_UG_P_satakeB_inj
import Theorems.Thm_Formalism_UG_P_satake_range_eq

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
theorem _root_.solution [Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩)] (hTjCosets : TjCosets) {j : ℕ}
    (hj : j ≤ n) (α : Fin n → ℂ) (φ : GL (Fin n) (v.adicCompletion F) → ℂ)
    (hφ : IsSpherical F v α φ) :
    hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ 1 =
      (∑ i : SatakeIdx v hϖ (n := n) j, chiDelta F v α (satakeB v hϖ hu i)) * φ 1 := by
  classical
  unfold hAct
  have hr := satake_range_eq v hϖ hu hTjCosets hj
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx v hϖ (n := n) j =>
      ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj v hϖ hu h), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨κ, hκ⟩ := QuotientGroup.mk_out_eq_mul (GLint (Fin n) (Ov F v)) (satakeB v hϖ hu i)
    have e : (Quotient.out (((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
        GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v)))) = satakeB v hϖ hu i * κ := hκ
    rw [e, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right v (satakeB_mem v hϖ hu i) κ.2),
      Pi.one_apply, one_smul, one_mul]
    have := hφ (satakeB v hϖ hu i) 1 κ (satakeB_upper v hϖ hu i) κ.2
    rwa [mul_one] at this
  · intro x hx
    rw [Function.mem_support] at hx
    have hT : Tj ℂ n (Ov F v) ϖ j x.out ≠ 0 := fun h0 => hx (by rw [h0, zero_smul])
    rw [satake_Tj_ne_zero_iff] at hT
    have hx' : x ∈ Set.range (fun i : SatakeIdx v hϖ (n := n) j =>
        ((satakeB v hϖ hu i : GL (Fin n) (v.adicCompletion F)) :
          GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v))) := by
      rw [hr]; exact hT
    obtain ⟨i, rfl⟩ := hx'
    simp
end Formalism.UG.P
