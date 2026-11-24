-- Prove2me | solution 1 for Formalism.UG.P.satake_hAct_spherical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:08:22.052508+00:00
-- url     : https://prove2.me/submissions/6a559cca-55aa-44e9-b52d-ed48f6cdfd7a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_chiDelta_one
import Theorems.Thm_Formalism_UG_P_satake_upper_one
import Theorems.Thm_Formalism_UG_P_satake_T_mul_right
import Theorems.Thm_Formalism_UG_P_satake_T_mul_left
import Theorems.Thm_Formalism_UG_P_finsum_out_mul


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
theorem _root_.solution (j : ℕ) (α : Fin n → ℂ)
    (φ : GL (Fin n) (v.adicCompletion F) → ℂ) (hφ : IsSpherical F v α φ) :
    IsSpherical F v α (hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ) := by
  intro b g k hb hk
  unfold hAct
  have step1 : ∀ x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v),
      Tj ℂ n (Ov F v) ϖ j x.out • φ (b * g * k * x.out) =
        chiDelta F v α b * (Tj ℂ n (Ov F v) ϖ j x.out • φ (g * k * x.out)) := by
    intro x
    have := hφ b (g * k * x.out) 1 hb (one_mem _)
    rw [mul_one] at this
    rw [show b * g * k * x.out = b * (g * k * x.out) by group, this, smul_eq_mul, smul_eq_mul]
    ring
  rw [finsum_congr step1, ← mul_finsum]
  congr 1
  have hF : ∀ (y : GL (Fin n) (v.adicCompletion F)) (c : GLint (Fin n) (Ov F v)),
      Tj ℂ n (Ov F v) ϖ j (k⁻¹ * (y * c)) • φ (g * (y * c)) =
        Tj ℂ n (Ov F v) ϖ j (k⁻¹ * y) • φ (g * y) := by
    intro y c
    rw [← mul_assoc, satake_T_mul_right v j _ _ c.2]
    have := hφ 1 (g * y) c (satake_upper_one v) c.2
    rw [one_mul, satake_chiDelta_one, one_mul] at this
    rw [← mul_assoc, this]
  have hr := finsum_out_mul (GLint (Fin n) (Ov F v)) k
    (fun y => Tj ℂ n (Ov F v) ϖ j (k⁻¹ * y) • φ (g * y)) hF
  simp only [inv_mul_cancel_left] at hr
  rw [show (fun x : GL (Fin n) (v.adicCompletion F) ⧸ GLint (Fin n) (Ov F v) =>
      Tj ℂ n (Ov F v) ϖ j x.out • φ (g * k * x.out)) =
      (fun x => Tj ℂ n (Ov F v) ϖ j x.out • φ (g * (k * x.out))) by
    funext x; rw [mul_assoc]]
  rw [hr]
  refine finsum_congr fun y => ?_
  rw [satake_T_mul_left v j _ _ ((GLint (Fin n) (Ov F v)).inv_mem hk)]
end Formalism.UG.P
