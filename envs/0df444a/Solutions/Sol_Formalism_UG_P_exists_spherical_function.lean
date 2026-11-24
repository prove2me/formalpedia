-- Prove2me | solution 1 for Formalism.UG.P.exists_spherical_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:27.566671+00:00
-- url     : https://prove2.me/submissions/9b59e898-663e-489b-8540-64b4749c0ec5

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
import Theorems.Thm_Formalism_UG_P_spherical_iwasawa
import Theorems.Thm_Formalism_UG_P_spherical_wd
import Theorems.Thm_Formalism_UG_P_spherical_chiDelta_int
import Theorems.Thm_Formalism_UG_P_spherical_chiDelta_mul
import Theorems.Thm_Formalism_UG_P_spherical_upper_iff
import Theorems.Thm_Formalism_UG_P_spherical_upper_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.SphericalExists := by
  intro F _ _ v n α hα
  classical
  have dec := fun g : GL (Fin n) (v.adicCompletion F) => spherical_iwasawa F v g
  let φ : GL (Fin n) (v.adicCompletion F) → ℂ := fun g => chiDelta F v α (Classical.choose (dec g))
  have hφ : ∀ g b k : GL (Fin n) (v.adicCompletion F),
      (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id →
      k ∈ GLint (Fin n) (Ov F v) → g = b * k → φ g = chiDelta F v α b := by
    intro g b k hb hk hg
    obtain ⟨k0, hb0, hk0, hg0⟩ := Classical.choose_spec (dec g)
    exact spherical_wd F v α hα _ _ _ _ hb0 hb hk0 hk (hg0.symm.trans hg)
  have hone : ((1 : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id :=
    (spherical_upper_iff 1).mp (fun i j h => by simp [Matrix.one_apply_ne (ne_of_gt h)])
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro b g k hb hk
    have hb' := (spherical_upper_iff b).mp hb
    obtain ⟨b0, k0, hb0, hk0, hg0⟩ := dec g
    rw [hφ g b0 k0 hb0 hk0 hg0,
      hφ (b * g * k) (b * b0) (k0 * k) (spherical_upper_mul b b0 hb' hb0)
        (Subgroup.mul_mem _ hk0 hk) (by rw [hg0]; group),
      spherical_chiDelta_mul F v α hα b b0 hb' hb0]
  · rw [hφ 1 1 1 hone (Subgroup.one_mem _) (by simp)]
    exact spherical_chiDelta_int F v α 1 hone (Subgroup.one_mem _)
  · intro ψ hψ
    funext g
    obtain ⟨b0, k0, hb0, hk0, hg0⟩ := dec g
    have h1 := hψ b0 1 k0 ((spherical_upper_iff b0).mpr hb0) hk0
    rw [mul_one] at h1
    rw [hg0, hφ (b0 * k0) b0 k0 hb0 hk0 rfl, h1, mul_comm]
end Formalism.UG.P
