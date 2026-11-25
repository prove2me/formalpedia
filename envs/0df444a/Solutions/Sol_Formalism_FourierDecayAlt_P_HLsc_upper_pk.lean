-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.upper_pk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:05:23.593224+00:00
-- url     : https://prove2.me/submissions/6cfb0be7-dd05-4f1a-a414-3b09bb9880a7

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_key_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_parseval
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_exists_tp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_tp_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_normSq_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Herglotz_norm_ee


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution {N : (Fin d → ℝ) → ℝ} {A : (Fin d → ℤ) → ℂ} (hint : Integrable N)
    (hPD : ∀ (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℂ),
        0 ≤ (∑ σ ∈ S, ∑ σ' ∈ S, A (σ - σ') * c σ * starRingEnd ℂ (c σ')).re)
    (hsum : Summable (fun σ : Fin d → ℤ => ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖))
    (z₀ : Fin d → ℝ) (n : ℕ) :
    ∫ z, N z * pk (z - z₀) ^ n ≤
      (∑' σ : Fin d → ℤ, ‖(∫ z, (N z : ℂ) * ee z σ) + A σ‖) * ∫ y in cube d, pk y ^ n := by
  obtain ⟨B, c, hBc⟩ := exists_tp (d := d) n
  have hpk : ∀ y, ‖tp B c y‖ ^ 2 = pk y ^ n := fun y => by rw [hBc, normSq_prod]
  have h1 := key_upper hint hPD hsum B (fun σ => c σ * ee (-z₀) σ)
  simp_rw [← tp_sub, hpk, norm_mul, norm_ee, mul_one] at h1
  rw [← parseval] at h1
  simp_rw [hpk] at h1
  exact h1
end Formalism.FourierDecayAlt.P.HLsc
