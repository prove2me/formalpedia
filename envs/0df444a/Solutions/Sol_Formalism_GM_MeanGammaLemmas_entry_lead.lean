-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.entry_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:04.599904+00:00
-- url     : https://prove2.me/submissions/76167319-931e-4095-bf0f-0d4f2856ce7e

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Polynomial Finset Formalism.GM.M
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (hLead : GamLead) {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (z e : ℕ) (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r)
    (hv : LLw.vec (Fin.last K) = true) (hf : f ∈ Pol p r LLw) (hf' : f' ∈ Pol p r LLw)
    (he : HasOrder (Fin.last K, ρ) e f) (he' : HasOrder (Fin.last K, ρ) e f')
    (Q : ℚ_[p][X]) (a : ℚ_[p]) (ha : a ≠ 0)
    (hQ : ∀ n : ℕ, LLw.total ≤ n → Q.eval (n : ℚ_[p]) = a * tieGam p LLw ρ z n f f') :
    Q.coeff (LLw.total + LLw.deg (Fin.last K) - e) =
      a * (((e.factorial * (z + e).choose e : ℕ) : ℚ_[p]) *
        fock p (initPart (Fin.last K, ρ) e f) (initPart (Fin.last K, ρ) e f') /
        ((((LLw.deg (Fin.last K)).factorial * LLw.total.factorial : ℕ) : ℚ_[p]) *
          ∏ i, ((LLw.deg i).factorial : ℚ_[p]))) := by
  have hP : ∀ n : ℕ, LLw.total ≤ n → tieGam p LLw ρ z n f f' = (C a⁻¹ * Q).eval (n : ℚ_[p]) := by
    intro n hn
    rw [eval_mul, eval_C, hQ n hn, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  have h := hLead p K r LLw ρ z e f f' (C a⁻¹ * Q) hr hv hf hf' he he' hP
  rw [coeff_C_mul] at h
  rw [← h, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
end Formalism.GM.MeanGammaLemmas
