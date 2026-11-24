-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.entry_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:23.065809+00:00
-- url     : https://prove2.me/submissions/e8e6980a-3c03-422e-b1ee-6d35e3463f64

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_MeanGammaLemmas_poly_eq_of_eval

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
theorem _root_.solution (hDeg : GamDeg) {p : ℕ} [Fact p.Prime] {K r : ℕ} (LLw : Letters (K + 1)) (ρ : Fin r)
    (z e e' : ℕ) (f f' : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hr : 1 ≤ r)
    (hv : LLw.vec (Fin.last K) = true) (hf : f ∈ Pol p r LLw) (hf' : f' ∈ Pol p r LLw)
    (he : HasOrder (Fin.last K, ρ) e f) (he' : HasOrder (Fin.last K, ρ) e' f')
    (Q : ℚ_[p][X]) (a : ℚ_[p])
    (hQ : ∀ n : ℕ, LLw.total ≤ n → Q.eval (n : ℚ_[p]) = a * tieGam p LLw ρ z n f f') :
    Q.natDegree ≤ LLw.total + LLw.deg (Fin.last K) - max e e' := by
  obtain ⟨P, hP, hPe⟩ := hDeg p K r LLw ρ z e e' f f' hr hv hf hf' he he'
  have hQP : Q = C a * P := poly_eq_of_eval p Q P LLw.total a (fun n hn => by rw [hQ n hn, hPe n hn])
  rw [hQP]
  exact (natDegree_C_mul_le a P).trans hP
end Formalism.GM.MeanGammaLemmas
