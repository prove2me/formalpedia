-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_Km_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:35:30.833917+00:00
-- url     : https://prove2.me/submissions/bbd8577e-9ea2-472d-8f88-a3e1f5e323c0

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaRed
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
private theorem cT_mul_reverse (A B : Matrix (Fin n) (Fin n) L) :
    cT σ (A * B) = cT σ B * cT σ A := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]
end FIwasawaRed
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {A B : Matrix (Fin n) (Fin n) L} (hA : fIwasawaKm σ A) (hB : fIwasawaKm σ B) :
    fIwasawaKm σ (A * B) := by
  unfold fIwasawaKm fIwasawaUn fIwasawaInt at *
  obtain ⟨hAu, hAi⟩ := hA
  obtain ⟨hBu, hBi⟩ := hB
  refine ⟨?_, fun i j => ?_⟩
  · calc cT σ (A * B) * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B := by
          rw [cT_mul_reverse]
          simp only [Matrix.mul_assoc]
      _ = antiJ L n := by rw [hAu, hBu]
  · rw [Matrix.mul_apply]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul]
    exact mul_le_one' (hAi i k) (hBi k j)
end Formalism.UG.P
