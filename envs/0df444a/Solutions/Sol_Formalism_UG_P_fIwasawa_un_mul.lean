-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_un_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:12.959803+00:00
-- url     : https://prove2.me/submissions/32943767-0486-419e-9338-22d48349064e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaA
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
section FIwasawaGen
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
private theorem cT_apply' (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) : cT σ M i j = σ (M j i) := by
  first | rfl | simp [cT] | (unfold cT; simp)
private theorem cT_mul_adelic_iwasawa_hecke (A B : Matrix (Fin n) (Fin n) L) : cT σ (A * B) = cT σ B * cT σ A := by
  ext i j
  simp only [cT_apply', Matrix.mul_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
end FIwasawaGen
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (σ : L →+* L) {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) L) (hA : fIwasawaUn σ A) (hB : fIwasawaUn σ B) :
    fIwasawaUn σ (A * B) := by
  unfold fIwasawaUn at *
  rw [cT_mul_adelic_iwasawa_hecke, show cT σ B * cT σ A * antiJ L n * (A * B) = cT σ B * (cT σ A * antiJ L n * A) * B by
    simp only [Matrix.mul_assoc], hA, hB]
end Formalism.UG.P
