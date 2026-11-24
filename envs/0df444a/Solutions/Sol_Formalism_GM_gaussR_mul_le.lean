-- Prove2me | solution 1 for Formalism.GM.gaussR_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:48.205733+00:00
-- url     : https://prove2.me/submissions/cdcdacec-5a16-4cad-8959-7ded4ae96585

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Theorems.Thm_Formalism_GM_gaussR_term_le
import Theorems.Thm_Formalism_GM_gaussR_le_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]
variable [IsUltrametricDist K]
namespace Formalism.GM
theorem _root_.solution (ρ : NNReal) (P Q : K[X]) :
    gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by
  rw [gaussR_le_iff]
  intro k
  rw [Polynomial.coeff_mul]
  have h1 : ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ ≤
      (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) :=
    IsUltrametricDist.nnnorm_sum_le_of_forall_le
      (fun x hx => Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) hx)
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup (Finset.HasAntidiagonal.antidiagonal k) ⟨(0, k), by simp⟩
    (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊)
  have hk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  calc ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k
      ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) * ρ ^ k :=
        mul_le_mul_of_nonneg_right h1 zero_le
    _ = ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k := by rw [hxe]
    _ = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
        rw [nnnorm_mul, ← hk, pow_add]
        ring
    _ ≤ gaussR ρ P * gaussR ρ Q := mul_le_mul' (gaussR_term_le ρ P _) (gaussR_term_le ρ Q _)
end Formalism.GM
