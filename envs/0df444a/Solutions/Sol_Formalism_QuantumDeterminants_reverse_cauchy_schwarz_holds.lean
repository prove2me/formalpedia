-- Prove2me | solution 1 for Formalism.QuantumDeterminants.reverse_cauchy_schwarz_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:28:01.168712+00:00
-- url     : https://prove2.me/submissions/99d69d63-07bf-42ed-af61-0f921195fdbb

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Theorems.Thm_Formalism_QuantumDeterminants_ggHerm_Wb
import Theorems.Thm_Formalism_QuantumDeterminants_ggRe_star_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution : RevCS := by
  intro k r z z' hz hz' h1 h2
  have e12 := ggHerm_Wb k r z z' hz'
  have e11 := ggHerm_Wb k r z z hz
  have e22 := ggHerm_Wb k r z' z' hz'
  set L : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩ with hL
  set s := (Finset.univ : Finset (Fin (2 * r + k + 1))).erase L with hs
  set A := ∑ i ∈ s, ‖z i‖ ^ 2 with hA
  set B := ∑ i ∈ s, ‖z' i‖ ^ 2 with hB
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => by positivity)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => by positivity)
  have hre : ∀ w : Fin (2 * r + k + 1) → ℂ, (∑ i ∈ s, star (w i) * w i).re = ∑ i ∈ s, ‖w i‖ ^ 2 := by
    intro w
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl (fun i _ => ggRe_star_mul (w i))
  have hzz : (herm (Hpk k r) z z).re = A - ‖z L‖ ^ 2 := by
    rw [e11, Complex.sub_re, hre, ggRe_star_mul]
  have hzz' : (herm (Hpk k r) z' z').re = B - ‖z' L‖ ^ 2 := by
    rw [e22, Complex.sub_re, hre, ggRe_star_mul]
  unfold Tz
  rw [hzz, hzz', e12, Complex.normSq_eq_norm_sq]
  rw [hzz] at h1
  rw [hzz'] at h2
  set S := ∑ i ∈ s, star (z i) * z' i with hS
  set p := ‖z L‖ with hp
  set q := ‖z' L‖ with hq
  have hp0 : 0 ≤ p := norm_nonneg _
  have hq0 : 0 ≤ q := norm_nonneg _
  have hSle : ‖S‖ ≤ √A * √B := by
    refine (norm_sum_le _ _).trans ?_
    have := Real.sum_mul_le_sqrt_mul_sqrt s (fun i => ‖z i‖) (fun i => ‖z' i‖)
    simpa [norm_mul] using this
  have hc : ‖star (z L) * z' L‖ = p * q := by simp [norm_mul, hp, hq]
  have hD : p * q - ‖S‖ ≤ ‖S - star (z L) * z' L‖ := by
    rw [norm_sub_rev, ← hc]; exact norm_sub_norm_le _ _
  have ha2 : (√A) ^ 2 = A := Real.sq_sqrt hA0
  have hb2 : (√B) ^ 2 = B := Real.sq_sqrt hB0
  have ha0 : 0 ≤ √A := Real.sqrt_nonneg _
  have hb0 : 0 ≤ √B := Real.sqrt_nonneg _
  have hap : √A < p := by
    by_contra hc'
    push Not at hc'
    nlinarith [mul_le_mul hc' hc' hp0 ha0]
  have hbq : √B < q := by
    by_contra hc'
    push Not at hc'
    nlinarith [mul_le_mul hc' hc' hq0 hb0]
  have h0 : 0 ≤ p * q - √A * √B := by nlinarith [mul_le_mul hap.le hbq.le hb0 hp0]
  have hX : p * q - √A * √B ≤ ‖S - star (z L) * z' L‖ := by linarith
  rw [← ha2, ← hb2]
  nlinarith [mul_self_le_mul_self h0 hX, sq_nonneg (p * √B - q * √A)]
end Formalism.QuantumDeterminants
