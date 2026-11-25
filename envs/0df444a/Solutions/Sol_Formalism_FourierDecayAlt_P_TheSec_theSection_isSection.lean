-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSec.theSection_isSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:57:18.94075+00:00
-- url     : https://prove2.me/submissions/0af7d250-b47a-4c8f-8819-1e55f62acc3a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Theorems.Thm_Formalism_FourierDecayAlt_P_TheSec_theSecB_core
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)
private theorem herm_Hb_wbPart_eq_herm_Hpk_of_inWb (r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hb k) (wbPart k r z) (wbPart k r z) = herm (Hpk k r) z z := by
  have hin : ∀ i : Fin (2 * r + k + 1), r ≤ i.val → i.val ≤ r + k →
      (Hpk k r *ᵥ z) i = (if i.val = r + k then -1 else 1) * z i := by
    intro i h1 h2
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · simp only [Hpk]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by simp [h1, h2])]
    · intro j _ hji
      by_cases hj : j.val < r ∨ r + k < j.val
      · rw [hz j hj, mul_zero]
      · simp only [Hpk]
        rw [if_neg (by omega), if_neg (by omega), if_neg (by
          rintro ⟨_, _, h⟩
          exact hji h.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  unfold herm
  simp only [dotProduct, Pi.star_apply]
  refine Fintype.sum_of_injective (wI k r) ?_ _ _ ?_ ?_
  · intro a b h
    simp only [wI, Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  · intro i hi
    have hout : i.val < r ∨ r + k < i.val := by
      by_contra hc
      apply hi
      refine ⟨⟨i.val - r, by omega⟩, ?_⟩
      simp only [wI]
      exact Fin.ext (by simp only; omega)
    rw [hz i hout, star_zero, zero_mul]
  · intro j
    have hj := j.isLt
    have h1 : r ≤ (wI k r j).val := by simp [wI]
    have h2 : (wI k r j).val ≤ r + k := by simp [wI]; omega
    rw [hin _ h1 h2]
    unfold Hb
    rw [Matrix.mulVec_diagonal]
    have hc : (j = Fin.last k) ↔ (wI k r j).val = r + k := by
      simp [wI, Fin.ext_iff]
    simp only [wbPart]
    by_cases hjl : j = Fin.last k
    · rw [if_pos hjl, if_pos (hc.1 hjl)]
    · rw [if_neg hjl, if_neg (fun h => hjl (hc.2 h))]
end Formalism.FourierDecayAlt.P.TheSec
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSec
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction
variable (k : ℕ)
namespace Formalism.FourierDecayAlt.P.TheSec
theorem _root_.solution (r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (hk : 1 ≤ k) (hz : inWb k r z)
    (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') :
    IsSection k r z z' (theSection k r z z') := by
  have hreal : ∀ x : Fin (k + 1) → ℂ, (herm (Hb k) x x).im = 0 := by
    intro x
    unfold herm Hb
    rw [dotProduct, Complex.im_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [Matrix.mulVec_diagonal]
    split_ifs <;> simp [Complex.mul_im] <;> (try ring)
  have hrel : ∀ v : Fin (2 * r + k + 1) → ℂ, inWb k r v →
      herm (Hb k) (wbPart k r v) (wbPart k r v) = -(Tz k r v : ℂ) := by
    intro v hv
    have e := herm_Hb_wbPart_eq_herm_Hpk_of_inWb k r v hv
    unfold Tz
    rw [← e]
    apply Complex.ext <;> simp [hreal]
  exact theSecB_core k hk _ _ _ _ hT hT' (hrel z hz) (hrel z' hz')
end Formalism.FourierDecayAlt.P.TheSec
