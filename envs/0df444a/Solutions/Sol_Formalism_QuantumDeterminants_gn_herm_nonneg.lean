-- Prove2me | solution 1 for Formalism.QuantumDeterminants.gn_herm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:34:13.410323+00:00
-- url     : https://prove2.me/submissions/4db420b8-91de-473c-ad39-dfcf8ea41196

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
import Theorems.Thm_Formalism_QuantumDeterminants_gn_re_star_mul_self
import Theorems.Thm_Formalism_QuantumDeterminants_gn_Hpk_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ)
    (h1 : ∀ a : Fin r, y (eI k r a) = y (esI k r a)) (h2 : y ⟨r + k, by omega⟩ = 0) :
    0 ≤ (herm (Hpk k r) y y).re := by
  have hy : Hpk k r *ᵥ y = y := by
    funext i
    have hi := i.isLt
    rw [gn_Hpk_mulVec]
    split_ifs with hio hk
    · rcases hio with hio | hio
      · have e := h1 ⟨i.val, hio⟩
        have e1 : eI k r ⟨i.val, hio⟩ = i := Fin.ext rfl
        have e2 : esI k r ⟨i.val, hio⟩ = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext rfl
        rw [e1, e2] at e
        exact e.symm
      · have ha : 2 * r + k - i.val < r := by omega
        have e := h1 ⟨2 * r + k - i.val, ha⟩
        have e1 : eI k r ⟨2 * r + k - i.val, ha⟩ = ⟨2 * r + k - i.val, by omega⟩ := Fin.ext rfl
        have e2 : esI k r ⟨2 * r + k - i.val, ha⟩ = i :=
          Fin.ext (by show 2 * r + k - (2 * r + k - i.val) = i.val; omega)
        rw [e1, e2] at e
        exact e
    · have ei : i = ⟨r + k, by omega⟩ := Fin.ext hk
      rw [ei, h2, neg_zero]
    · rfl
  simp only [herm]
  rw [hy]
  simp only [_root_.dotProduct, Pi.star_apply]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [gn_re_star_mul_self]
  exact Complex.normSq_nonneg _
end Formalism.QuantumDeterminants
