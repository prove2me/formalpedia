-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.mirabolic_mackey_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:40:52.220889+00:00
-- url     : https://prove2.me/submissions/2bef71c7-1bc8-41fa-b1c8-40113dac79bf

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_Mirabolic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_exists_gl_of_isUniU
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pair_comm
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairU_isUniU
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_pairV_isUniU
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_pairU
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_supd_pairV
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_exists_bad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.EigenvalueLevelCeiling
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : MirabolicMackey := by
  intro k A _ _ _ n ψ hψ h hm hu
  obtain ⟨s, l, hl, hgood, hbad⟩ := exists_bad (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) hm hu
  have hg : ∀ j, s.castSucc < j → ∀ b, b < j → (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) j b = 0 :=
    fun j hj b hb => (hgood j hj).2 b hb
  have hrow : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.succ l.succ = if l = s then 1 else 0 := by
    by_cases hls : l = s
    · subst hls
      rw [if_pos rfl]
      exact (hgood _ (Fin.castSucc_lt_succ : l.castSucc < l.succ)).1
    · rw [if_neg hls]
      exact (hgood _ (Fin.castSucc_lt_succ : s.castSucc < s.succ)).2 _
        (Fin.succ_lt_succ_iff.2 (lt_of_le_of_ne hl hls))
  obtain ⟨c, hc⟩ : ∃ c : k,
      c = (if l = s then 1 else 0) - (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc :=
    ⟨_, rfl⟩
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact sub_ne_zero.2 (Ne.symm hbad)
  obtain ⟨x, hx⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hno
    push_neg at hno
    exact hψ (AddChar.ext ψ 1 fun y => by rw [hno y, AddChar.one_apply])
  obtain ⟨t, ht⟩ : ∃ t : k, t = x / c := ⟨_, rfl⟩
  have htc : t * c = x := by rw [ht]; field_simp
  obtain ⟨g, hgM⟩ := exists_gl_of_isUniU _ (pairU_isUniU (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l hl hg t)
  have hconj : ((h⁻¹ * g * h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      pairV (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s l t := by
    rw [Units.val_mul, Units.val_mul, hgM, mul_assoc, pair_comm, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]
  refine ⟨g, by rw [hgM]; exact pairU_isUniU _ s l hl hg t, by rw [hconj]; exact pairV_isUniU _ s l hl hg t, ?_⟩
  rw [hconj, hgM, supd_pairV, supd_pairU, hrow]
  intro heq
  apply hx
  have e : t * (if l = s then (1 : k) else 0) =
      t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc + x := by
    linear_combination htc - t * hc
  rw [e, AddChar.map_add_eq_mul] at heq
  obtain ⟨v, hv⟩ : IsUnit (ψ (t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc)) :=
    IsUnit.of_mul_eq_one (ψ (-(t * (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k) s.castSucc l.castSucc)))
      (by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one])
  rw [← hv] at heq
  calc ψ x = ↑v⁻¹ * (↑v * ψ x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = ↑v⁻¹ * ↑v := by rw [heq]
    _ = 1 := Units.inv_mul v
end Formalism.EigenvalueLevelCeiling
