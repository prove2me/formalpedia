-- Prove2me | solution 1 for Formalism.QuantumDeterminants.hermitian_pos_facts_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:56:37.8908+00:00
-- url     : https://prove2.me/submissions/ff0f212f-c3c9-451e-9d76-a22a02a486e8

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_herm_bvec
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_hi
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_PJP
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_herm
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq

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
open GBasic
namespace Formalism.QuantumDeterminants
theorem _root_.solution : HpkFacts := by
  intro k r
  have hsq := Hpk_sq k r
  refine ⟨Hpk_herm k r, hsq, ?_, ⟨epsK k r, ?_, Pk k r, ?_, PJP k r⟩⟩
  · intro a b
    have hb := b.isLt
    have h1 : sig k r (esI k r b) = eI k r b := by
      apply Fin.ext
      rw [sig_hi k r _ (by show r + k < 2 * r + k - b.val; omega)]
      show 2 * r + k - (2 * r + k - b.val) = b.val
      omega
    have h2 : sgn k r (esI k r b) = 1 := by
      unfold sgn
      rw [if_neg]
      show ¬ (2 * r + k - b.val = r + k)
      omega
    rw [herm_bvec, Hpk_eq, h1, h2]
    by_cases h : a = b
    · subst h
      simp
    · rw [if_neg, if_neg h]
      intro e
      apply h
      have e2 := congrArg Fin.val e
      exact Fin.ext e2
  · have e0 : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => epsK k r i = true)
        = Finset.univ.filter (fun i : Fin (2 * r + k + 1) => i.val < r + k) := by
      ext i
      simp [epsK]
    rw [e0, ← Finset.card_map Fin.valEmbedding]
    have e : (Finset.univ.filter fun i : Fin (2 * r + k + 1) => i.val < r + k).map Fin.valEmbedding
        = Finset.range (r + k) := by
      ext x
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_range]
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ha
      · intro hx
        exact ⟨⟨x, by omega⟩, hx, rfl⟩
    rw [e, Finset.card_range, Nat.add_comm]
  · have hdet := congrArg Matrix.det (PJP k r)
    rw [Matrix.det_mul, Matrix.det_mul] at hdet
    have hH : (Hpk k r).det ≠ 0 := by
      have e := congrArg Matrix.det hsq
      rw [Matrix.det_mul, Matrix.det_one] at e
      intro h0
      rw [h0, mul_zero] at e
      exact zero_ne_one e
    rw [isUnit_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hdet
    exact hH hdet.symm
end Formalism.QuantumDeterminants
