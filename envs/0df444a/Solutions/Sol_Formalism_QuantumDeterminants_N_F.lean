-- Prove2me | solution 1 for Formalism.QuantumDeterminants.N_F
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:33.688997+00:00
-- url     : https://prove2.me/submissions/c3a9bec0-1647-4ef5-aec2-15476fa111bc

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Theorems.Thm_Formalism_QuantumDeterminants_mF_col
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_lt
import Theorems.Thm_Formalism_QuantumDeterminants_fvec_apply_ge

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
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r) :
    m * Fm k r z = Fm k r z * Uof k r z m := by
  have hm2 := hm.2.1
  have hm3 := hm.2.2
  ext i a
  conv_rhs => rw [Matrix.mul_apply]
  by_cases hi : i.val < r
  · have hF : ∀ c, Fm k r z i c = if c = ⟨i.val, by omega⟩ then 1 else 0 := fun c => by
      change fvec k r z c i = _
      rw [fvec_apply_lt z hz c i hi]
      simp [Fin.ext_iff]
    simp only [hF, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    simp [Uof, hi, eI]
  · have hF : ∀ c, Fm k r z i c = if c = Fin.last r then z i else 0 := fun c => by
      change fvec k r z c i = _
      rw [fvec_apply_ge z c i (by omega)]
      simp [Fin.ext_iff]
    simp only [hF, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have hU : Uof k r z m (Fin.last r) a = if Fin.last r = a then 1 else 0 := by simp [Uof]
    rw [hU]
    by_cases ha : a.val < r
    · rw [mF_col z m i a ha, hm2 ⟨a.val, ha⟩ i (by show a.val ≤ i.val; omega)]
      have h1 : i ≠ eI k r ⟨a.val, ha⟩ := by
        intro h
        have := congrArg Fin.val h
        change i.val = a.val at this
        omega
      have h2 : Fin.last r ≠ a := by
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      simp [h1, h2]
    · have ha' : a = Fin.last r := Fin.ext (by have := a.isLt; simp; omega)
      subst ha'
      simp only [if_true, mul_one]
      change (m *ᵥ fvec k r z (Fin.last r)) i = z i
      have hf : fvec k r z (Fin.last r) = z := by simp [fvec]
      rw [hf]
      have hterm : ∀ j, m i j * z j = if i = j then z j else 0 := by
        intro j
        by_cases hj : j.val < r ∨ r + k < j.val
        · rw [hz j hj]
          simp
        · push_neg at hj
          rw [hm3 i j hj.1 hj.2 (by omega)]
          split_ifs <;> simp
      simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end Formalism.QuantumDeterminants
