-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_arith
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:11.807316+00:00
-- url     : https://prove2.me/submissions/079f2571-5073-450f-bd85-bf9215013d3e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Theorems.Thm_Formalism_UG_P_tjcosets_prod_shift
import Theorems.Thm_Formalism_UG_P_tjcosets_cast_gl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (q n j C : ℕ) (hq : 2 ≤ q) (hj : j ≤ n)
    (h : C * ∏ i : Fin (n - j), (q ^ (n - j) - q ^ (i : ℕ)) =
      ∏ i : Fin (n - j), (q ^ n - q ^ (i : ℕ))) :
    (C : ℤ) * ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = j + m := ⟨n - j, by omega⟩
  rw [Nat.add_sub_cancel_left] at h
  have hq1 : 1 ≤ q := by omega
  have h' := congrArg (Nat.cast : ℕ → ℤ) h
  rw [Nat.cast_mul, tjcosets_cast_gl q m m hq1 le_rfl, tjcosets_cast_gl q (j + m) m hq1 (by omega)] at h'
  have hqs : ((q : ℤ) ^ (∑ i ∈ Finset.range m, i)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (by omega : q ≠ 0))
  have hAm : ∏ i ∈ Finset.range m, ((q : ℤ) ^ (m - i) - 1) = ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1) := by
    simpa using tjcosets_prod_shift (q : ℤ) 0 m
  have hX : (C : ℤ) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range m, ((q : ℤ) ^ (j + m - i) - 1) := by
    rw [← hAm]
    apply mul_left_cancel₀ hqs
    linear_combination h'
  have s1 := tjcosets_prod_shift (q : ℤ) j m
  have s2 := tjcosets_prod_shift (q : ℤ) m j
  rw [add_comm m j] at s2
  have hAm0 : ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    have : (1 : ℤ) < (q : ℤ) ^ (i + 1) := one_lt_pow₀ (by exact_mod_cast (by omega : 1 < q)) (by omega)
    linarith
  apply mul_left_cancel₀ hAm0
  calc (∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1)) * ((C : ℤ) * ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1))
      = (∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1)) *
          ((C : ℤ) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (i + 1) - 1)) := by ring
    _ = _ := by rw [hX, s1, ← s2]
end Formalism.UG.P
