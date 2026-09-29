-- Prove2me | solution 1 for EulerMascheroni.Arithmetic.no_small_integral_pade_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:17:18.814135+00:00
-- url     : https://prove2.me/submissions/8d7ca726-2a7d-4efe-8f81-8f9e44f4ab1a

import Theorems.Thm_EulerMascheroni_Arithmetic_real_affine_integral_eventually_zero
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_recurrence_bound
import Theorems.Thm_EulerMascheroni_Arithmetic_normalized_pade_tendsto_zero
import Definitions.Def_eulerMascheroni_padeTransform
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_determinant_and_nonvanishing
set_option autoImplicit false
open Filter EulerMascheroni.Arithmetic
open scoped Topology

namespace EulerPadeContradiction

lemma no_small_integral_forms (a : ℝ) (ha : IsAlgebraic ℚ a)
    (C : ℝ) (hC : 1 ≤ C) (D : ℕ → ℕ)
    (hDpos : ∀ n, 0 < D n) (hD : ∀ n, (D n : ℝ) ≤ C^(2*n+1))
    (hi : ∀ n, IsIntegral ℤ
      ((D n:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))/(n.factorial:ℝ)^2)) : False := by
  have hP : ∀ n : ℕ, padeP (n+2) = (2*(n:ℤ)+4)*padeP (n+1) - ((n:ℤ)+1)^2*padeP n :=
    fun _ => rfl
  have hQ : ∀ n : ℕ, padeQ (n+2) = (2*(n:ℤ)+4)*padeQ (n+1) - ((n:ℤ)+1)^2*padeQ n :=
    fun _ => rfl
  have hPb := pade_recurrence_bound padeP (by norm_num [padeP, padeSeq])
    (by norm_num [padeP, padeSeq]) hP
  have hQb := pade_recurrence_bound padeQ (by norm_num [padeQ, padeSeq])
    (by norm_num [padeQ, padeSeq]) hQ
  let r : ℕ → ℚ := fun n => (D n:ℚ)*(padeQ n:ℚ)/(n.factorial:ℚ)^2
  let s : ℕ → ℚ := fun n => -((D n:ℚ)*(padeP n:ℚ)/(n.factorial:ℚ)^2)
  have hr : Tendsto (fun n => (r n:ℝ)) atTop (𝓝 0) := by
    simpa [r] using normalized_pade_tendsto_zero padeQ C hC D hD hQb
  have hs : Tendsto (fun n => (s n:ℝ)) atTop (𝓝 0) := by
    simpa [s] using (normalized_pade_tendsto_zero padeP C hC D hD hPb).neg
  have his : ∀ n, IsIntegral ℤ ((r n:ℝ)*a+(s n:ℝ)) := by
    intro n
    convert hi n using 1 <;> dsimp [r,s] <;> push_cast <;> ring
  have he := real_affine_integral_eventually_zero a ha r s hr hs his
  have hz : ∀ᶠ n in atTop, (padeQ n:ℝ)*a-(padeP n:ℝ) = 0 := by
    filter_upwards [he] with n hn
    have hd0 : (D n:ℝ) ≠ 0 := by exact_mod_cast (hDpos n).ne'
    have hf0 : (n.factorial:ℝ) ≠ 0 := by positivity
    dsimp [r,s] at hn
    push_cast at hn
    field_simp at hn
    apply (mul_eq_zero.mp (show (D n:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))=0 by
      linear_combination hn)).resolve_left hd0
  obtain ⟨N,hN⟩ := eventually_atTop.mp hz
  have hn := (pade_determinant_and_nonvanishing padeP padeQ
    (by norm_num [padeP,padeQ,padeSeq]) hP hQ N).2 a
  exact hn.elim (fun h => h (hN N le_rfl)) (fun h => h (hN (N+1) (by omega)))

end EulerPadeContradiction


theorem solution (a : ℝ) (ha : IsAlgebraic ℚ a)
    (C : ℝ) (hC : 1 ≤ C) (D : ℕ → ℕ)
    (hDpos : ∀ n, 0 < D n) (hD : ∀ n, (D n : ℝ) ≤ C^(2*n+1))
    (hi : ∀ n, IsIntegral ℤ
      ((D n:ℝ)*((padeQ n:ℝ)*a-(padeP n:ℝ))/(n.factorial:ℝ)^2)) : False := by
  exact EulerPadeContradiction.no_small_integral_forms a ha C hC D hDpos hD hi

#print axioms solution
