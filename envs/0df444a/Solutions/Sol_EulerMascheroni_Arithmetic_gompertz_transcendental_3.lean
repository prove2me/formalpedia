-- Prove2me | solution 3 for EulerMascheroni.Arithmetic.gompertz_transcendental
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T21:37:51.661386+00:00
-- url     : https://prove2.me/submissions/9348f47f-8582-4da1-be24-faff976e585a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Arithmetic_real_affine_integral_eventually_zero
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_recurrence_bound
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_primitive_remainder_lower_bound
import Theorems.Thm_EulerMascheroni_Arithmetic_factorial_division_decay_conjecture
import Theorems.Thm_EulerMascheroni_Arithmetic_pade_normalized_form_integral
import Definitions.Def_eulerMascheroni_padeDecay
open Filter EulerMascheroni.Arithmetic
open scoped Topology
namespace EulerPrimitiveWiring
lemma scaled_decay (U : ℕ → ℤ) (D : ℕ → ℕ)
    (hU : ∀ n, |U n| ≤ (4:ℤ)^n*(n.factorial:ℤ))
    (hD : Tendsto (fun n => (D n:ℝ)*4^n/(n.factorial:ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (D n:ℝ)*(U n:ℝ)/(n.factorial:ℝ)^2) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ hD
  filter_upwards [] with n
  have hn : (0:ℝ) < n.factorial := by positivity
  have hu : |(U n:ℝ)| ≤ (4:ℝ)^n*(n.factorial:ℝ) := by exact_mod_cast hU n
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (sq_nonneg (n.factorial:ℝ))]
  calc
    (D n:ℝ)*|(U n:ℝ)|/(n.factorial:ℝ)^2 ≤
        (D n:ℝ)*((4:ℝ)^n*(n.factorial:ℝ))/(n.factorial:ℝ)^2 := by gcongr
    _ = (D n:ℝ)*4^n/(n.factorial:ℝ) := by field_simp

lemma no_decay_denominators (ha : IsAlgebraic ℚ EulerMascheroni.gompertzConstant)
    (D : ℕ → ℕ) (hDpos : ∀ n, 0 < D n)
    (hD : Tendsto (fun n => (D n:ℝ)*4^n/(n.factorial:ℝ)) atTop (𝓝 0))
    (hq : ∀ n k : ℕ, k ≤ 2*n → IsIntegral ℤ ((D n:ℝ)*quotientCoeff EulerMascheroni.gompertzConstant k)) : False := by
  have hi := fun n => pade_normalized_form_integral EulerMascheroni.gompertzConstant n (D n) (hq n)
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
    simpa [r] using scaled_decay padeQ D hQb hD
  have hs : Tendsto (fun n => (s n:ℝ)) atTop (𝓝 0) := by
    simpa [s] using (scaled_decay padeP D hPb hD).neg
  have his : ∀ n, IsIntegral ℤ ((r n:ℝ)*EulerMascheroni.gompertzConstant+(s n:ℝ)) := by
    intro n
    convert hi n using 1 <;> dsimp [r,s] <;> push_cast <;> ring
  have he := real_affine_integral_eventually_zero EulerMascheroni.gompertzConstant ha r s hr hs his
  have hz : ∀ᶠ n in atTop, (padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ) = 0 := by
    filter_upwards [he] with n hn
    have hd0 : (D n:ℝ) ≠ 0 := by exact_mod_cast (hDpos n).ne'
    have hf0 : (n.factorial:ℝ) ≠ 0 := by positivity
    dsimp [r,s] at hn
    push_cast at hn
    field_simp at hn
    apply (mul_eq_zero.mp (show (D n:ℝ)*((padeQ n:ℝ)*EulerMascheroni.gompertzConstant-(padeP n:ℝ))=0 by
      linear_combination hn)).resolve_left hd0
  obtain ⟨N,hN⟩ := eventually_atTop.mp hz
  have hb := pade_primitive_remainder_lower_bound N 1 (by omega)
  rw [hN (N+1) (by omega), zero_div] at hb
  simp only [Nat.cast_one] at hb
  have hg : (0:ℝ) < (Int.gcd (padeQ (N+1)) ((N.factorial:ℤ)^2):ℝ) := by
    have hf : (N.factorial:ℤ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
    have hgp : 0 < Int.gcd (padeQ (N+1)) ((N.factorial:ℤ)^2) :=
      Int.gcd_pos_of_ne_zero_right _ (pow_ne_zero 2 hf)
    exact_mod_cast hgp
  have hp : (0:ℝ) < ((N+1).factorial:ℝ)*(1:ℝ)^(N+1) /
      (((1:ℝ)+1)^(N+1) * 3^(1+1) * ((1:ℝ)+2) *
        (Int.gcd (padeQ (N+1)) ((N.factorial:ℤ)^2):ℝ)) := by positivity
  exact (not_le_of_gt hp) hb



end EulerPrimitiveWiring


theorem solution : Transcendental ℚ EulerMascheroni.gompertzConstant := by
  intro ha
  obtain ⟨D, hpos, hdec, hint⟩ :=
    EulerMascheroni.Arithmetic.factorial_division_decay_conjecture ha
  exact EulerPrimitiveWiring.no_decay_denominators ha D hpos hdec hint

#print axioms solution
