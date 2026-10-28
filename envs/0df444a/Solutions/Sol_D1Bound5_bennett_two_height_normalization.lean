-- Prove2me | solution 1 for D1Bound5.bennett_two_height_normalization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:51:52.948947+00:00
-- url     : https://prove2.me/submissions/641ae5d7-994e-4742-aacd-f44fe0a6acac

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_bennett_prefactor_absorb
import Theorems.Thm_D1Bound5_bennett_two_coefficient_rounding
import Theorems.Thm_D1Bound5_bennett_two_scaled_radius_ratio_le

section
namespace D1Bound5



/-- The exact local coefficient majorant, after multiplication by the
integral clearing factor, has exponential base strictly below 42. All
geometric and scale hypotheses are elementary real inequalities; no bound
on the coefficient being estimated occurs among the assumptions. -/
theorem _root_.solution
    (X Y δ B C N U r : ℝ) (k : ℕ)
    (hX : 0 < X) (hY : 0 < Y) (hδ : 0 < δ)
    (hB : 0 < B) (hC : 0 < C) (hXB : X ≤ B)
    (hδB : δ ≤ X+B) (hN : N = X*Y*C)
    (hscale : 1000 ≤ N/B) (hUlo : N-X ≤ U) (hUhi : U ≤ N+X)
    (hradius : r = 2*min X δ/5) (hk : 1 ≤ k) :
    (4*X*Y*δ^2)^k * ((U+r)/U) *
        ((U+r)/(r*(X-r)*(δ-r)))^k < (42*Y^2*B*C)^k := by
  let T := N/B
  let F := 1+7/(5*T)
  let η := 1-1/T
  let M := F/η
  let H := (125/3 : ℝ)*F
  let L := Y^2*B*C
  have hN0 : 0 < N := by rw [hN]; positivity
  have hT1000 : 1000 ≤ T := hscale
  have hT : 0 < T := by linarith
  have hF : 0 < F := by dsimp [F]; positivity
  have hη : 0 < η := by
    have hdiv : 1/T < 1 := (div_lt_one hT).2 (by linarith)
    dsimp [η]
    linarith
  have hη1 : η ≤ 1 := by
    dsimp [η]
    have : 0 ≤ 1/T := by positivity
    linarith
  have hF1 : 1 ≤ F := by
    dsimp [F]
    have : 0 ≤ 7/(5*T) := by positivity
    linarith
  have hM : 1 ≤ M := by
    dsimp [M]
    apply (le_div_iff₀ hη).2
    simpa only [one_mul] using hη1.trans hF1
  have hM0 : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hH : 0 < H := by dsimp [H]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hr : 0 < r := by
    rw [hradius]
    exact div_pos (mul_pos (by norm_num) (lt_min hX hδ)) (by norm_num)
  have hrX : r ≤ 2*X/5 := by
    rw [hradius]
    gcongr
    exact min_le_left _ _
  have hrδ : r ≤ 2*δ/5 := by
    rw [hradius]
    gcongr
    exact min_le_right _ _
  have hDX : 0 < X-r := by linarith
  have hDδ : 0 < δ-r := by linarith
  have hden : 0 < r*(X-r)*(δ-r) := by positivity
  have hNF : N*F = N+7*B/5 := by
    dsimp [F, T]
    field_simp [hN0.ne', hB.ne']
    <;> ring
  have hNη : N*η = N-B := by
    dsimp [η, T]
    field_simp [hN0.ne', hB.ne']
    <;> ring
  have hnum : U+r ≤ N*F := by rw [hNF]; linarith
  have hdenU : N*η ≤ U := by rw [hNη]; linarith
  have hU : 0 < U := (mul_pos hN0 hη).trans_le hdenU
  have hUr : 0 < U+r := by positivity
  have hpref : (U+r)/U ≤ M := by
    dsimp [M]
    apply (div_le_div_iff₀ hU hη).2
    have h1 := mul_le_mul_of_nonneg_right hnum hη.le
    have h2 := mul_le_mul_of_nonneg_left hdenU hF.le
    nlinarith only [h1, h2]
  have hratio := bennett_two_scaled_radius_ratio_le X δ B r
    hX hδ hB hXB hδB hradius
  let V := (4*X*Y*δ^2)*((U+r)/(r*(X-r)*(δ-r)))
  have hV : 0 < V := by dsimp [V]; positivity
  have hbase : V ≤ H*L := by
    calc
      V = (4*X*δ^2/(r*(X-r)*(δ-r)))*(Y*(U+r)) := by
        dsimp [V]
        ring
      _ ≤ ((125/3 : ℝ)*B/X)*(Y*(U+r)) :=
        mul_le_mul_of_nonneg_right hratio (by positivity)
      _ ≤ ((125/3 : ℝ)*B/X)*(Y*(N*F)) := by gcongr
      _ = H*L := by
        dsimp [H, L]
        rw [hN]
        field_simp [hX.ne']
        <;> ring
  have hround : M*H < 42 := bennett_two_coefficient_rounding T hT1000
  have hfinalbase : M*(H*L) < 42*L := by
    simpa only [mul_assoc] using mul_lt_mul_of_pos_right hround hL
  have hpow : (M*(H*L))^k < (42*L)^k := by
    have hk0 : k ≠ 0 := by omega
    exact pow_lt_pow_left₀ hfinalbase (by positivity) hk0
  calc
    _ = ((U+r)/U)*V^k := by
      dsimp only [V]
      rw [mul_pow (4*X*Y*δ^2) ((U+r)/(r*(X-r)*(δ-r))) k]
      ring
    _ ≤ M*(H*L)^k := mul_le_mul hpref
      (pow_le_pow_left₀ hV.le hbase k) (pow_nonneg hV.le _) hM0.le
    _ ≤ (M*(H*L))^k := bennett_prefactor_absorb M (H*L) hM
      (mul_pos hH hL).le k hk
    _ < (42*L)^k := hpow
    _ = _ := by dsimp [L]; ring

end D1Bound5
end
