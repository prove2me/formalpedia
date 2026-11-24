-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.prime_divisor_count_absorption
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:47.117924+00:00
-- url     : https://prove2.me/submissions/ce35ece3-0a8a-4a9b-8a56-69a3c0afc2c9

import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.GL2PrimeSums
private lemma gl2a4_rho_pos {C c B X : ℝ} (hC : 0 < C) : 0 < rhoErr C c B X := by
  unfold rhoErr
  have h1 := mul_pos hC (Real.exp_pos (-c * Real.log X / Real.log B))
  have h2 := mul_pos hC (Real.exp_pos (-c * Real.sqrt (Real.log X)))
  linarith
private lemma gl2a4_le_of_deriv {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x) (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ f' x) : f a ≤ f b := by
  have hmono : MonotoneOn f (Set.Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
      (fun x hx => (h x hx).continuousAt.continuousWithinAt)
      (fun x hx => (h x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => h0 x (interior_subset hx))
  exact hmono (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab) hab
private lemma gl2a4_Li_deriv {x : ℝ} (hx : 1 < x) : HasDerivAt Li (1 / Real.log x) x := by
  have hcont : ContinuousOn (fun t : ℝ => 1 / Real.log t) (Set.Ioi 1) := by
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun t ht => (show (0:ℝ) < t from lt_trans one_pos ht).ne')
    · intro t ht
      exact (Real.log_pos ht).ne'
  have hsub : Set.uIcc 2 x ⊆ Set.Ioi 1 := by
    intro t ht
    rcases Set.mem_uIcc.1 ht with h | h
    · show (1:ℝ) < t
      linarith [h.1]
    · show (1:ℝ) < t
      linarith [h.1]
  have hint_r : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume 2 x :=
    (hcont.mono hsub).intervalIntegrable
  show HasDerivAt (fun X => ∫ t in (2:ℝ)..X, 1 / Real.log t) (1 / Real.log x) x
  exact intervalIntegral.integral_hasDerivAt_right hint_r
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx) (hcont.continuousAt (Ioi_mem_nhds hx))
private lemma gl2a4_E_deriv (θ : ℤ) {β t : ℝ} (hβ : 0 < β) (ht : 1 < t) :
    HasDerivAt (Emain θ β) ((1 - θ * t ^ (β - 1)) / Real.log t) t := by
  have ht0 : 0 < t := by linarith
  have h1 : 1 < t ^ β := Real.one_lt_rpow ht hβ
  have hA := gl2a4_Li_deriv ht
  have hB := (gl2a4_Li_deriv h1).comp (x := t)
    (Real.hasDerivAt_rpow_const (p := β) (Or.inl ht0.ne'))
  have hC := hA.sub (hB.const_mul (θ : ℝ))
  have hk : 1 / (β * Real.log t) * (β * t ^ (β - 1)) = t ^ (β - 1) / Real.log t := by
    rw [one_div_mul_eq_div, mul_div_mul_left _ _ hβ.ne']
  have heq : 1 / Real.log t - (θ : ℝ) * (1 / Real.log (t ^ β) * (β * t ^ (β - 1))) =
      (1 - (θ : ℝ) * t ^ (β - 1)) / Real.log t := by
    rw [Real.log_rpow ht0, hk]
    ring
  rw [← heq]
  exact hC
private lemma gl2a4_Li_two : Li 2 = 0 := by
  unfold Li
  exact intervalIntegral.integral_same
private lemma gl2a4_Li_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : Li a ≤ Li b :=
  gl2a4_le_of_deriv (f := Li) (f' := fun x => 1 / Real.log x) hab
    (fun x hx => gl2a4_Li_deriv (by linarith [hx.1] : 1 < x))
    (fun x hx => by
      show 0 ≤ 1 / Real.log x
      exact div_nonneg zero_le_one (Real.log_nonneg (by linarith [hx.1])))
private lemma gl2a4_Li_sub_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Li b - Li a ≤ (b - a) / Real.log a := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have key := gl2a4_le_of_deriv (f := fun x => (x - a) / Real.log a - Li x)
    (f' := fun x => 1 / Real.log a - 1 / Real.log x) hab
    (fun x hx => ((((hasDerivAt_id' (x := x)).sub_const a).div_const (Real.log a)).sub
      (gl2a4_Li_deriv (by linarith [hx.1] : 1 < x))))
    (fun x hx => by
      have hlx : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hx.1
      show 0 ≤ 1 / Real.log a - 1 / Real.log x
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le hla hlx)
  simp only [sub_self, zero_div] at key
  linarith
private lemma gl2a4_E_lower (θ : ℤ) {β a b W : ℝ} (hβ : 0 < β) (ha : 1 < a) (hab : a ≤ b) (hW : 0 ≤ W)
    (hw : ∀ t, a ≤ t → t ≤ b → W ≤ 1 - θ * t ^ (β - 1)) :
    W * (b - a) / Real.log b ≤ Emain θ β b - Emain θ β a := by
  have hlb : 0 < Real.log b := Real.log_pos (by linarith)
  have key := gl2a4_le_of_deriv (f := fun x => Emain θ β x - W * (x - a) / Real.log b)
    (f' := fun x => (1 - (θ:ℝ) * x ^ (β - 1)) / Real.log x - W * 1 / Real.log b) hab
    (fun x hx => (gl2a4_E_deriv θ hβ (by linarith [hx.1] : 1 < x)).sub
      ((((hasDerivAt_id' (x := x)).sub_const a).const_mul W).div_const (Real.log b)))
    (fun x hx => by
      have hx1 : 1 < x := by linarith [hx.1]
      have hlx : 0 < Real.log x := Real.log_pos hx1
      have hlxb : Real.log x ≤ Real.log b := Real.log_le_log (by linarith) hx.2
      have hn := hw x hx.1 hx.2
      show 0 ≤ (1 - (θ:ℝ) * x ^ (β - 1)) / Real.log x - W * 1 / Real.log b
      rw [mul_one, sub_nonneg, div_le_div_iff₀ hlb hlx]
      nlinarith [mul_le_mul_of_nonneg_left hlxb hW, mul_le_mul_of_nonneg_right hn hlb.le])
  simp only [sub_self, mul_zero, zero_div, sub_zero] at key
  linarith
private lemma gl2a4_E_upper (θ : ℤ) {β a b V : ℝ} (hβ : 0 < β) (ha : 1 < a) (hab : a ≤ b)
    (hw : ∀ t, a ≤ t → t ≤ b → 1 - θ * t ^ (β - 1) ≤ V) :
    Emain θ β b - Emain θ β a ≤ V * (Li b - Li a) := by
  have key := gl2a4_le_of_deriv (f := fun x => V * Li x - Emain θ β x)
    (f' := fun x => V * (1 / Real.log x) - (1 - (θ:ℝ) * x ^ (β - 1)) / Real.log x) hab
    (fun x hx => ((gl2a4_Li_deriv (by linarith [hx.1] : 1 < x)).const_mul V).sub
      (gl2a4_E_deriv θ hβ (by linarith [hx.1] : 1 < x)))
    (fun x hx => by
      have hlx : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      have hn := hw x hx.1 hx.2
      show 0 ≤ V * (1 / Real.log x) - (1 - (θ:ℝ) * x ^ (β - 1)) / Real.log x
      rw [mul_one_div, ← sub_div]
      exact div_nonneg (by linarith) hlx.le)
  linarith
private lemma gl2a4_Li_four : Li 4 ≤ 3 := by
  have h := gl2a4_Li_sub_le (a := 2) (b := 4) (by norm_num) (by norm_num)
  rw [gl2a4_Li_two] at h
  have hl2 : (2:ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  have hpos : 0 < Real.log 2 := by linarith
  have h3 : (4 - 2) / Real.log 2 ≤ 3 := by
    rw [div_le_iff₀ hpos]
    linarith
  linarith
private lemma gl2a4_E_four {θ : ℤ} (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) {β : ℝ} (h1 : 1 / 2 ≤ β) (h2 : β < 1) :
    0 ≤ Emain θ β 4 ∧ Emain θ β 4 ≤ 6 := by
  have e : (4:ℝ) ^ ((1:ℝ) / 2) = 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hlo : (2:ℝ) ≤ (4:ℝ) ^ β := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) h1
    linarith
  have hhi : (4:ℝ) ^ β ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) h2.le
    rwa [Real.rpow_one] at h
  have hl4 : 0 ≤ Li 4 := by
    have := gl2a4_Li_mono (a := 2) (b := 4) (by norm_num) (by norm_num)
    rwa [gl2a4_Li_two] at this
  have hl4b : Li 4 ≤ 3 := gl2a4_Li_four
  have hlb0 : 0 ≤ Li ((4:ℝ) ^ β) := by
    have := gl2a4_Li_mono (a := 2) (by norm_num) hlo
    rwa [gl2a4_Li_two] at this
  have hlb1 : Li ((4:ℝ) ^ β) ≤ Li 4 := gl2a4_Li_mono (by linarith) hhi
  unfold Emain
  rcases hθ with rfl | rfl | rfl
  · rw [show ((-1:ℤ):ℝ) = -1 by norm_num]
    constructor <;> linarith
  · rw [show ((0:ℤ):ℝ) = 0 by norm_num]
    constructor <;> linarith
  · rw [show ((1:ℤ):ℝ) = 1 by norm_num]
    constructor <;> linarith
private lemma Li_le_three_mul_div_log {Y : ℝ} (hY : 1296 ≤ Y) : Li Y ≤ 3 * Y / Real.log Y := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt Y := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg Y
  have hs2 : s ^ 2 = Y := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs36 : 36 ≤ s := by nlinarith
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt s := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg s
  have hr2 : r ^ 2 = s := by rw [hr]; exact Real.sq_sqrt hs0
  have hr6 : 6 ≤ r := by nlinarith
  have hrpos : 0 < r := by linarith
  have hlogs : Real.log s = 2 * Real.log r := by
    rw [← hr2, Real.log_pow]
    norm_num
  have hlogr : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hrpos
  have hLpos : 0 < Real.log s := Real.log_pos (by linarith)
  have hLY : Real.log Y = 2 * Real.log s := by
    rw [← hs2, Real.log_pow]
    norm_num
  have hl2 : (2:ℝ) / 3 < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this
    linarith
  have hl2pos : 0 < Real.log 2 := by linarith
  have h1 := gl2a4_Li_sub_le (a := s) (b := Y) (by linarith) (by nlinarith)
  have h2 := gl2a4_Li_sub_le (a := 2) (b := s) (by norm_num) (by linarith)
  rw [gl2a4_Li_two] at h2
  have hkey' : 2 * (2 * Real.log r) ≤ r ^ 2 * Real.log 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r - 6) (by linarith : (0:ℝ) ≤ r - 6),
      mul_le_mul_of_nonneg_left hl2.le (sq_nonneg r)]
  have hkey : 2 * Real.log s ≤ s * Real.log 2 := by
    rw [hlogs, ← hr2]
    exact hkey'
  have hA : (s - 2) / Real.log 2 ≤ s ^ 2 / (2 * Real.log s) := by
    rw [div_le_div_iff₀ hl2pos (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hs0]
  have hB : (Y - s) / Real.log s ≤ s ^ 2 / Real.log s :=
    div_le_div_of_nonneg_right (by linarith) hLpos.le
  have hC : s ^ 2 / Real.log s + s ^ 2 / (2 * Real.log s) = 3 * s ^ 2 / (2 * Real.log s) := by
    ring
  have hD : 3 * Y / Real.log Y = 3 * s ^ 2 / (2 * Real.log s) := by
    rw [hLY, hs2]
  rw [hD]
  linarith
private lemma gl2a4_weight_nonneg {θ : ℤ} (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) {β t : ℝ} (hβ : β < 1)
    (ht : 1 ≤ t) : 0 ≤ 1 - θ * t ^ (β - 1) := by
  have h0 : 0 ≤ t ^ (β - 1) := Real.rpow_nonneg (by linarith) _
  have h1 : t ^ (β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by linarith)
  rcases hθ with rfl | rfl | rfl
  · rw [show ((-1:ℤ):ℝ) = -1 by norm_num]
    linarith
  · rw [show ((0:ℤ):ℝ) = 0 by norm_num]
    linarith
  · rw [show ((1:ℤ):ℝ) = 1 by norm_num]
    linarith
private lemma gl2a4_weight {θ : ℤ} (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) {β B Z : ℝ} (hβ : β < 1) (hB : 1 ≤ B)
    (hZ : 1 ≤ Z) (hd : θ = 1 → 1 / B ^ 2 ≤ (1 - β) * Real.log Z) :
    ∃ W : ℝ, 1 / (2 * B ^ 2) ≤ W ∧ W ≤ 1 ∧ (∀ t, Z ≤ t → W ≤ 1 - θ * t ^ (β - 1)) ∧
      (∀ t, 1 ≤ t → t ≤ Z ^ 2 → 1 - θ * t ^ (β - 1) ≤ 2 * W) := by
  have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hB2pos : 0 < B ^ 2 := by linarith
  have hhalf : 1 / (2 * B ^ 2) ≤ 1 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hZ0 : 0 < Z := by linarith
  have hexp0 : β - 1 ≤ 0 := by linarith
  rcases hθ with rfl | rfl | rfl
  · refine ⟨1, hhalf, le_rfl, ?_, ?_⟩
    · intro t ht
      have : 0 ≤ t ^ (β - 1) := Real.rpow_nonneg (by linarith) _
      rw [show ((-1:ℤ):ℝ) = -1 by norm_num]
      linarith
    · intro t ht1 _
      have : t ^ (β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 hexp0
      rw [show ((-1:ℤ):ℝ) = -1 by norm_num]
      linarith
  · refine ⟨1, hhalf, le_rfl, ?_, ?_⟩
    · intro t _
      rw [show ((0:ℤ):ℝ) = 0 by norm_num]
      linarith
    · intro t _ _
      rw [show ((0:ℤ):ℝ) = 0 by norm_num]
      linarith
  · have hd' := hd rfl
    obtain ⟨x, hx⟩ : ∃ x, x = (1 - β) * Real.log Z := ⟨_, rfl⟩
    rw [← hx] at hd'
    have hx0 : 0 ≤ x := le_trans (by positivity) hd'
    have hZe : Z ^ (β - 1) = Real.exp (-x) := by
      rw [Real.rpow_def_of_pos hZ0, hx]
      congr 1
      ring
    have h3 : 0 ≤ Z ^ (β - 1) := Real.rpow_nonneg hZ0.le _
    have h4 : Z ^ (β - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ hexp0
    refine ⟨1 - Z ^ (β - 1), ?_, ?_, ?_, ?_⟩
    · rw [hZe]
      have e1 := Real.add_one_le_exp x
      have e2 : Real.exp (-x) * Real.exp x = 1 := by
        rw [← Real.exp_add]
        simp
      have e3 : 0 < Real.exp (-x) := Real.exp_pos _
      have e4 : Real.exp (-x) * (x + 1) ≤ 1 := by
        nlinarith [mul_le_mul_of_nonneg_left e1 e3.le]
      have e5 : 1 ≤ x * B ^ 2 := by rwa [div_le_iff₀ hB2pos] at hd'
      have hy : x ≤ (1 - Real.exp (-x)) * (1 + x) := by nlinarith
      have hBx : x ≤ x * B ^ 2 := le_mul_of_one_le_right hx0 hB2
      have key : 1 * (1 + x) ≤ (1 - Real.exp (-x)) * (2 * B ^ 2) * (1 + x) := by
        nlinarith [mul_le_mul_of_nonneg_left hy (by linarith : (0:ℝ) ≤ 2 * B ^ 2)]
      have key2 := le_of_mul_le_mul_right key (by linarith : (0:ℝ) < 1 + x)
      rw [div_le_iff₀ (by linarith)]
      linarith
    · linarith
    · intro t ht
      have : t ^ (β - 1) ≤ Z ^ (β - 1) := Real.rpow_le_rpow_of_nonpos hZ0 ht hexp0
      rw [show ((1:ℤ):ℝ) = 1 by norm_num]
      linarith
    · intro t ht1 ht2
      have g1 : (Z ^ 2) ^ (β - 1) ≤ t ^ (β - 1) := Real.rpow_le_rpow_of_nonpos (by linarith) ht2 hexp0
      have g2 : (Z ^ 2) ^ (β - 1) = Z ^ (β - 1) * Z ^ (β - 1) := by
        rw [sq, Real.mul_rpow hZ0.le hZ0.le]
      rw [show ((1:ℤ):ℝ) = 1 by norm_num]
      nlinarith [mul_self_nonneg (1 - Z ^ (β - 1))]
private lemma gl2a4_E_nonneg {θ : ℤ} (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) {β Y : ℝ} (h1 : 1 / 2 ≤ β)
    (h2 : β < 1) (hY : 4 ≤ Y) : 0 ≤ Emain θ β Y := by
  have h4 := (gl2a4_E_four hθ h1 h2).1
  have hβ0 : 0 < β := by linarith
  have hmono := gl2a4_le_of_deriv (f := Emain θ β)
    (f' := fun x => (1 - (θ:ℝ) * x ^ (β - 1)) / Real.log x) hY
    (fun x hx => gl2a4_E_deriv θ hβ0 (by linarith [hx.1] : (1:ℝ) < x))
    (fun x hx => by
      show 0 ≤ (1 - (θ:ℝ) * x ^ (β - 1)) / Real.log x
      exact div_nonneg (gl2a4_weight_nonneg hθ h2 (by linarith [hx.1]))
        (Real.log_nonneg (by linarith [hx.1])))
  linarith
private lemma gl2a4_rho_mono {C c B X X' : ℝ} (hC : 0 < C) (hc : 0 < c) (hB : 1 < B) (hX : 1 ≤ X)
    (h : X ≤ X') : rhoErr C c B X' ≤ rhoErr C c B X := by
  unfold rhoErr
  have hX0 : 0 < X := by linarith
  have hlogle : Real.log X ≤ Real.log X' := Real.log_le_log hX0 h
  have hlogB : 0 < Real.log B := Real.log_pos hB
  have e1 : Real.exp (-c * Real.log X' / Real.log B) ≤ Real.exp (-c * Real.log X / Real.log B) := by
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ hlogB.le
    nlinarith [mul_le_mul_of_nonneg_left hlogle hc.le]
  have e2 : Real.exp (-c * Real.sqrt (Real.log X')) ≤ Real.exp (-c * Real.sqrt (Real.log X)) := by
    apply Real.exp_le_exp.mpr
    have := Real.sqrt_le_sqrt hlogle
    nlinarith [mul_le_mul_of_nonneg_left this hc.le]
  nlinarith [mul_le_mul_of_nonneg_left e1 hC.le, mul_le_mul_of_nonneg_left e2 hC.le]
private lemma gl2a4_root {B X : ℝ} (hB : 4 ≤ B) (hX : B ^ (60 : ℝ) ≤ X) :
    ∃ u : ℝ, 1024 ≤ u ∧ u ^ 12 = X ∧ Real.sqrt X = u ^ 6 ∧ X ^ ((1 : ℝ) / 3) = u ^ 4 ∧
      Real.log X ≤ 12 * u := by
  have e60 : B ^ (60 : ℝ) = B ^ (60 : ℕ) := by exact_mod_cast Real.rpow_natCast B 60
  rw [e60] at hX
  have hB60 : (4:ℝ) ^ 60 ≤ B ^ 60 := pow_le_pow_left₀ (by norm_num) hB 60
  have hpos : (0:ℝ) < 4 ^ 60 := by norm_num
  have hX0 : 0 < X := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = X ^ ((1:ℝ) / 12) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; exact Real.rpow_nonneg hX0.le _
  have hu12 : u ^ 12 = X := by
    rw [hu, show (1:ℝ) / 12 = ((12:ℕ):ℝ)⁻¹ by norm_num]
    exact Real.rpow_inv_natCast_pow hX0.le (by norm_num)
  have hu1024 : 1024 ≤ u := by
    apply le_of_pow_le_pow_left₀ (n := 12) (by norm_num) hu0
    rw [hu12]
    have e : (1024:ℝ) ^ 12 = 4 ^ 60 := by norm_num
    linarith
  refine ⟨u, hu1024, hu12, ?_, ?_, ?_⟩
  · rw [← hu12, show u ^ 12 = (u ^ 6) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  · rw [← hu12, show u ^ 12 = (u ^ 4) ^ 3 by ring, show (1:ℝ) / 3 = ((3:ℕ):ℝ)⁻¹ by norm_num]
    exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  · have hl := Real.log_le_sub_one_of_pos (show 0 < u by linarith)
    have e : Real.log X = 12 * Real.log u := by
      rw [← hu12, Real.log_pow]
      norm_num
    linarith
private lemma Emain_lower_bound {B β X : ℝ} {θ : ℤ} (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) (hB : 4 ≤ B)
    (hβ1 : 1 / 2 ≤ β) (hβ2 : β < 1) (hd : θ = 1 → 2 / B ^ 2 ≤ (1 - β) * Real.log X)
    (hX : B ^ (60 : ℝ) ≤ X) :
    1 / 100 * B ^ (-5 : ℝ) * X / Real.log X ≤ Emain θ β X := by
  obtain ⟨u, hu, hu12, -, -, -⟩ := gl2a4_root hB hX
  have hB0 : 0 < B := by linarith
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hβ0 : 0 < β := by linarith
  have hu6 : 1024 ≤ u ^ 6 := le_trans hu (le_self_pow₀ hu1 (by norm_num))
  have hXeq : X = u ^ 6 * u ^ 6 := by rw [← hu12]; ring
  have hX0 : 0 < X := by rw [← hu12]; exact pow_pos hu0 12
  have hv2 : u ^ 6 ≤ X / 2 := by
    rw [hXeq]
    linarith [mul_le_mul_of_nonneg_left hu6 (by positivity : (0:ℝ) ≤ u ^ 6)]
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have hlogX : Real.log X = 12 * Real.log u := by
    rw [← hu12, Real.log_pow]
    norm_num
  have hlogv : Real.log (u ^ 6) = 6 * Real.log u := by
    rw [Real.log_pow]
    norm_num
  have hdZ : θ = 1 → 1 / B ^ 2 ≤ (1 - β) * Real.log (u ^ 6) := by
    intro h1
    have h2 := hd h1
    rw [hlogX] at h2
    rw [hlogv]
    have e : 2 / B ^ 2 = 2 * (1 / B ^ 2) := by ring
    linarith
  obtain ⟨W, hW1, hW2, hWlo, -⟩ :=
    gl2a4_weight hθ hβ2 (by linarith : (1:ℝ) ≤ B) (by linarith : (1:ℝ) ≤ u ^ 6) hdZ
  have hW0 : 0 ≤ W := le_trans (by positivity) hW1
  have hdiff := gl2a4_E_lower θ hβ0 (by linarith : (1:ℝ) < u ^ 6)
    (by linarith : u ^ 6 ≤ X) hW0 (fun t ht _ => hWlo t ht)
  have hMv := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith : (4:ℝ) ≤ u ^ 6)
  obtain ⟨q, hq⟩ : ∃ q, q = X / Real.log X := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have e5 : B ^ (5 : ℝ) = B ^ (5 : ℕ) := by exact_mod_cast Real.rpow_natCast B 5
  have hT : 1 / 100 * B ^ (-5 : ℝ) * X / Real.log X = q / (100 * B ^ 5) := by
    rw [Real.rpow_neg hB0.le, e5, hq]
    ring
  have h1 : W * (X / 2) / Real.log X ≤ W * (X - u ^ 6) / Real.log X :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hW0) hL.le
  have h2 : W * (X / 2) / Real.log X = W * q / 2 := by
    rw [hq]
    ring
  have h3 : 1 / (2 * B ^ 2) * q ≤ W * q := mul_le_mul_of_nonneg_right hW1 hq0
  have h4 : q / (100 * B ^ 5) ≤ 1 / (2 * B ^ 2) * q / 2 := by
    have hB3 : 1 ≤ B ^ 3 := one_le_pow₀ (by linarith)
    have e : 1 / (2 * B ^ 2) * q / 2 = q / (4 * B ^ 2) := by ring
    rw [e]
    exact div_le_div_of_nonneg_left hq0 (by positivity)
      (by nlinarith [mul_le_mul_of_nonneg_left hB3 (by positivity : (0:ℝ) ≤ B ^ 2), sq_nonneg B])
  rw [hT]
  linarith
set_option maxHeartbeats 1000000 in
private lemma gl2a4_claim2 {Cr cr B G β X : ℝ} {θ : ℤ} {π₁ π₂ : ℝ → ℕ} (hCr : 0 < Cr) (hcr : 0 < cr)
    (hθ : θ = -1 ∨ θ = 0 ∨ θ = 1) (hB : 4 ≤ B) (hG1 : 1 ≤ G) (hGB : G ≤ B)
    (hβ1 : 1 / 2 ≤ β) (hβ2 : β < 1) (hd : θ = 1 → 2 / B ^ 2 ≤ (1 - β) * Real.log X)
    (hX : B ^ (60 : ℝ) ≤ X)
    (hπ₂ : ∀ Y : ℝ, 1 ≤ Y → (π₂ Y : ℝ) ≤ 2 * Real.sqrt Y)
    (hQ : ∀ Y : ℝ, X ≤ Y →
      |G * ((π₁ Y : ℝ) + π₂ Y) - Emain θ β Y| ≤ rhoErr Cr cr B Y * Emain θ β Y)
    {h : ℝ} (hh1 : h ≤ 1) (hρ : rhoErr Cr cr B X ≤ h / 100) (hB7 : B ^ (7 : ℝ) ≤ h * X ^ ((1 : ℝ) / 3)) :
    1 / 100 * h * B ^ (-6 : ℝ) * X / Real.log X ≤ (π₁ (X * (1 + h)) : ℝ) - π₁ X := by
  obtain ⟨u, hu, hu12, -, hcube, hlogu⟩ := gl2a4_root hB hX
  have hB0 : 0 < B := by linarith
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hβ0 : 0 < β := by linarith
  have hG0 : 0 < G := by linarith
  have hXu : u ^ 2 ≤ X := by rw [← hu12]; exact pow_le_pow_right₀ hu1 (by norm_num)
  have hX1296 : 1296 ≤ X := by nlinarith only [hXu, hu]
  have hX0 : 0 < X := by linarith
  have hX1 : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  have e7 : B ^ (7 : ℝ) = B ^ (7 : ℕ) := by exact_mod_cast Real.rpow_natCast B 7
  rw [e7, hcube] at hB7
  have hh : 0 < h := by nlinarith only [hB7, pow_pos hB0 7, pow_pos hu0 4]
  obtain ⟨X', hX'⟩ : ∃ X', X' = X * (1 + h) := ⟨_, rfl⟩
  rw [← hX']
  have hXX' : X ≤ X' := by rw [hX']; linarith [mul_pos hX0 hh]
  have hX'2 : X' ≤ 2 * X := by rw [hX']; linarith [mul_le_mul_of_nonneg_left hh1 hX0.le]
  have hX'0 : 0 < X' := by linarith
  have hρ' : rhoErr Cr cr B X' ≤ rhoErr Cr cr B X :=
    gl2a4_rho_mono hCr hcr (by linarith) hX1.le hXX'
  have hMX : 0 ≤ Emain θ β X := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith)
  have hMX' : 0 ≤ Emain θ β X' := gl2a4_E_nonneg hθ hβ1 hβ2 (by linarith)
  have hQX := abs_le.mp (hQ X le_rfl)
  have hQX' := abs_le.mp (hQ X' hXX')
  have hE1 : rhoErr Cr cr B X' * Emain θ β X' ≤ h / 100 * Emain θ β X' :=
    mul_le_mul_of_nonneg_right (le_trans hρ' hρ) hMX'
  have hE2 : rhoErr Cr cr B X * Emain θ β X ≤ h / 100 * Emain θ β X :=
    mul_le_mul_of_nonneg_right hρ hMX
  have hπX : 0 ≤ G * (π₂ X : ℝ) := mul_nonneg hG0.le (Nat.cast_nonneg _)
  have hsqX' : Real.sqrt X' ≤ 2 * u ^ 6 := by
    rw [Real.sqrt_le_left (by positivity)]
    linarith [hu12]
  have hπX' : G * (π₂ X' : ℝ) ≤ B * (4 * u ^ 6) := by
    have h1 := hπ₂ X' (by linarith)
    exact mul_le_mul hGB (by linarith) (Nat.cast_nonneg _) hB0.le
  have hu8 : 1 ≤ u ^ 8 := one_le_pow₀ hu1
  have hlogX : Real.log X = 12 * Real.log u := by
    rw [← hu12, Real.log_pow]
    norm_num
  have hlogZ : Real.log (u ^ 8) = 8 * Real.log u := by
    rw [Real.log_pow]
    norm_num
  have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hdZ : θ = 1 → 1 / B ^ 2 ≤ (1 - β) * Real.log (u ^ 8) := by
    intro h1
    have h2 := hd h1
    rw [hlogX] at h2
    rw [hlogZ]
    have e : 2 / B ^ 2 = 2 * (1 / B ^ 2) := by ring
    have h3 : 0 ≤ 1 / B ^ 2 := by positivity
    linarith
  obtain ⟨W, hW1, hW2, hWlo, hWhi⟩ :=
    gl2a4_weight hθ hβ2 (by linarith : (1:ℝ) ≤ B) hu8 hdZ
  have hW0 : 0 ≤ W := le_trans (by positivity) hW1
  have hu8X : u ^ 8 ≤ X := by rw [← hu12]; exact pow_le_pow_right₀ hu1 (by norm_num)
  have hu4 : 2 ≤ u ^ 4 := by linarith [le_self_pow₀ hu1 (by norm_num : (4:ℕ) ≠ 0)]
  have hZ2 : X' ≤ (u ^ 8) ^ 2 := by
    have e : (u ^ 8) ^ 2 = u ^ 12 * u ^ 4 := by ring
    rw [e, hu12]
    linarith [mul_le_mul_of_nonneg_left hu4 hX0.le]
  have hdiff := gl2a4_E_lower θ hβ0 hX1 hXX' hW0
    (fun t ht _ => hWlo t (le_trans hu8X ht))
  have hli4 : 0 ≤ Li 4 := by
    have := gl2a4_Li_mono (a := 2) (b := 4) (by norm_num) (by norm_num)
    rwa [gl2a4_Li_two] at this
  have h4 := (gl2a4_E_four hθ hβ1 hβ2).2
  have hupper : ∀ Y : ℝ, 1296 ≤ Y → Y ≤ X' →
      Emain θ β Y ≤ 6 + 2 * W * (3 * Y / Real.log Y) := by
    intro Y hY1 hY2
    have h8 := gl2a4_E_upper θ (V := 2 * W) hβ0 (by norm_num : (1:ℝ) < 4)
      (by linarith : (4:ℝ) ≤ Y) (fun t ht1 ht2 => hWhi t (by linarith) (by linarith))
    have hliY := Li_le_three_mul_div_log hY1
    have h9 : 2 * W * (Li Y - Li 4) ≤ 2 * W * (3 * Y / Real.log Y) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hMXu := hupper X hX1296 hXX'
  have hMX'u := hupper X' (by linarith) le_rfl
  obtain ⟨q, hq⟩ : ∃ q, q = X / Real.log X := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have hlogX' : Real.log X ≤ Real.log X' := Real.log_le_log hX0 hXX'
  have hlogX'2 : Real.log X' ≤ 2 * Real.log X := by
    have h1 : Real.log X' ≤ Real.log (X ^ 2) := Real.log_le_log hX'0 (by nlinarith only [hX'2, hX1296, mul_le_mul_of_nonneg_left hX1296 hX0.le])
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL' : 0 < Real.log X' := by linarith
  have h3X' : 3 * X' / Real.log X' ≤ 6 * q := by
    have h1 : 3 * X' / Real.log X' ≤ 6 * X / Real.log X :=
      div_le_div₀ (by positivity) (by linarith) hL hlogX'
    have h2 : 6 * X / Real.log X = 6 * q := by rw [hq]; ring
    linarith
  have h3X : 3 * X / Real.log X = 3 * q := by rw [hq]; ring
  have hmain : W * h * q / 2 ≤ W * (X' - X) / Real.log X' := by
    have e1 : W * (X' - X) = W * h * X := by rw [hX']; ring
    have e2 : W * h * q / 2 = W * h * X / (2 * Real.log X) := by rw [hq]; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_left (by positivity) hL' hlogX'2
  have hMX'b : h / 100 * Emain θ β X' ≤ h / 100 * (6 + 2 * W * (6 * q)) := by
    have h1 := mul_le_mul_of_nonneg_left h3X' (by positivity : (0:ℝ) ≤ 2 * W)
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hMXb : h / 100 * Emain θ β X ≤ h / 100 * (6 + 2 * W * (3 * q)) := by
    rw [← h3X]
    exact mul_le_mul_of_nonneg_left hMXu (by positivity)
  have hGD : W * h * q / 2 - h / 100 * (12 + 18 * W * q) - B * (4 * u ^ 6) ≤
      G * ((π₁ X' : ℝ) - π₁ X) := by
    linarith [hQX.2, hQX'.1]
  obtain ⟨s, hs⟩ : ∃ s, s = h * q / B ^ 2 := ⟨_, rfl⟩
  have hB2 : 0 < B ^ 2 := by positivity
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hWs : s / 2 ≤ W * h * q := by
    have h1 := mul_le_mul_of_nonneg_right hW1 (by positivity : (0:ℝ) ≤ h * q)
    have e : 1 / (2 * B ^ 2) * (h * q) = s / 2 := by rw [hs]; ring
    linarith
  have hqL : q * Real.log X = X := by rw [hq]; exact div_mul_cancel₀ X hL.ne'
  have hXq : X ≤ q * (12 * u) := by
    calc X = q * Real.log X := hqL.symm
      _ ≤ q * (12 * u) := mul_le_mul_of_nonneg_left hlogu hq0
  have hbig1 : B ^ 7 * u ^ 8 ≤ h * X := by
    rw [← hu12]
    linarith [mul_le_mul_of_nonneg_right hB7 (pow_pos hu0 8).le]
  have hbig2 : B ^ 7 * u ^ 7 ≤ 12 * (h * q) := by
    have h1 : h * X ≤ h * (q * (12 * u)) := mul_le_mul_of_nonneg_left hXq hh.le
    have h2 : (B ^ 7 * u ^ 7) * u ≤ (12 * (h * q)) * u := by linarith
    exact le_of_mul_le_mul_right h2 hu0
  have hs_big : B ^ 5 * u ^ 7 ≤ 12 * s := by
    have e : 12 * s = 12 * (h * q) / B ^ 2 := by rw [hs]; ring
    rw [e, le_div_iff₀ hB2]
    linarith
  have hB4 : 256 ≤ B ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) hB 4
    norm_num at this
    linarith
  have hB4u : 262144 ≤ B ^ 4 * u := by nlinarith only [hB4, hu]
  have hBu6 : 1 ≤ B * u ^ 6 := by
    have := one_le_pow₀ (n := 6) hu1
    nlinarith only [this, hB]
  have hbig : 400 * (B * u ^ 6) + 12 ≤ B ^ 5 * u ^ 7 := by
    have e : B ^ 5 * u ^ 7 = (B * u ^ 6) * (B ^ 4 * u) := by ring
    rw [e]
    linarith [mul_le_mul_of_nonneg_left hB4u (by linarith : (0:ℝ) ≤ B * u ^ 6)]
  have e6 : B ^ (6 : ℝ) = B ^ (6 : ℕ) := by exact_mod_cast Real.rpow_natCast B 6
  have hT : 1 / 100 * h * B ^ (-6 : ℝ) * X / Real.log X = h * q / (100 * B ^ 6) := by
    rw [Real.rpow_neg hB0.le, e6, hq]
    ring
  rw [hT]
  have hT0 : 0 ≤ h * q / (100 * B ^ 6) := by positivity
  have hBT : B * (h * q / (100 * B ^ 6)) ≤ s / 100 := by
    have e : s / 100 = h * q / (100 * B ^ 2) := by rw [hs]; ring
    rw [e, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have hB36 : B ^ 3 ≤ B ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hhq : 0 ≤ h * q := by positivity
    linarith [mul_le_mul_of_nonneg_left hB36 (by positivity : (0:ℝ) ≤ 100 * (h * q))]
  have hGT := mul_le_mul_of_nonneg_right hGB hT0
  have hfinal : G * (h * q / (100 * B ^ 6)) ≤ G * ((π₁ X' : ℝ) - π₁ X) := by
    linarith
  exact le_of_mul_le_mul_left hfinal hG0
end Formalism.HermitianLattices.GL2PrimeSums
end
end
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset NumberField
open Formalism.LogVandermondeBounds.StandardLattice
section alg
variable (K : Type) [Field K] [NumberField K]
private lemma maximal_ideal_ne_bot (P : Ideal (𝓞 K)) (hP : P.IsMaximal) : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField K)
private lemma residue_characteristic_prime (P : Ideal (𝓞 K)) (hP : P.IsMaximal) : (residueCharacteristic K P).Prime := by
  haveI : P.IsMaximal := hP
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
    exact maximal_ideal_ne_bot K P hP)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  letI := Ideal.Quotient.field P
  unfold residueCharacteristic
  exact (CharP.char_is_prime_or_zero (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P))).resolve_right
    (CharP.char_ne_zero_of_finite (𝓞 K ⧸ P) (ringChar (𝓞 K ⧸ P)))
private lemma residue_characteristic_mem (P : Ideal (𝓞 K)) : ((residueCharacteristic K P : ℕ) : 𝓞 K) ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.Nat.cast_ringChar
private lemma prod_norm_dvd_prime_pow_degree (p : ℕ) (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ P ∈ T, P.IsMaximal ∧ (p : 𝓞 K) ∈ P) :
    ∏ P ∈ T, Ideal.absNorm P ∣ p ^ Module.finrank ℚ K := by
  classical
  have hdvd : (∏ P ∈ T, P) ∣ Ideal.span {(p : 𝓞 K)} := by
    apply Finset.prod_dvd_of_coprime
    · intro P hP Q hQ hPQ
      exact Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne (hT P hP).1 (hT Q hQ).1 hPQ)
    · intro P hP
      try dsimp only
      rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
      exact (hT P hP).2
  have h3 : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ Module.finrank ℚ K := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have := map_dvd Ideal.absNorm hdvd
  rwa [map_prod, h3] at this
private lemma abs_norm_eq_prime_pow (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    ∃ k, 1 ≤ k ∧ Ideal.absNorm P = residueCharacteristic K P ^ k := by
  haveI : P.IsMaximal := hP
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
    exact maximal_ideal_ne_bot K P hP)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  haveI : CharP (𝓞 K ⧸ P) (residueCharacteristic K P) := ringChar.charP _
  obtain ⟨n, -, hn⟩ := FiniteField.card (𝓞 K ⧸ P) (residueCharacteristic K P)
  refine ⟨n, n.one_le, ?_⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card, hn]
private lemma exists_int_congruent_mod_prime (P : Ideal (𝓞 K)) (p : ℕ) (hp : p.Prime) (hN : Ideal.absNorm P = p)
    (x : 𝓞 K) : ∃ n : ℤ, x - (n : 𝓞 K) ∈ P := by
  have hne : P ≠ ⊥ := by
    intro h; rw [h, Ideal.absNorm_bot] at hN; exact hp.ne_zero hN.symm
  have hPr : P.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hN]; exact hp)
  have hM : P.IsMaximal := hPr.isMaximal hne
  obtain ⟨k, hk1, hk⟩ := abs_norm_eq_prime_pow K P hM
  rw [hN] at hk
  have hpr : residueCharacteristic K P = p := ((Nat.Prime.pow_eq_iff hp).mp hk.symm).1
  haveI : CharP (𝓞 K ⧸ P) p := by rw [← hpr]; exact ringChar.charP _
  haveI : Fact p.Prime := ⟨hp⟩
  letI := Ideal.Quotient.field P
  haveI : Finite (𝓞 K ⧸ P) := Nat.finite_of_card_ne_zero (by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ne, Ideal.absNorm_eq_zero_iff]
    exact hne)
  letI : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hinj : Function.Injective (ZMod.castHom (dvd_refl p) (𝓞 K ⧸ P)) :=
    (ZMod.castHom (dvd_refl p) (𝓞 K ⧸ P)).injective
  have hcard : Nat.card (𝓞 K ⧸ P) ≤ Nat.card (ZMod p) := by
    rw [Nat.card_zmod, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
  obtain ⟨z, hz⟩ := (hinj.bijective_of_nat_card_le hcard).2 (Ideal.Quotient.mk P x)
  refine ⟨(z.val : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hz, map_intCast, Int.cast_natCast, ZMod.castHom_apply,
    ZMod.natCast_val, sub_self]
variable [StarRing K]
private lemma inert_prime_norm_ge_sq (P : Ideal (𝓞 K)) (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P)
    (hu : ∃ θ t : 𝓞 K, algebraMap (𝓞 K) K t = star (algebraMap (𝓞 K) K θ) ∧ θ - t ∉ P) :
    residueCharacteristic K P ^ 2 ≤ Ideal.absNorm P := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨θ, t, ht, hθt⟩ := hu
  obtain ⟨k, hk1, hk⟩ := abs_norm_eq_prime_pow K P hP
  have hp := residue_characteristic_prime K P hP
  have hk2 : k = 1 := by
    by_contra hne
    have h2k : 2 ≤ k := by omega
    have := Nat.pow_le_pow_right hp.pos h2k
    rw [← hk] at this
    exact absurd this (not_le.mpr hlt)
  rw [hk2, pow_one] at hk
  obtain ⟨n, hn⟩ := exists_int_congruent_mod_prime K P _ hp hk θ
  apply hθt
  have h2 : t - (n : 𝓞 K) ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by
    apply Ideal.subset_span
    refine ⟨θ - n, hn, ?_⟩
    rw [map_sub, map_sub, ht, star_sub, map_intCast, star_intCast]
  rw [hc] at h2
  have := P.sub_mem hn h2
  rwa [sub_sub_sub_cancel_right] at this
end alg
section ana
private lemma summable_inv_pow_real (M : ℕ) (hM : 2 ≤ M) : Summable (fun n : ℕ => ((n : ℝ)⁻¹) ^ M) := by
  have := Real.summable_nat_pow_inv.mpr (by omega : 1 < M)
  simpa [inv_pow] using this
private lemma tsum_inv_pow_eq_zeta_real (M : ℕ) (hM : 2 ≤ M) : ∑' n : ℕ, ((n : ℝ)⁻¹) ^ M = zetaR M := by
  rw [(summable_inv_pow_real M hM).tsum_eq_zero_add]
  rw [Nat.cast_zero, inv_zero, zero_pow (by omega), zero_add]
  show _ = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ M
  congr 1
  ext n
  push_cast
  rw [one_div, inv_pow]
private lemma inv_prime_pow_lt_one' (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) :
    ((p : ℝ)⁻¹) ^ M < 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  exact pow_lt_one₀ (by positivity) h1 (by omega)
private lemma euler_product_le_zeta (M : ℕ) (hM : 2 ≤ M) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹ ≤ zetaR M := by
  classical
  have hfv : ∀ n : ℕ, invPowMonoidHomReal M n = ((n : ℝ)⁻¹) ^ M := fun n => rfl
  set N := S.sup id + 1 with hNdef
  have hsub : S ⊆ N.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨Nat.lt_succ_of_le (Finset.le_sup (f := id) hp), hS p hp⟩
  have hf : ∀ {p : ℕ}, p.Prime → ‖invPowMonoidHomReal M p‖ < 1 := by
    intro p hp
    rw [hfv, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact inv_prime_pow_lt_one' M (by omega) p hp
  obtain ⟨-, hhs⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf N
  have hsum : Summable (fun n : ℕ => invPowMonoidHomReal M n) := by
    simp only [hfv]; exact summable_inv_pow_real M hM
  have key : ∏ p ∈ N.primesBelow, (1 - invPowMonoidHomReal M p)⁻¹ ≤ ∑' n : ℕ, invPowMonoidHomReal M n := by
    rw [← hhs.tsum_eq]
    exact Summable.tsum_subtype_le (fun n : ℕ => invPowMonoidHomReal M n) _ (fun n => by rw [hfv]; positivity) hsum
  have hfac : ∀ p ∈ N.primesBelow, 1 ≤ (1 - invPowMonoidHomReal M p)⁻¹ := by
    intro p hp
    have hp' := (Nat.mem_primesBelow.mp hp).2
    have h1 := inv_prime_pow_lt_one' M (by omega) p hp'
    have h0 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
    rw [hfv]
    exact (one_le_inv₀ (by linarith)).mpr (by linarith)
  have hsplit := Finset.prod_sdiff hsub (f := fun p => (1 - invPowMonoidHomReal M p)⁻¹)
  have hrest : 1 ≤ ∏ p ∈ N.primesBelow \ S, (1 - invPowMonoidHomReal M p)⁻¹ :=
    Finset.prod_induction _ (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl (fun p hp => hfac p (Finset.sdiff_subset hp))
  have hSpos : 0 ≤ ∏ p ∈ S, (1 - invPowMonoidHomReal M p)⁻¹ :=
    Finset.prod_nonneg (fun p hp => by linarith [hfac p (hsub hp)])
  calc ∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹ = ∏ p ∈ S, (1 - invPowMonoidHomReal M p)⁻¹ := rfl
    _ ≤ (∏ p ∈ N.primesBelow \ S, (1 - invPowMonoidHomReal M p)⁻¹) * ∏ p ∈ S, (1 - invPowMonoidHomReal M p)⁻¹ :=
        le_mul_of_one_le_left hSpos hrest
    _ = ∏ p ∈ N.primesBelow, (1 - invPowMonoidHomReal M p)⁻¹ := hsplit
    _ ≤ ∑' n : ℕ, invPowMonoidHomReal M n := key
    _ = zetaR M := by simp only [hfv]; exact tsum_inv_pow_eq_zeta_real M hM
private lemma inv_prime_pow_lt_one (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) : ((p : ℝ)⁻¹) ^ M < 1 := by
  exact inv_prime_pow_lt_one' M hM p hp
private lemma neg_log_one_sub_inv_pow_nonneg (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) : 0 ≤ negLogOneSubInvPow M p := by
  have h := inv_prime_pow_lt_one M hM p hp
  have h0 : 0 ≤ ((p : ℝ)⁻¹) ^ M := by positivity
  unfold negLogOneSubInvPow
  have : Real.log (1 - ((p : ℝ)⁻¹) ^ M) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith
private lemma sum_neg_log_le_log_zeta (M : ℕ) (hM : 2 ≤ M) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, negLogOneSubInvPow M p ≤ Real.log (zetaR M) := by
  have hpos : ∀ p ∈ S, 0 < 1 - ((p : ℝ)⁻¹) ^ M := fun p hp => by
    linarith [inv_prime_pow_lt_one M (by omega) p (hS p hp)]
  have hsum : ∑ p ∈ S, negLogOneSubInvPow M p = Real.log (∏ p ∈ S, (1 - ((p : ℝ)⁻¹) ^ M)⁻¹) := by
    rw [Real.log_prod (fun p hp => (inv_pos.mpr (hpos p hp)).ne')]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [negLogOneSubInvPow, Real.log_inv]
  rw [hsum]
  exact Real.log_le_log (Finset.prod_pos (fun p hp => inv_pos.mpr (hpos p hp))) (euler_product_le_zeta M hM S hS)
private lemma abs_log_inv_one_sub_le_real (s y x : ℝ) (hs : s = 1 ∨ s = -1) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x < 1) :
    |Real.log ((1 - s * y)⁻¹)| ≤ -Real.log (1 - x) := by
  have hx0 : 0 < 1 - x := by linarith
  rcases hs with rfl | rfl
  · rw [one_mul, Real.log_inv, abs_neg, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
    have := Real.log_le_log hx0 (by linarith : 1 - x ≤ 1 - y)
    linarith
  · rw [neg_one_mul, sub_neg_eq_add, Real.log_inv, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by linarith))]
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + y)
    have h2 := Real.log_le_sub_one_of_pos hx0
    linarith
private lemma euler_factor_inert_prime_bound (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) (N : ℕ) (hN : p ^ 2 ≤ N) :
    0 < (1 - (-1 : ℝ) ^ M * (Real.sqrt (N : ℝ)) ^ (-(M : ℤ)))⁻¹ ∧
    |Real.log ((1 - (-1 : ℝ) ^ M * (Real.sqrt (N : ℝ)) ^ (-(M : ℤ)))⁻¹)| ≤ negLogOneSubInvPow M p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsq : (p : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hN
  have hpN : (p : ℝ) ≤ Real.sqrt (N : ℝ) := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have hzp : (Real.sqrt (N : ℝ)) ^ (-(M : ℤ)) = ((Real.sqrt (N : ℝ))⁻¹) ^ M := by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have hy0 : 0 ≤ ((Real.sqrt (N : ℝ))⁻¹) ^ M := by positivity
  have hyx : ((Real.sqrt (N : ℝ))⁻¹) ^ M ≤ ((p : ℝ)⁻¹) ^ M :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ (by linarith) hpN) M
  have hx := inv_prime_pow_lt_one M hM p hp
  have hs := neg_one_pow_eq_or ℝ M
  rw [hzp]
  refine ⟨?_, abs_log_inv_one_sub_le_real _ _ _ hs hy0 hyx hx⟩
  apply inv_pos.mpr
  rcases hs with h | h <;> rw [h] <;> linarith
private lemma euler_factor_split_prime_bound (M : ℕ) (hM : 1 ≤ M) (p : ℕ) (hp : p.Prime) (N : ℕ) (hN : p ≤ N) :
    0 < (1 - (N : ℝ) ^ (-(M : ℤ))) ^ (-(1 : ℝ) / 2) ∧
    |Real.log ((1 - (N : ℝ) ^ (-(M : ℤ))) ^ (-(1 : ℝ) / 2))| ≤ 1 / 2 * negLogOneSubInvPow M p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpN : (p : ℝ) ≤ N := by exact_mod_cast hN
  have hzp : (N : ℝ) ^ (-(M : ℤ)) = ((N : ℝ)⁻¹) ^ M := by rw [zpow_neg, zpow_natCast, inv_pow]
  rw [hzp]
  have hyx : ((N : ℝ)⁻¹) ^ M ≤ ((p : ℝ)⁻¹) ^ M :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ (by linarith) hpN) M
  have hy0 : 0 ≤ ((N : ℝ)⁻¹) ^ M := by positivity
  have hx := inv_prime_pow_lt_one M hM p hp
  have hb : 0 < 1 - ((N : ℝ)⁻¹) ^ M := by linarith
  refine ⟨Real.rpow_pos_of_pos hb _, ?_⟩
  rw [Real.log_rpow hb, abs_mul]
  have hl := abs_log_inv_one_sub_le_real 1 _ _ (Or.inl rfl) hy0 hyx hx
  rw [one_mul, Real.log_inv, abs_neg] at hl
  have h12 : |(-(1 : ℝ) / 2)| = 1 / 2 := by norm_num
  rw [h12]
  unfold negLogOneSubInvPow
  linarith
end ana
section main
variable (K : Type) [Field K] [NumberField K]
private lemma log_prime_pos (p : ℕ) (hp : p.Prime) : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
private lemma sum_weights_over_prime_le_half_degree (p : ℕ) (T : Finset {P : Ideal (𝓞 K) // P.IsMaximal})
    (hT : ∀ P ∈ T, residueCharacteristic K P.1 = p) :
    ∑ P ∈ T, idealPrimeWeight K P.1 ≤ (Module.finrank ℚ K : ℝ) / 2 := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨P0, hP0⟩
  · simp only [Finset.sum_empty]; positivity
  have hp : p.Prime := by rw [← hT P0 hP0]; exact residue_characteristic_prime K P0.1 P0.2
  have hlp := log_prime_pos p hp
  have hdvd : ∏ P ∈ T, Ideal.absNorm P.1 ∣ p ^ Module.finrank ℚ K := by
    have := prod_norm_dvd_prime_pow_degree K p (T.map (Function.Embedding.subtype _)) (by
      intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_map.mp hP
      refine ⟨Q.2, ?_⟩
      have := residue_characteristic_mem K Q.1
      rwa [hT Q hQ] at this)
    simpa [Finset.prod_map] using this
  have hpos : ∀ P ∈ T, 0 < Ideal.absNorm P.1 := fun P _ => Nat.pos_of_ne_zero (by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact maximal_ideal_ne_bot K P.1 P.2)
  have hle : ∏ P ∈ T, Ideal.absNorm P.1 ≤ p ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (pow_pos hp.pos _) hdvd
  have hlog : ∑ P ∈ T, Real.log (Ideal.absNorm P.1 : ℝ) ≤ Module.finrank ℚ K * Real.log p := by
    rw [← Real.log_prod (fun P hP => by exact_mod_cast (hpos P hP).ne'), ← Real.log_pow]
    apply Real.log_le_log (Finset.prod_pos fun P hP => by exact_mod_cast hpos P hP)
    exact_mod_cast hle
  have hlne := hlp.ne'
  calc ∑ P ∈ T, idealPrimeWeight K P.1 = ∑ P ∈ T, Real.log (Ideal.absNorm P.1 : ℝ) / (2 * Real.log p) :=
        Finset.sum_congr rfl (fun P hP => by rw [idealPrimeWeight, hT P hP])
    _ = (∑ P ∈ T, Real.log (Ideal.absNorm P.1 : ℝ)) / (2 * Real.log p) := by rw [Finset.sum_div]
    _ ≤ (Module.finrank ℚ K * Real.log p) / (2 * Real.log p) := by
        apply div_le_div_of_nonneg_right hlog; linarith
    _ = (Module.finrank ℚ K : ℝ) / 2 := by field_simp; try ring
variable [StarRing K]
private lemma euler_factor_log_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 1 ≤ M) (P : Ideal (𝓞 K))
    (hP : P.IsMaximal) :
    0 < Formalism.HermitianLatticesTheory.eulerFac K M P ∧
    |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P)| ≤ idealPrimeWeight K P * negLogOneSubInvPow M (residueCharacteristic K P) := by
  have hp := residue_characteristic_prime K P hP
  obtain ⟨k, hk1, hk⟩ := abs_norm_eq_prime_pow K P hP
  have hlp := log_prime_pos _ hp
  have hlne := hlp.ne'
  have hc : idealPrimeWeight K P = (k : ℝ) / 2 := by
    rw [idealPrimeWeight, hk, Nat.cast_pow, Real.log_pow]; field_simp; try ring
  have hg := neg_log_one_sub_inv_pow_nonneg M hM _ hp
  unfold Formalism.HermitianLatticesTheory.eulerFac
  split_ifs with hconj
  · have hN := inert_prime_norm_ge_sq K P hP hconj (hK.2.2 P hP)
    obtain ⟨h1, h2⟩ := euler_factor_inert_prime_bound M hM _ hp _ hN
    refine ⟨h1, h2.trans ?_⟩
    have hk2 : 2 ≤ k := by
      by_contra h
      have h1k : k = 1 := by omega
      rw [hk, h1k, pow_one] at hN
      have := hp.two_le
      nlinarith
    rw [hc]
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
    nlinarith
  · obtain ⟨h1, h2⟩ := euler_factor_split_prime_bound M hM _ hp (Ideal.absNorm P) (by rw [hk]; exact Nat.le_self_pow (by omega) _)
    refine ⟨h1, h2.trans ?_⟩
    rw [hc]
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    nlinarith
private lemma partial_sums_log_euler_factor_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M)
    (u : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) :
    ∑ P ∈ u, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)| ≤
      (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M) := by
  classical
  have hn : (Formalism.HermitianLatticesTheory.fDeg K : ℝ) = (Module.finrank ℚ K : ℝ) / 2 := by
    haveI := hK.1
    have h1 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero K
    unfold Formalism.HermitianLatticesTheory.fDeg
    rw [h2, ← h1, h3]; push_cast; ring
  set S := u.image (fun P => residueCharacteristic K P.1) with hSdef
  have hSp : ∀ p ∈ S, p.Prime := by
    intro p hp
    obtain ⟨P, -, rfl⟩ := Finset.mem_image.mp hp
    exact residue_characteristic_prime K P.1 P.2
  calc ∑ P ∈ u, |Real.log (Formalism.HermitianLatticesTheory.eulerFac K M P.1)|
      ≤ ∑ P ∈ u, idealPrimeWeight K P.1 * negLogOneSubInvPow M (residueCharacteristic K P.1) :=
        Finset.sum_le_sum (fun P _ => (euler_factor_log_bound K hK M (by omega) P.1 P.2).2)
    _ = ∑ p ∈ S, ∑ P ∈ u.filter (fun P => residueCharacteristic K P.1 = p),
          idealPrimeWeight K P.1 * negLogOneSubInvPow M (residueCharacteristic K P.1) :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ p ∈ S, negLogOneSubInvPow M p * ∑ P ∈ u.filter (fun P => residueCharacteristic K P.1 = p), idealPrimeWeight K P.1 := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun P hP => ?_)
        rw [(Finset.mem_filter.mp hP).2]; ring
    _ ≤ ∑ p ∈ S, negLogOneSubInvPow M p * ((Module.finrank ℚ K : ℝ) / 2) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        exact mul_le_mul_of_nonneg_left
          (sum_weights_over_prime_le_half_degree K p _ (fun P hP => (Finset.mem_filter.mp hP).2))
          (neg_log_one_sub_inv_pow_nonneg M (by omega) p (hSp p hp))
    _ = (Module.finrank ℚ K : ℝ) / 2 * ∑ p ∈ S, negLogOneSubInvPow M p := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    _ ≤ (Module.finrank ℚ K : ℝ) / 2 * Real.log (zetaR M) :=
        mul_le_mul_of_nonneg_left (sum_neg_log_le_log_zeta M hM S hSp) (by positivity)
    _ = (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M) := by rw [hn]
end main
end Formalism.HermitianLattices.GenusMassVolumes
end
section
open Finset Filter Topology ArithmeticFunction
noncomputable section
namespace Formalism.HermitianLattices.GlobalBoundRefinements
section ShortIntervalLowerBound
open Formalism.HermitianLattices.GL2PrimeSums
open Formalism.HermitianLattices.GL2PrimeSums
private lemma exists_adjusted_exceptional_exponent {cb B β X : ℝ} {θ : ℤ} (hcb : 0 < cb) (hB : 4 ≤ B)
    (hβ : θ ≠ 0 → 1 / 2 ≤ β ∧ β < 1 ∧ cb / (B ^ 2 * Real.log B) ≤ 1 - β)
    (hcbX : 2 / cb * Real.log B ≤ Real.log X) :
    ∃ β' : ℝ, 1 / 2 ≤ β' ∧ β' < 1 ∧
      (∀ Y, Emain θ β Y = Emain θ β' Y) ∧ (θ = 1 → 2 / B ^ 2 ≤ (1 - β') * Real.log X) := by
  by_cases hθ : θ = 0
  · refine ⟨1 / 2, by norm_num, by norm_num, fun Y => ?_, fun h1 => ?_⟩
    · simp only [Emain, hθ, Int.cast_zero, zero_mul, sub_zero]
    · exfalso
      omega
  · obtain ⟨h1, h2, h3⟩ := hβ hθ
    refine ⟨β, h1, h2, fun Y => rfl, fun _ => ?_⟩
    have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
    have hBpos : 0 < B := by linarith
    have hcbne : cb ≠ 0 := hcb.ne'
    have hlogne : Real.log B ≠ 0 := hlogB.ne'
    have hBne : B ≠ 0 := hBpos.ne'
    have e : 2 / B ^ 2 = cb / (B ^ 2 * Real.log B) * (2 / cb * Real.log B) := by
      field_simp
      try ring
    rw [e]
    exact mul_le_mul h3 hcbX (mul_nonneg (div_nonneg (by norm_num) hcb.le) hlogB.le) (by linarith)
private lemma mul_log_le_log_of_rpow_le {B K X : ℝ} (hB : 4 ≤ B) (h : B ^ K ≤ X) : K * Real.log B ≤ Real.log X := by
  have hB0 : 0 < B := by linarith
  have h1 := Real.log_le_log (Real.rpow_pos_of_pos hB0 K) h
  rwa [Real.log_rpow hB0] at h1
private lemma numerical_exponential_inequality {Cr cr l L : ℝ} (hCr : 0 < Cr) (h60 : 60 * l ≤ L)
    (h16 : 16 * cr ^ 2 ≤ L) (h48 : 4800 / Cr ≤ L) (hL : 0 < L) :
    3 * Real.exp l * l ≤
      Cr * Real.exp (-cr * Real.sqrt L) * (1 / 100 * Real.exp (-5 * l) * Real.exp L / L) := by
  rcases le_or_gt l 0 with hl0 | hl0
  · have h1 : 3 * Real.exp l * l ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hl0
    have h2 : 0 ≤ Cr * Real.exp (-cr * Real.sqrt L) * (1 / 100 * Real.exp (-5 * l) * Real.exp L / L) :=
      mul_nonneg (mul_nonneg hCr.le (Real.exp_pos _).le) (div_nonneg (by positivity) hL.le)
    linarith
  · have hs0 : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have hs : Real.sqrt L ^ 2 = L := Real.sq_sqrt hL.le
    have hcs : cr * Real.sqrt L ≤ L / 4 := by nlinarith [sq_nonneg (Real.sqrt L - 4 * cr)]
    have hE : Real.exp (2 * L / 3) ≤ Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hll : l ≤ L / 60 := by linarith
    have hA : 0 < Real.exp (L / 60) := Real.exp_pos _
    have hel : Real.exp l ≤ Real.exp (L / 60) := Real.exp_le_exp.mpr hll
    have hy : 13 * L / 60 ≤ Real.exp (13 * L / 60) := by linarith [Real.add_one_le_exp (13 * L / 60)]
    have e3 : Real.exp (39 * L / 60) = Real.exp (13 * L / 60) ^ 3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hcube : (13 * L / 60) ^ 3 ≤ Real.exp (39 * L / 60) := by
      rw [e3]
      first
      | exact pow_le_pow_left₀ (by linarith) hy 3
      | exact pow_le_pow_left (by linarith) hy 3
    have e23 : Real.exp (L / 60) * Real.exp (39 * L / 60) = Real.exp (2 * L / 3) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hK : 4800 ≤ Cr * L := by
      have := (div_le_iff₀ hCr).mp h48
      linarith
    have key : 3 * Real.exp l * l * (100 * L)
        ≤ Cr * (Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L) := by
      have k1 : 3 * Real.exp l * l ≤ 3 * Real.exp (L / 60) * (L / 60) :=
        mul_le_mul (by linarith) hll hl0.le (by positivity)
      have k2 : 3 * Real.exp (L / 60) * (L / 60) * (100 * L)
          ≤ Cr * (Real.exp (L / 60) * (13 * L / 60) ^ 3) := by
        nlinarith [mul_nonneg (mul_nonneg hA.le (sq_nonneg L)) (sub_nonneg.mpr hK),
          mul_nonneg hA.le (sq_nonneg L)]
      have k3 : Cr * (Real.exp (L / 60) * (13 * L / 60) ^ 3)
          ≤ Cr * (Real.exp (L / 60) * Real.exp (39 * L / 60)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcube hA.le) hCr.le
      rw [e23] at k3
      have k4 : Cr * Real.exp (2 * L / 3)
          ≤ Cr * (Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L) :=
        mul_le_mul_of_nonneg_left hE hCr.le
      nlinarith [mul_le_mul_of_nonneg_right k1 (by linarith : (0 : ℝ) ≤ 100 * L)]
    have e : Cr * Real.exp (-cr * Real.sqrt L) * (1 / 100 * Real.exp (-5 * l) * Real.exp L / L)
        = Cr * (Real.exp (-cr * Real.sqrt L) * Real.exp (-5 * l) * Real.exp L) / (100 * L) := by
      first
      | ring
      | (field_simp; ring)
      | field_simp
    rw [e, le_div_iff₀ (by linarith)]
    exact key
end ShortIntervalLowerBound
section T2
open NumberField
open Formalism.LogVandermondeBounds.StandardLattice
open Formalism.HermitianLattices.GenusMassVolumes
end T2
end Formalism.HermitianLattices.GlobalBoundRefinements
end
end

set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
open Formalism.HermitianLattices.GL2PrimeSums
open Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : PrimeDivisorCountAbsorption := by
  intro C₀ Cr cr cb hC₀ hCr hcr hcb
  obtain ⟨Cm, hC0m, hC60, hCcb, hC16, hC48⟩ : ∃ Cm : ℝ, C₀ ≤ Cm ∧ 60 ≤ Cm ∧ 2 / cb ≤ Cm ∧
      16 * cr ^ 2 ≤ Cm ∧ 4800 / Cr ≤ Cm :=
    ⟨max C₀ (max 60 (max (2 / cb) (max (16 * cr ^ 2) (4800 / Cr)))), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)),
      le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))),
      le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))⟩
  refine ⟨Cm, hC0m, ?_⟩
  intro B G β θ P η' hB hG1 hGB hθ hβ hη hQ Y hY
  have hθ' : θ = -1 ∨ θ = 0 ∨ θ = 1 := by simpa using hθ
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB0 : 0 < B := by linarith
  have hlogB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]
    have := Real.exp_one_lt_d9
    linarith
  have hlogB : 0 < Real.log B := by linarith
  have hK := mul_log_le_log_of_rpow_le hB hY
  have hL60 : 60 * Real.log B ≤ Real.log Y := le_trans (mul_le_mul_of_nonneg_right hC60 hlogB.le) hK
  have hLC : Cm ≤ Real.log Y := le_trans (le_mul_of_one_le_right (by linarith) hlogB1) hK
  have hL16 : 16 * cr ^ 2 ≤ Real.log Y := le_trans hC16 hLC
  have hL48 : 4800 / Cr ≤ Real.log Y := le_trans hC48 hLC
  have hLpos : 0 < Real.log Y := by linarith
  have hcbX : 2 / cb * Real.log B ≤ Real.log Y :=
    le_trans (mul_le_mul_of_nonneg_right hCcb hlogB.le) hK
  have hY60 : B ^ (60 : ℝ) ≤ Y := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC60) hY
  have hYC₀ : B ^ C₀ ≤ Y := le_trans (Real.rpow_le_rpow_of_exponent_le hB1 hC0m) hY
  have hY0 : 0 < Y := lt_of_lt_of_le (Real.rpow_pos_of_pos hB0 _) hY
  obtain ⟨β', hβ1, hβ2, hE, hd⟩ := exists_adjusted_exceptional_exponent hcb hB hβ hcbX
  have hlow := Emain_lower_bound hθ' hB hβ1 hβ2 hd hY60
  rw [← hE Y] at hlow
  have hnum := numerical_exponential_inequality hCr hL60 hL16 hL48 hLpos
  rw [Real.exp_log hB0, Real.exp_log hY0] at hnum
  have e5 : Real.exp (-5 * Real.log B) = B ^ (-5 : ℝ) := by
    rw [Real.rpow_def_of_pos hB0]
    congr 1
    ring
  rw [e5] at hnum
  have hρ : Cr * Real.exp (-cr * Real.sqrt (Real.log Y)) ≤ rhoErr Cr cr B Y := by
    unfold rhoErr
    linarith [mul_pos hCr (Real.exp_pos (-cr * Real.log Y / Real.log B))]
  have hm0 : 0 ≤ 1 / 100 * B ^ (-5 : ℝ) * Y / Real.log Y :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_pos_of_pos hB0 _).le) hY0.le) hLpos.le
  have hρE : Cr * Real.exp (-cr * Real.sqrt (Real.log Y)) * (1 / 100 * B ^ (-5 : ℝ) * Y / Real.log Y)
      ≤ rhoErr Cr cr B Y * Emain θ β Y :=
    mul_le_mul hρ hlow hm0 (le_of_lt (gl2a4_rho_pos hCr))
  have hGη : G * η' Y ≤ B * (3 * Real.log B) := mul_le_mul hGB (hη Y).2 (hη Y).1 hB0.le
  have hGη0 : 0 ≤ G * η' Y := mul_nonneg (by linarith) (hη Y).1
  have h2 : rhoErr (2 * Cr) cr B Y = 2 * rhoErr Cr cr B Y := by
    unfold rhoErr
    ring
  have hQY := abs_le.mp (hQ Y hYC₀)
  rw [h2, abs_le]
  constructor <;> linarith [hQY.1, hQY.2]
end Formalism.HermitianLattices.GlobalBoundRefinements
