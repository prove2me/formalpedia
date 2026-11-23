-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.shortIntervalImpliesProgressions_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:36.318837+00:00
-- url     : https://prove2.me/submissions/f62adea1-50ed-4980-8ca7-2b4d45e259d4

import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
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
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
open Formalism.HermitianLattices.GL2PrimeSums
open Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : ShortIntervalImpliesProgressions := by
  intro hL C₀ Cr cr cb hC₀ hCr hcr hcb hQ
  obtain ⟨C₀', c, hC₀', hc, H⟩ := hL C₀ Cr cr cb hC₀ hCr hcr hcb
  refine ⟨C₀', c, lt_of_lt_of_le hC₀ hC₀', hc, ?_⟩
  intro m a hm ha Y h hY hh1 hρ h7
  obtain ⟨θ, β, η', hθ, hβ, hη, happrox⟩ := hQ m a hm ha
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB : (4 : ℝ) ≤ 4 * m := by linarith
  have htot0 : 0 < m.totient := by
    first
    | exact Nat.totient_pos.mpr (by omega)
    | exact Nat.totient_pos (by omega)
  have htot1 : (1 : ℝ) ≤ (m.totient : ℝ) := by exact_mod_cast htot0
  have htotB : (m.totient : ℝ) ≤ 4 * m := by
    have h1 : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
    linarith
  have key := (H (4 * m) (m.totient : ℝ) β θ
    (fun Z => ((Icc 1 ⌊Z⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card) (fun _ => 0) η'
    hB htot1 htotB hθ hβ
    (fun Z _ => by
      show ((0 : ℕ) : ℝ) ≤ 2 * Real.sqrt Z
      rw [Nat.cast_zero]
      positivity)
    hη
    (fun Z hZ => by
      have hz := happrox Z hZ
      show |(m.totient : ℝ) * ((((Icc 1 ⌊Z⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ)
        + ((0 : ℕ) : ℝ) + η' Z) - Emain θ β Z| ≤ rhoErr Cr cr (4 * m) Z * Emain θ β Z
      rw [Nat.cast_zero, add_zero]
      exact hz)
    Y hY).2 h hh1 hρ h7
  have hY1 : (1 : ℝ) ≤ Y := by
    have h41 : (1 : ℝ) ≤ 4 * m := by linarith
    have := Real.one_le_rpow h41 (le_trans hC₀.le hC₀')
    linarith
  have hYpos : 0 < Y := by linarith
  have hY13 : 0 ≤ Y ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hYpos.le _
  have h47 : 0 < (4 * (m : ℝ)) ^ (7 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpos : 0 < h := by
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hfl1 : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY1)
  have hfl2 : ⌊Y⌋₊ ≤ ⌊Y * (1 + h)⌋₊ := Nat.floor_mono (by nlinarith)
  have hunion : Icc 1 ⌊Y * (1 + h)⌋₊ = Icc 1 ⌊Y⌋₊ ∪ Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint ((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a))
      ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_filter, Finset.mem_Icc] at hx1
    rw [Finset.mem_filter, Finset.mem_Ioc] at hx2
    omega
  have hcard : ((Icc 1 ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card
      = ((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card
        + ((Ioc ⌊Y⌋₊ ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card := by
    rw [hunion, Finset.filter_union]
    first
    | exact Finset.card_union_of_disjoint hdisj
    | exact Finset.card_disjoint_union hdisj
    | exact Finset.card_union_eq_card_add_card.mpr hdisj
  have key2 : c * h * (4 * (m : ℝ)) ^ (-6 : ℝ) * Y / Real.log Y ≤
      (((Icc 1 ⌊Y * (1 + h)⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ)
        - (((Icc 1 ⌊Y⌋₊).filter (fun p => p.Prime ∧ Nat.ModEq m p a)).card : ℝ) := key
  rw [hcard, Nat.cast_add] at key2
  linarith
end Formalism.HermitianLattices.GlobalBoundRefinements
