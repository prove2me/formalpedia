-- Prove2me | solution 1 for ChenFarias.SimplePolicy.lemma_8
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T18:48:50.743477+00:00
-- url     : https://prove2.me/submissions/88447aa8-2dad-43e4-9c27-39f277a6ccfd

import Mathlib
import Definitions.Def_ChenFarias_SimplePolicy_Model
import Theorems.Thm_ChenFarias_SimplePolicy_compensator_identity
import Theorems.Thm_ChenFarias_SimplePolicy_lemma_7

open MeasureTheory Set
open scoped ENNReal
open ChenFarias.SimplePolicy

/-- Averages of a nonincreasing nonnegative rate over `(0, T]` decrease with `T`. -/
lemma cf_avg_antitone (r : ℝ → ℝ) (hr : Antitone r) {T T' : ℝ} (hT' : 0 < T')
    (hTT' : T' < T) :
    (∫⁻ t in Ioc 0 T, ENNReal.ofReal (r t)) / ENNReal.ofReal T ≤
      (∫⁻ t in Ioc 0 T', ENNReal.ofReal (r t)) / ENNReal.ofReal T' := by
  set A := ∫⁻ t in Ioc 0 T', ENNReal.ofReal (r t)
  set B := ∫⁻ t in Ioc T' T, ENNReal.ofReal (r t)
  set c := ENNReal.ofReal (r T')
  have hT : 0 < T := hT'.trans hTT'
  have hsplit : (∫⁻ t in Ioc 0 T, ENNReal.ofReal (r t)) = A + B := by
    rw [← Ioc_union_Ioc_eq_Ioc hT'.le hTT'.le,
      lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
  have hB : B ≤ c * ENNReal.ofReal (T - T') := by
    calc B ≤ ∫⁻ _ in Ioc T' T, c :=
          setLIntegral_mono' measurableSet_Ioc (fun t ht =>
            ENNReal.ofReal_le_ofReal (hr ht.1.le))
      _ = c * ENNReal.ofReal (T - T') := by rw [setLIntegral_const, Real.volume_Ioc]
  have hA : c * ENNReal.ofReal T' ≤ A := by
    calc c * ENNReal.ofReal T' = ∫⁻ _ in Ioc 0 T', c := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
      _ ≤ A := setLIntegral_mono' measurableSet_Ioc (fun t ht =>
            ENNReal.ofReal_le_ofReal (hr ht.2))
  have key : ENNReal.ofReal T' * (A + B) ≤ ENNReal.ofReal T * A := by
    have hTsplit : ENNReal.ofReal T = ENNReal.ofReal T' + ENNReal.ofReal (T - T') := by
      rw [← ENNReal.ofReal_add hT'.le (by linarith)]; congr 1; ring
    calc ENNReal.ofReal T' * (A + B)
        = ENNReal.ofReal T' * A + ENNReal.ofReal T' * B := by rw [mul_add]
      _ ≤ ENNReal.ofReal T' * A + ENNReal.ofReal T' * (c * ENNReal.ofReal (T - T')) := by
          gcongr
      _ = ENNReal.ofReal T' * A + (c * ENNReal.ofReal T') * ENNReal.ofReal (T - T') := by
          ring
      _ ≤ ENNReal.ofReal T' * A + A * ENNReal.ofReal (T - T') := by gcongr
      _ = ENNReal.ofReal T * A := by rw [hTsplit]; ring
  have hTne : ENNReal.ofReal T ≠ 0 := by simp [hT]
  have hT'ne : ENNReal.ofReal T' ≠ 0 := by simp [hT']
  rw [hsplit, ← ENNReal.mul_div_mul_left (A + B) (ENNReal.ofReal T) hT'ne ENNReal.ofReal_ne_top,
    ← ENNReal.mul_div_mul_left A (ENNReal.ofReal T') hTne ENNReal.ofReal_ne_top,
    mul_comm (ENNReal.ofReal T) (ENNReal.ofReal T')]
  exact ENNReal.div_le_div_right key _

theorem solution (lam β T T' : ℝ) (f : ℝ → ℝ) (V : ℕ → ℝ)
    (π : ℕ → ℝ) (x0 : ℕ) (hlam : 0 < lam) (hβ : 0 < β)
    (hT' : 0 < T') (hTT' : T' < T) (hf : Assumption1 f)
    (hV : IsValueFn lam β f V) (hπ : IsRootPolicy f V π) :
    J lam f π x0 T / ENNReal.ofReal T ≤
      J lam f π x0 T' / ENNReal.ofReal T' := by
  have hπ0 : ∀ x : ℕ, 1 ≤ x → 0 ≤ π x := fun x hx => (hπ x hx).1
  have hT : 0 < T := hT'.trans hTT'
  rw [compensator_identity lam f π x0 T hlam hf hπ0 hT.le,
    compensator_identity lam f π x0 T' hlam hf hπ0 hT'.le]
  have hTi : (ENNReal.ofReal T)⁻¹ ≠ ⊤ := by simp [hT]
  have hT'i : (ENNReal.ofReal T')⁻¹ ≠ ⊤ := by simp [hT']
  rw [div_eq_mul_inv, div_eq_mul_inv, ← lintegral_mul_const' _ _ hTi,
    ← lintegral_mul_const' _ _ hT'i]
  refine lintegral_mono (fun e => ?_)
  rw [← div_eq_mul_inv, ← div_eq_mul_inv]
  have hmono : Antitone (fun t => lam * rateRev f π (Xminus lam f π x0 e t)) := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left
      ((lemma_7 lam β f V π x0 hlam hβ hf hV hπ e s t hst).2) hlam.le
  exact cf_avg_antitone _ hmono hT' hTT'
