-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_queue_increment_from_renewal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:58.083892+00:00
-- url     : https://prove2.me/submissions/62945382-787a-4e38-b7de-9265bb854e82

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Set
open scoped ENNReal

private theorem occupancy_diff {C : Set ℝ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (volume (Ioc 0 b ∩ C)).toReal - (volume (Ioc 0 a ∩ C)).toReal =
      (volume (Ioc a b ∩ C)).toReal := by
  have h₁ : ((Ioc 0 b ∩ C) ∩ Ioc a b) = Ioc a b ∩ C := by
    ext s
    simp only [mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨_,hc⟩,hs⟩
      exact ⟨hs,hc⟩
    · rintro ⟨hs,hc⟩
      exact ⟨⟨⟨ha.trans_lt hs.1,hs.2⟩,hc⟩,hs⟩
  have h₂ : ((Ioc 0 b ∩ C) \ Ioc a b) = Ioc 0 a ∩ C := by
    ext s
    simp only [mem_sdiff, mem_inter_iff, mem_Ioc]
    constructor
    · rintro ⟨⟨⟨hs,hb⟩,hc⟩,h⟩
      exact ⟨⟨hs,le_of_not_gt fun hsa => h ⟨hsa,hb⟩⟩,hc⟩
    · rintro ⟨⟨hs,hsa⟩,hc⟩
      exact ⟨⟨⟨hs,hsa.trans hab⟩,hc⟩,fun h => (not_lt_of_ge hsa) h.1⟩
  have hf (u v : ℝ) : volume (Ioc u v ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top (Real.volume_Ioc ▸ ENNReal.ofReal_ne_top) (measure_mono inter_subset_left)
  have h := measure_sdiff_add_inter (μ := volume) (Ioc 0 b ∩ C) (measurableSet_Ioc (a := a) (b := b))
  rw [h₁,h₂] at h
  rw [← h, ENNReal.toReal_add (hf 0 a) (hf a b), add_sub_cancel_left]

private theorem alloc_range {Ω : Type*} [MeasurableSpace Ω]
    (M : SystemSequence Ω) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T)
    (ω : Ω) (j : Fin 3) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ T ω j a ∧ T ω j a ≤ T ω j b ∧ T ω j b ≤ b ∧
      T ω j b - T ω j a ≤ b-a := by
  have ha' : a ∈ Ici (0:ℝ) := ha
  have hb' : b ∈ Ici (0:ℝ) := ha.trans hab
  have hz : (0:ℝ) ∈ Ici (0:ℝ) := mem_Ici.mpr le_rfl
  have nonNeg (j : Fin 3) : 0 ≤ T ω j a := by
    have h := hA.alloc_mono ω j hz ha' ha
    rwa [hA.alloc_zero] at h
  have mono (j : Fin 3) : T ω j a ≤ T ω j b := hA.alloc_mono ω j ha' hb' hab
  have hi₀ := hA.idle_mono ω 0 ha' hb' hab
  have hi₁ := hA.idle_mono ω 1 ha' hb' hab
  simp only [SystemSequence.idle, if_true, show (1:Fin 2) ≠ 0 by decide, if_false] at hi₀ hi₁
  have hd (j : Fin 3) : T ω j b - T ω j a ≤ b-a := by
    fin_cases j <;> simp at *
    · linarith
    · linarith [mono 2]
    · linarith [mono 1]
  have hCap (j : Fin 3) : T ω j b ≤ b := by
    have h0 := hA.idle_mono ω 0 hz hb' (ha.trans hab)
    have h1 := hA.idle_mono ω 1 hz hb' (ha.trans hab)
    rw [hA.idle_zero] at h0 h1
    simp only [SystemSequence.idle, if_true, show (1:Fin 2) ≠ 0 by decide, if_false] at h0 h1
    fin_cases j <;> simp at *
    · linarith
    · linarith [nonNeg 2,mono 2]
    · linarith [nonNeg 1,mono 1]
  exact ⟨nonNeg j,mono j,hCap j,hd j⟩

set_option maxHeartbeats 1100000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (c : ℝ) (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (hP : M.IsThreshold c n T)
    (hL : 1 ≤ M.threshold c n) (ω : Ω) (H η E α : ℝ) (hη : 0 ≤ η) (hE : 0 ≤ E)
    (hPosDrift : α + 2*η ≤ M.lamR n 0 - M.muR n 0)
    (hNegDrift : α + 3*η ≤ M.muR n 0 + M.muR n 1 - M.lamR n 0)
    (hArr : ∀ a b, 0 ≤ a → a ≤ b → b ≤ H →
      |M.A n 0 ω b - M.A n 0 ω a - M.lamR n 0 * (b-a)| ≤ η*(b-a) + E)
    (hServ : ∀ j : Fin 3, j ≠ 2 → ∀ a b, 0 ≤ a → a ≤ b → b ≤ H →
      |M.S n j ω b - M.S n j ω a - M.muR n j * (b-a)| ≤ η*(b-a) + E) :
    let q := M.queue n T ω 0
    let L : ℝ := M.threshold c n
    let K := M.lamR n 0 + M.muR n 0 + M.muR n 1 + 3*η
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → |q b-q a| ≤ K*(b-a)+3*E) ∧
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → (∀ s ∈ Ioc a b, q s ≤ L) → α*(b-a)-3*E ≤ q b-q a) ∧
    (∀ a b, 0 ≤ a → a ≤ b → b ≤ H → (∀ s ∈ Ioc a b, L < q s) → q b-q a ≤ -α*(b-a)+3*E) := by
  let q := M.queue n T ω 0
  let L : ℝ := M.threshold c n
  let K := M.lamR n 0 + M.muR n 0 + M.muR n 1 + 3*η
  have hL' : 1 ≤ L := by dsimp [L]; exact_mod_cast hL
  have hbal (a b : ℝ) : q b-q a =
      (M.A n 0 ω b - M.A n 0 ω a) - (M.S n 0 ω (T ω 0 b) - M.S n 0 ω (T ω 0 a)) -
      (M.S n 1 ω (T ω 1 b) - M.S n 1 ω (T ω 1 a)) := by
    simp only [q,SystemSequence.queue,if_true]
    ring
  have hServ' (j : Fin 3) (hj : j ≠ 2) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ H) :
      let d := T ω j b - T ω j a
      |M.S n j ω (T ω j b) - M.S n j ω (T ω j a) - M.muR n j * d| ≤ η*d + E ∧
      0 ≤ d ∧ d ≤ b-a := by
    obtain ⟨h₀,h₁,h₂,h₃⟩ := alloc_range M n T hA ω j ha hab
    exact ⟨hServ j hj _ _ h₀ h₁ (h₂.trans hb),sub_nonneg.mpr h₁,h₃⟩
  let C₀ : Set ℝ := {s | M.serverTwoHolds n T ω s < q s}
  let C₁ : Set ℝ := {s | L < q s}
  have hInc (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
      T ω 0 b - T ω 0 a = (volume (Ioc a b ∩ C₀)).toReal ∧
      T ω 1 b - T ω 1 a = (volume (Ioc a b ∩ C₁)).toReal := by
    obtain ⟨ha₀,ha₁,_⟩ := hP ω a ha
    obtain ⟨hb₀,hb₁,_⟩ := hP ω b (ha.trans hab)
    exact ⟨by rw [hb₀,ha₀]; exact occupancy_diff ha hab,
      by rw [hb₁,ha₁]; exact occupancy_diff ha hab⟩
  have hOnLow {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hLow : ∀ s ∈ Ioc a b, q s ≤ L) :
      T ω 1 b = T ω 1 a := by
    have hEmp : Ioc a b ∩ C₁ = ∅ := by
      ext s
      simp only [mem_inter_iff,notMem_empty,iff_false]
      exact fun hs => (not_lt_of_ge (hLow s hs.1)) hs.2
    have hh := (hInc a b ha hab).2
    rw [hEmp,measure_empty,ENNReal.toReal_zero] at hh
    linarith
  have hOnHigh {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hHigh : ∀ s ∈ Ioc a b, L < q s) :
      T ω 0 b - T ω 0 a = b-a ∧ T ω 1 b - T ω 1 a = b-a := by
    have hh (s : ℝ) : M.serverTwoHolds n T ω s ≤ 1 := by
      unfold SystemSequence.serverTwoHolds
      split <;> norm_num
    have h0 : Ioc a b ∩ C₀ = Ioc a b := inter_eq_left.2 fun s hs =>
      (hh s).trans_lt (hL'.trans_lt (hHigh s hs))
    have h1 : Ioc a b ∩ C₁ = Ioc a b := inter_eq_left.2 hHigh
    simpa only [h0,h1,Real.volume_Ioc,ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hInc a b ha hab
  refine ⟨?_,?_,?_⟩
  · intro a b ha hab hb
    have hAerr := abs_le.1 (hArr a b ha hab hb)
    obtain ⟨hS0,hD0,hD0'⟩ := hServ' 0 (by decide) ha hab hb
    obtain ⟨hS1,hD1,hD1'⟩ := hServ' 1 (by decide) ha hab hb
    have hSb0 := abs_le.1 hS0
    have hSb1 := abs_le.1 hS1
    have hMu0 := M.muR_pos n 0
    have hMu1 := M.muR_pos n 1
    have hLam := M.lamR_pos n 0
    have hdt := sub_nonneg.mpr hab
    rw [hbal]
    exact abs_le.2 ⟨by nlinarith,by nlinarith⟩
  · intro a b ha hab hb hLow
    have hAerr := (abs_le.1 (hArr a b ha hab hb)).1
    obtain ⟨hS0,_,hD0⟩ := hServ' 0 (by decide) ha hab hb
    have hSerr := (abs_le.1 hS0).2
    have hCap := mul_le_mul_of_nonneg_left hD0 (add_nonneg (M.muR_pos n 0).le hη)
    have hDrift := mul_le_mul_of_nonneg_right hPosDrift (sub_nonneg.mpr hab)
    rw [hbal, hOnLow ha hab hLow, sub_self, sub_zero]
    linarith
  · intro a b ha hab hb hHigh
    have hAerr := (abs_le.1 (hArr a b ha hab hb)).2
    have hS0 := (abs_le.1 (hServ' 0 (by decide) ha hab hb).1).1
    have hS1 := (abs_le.1 (hServ' 1 (by decide) ha hab hb).1).1
    obtain ⟨h0,h1⟩ := hOnHigh ha hab hHigh
    rw [h0] at hS0
    rw [h1] at hS1
    have hDrift := mul_le_mul_of_nonneg_right hNegDrift (sub_nonneg.mpr hab)
    rw [hbal]
    linarith
