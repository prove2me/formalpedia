-- Prove2me | solution 1 for BoxTDIMinMax.Separable.proposition_2_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:13:33.380313+00:00
-- url     : https://prove2.me/submissions/09b35326-c4da-4253-8133-6a4f8def455c

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Prop24Aux

variable {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]

/-- Interchange the two box rows of every column in `T`. -/
def sw (T : Finset S) : ι ⊕ (S ⊕ S) → ι ⊕ (S ⊕ S)
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl s) => if s ∈ T then Sum.inr (Sum.inr s) else Sum.inr (Sum.inl s)
  | Sum.inr (Sum.inr s) => if s ∈ T then Sum.inr (Sum.inl s) else Sum.inr (Sum.inr s)

theorem sw_invol (T : Finset S) : Function.Involutive (sw (ι := ι) T) := by
  intro r
  rcases r with i | s | s
  · rfl
  · by_cases h : s ∈ T <;> simp [sw, h]
  · by_cases h : s ∈ T <;> simp [sw, h]

def sgn (T : Finset S) (s : S) : ℚ := if s ∈ T then -1 else 1

theorem boxMat_sw (T : Finset S) (A : Matrix ι S ℚ) (r : ι ⊕ (S ⊕ S)) (s : S) :
    boxMat A (sw T r) s =
      sgn T s * boxMat (Matrix.of fun i s => if s ∈ T then -A i s else A i s) r s := by
  rcases r with i | t | t
  · by_cases h : s ∈ T <;> simp [sw, sgn, boxMat, h]
  · by_cases ht : t ∈ T <;> by_cases hs : s ∈ T <;> by_cases hst : t = s <;>
      simp [sw, sgn, boxMat, ht, hs, hst, Matrix.one_apply] <;> simp_all
  · by_cases ht : t ∈ T <;> by_cases hs : s ∈ T <;> by_cases hst : t = s <;>
      simp [sw, sgn, boxMat, ht, hs, hst, Matrix.one_apply] <;> simp_all

theorem sum_sw (T : Finset S) (F : ι ⊕ (S ⊕ S) → ℝ) :
    ∑ r, F (sw T r) = ∑ r, F r :=
  Equiv.sum_comp (Function.Involutive.toPerm _ (sw_invol T)) F

end BoxTDIMinMax.Separable.Prop24Aux

open BoxTDIMinMax.Separable.Prop24Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (T : Finset S) :
    IsBoxTDI (ratMat (Matrix.of fun i s => if s ∈ T then -Q i s else Q i s)) (ratVec p) := by
  set A := ratMat Q
  have hA' : ratMat (Matrix.of fun i s => if s ∈ T then -Q i s else Q i s) =
      Matrix.of fun i s => if s ∈ T then -A i s else A i s := by
    ext i s; by_cases h : s ∈ T <;> simp [A, ratMat, h]
  rw [hA']
  set A' : Matrix ι S ℚ := Matrix.of fun i s => if s ∈ T then -A i s else A i s
  intro f' g' hfg c' hfe hbdd
  -- transformed bounds and cost
  set f : S → ℚ := fun s => if s ∈ T then -g' s else f' s
  set g : S → ℚ := fun s => if s ∈ T then -f' s else g' s
  set c : S → ℤ := fun s => if s ∈ T then -c' s else c' s
  have hfg0 : f ≤ g := by
    intro s; by_cases h : s ∈ T <;> simp only [f, g, h, if_true, if_false]
    · linarith [hfg s]
    · exact hfg s
  have hrhs : ∀ r, boxRhs (ratVec p) f g (sw T r) = boxRhs (ratVec p) f' g' r := by
    intro r
    rcases r with i | s | s
    · rfl
    · by_cases h : s ∈ T <;> simp [sw, boxRhs, f, g, h]
    · by_cases h : s ∈ T <;> simp [sw, boxRhs, f, g, h]
  -- feasibility transfers along `sw`
  have hvec : ∀ y : ι ⊕ (S ⊕ S) → ℝ, ∀ s,
      ((fun r => y (sw T r)) ᵥ* (boxMat A).map ((↑) : ℚ → ℝ)) s =
        (sgn T s : ℝ) * (y ᵥ* (boxMat A').map ((↑) : ℚ → ℝ)) s := by
    intro y s
    simp only [vecMul, dotProduct, Matrix.map_apply]
    rw [Finset.mul_sum]
    rw [← sum_sw T (fun r => (sgn T s : ℝ) * (y r * ((boxMat A' r s : ℚ) : ℝ)))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have h := boxMat_sw T A (sw T r) s
    rw [sw_invol T r] at h
    rw [h]
    push_cast; ring
  have hsgn2 : ∀ s, (sgn T s : ℝ) * (sgn T s : ℝ) = 1 := by
    intro s; by_cases h : s ∈ T <;> simp [sgn, h]
  have hcs : ∀ s, ((c s : ℤ) : ℝ) = (sgn T s : ℝ) * (c' s : ℝ) := by
    intro s; by_cases h : s ∈ T <;> simp [sgn, c, h]
  have feas_iff : ∀ y : ι ⊕ (S ⊕ S) → ℝ,
      (fun r => y (sw T r)) ∈ DualFeas (boxMat A) c ↔ y ∈ DualFeas (boxMat A') c' := by
    intro y
    unfold DualFeas
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨fun r => ?_, ?_⟩
      · have := h0 (sw T r); simp only [sw_invol T r] at this; exact this
      · funext s
        have := congrFun h1 s
        rw [hvec, hcs] at this
        have h2 := congrArg (fun x => (sgn T s : ℝ) * x) this
        simp only [← mul_assoc, hsgn2, one_mul] at h2
        exact h2
    · rintro ⟨h0, h1⟩
      refine ⟨fun r => h0 (sw T r), ?_⟩
      funext s
      rw [hvec, hcs, h1]
  have hobj : ∀ y : ι ⊕ (S ⊕ S) → ℝ,
      dualObj (boxRhs (ratVec p) f g) (fun r => y (sw T r)) =
        dualObj (boxRhs (ratVec p) f' g') y := by
    intro y
    unfold dualObj
    rw [← sum_sw T (fun r => y (sw T r) * ((boxRhs (ratVec p) f g r : ℚ) : ℝ))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [sw_invol T r, hrhs]
  have hT := hbox f g hfg0
  obtain ⟨y0, hy0⟩ := hfe
  have hfe1 : (DualFeas (boxMat A) c).Nonempty := ⟨_, (feas_iff y0).mpr hy0⟩
  obtain ⟨B, hB⟩ := hbdd
  have hbdd1 : BddAbove (dualObj (boxRhs (ratVec p) f g) '' DualFeas (boxMat A) c) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (fun r => y (sw T r)) ∈ DualFeas (boxMat A') c' := by
      rw [← feas_iff]; simpa only [sw_invol T _] using hy
    have := hB ⟨_, hy', rfl⟩
    rw [← hobj] at this
    simpa only [sw_invol T _] using this
  obtain ⟨y, hyF, hyopt⟩ := hT c hfe1 hbdd1
  refine ⟨fun r => y (sw T r), ?_, fun y' hy' => ?_⟩
  · have hyF' : (fun r => ((fun r => y (sw T r)) (sw T r) : ℤ) : ι ⊕ (S ⊕ S) → ℝ) ∈
        DualFeas (boxMat A) c := by simpa only [sw_invol T _] using hyF
    exact (feas_iff (fun r => (y (sw T r) : ℝ))).mp hyF'
  · have h1 := hyopt _ ((feas_iff y').mpr hy')
    rw [hobj y'] at h1
    have h2 := hobj (fun r => (y (sw T r) : ℝ))
    simp only [sw_invol T _] at h2
    rw [← h2]
    exact h1
