-- Prove2me | solution 1 for BoxTDIMinMax.Separable.theorem_2_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T00:23:06.910707+00:00
-- url     : https://prove2.me/submissions/a23ee323-ffb3-4093-90c5-755197b63ef9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BoxTDIMinMax_Separable_Setting
import Theorems.Thm_LP_strong_duality_matrix
import Theorems.Thm_BoxTDIMinMax_Separable_proposition_2_10
import Theorems.Thm_BoxTDIMinMax_Separable_claim_2_13

open Matrix BoxTDIMinMax.Separable

namespace BoxTDIMinMax.Separable.Thm212Aux

variable {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]

theorem feas_iff {κ T : Type*} [Fintype κ] (M : Matrix κ T ℚ) (c : T → ℤ) (y : κ → ℝ) :
    y ∈ DualFeas M c ↔ (∀ r, 0 ≤ y r) ∧ ∀ t, ∑ r, y r * (M r t : ℝ) = (c t : ℝ) := by
  unfold DualFeas
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun r => h0 r, fun s => ?_⟩
    have := congrFun h1 s
    simpa [vecMul, dotProduct] using this
  · rintro ⟨h0, h1⟩
    refine ⟨fun r => h0 r, ?_⟩
    funext s
    simpa [vecMul, dotProduct] using h1 s

/-- Column sums of the box matrix of the auxiliary system (2.8). -/
theorem colsum (Q : Matrix ι S ℤ) (Y : ((S ⊕ S) ⊕ ι) ⊕ ((S ⊕ S) ⊕ (S ⊕ S)) → ℝ)
    (t : S ⊕ S) :
    ∑ r, Y r * ((boxMat (auxMat Q) r t : ℚ) : ℝ) =
      Y (Sum.inl (Sum.inl t)) +
        ∑ i, Y (Sum.inl (Sum.inr i)) * ((auxMat Q (Sum.inr i) t : ℚ) : ℝ) +
        Y (Sum.inr (Sum.inl t)) - Y (Sum.inr (Sum.inr t)) := by
  simp only [Fintype.sum_sum_type]
  rcases t with s | s <;> simp [boxMat, auxMat, Matrix.one_apply, apply_ite] <;> ring

theorem aux_inl (Q : Matrix ι S ℤ) (i : ι) (s : S) :
    ((auxMat Q (Sum.inr i) (Sum.inl s) : ℚ) : ℝ) = -(Q i s : ℝ) := by
  simp [auxMat, ratMat]

theorem aux_inr (Q : Matrix ι S ℤ) (i : ι) (s : S) :
    ((auxMat Q (Sum.inr i) (Sum.inr s) : ℚ) : ℝ) = (Q i s : ℝ) := by
  simp [auxMat, ratMat]

/-- Row values of the box matrix of (2.8) at a real point `x`. -/
theorem rowval (Q : Matrix ι S ℤ) (x : S ⊕ S → ℝ) :
    (∀ t, ∑ u, ((boxMat (auxMat Q) (Sum.inl (Sum.inl t)) u : ℚ) : ℝ) * x u = x t) ∧
    (∀ i, ∑ u, ((boxMat (auxMat Q) (Sum.inl (Sum.inr i)) u : ℚ) : ℝ) * x u =
      ∑ s, (Q i s : ℝ) * x (Sum.inr s) - ∑ s, (Q i s : ℝ) * x (Sum.inl s)) ∧
    (∀ t, ∑ u, ((boxMat (auxMat Q) (Sum.inr (Sum.inl t)) u : ℚ) : ℝ) * x u = x t) ∧
    (∀ t, ∑ u, ((boxMat (auxMat Q) (Sum.inr (Sum.inr t)) u : ℚ) : ℝ) * x u = -x t) := by
  refine ⟨fun t => ?_, fun i => ?_, fun t => ?_, fun t => ?_⟩
  · simp [boxMat, auxMat, Matrix.one_apply, ite_mul, apply_ite]
  · simp only [Fintype.sum_sum_type]
    simp [boxMat, auxMat, ratMat]
    ring
  · simp [boxMat, Matrix.one_apply, ite_mul, apply_ite]
  · simp [boxMat, Matrix.one_apply, ite_mul, apply_ite]

end BoxTDIMinMax.Separable.Thm212Aux

theorem BoxTDIMinMax.Separable.Thm212Aux.esum {S : Type*} (T : Finset S) (g : S → ℤ) :
    ∑ s ∈ T, (((g s : ℤ) : ℝ) : EReal) = (((∑ s ∈ T, g s : ℤ) : ℝ) : EReal) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, ih]
    push_cast
    rfl

open BoxTDIMinMax.Separable.Thm212Aux in
theorem solution {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq S]
    (Q : Matrix ι S ℤ) (p : ι → ℤ) (hbox : IsBoxTDI (ratMat Q) (ratVec p))
    (zStar : S → ℤ) (hz : zStar ∈ intPts Q p)
    (lo up : S → EReal)
    (hlo : ∀ s, lo s = ⊥ ∨ ∃ k : ℤ, lo s = ((k : ℝ) : EReal))
    (hup : ∀ s, up s = ⊤ ∨ ∃ k : ℤ, up s = ((k : ℝ) : EReal))
    (hlu : ∀ s, lo s ≤ up s) :
    (∃ yStar : ι → ℤ, 0 ≤ yStar ∧
        (∀ s, lo s ≤ ((((yStar ᵥ* Q) s : ℤ) : ℝ) : EReal) ∧
          ((((yStar ᵥ* Q) s : ℤ) : ℝ) : EReal) ≤ up s) ∧
        yStar ⬝ᵥ (Q *ᵥ zStar - p) = 0) ↔
      Cond29 Q p zStar lo up := by
  constructor
  · -- necessity of (2.9)
    rintro ⟨y, hy0, hbd, hcs⟩ Sm Sp hdisj hz'
    have h1 : y ⬝ᵥ p ≤ y ⬝ᵥ (Q *ᵥ (zStar + chi Sp - chi Sm)) := by
      unfold dotProduct
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hz' i) (hy0 i))
    have h2 : y ⬝ᵥ (Q *ᵥ zStar) = y ⬝ᵥ p := by rw [dotProduct_sub] at hcs; linarith
    rw [Matrix.dotProduct_mulVec] at h1 h2
    rw [dotProduct_sub, dotProduct_add] at h1
    have hchi : ∀ T : Finset S, (y ᵥ* Q) ⬝ᵥ chi T = ∑ s ∈ T, (y ᵥ* Q) s := by
      intro T
      unfold dotProduct chi
      simp [mul_ite, Finset.sum_ite_mem]
    rw [hchi, hchi] at h1
    have hint : ∑ s ∈ Sm, (y ᵥ* Q) s ≤ ∑ s ∈ Sp, (y ᵥ* Q) s := by linarith
    calc ∑ s ∈ Sm, lo s ≤ ∑ s ∈ Sm, ((((y ᵥ* Q) s : ℤ) : ℝ) : EReal) :=
          Finset.sum_le_sum (fun s _ => (hbd s).1)
      _ = (((∑ s ∈ Sm, (y ᵥ* Q) s : ℤ) : ℝ) : EReal) := esum _ _
      _ ≤ (((∑ s ∈ Sp, (y ᵥ* Q) s : ℤ) : ℝ) : EReal) := by
          exact EReal.coe_le_coe_iff.mpr (by exact_mod_cast hint)
      _ = ∑ s ∈ Sp, ((((y ᵥ* Q) s : ℤ) : ℝ) : EReal) := (esum _ _).symm
      _ ≤ ∑ s ∈ Sp, up s := Finset.sum_le_sum (fun s _ => (hbd s).2)
  · -- sufficiency via Claim 2.13, Proposition 2.10 and LP duality
    intro h29
    set Lz : S → ℤ := fun s => ⌊(lo s).toReal⌋ with hLzdef
    set Uz : S → ℤ := fun s => ⌊(up s).toReal⌋ with hUzdef
    have hLz : ∀ s, (lo s).toReal = (Lz s : ℝ) := by
      intro s; rcases hlo s with h | ⟨k, h⟩ <;> simp [Lz, h]
    have hUz : ∀ s, (up s).toReal = (Uz s : ℝ) := by
      intro s; rcases hup s with h | ⟨k, h⟩ <;> simp [Uz, h]
    have hLz' : ∀ s, lo s ≠ ⊥ → lo s = ((Lz s : ℝ) : EReal) := by
      intro s hs
      rcases hlo s with h | ⟨k, h⟩
      · exact absurd h hs
      · rw [h]; simp [Lz, h]
    have hUz' : ∀ s, up s ≠ ⊤ → up s = ((Uz s : ℝ) : EReal) := by
      intro s hs
      rcases hup s with h | ⟨k, h⟩
      · exact absurd h hs
      · rw [h]; simp [Uz, h]
    set cost : S ⊕ S → ℤ := Sum.elim (fun s => -Lz s) Uz with hcost
    set f : S ⊕ S → ℚ := 0 with hf
    set g : S ⊕ S → ℚ := Sum.elim (fun s => if lo s = ⊥ then 0 else 1)
      (fun s => if up s = ⊤ then 0 else 1) with hg
    have hfg : f ≤ g := by
      intro t
      rcases t with s | s
      · simp only [hf, hg, Pi.zero_apply, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [hf, hg, Pi.zero_apply, Sum.elim_inr]; split_ifs <;> norm_num
    have hT := proposition_2_10 Q p hbox zStar hz f g hfg
    set rhs := boxRhs (auxRhs Q p zStar) f g with hrhs
    set B := boxMat (auxMat Q) with hB
    -- right-hand side values
    have rhs_nn : ∀ t, (rhs (Sum.inl (Sum.inl t)) : ℝ) = 0 := by
      intro t; simp [rhs, boxRhs, auxRhs]
    have rhs_Q : ∀ i, (rhs (Sum.inl (Sum.inr i)) : ℝ) = (((p - Q *ᵥ zStar) i : ℤ) : ℝ) := by
      intro i; simp [rhs, boxRhs, auxRhs, ratVec]
    have rhs_lo : ∀ t, (rhs (Sum.inr (Sum.inl t)) : ℝ) = 0 := by
      intro t; simp [rhs, boxRhs, f]
    have rhs_up : ∀ t, (rhs (Sum.inr (Sum.inr t)) : ℝ) = -(g t : ℝ) := by
      intro t; simp [rhs, boxRhs]
    have hpQ : ∀ i, (((p - Q *ᵥ zStar) i : ℤ) : ℝ) ≤ 0 := by
      intro i; have := hz i; simp only [Pi.sub_apply]; push_cast
      have : ((p i : ℤ) : ℝ) ≤ (((Q *ᵥ zStar) i : ℤ) : ℝ) := by exact_mod_cast this
      linarith
    have hg0 : ∀ t, 0 ≤ (g t : ℝ) := by
      intro t; have := hfg t; simp only [hf, Pi.zero_apply] at this; exact_mod_cast this
    have rhs_nonpos : ∀ r, (rhs r : ℝ) ≤ 0 := by
      intro r
      rcases r with (t | i) | (t | t)
      · rw [rhs_nn]
      · rw [rhs_Q]; exact hpQ i
      · rw [rhs_lo]
      · rw [rhs_up]; linarith [hg0 t]
    -- a dual feasible solution supported on the box rows
    set Y0 : ((S ⊕ S) ⊕ ι) ⊕ ((S ⊕ S) ⊕ (S ⊕ S)) → ℝ :=
      Sum.elim 0 (Sum.elim (fun t => max (cost t : ℝ) 0) (fun t => max (-(cost t : ℝ)) 0))
      with hY0
    have hY0F : Y0 ∈ DualFeas B cost := by
      refine (feas_iff B cost Y0).mpr ⟨fun r => ?_, fun t => ?_⟩
      · rcases r with r | (t | t)
        · simp [Y0]
        · simp [Y0]
        · simp [Y0]
      · rw [hB, colsum]
        simp only [Y0, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_mul,
          Finset.sum_const_zero, zero_add]
        rcases le_total (cost t : ℝ) 0 with h | h
        · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    have hdual_le : ∀ Y ∈ DualFeas B cost, dualObj rhs Y ≤ 0 := by
      intro Y hY
      obtain ⟨hYnn, -⟩ := (feas_iff B cost Y).mp hY
      unfold dualObj
      exact Finset.sum_nonpos (fun r _ => mul_nonpos_of_nonneg_of_nonpos (hYnn r)
        (rhs_nonpos r))
    have hbdd : BddAbove (dualObj rhs '' DualFeas B cost) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨Y, hY, rfl⟩
      exact hdual_le Y hY
    obtain ⟨Y, hYF, hYopt⟩ := hT cost ⟨Y0, hY0F⟩ hbdd
    obtain ⟨hYnn, hYcol⟩ := (feas_iff B cost _).mp hYF
    -- strong duality for the boxed primal (2.11)
    obtain ⟨xh, yh, hxh, hyh0, hyhA, hval, -⟩ := LP.strong_duality_matrix
      (Matrix.of fun r t => -((B r t : ℚ) : ℝ)) (fun r => -((rhs r : ℚ) : ℝ))
      (fun t => -((cost t : ℤ) : ℝ))
      ⟨0, fun r => by
        have := rhs_nonpos r
        simp only [Matrix.mulVec_zero, Pi.zero_apply]
        linarith⟩
      ⟨Y0, ((feas_iff B cost Y0).mp hY0F).1, by
        funext t
        have := ((feas_iff B cost Y0).mp hY0F).2 t
        simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, neg_mul,
          Finset.sum_neg_distrib, neg_inj]
        rw [← this]; exact Finset.sum_congr rfl (fun _ _ => by ring)⟩
    have hxh' : ∀ r, (rhs r : ℝ) ≤ ∑ t, ((B r t : ℚ) : ℝ) * xh t := by
      intro r
      have := hxh r
      simp only [mulVec, dotProduct, Matrix.of_apply, neg_mul, Finset.sum_neg_distrib] at this
      linarith
    have hyhF : yh ∈ DualFeas B cost := by
      refine (feas_iff B cost yh).mpr ⟨fun r => hyh0 r, fun t => ?_⟩
      have := congrFun hyhA t
      simp only [mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, neg_mul,
        Finset.sum_neg_distrib, neg_inj] at this
      rw [← this]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    have hval' : ∑ t, (cost t : ℝ) * xh t = dualObj rhs yh := by
      unfold dualObj
      simp only [dotProduct, neg_mul, Finset.sum_neg_distrib, neg_inj] at hval
      rw [hval]; exact Finset.sum_congr rfl (fun _ _ => by ring)
    obtain ⟨rv1, rv2, rv3, rv4⟩ := rowval Q xh
    -- the boxed optimum lies in the feasible region of Claim 2.13
    have hmem : (∑ t, (cost t : ℝ) * xh t) ∈ {v : ℝ | ∃ x₁ x₂ : S → ℝ, 0 ≤ x₁ ∧ 0 ≤ x₂ ∧
        (∀ s, lo s = ⊥ → x₁ s = 0) ∧ (∀ s, up s = ⊤ → x₂ s = 0) ∧
        (∀ i, (((p - Q *ᵥ zStar) i : ℤ) : ℝ) ≤
          ∑ s, (Q i s : ℝ) * x₂ s - ∑ s, (Q i s : ℝ) * x₁ s) ∧
        v = ∑ s, (up s).toReal * x₂ s - ∑ s, (lo s).toReal * x₁ s} := by
      have hnn : ∀ t, 0 ≤ xh t := by
        intro t; have := hxh' (Sum.inl (Sum.inl t)); rw [rhs_nn, rv1] at this; exact this
      refine ⟨fun s => xh (Sum.inl s), fun s => xh (Sum.inr s), fun s => hnn _,
        fun s => hnn _, fun s hs => ?_, fun s hs => ?_, fun i => ?_, ?_⟩
      · have := hxh' (Sum.inr (Sum.inr (Sum.inl s)))
        rw [rhs_up, rv4] at this
        simp only [hg, Sum.elim_inl, hs, if_true, Rat.cast_zero, neg_zero] at this
        linarith [hnn (Sum.inl s)]
      · have := hxh' (Sum.inr (Sum.inr (Sum.inr s)))
        rw [rhs_up, rv4] at this
        simp only [hg, Sum.elim_inr, hs, if_true, Rat.cast_zero, neg_zero] at this
        linarith [hnn (Sum.inr s)]
      · have := hxh' (Sum.inl (Sum.inr i))
        rw [rhs_Q, rv2] at this
        exact this
      · rw [Fintype.sum_sum_type]
        simp only [hcost, Sum.elim_inl, Sum.elim_inr, hLz, hUz, Int.cast_neg, neg_mul,
          Finset.sum_neg_distrib]
        ring
    have hpos : 0 ≤ ∑ t, (cost t : ℝ) * xh t :=
      (claim_2_13 Q p hbox zStar hz lo up hlo hup hlu h29).2 hmem
    have hYval : dualObj rhs (fun r => (Y r : ℝ)) = 0 := by
      have h1 := hYopt yh hyhF
      have h2 := hdual_le _ hYF
      linarith
    -- complementary slackness term by term
    have hterm : ∀ r, (Y r : ℝ) * (rhs r : ℝ) = 0 := by
      intro r
      have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun r _ =>
        mul_nonpos_of_nonneg_of_nonpos (hYnn r) (rhs_nonpos r))).mp hYval
      exact hall r (Finset.mem_univ r)
    have hYup : ∀ t, g t = 1 → (Y (Sum.inr (Sum.inr t)) : ℝ) = 0 := by
      intro t ht
      have := hterm (Sum.inr (Sum.inr t))
      rw [rhs_up, ht] at this
      simpa using this
    set y : ι → ℤ := fun i => Y (Sum.inl (Sum.inr i)) with hydef
    have hyQ : ∀ s, ((((y ᵥ* Q) s : ℤ) : ℝ)) = ∑ i, (Y (Sum.inl (Sum.inr i)) : ℝ) * (Q i s : ℝ) := by
      intro s; simp [vecMul, dotProduct, y]
    refine ⟨y, fun i => by have := hYnn (Sum.inl (Sum.inr i)); exact_mod_cast this,
      fun s => ⟨?_, ?_⟩, ?_⟩
    · -- lower bound from the `x₁(s)` column
      by_cases hs : lo s = ⊥
      · rw [hs]; exact bot_le
      have hcol := hYcol (Sum.inl s)
      rw [hB, colsum] at hcol
      simp only [aux_inl, mul_neg, Finset.sum_neg_distrib, hcost, Sum.elim_inl,
        Int.cast_neg] at hcol
      have hup0 := hYup (Sum.inl s) (by simp [hg, hs])
      have h1 := hYnn (Sum.inl (Sum.inl (Sum.inl s)))
      have h2 := hYnn (Sum.inr (Sum.inl (Sum.inl s)))
      rw [hLz' s hs]
      refine EReal.coe_le_coe_iff.mpr ?_
      rw [hyQ]
      linarith
    · -- upper bound from the `x₂(s)` column
      by_cases hs : up s = ⊤
      · rw [hs]; exact le_top
      have hcol := hYcol (Sum.inr s)
      rw [hB, colsum] at hcol
      simp only [aux_inr, hcost, Sum.elim_inr] at hcol
      have hup0 := hYup (Sum.inr s) (by simp [hg, hs])
      have h1 := hYnn (Sum.inl (Sum.inl (Sum.inr s)))
      have h2 := hYnn (Sum.inr (Sum.inl (Sum.inr s)))
      rw [hUz' s hs]
      refine EReal.coe_le_coe_iff.mpr ?_
      rw [hyQ]
      linarith
    · -- y (Q z* - p) = 0
      have h : ∀ i, y i * (p - Q *ᵥ zStar) i = 0 := by
        intro i
        have := hterm (Sum.inl (Sum.inr i))
        rw [rhs_Q] at this
        exact_mod_cast this
      have : y ⬝ᵥ (Q *ᵥ zStar - p) = -(y ⬝ᵥ (p - Q *ᵥ zStar)) := by
        rw [← dotProduct_neg, neg_sub]
      rw [this, neg_eq_zero]
      unfold dotProduct
      exact Finset.sum_eq_zero (fun i _ => h i)
