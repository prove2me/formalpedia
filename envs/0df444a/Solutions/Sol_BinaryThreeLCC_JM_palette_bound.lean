-- Prove2me | solution 1 for BinaryThreeLCC.JM.palette_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:05:49.107678+00:00
-- url     : https://prove2.me/submissions/efca79a1-33df-47b1-a7a1-2f50b4358dd9

import Mathlib

set_option autoImplicit false

namespace BinaryThreeLCC.JM

namespace T7aux

lemma zmod2_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert x y h; decide

lemma zmod2_add_eq_one {x y : ZMod 2} (h : x + y = 1) : x ≠ y := by
  revert x y h; decide

lemma fact32 {V E C : Type} [DecidableEq V] [DecidableEq C]
    (p q : E → V) (c : E → C) (φ : C → V → ZMod 2)
    (hφ : ∀ i e, φ i (p e) + φ i (q e) = if c e = i then 1 else 0) (Ed : Finset E) :
    ∀ (k : ℕ) (S : Finset V), S.Nonempty →
      (∀ v ∈ S, ∃ T : Finset C, k ≤ T.card ∧ ∀ i ∈ T, ∃ e ∈ Ed, c e = i ∧ p e ∈ S ∧
        q e ∈ S ∧ (p e = v ∨ q e = v)) →
      2 ^ k ≤ S.card := by
  intro k
  induction k with
  | zero => intro S hS _; simpa using hS.card_pos
  | succ k ih =>
    intro S hS hT
    obtain ⟨v0, hv0⟩ := hS
    obtain ⟨T, hTc, hTe⟩ := hT v0 hv0
    obtain ⟨i, hi⟩ : T.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, -, hce, hpS, hqS, -⟩ := hTe i hi
    have hne : φ i (p e) ≠ φ i (q e) := by
      have := hφ i e; rw [if_pos hce] at this; exact zmod2_add_eq_one this
    have key : ∀ (P : ZMod 2 → Prop) [DecidablePred P],
        (S.filter (fun x => P (φ i x))).Nonempty →
          2 ^ k ≤ (S.filter (fun x => P (φ i x))).card := by
      intro P _ hne'
      apply ih _ hne'
      intro v hv
      rw [Finset.mem_filter] at hv
      obtain ⟨Tv, hTvc, hTve⟩ := hT v hv.1
      refine ⟨Tv.erase i, ?_, ?_⟩
      · have := Finset.pred_card_le_card_erase (a := i) (s := Tv); omega
      · intro j hj
        rw [Finset.mem_erase] at hj
        obtain ⟨e', he'E, hce', hp', hq', hinc⟩ := hTve j hj.2
        have heq : φ i (p e') = φ i (q e') := by
          have := hφ i e'
          rw [if_neg (by rw [hce']; exact hj.1)] at this
          exact zmod2_add_eq_zero this
        refine ⟨e', he'E, hce', ?_, ?_, hinc⟩
        · rw [Finset.mem_filter]; refine ⟨hp', ?_⟩
          rcases hinc with h | h
          · rw [h]; exact hv.2
          · rw [heq, h]; exact hv.2
        · rw [Finset.mem_filter]; refine ⟨hq', ?_⟩
          rcases hinc with h | h
          · rw [← heq, h]; exact hv.2
          · rw [h]; exact hv.2
    have h0 : 2 ^ k ≤ (S.filter (fun x => φ i x = φ i (p e))).card :=
      key (fun x => x = φ i (p e)) ⟨p e, by simp [hpS]⟩
    have h1 : 2 ^ k ≤ (S.filter (fun x => ¬ φ i x = φ i (p e))).card :=
      key (fun x => ¬ x = φ i (p e)) ⟨q e, by simp [hqS, Ne.symm hne]⟩
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := S) (p := fun x => φ i x = φ i (p e))
    rw [pow_succ]; omega

set_option linter.unusedSectionVars false
variable {V E C : Type} [Fintype V] [Fintype E] [Fintype C] [DecidableEq V] [DecidableEq C]

def dcol (p q : E → V) (c : E → C) (i : C) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => c e = i ∧ p e = v)).card +
    (Finset.univ.filter (fun e => c e = i ∧ q e = v)).card

def dtot (p q : E → V) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => p e = v)).card + (Finset.univ.filter (fun e => q e = v)).card

lemma sum_filter_col (f : E → V) (c : E → C) (v : V) :
    ∑ i, (Finset.univ.filter (fun e => c e = i ∧ f e = v)).card =
      (Finset.univ.filter (fun e => f e = v)).card := by
  have h : ∀ i, (Finset.univ.filter (fun e => c e = i ∧ f e = v)) =
      (Finset.univ.filter (fun e => f e = v)).filter (fun e => c e = i) := by
    intro i; ext e; simp [and_comm]
  simp_rw [h]
  exact (Finset.card_eq_sum_card_fiberwise (by intro x _; simp)).symm

lemma sum_dcol (p q : E → V) (c : E → C) (v : V) : ∑ i, dcol p q c i v = dtot p q v := by
  unfold dcol dtot
  rw [Finset.sum_add_distrib, sum_filter_col, sum_filter_col]

lemma sum_filter_fib (f : E → V) :
    ∑ v, (Finset.univ.filter (fun e => f e = v)).card = Fintype.card E := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise (by intro x _; simp)).symm

lemma sum_dtot (p q : E → V) : ∑ v, dtot p q v = 2 * Fintype.card E := by
  unfold dtot
  rw [Finset.sum_add_distrib, sum_filter_fib, sum_filter_fib]; ring

lemma nbad_le (p q : E → V) (c : E → C) (v : V) :
    ((Finset.univ.filter (fun i => 10 * (dtot p q v : ℝ) <
        (Fintype.card C : ℝ) * dcol p q c i v)).card : ℝ) * 10 ≤ Fintype.card C := by
  set B := Finset.univ.filter (fun i => 10 * (dtot p q v : ℝ) <
        (Fintype.card C : ℝ) * dcol p q c i v) with hB
  rcases B.eq_empty_or_nonempty with h | hne
  · rw [h]; simp
  have h1 : ∑ i ∈ B, (10 * (dtot p q v : ℝ)) < ∑ i ∈ B, (Fintype.card C : ℝ) * dcol p q c i v :=
    Finset.sum_lt_sum_of_nonempty hne (fun i hi => (Finset.mem_filter.mp hi).2)
  have h2 : ∑ i ∈ B, (dcol p q c i v : ℝ) ≤ dtot p q v := by
    rw [← sum_dcol p q c v]; push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => by positivity)
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h1
  have hK : (0 : ℝ) ≤ Fintype.card C := by positivity
  have hd : (0 : ℝ) ≤ dtot p q v := by positivity
  have h3 : (B.card : ℝ) * (10 * dtot p q v) < (Fintype.card C) * dtot p q v :=
    lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_left h2 hK)
  by_contra hc; push Not at hc
  nlinarith

lemma bad_sum_le (p q : E → V) (c : E → C) (hV : 0 < Fintype.card V) (hC : 0 < Fintype.card C)
    (hvar : ∑ v, ∑ i, ((dcol p q c i v : ℝ) - (dtot p q v : ℝ) / Fintype.card C) ^ 2 ≤
      (Fintype.card V : ℝ) * Fintype.card C *
        ((Fintype.card E : ℝ) / (Fintype.card C * Fintype.card V)) ^ 2) :
    ∑ iv ∈ (Finset.univ : Finset (C × V)).filter (fun iv => 10 * (dtot p q iv.2 : ℝ) <
        (Fintype.card C : ℝ) * dcol p q c iv.1 iv.2), (dcol p q c iv.1 iv.2 : ℝ) ≤
      (Fintype.card E : ℝ) / 2 := by
  set K : ℝ := (Fintype.card C : ℝ) with hKdef
  set NV : ℝ := (Fintype.card V : ℝ) with hNV
  set ER : ℝ := (Fintype.card E : ℝ) with hER
  have hK : 0 < K := by rw [hKdef]; exact_mod_cast hC
  have hNVp : 0 < NV := by rw [hNV]; exact_mod_cast hV
  have hERn : 0 ≤ ER := by positivity
  set BP := (Finset.univ : Finset (C × V)).filter (fun iv => 10 * (dtot p q iv.2 : ℝ) <
        K * dcol p q c iv.1 iv.2) with hBP
  set x : C × V → ℝ := fun iv => (dcol p q c iv.1 iv.2 : ℝ) - (dtot p q iv.2 : ℝ) / K with hx
  have hxbad : ∀ iv ∈ BP, (9 / 10 : ℝ) * dcol p q c iv.1 iv.2 ≤ x iv := by
    intro iv hiv
    have h := (Finset.mem_filter.mp hiv).2
    have : (dtot p q iv.2 : ℝ) / K ≤ dcol p q c iv.1 iv.2 / 10 := by
      rw [div_le_iff₀ hK]; nlinarith
    simp only [hx]; linarith
  have hsumx2 : ∑ iv ∈ BP, x iv ^ 2 ≤ ER ^ 2 / (K * NV) := by
    calc ∑ iv ∈ BP, x iv ^ 2 ≤ ∑ iv, x iv ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by positivity)
      _ = ∑ v, ∑ i, ((dcol p q c i v : ℝ) - (dtot p q v : ℝ) / K) ^ 2 := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ ≤ NV * K * (ER / (K * NV)) ^ 2 := hvar
      _ = ER ^ 2 / (K * NV) := by field_simp
  have hcard : (BP.card : ℝ) ≤ NV * K / 10 := by
    have hc : BP.card = ∑ v, (Finset.univ.filter (fun i => 10 * (dtot p q v : ℝ) <
        K * dcol p q c i v)).card := by
      rw [hBP, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro v _; rw [Finset.card_filter]
    rw [hc]; push_cast
    have := fun v => nbad_le p q c v
    have hs : ∑ v, ((Finset.univ.filter (fun i => 10 * (dtot p q v : ℝ) <
        K * dcol p q c i v)).card : ℝ) * 10 ≤ ∑ _v : V, K :=
      Finset.sum_le_sum (fun v _ => this v)
    rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    linarith
  have hcs := sq_sum_le_card_mul_sum_sq (s := BP) (f := x)
  have ht2 : (∑ iv ∈ BP, x iv) ^ 2 ≤ ER ^ 2 / 10 := by
    calc (∑ iv ∈ BP, x iv) ^ 2 ≤ (BP.card : ℝ) * ∑ iv ∈ BP, x iv ^ 2 := hcs
      _ ≤ (NV * K / 10) * (ER ^ 2 / (K * NV)) :=
          mul_le_mul hcard hsumx2 (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
      _ = ER ^ 2 / 10 := by field_simp
  have hsx : (9 / 10 : ℝ) * ∑ iv ∈ BP, (dcol p q c iv.1 iv.2 : ℝ) ≤ ∑ iv ∈ BP, x iv := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hxbad
  have hs0 : 0 ≤ ∑ iv ∈ BP, (dcol p q c iv.1 iv.2 : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
  by_contra hcon; push Not at hcon
  nlinarith

lemma deleted_le (p q : E → V) (c : E → C) (bad : C → V → Prop) [DecidablePred (fun iv : C × V => bad iv.1 iv.2)]
    [DecidablePred (fun e => ¬ bad (c e) (p e) ∧ ¬ bad (c e) (q e))] :
    Fintype.card E ≤ (Finset.univ.filter (fun e => ¬ bad (c e) (p e) ∧ ¬ bad (c e) (q e))).card +
      ∑ iv ∈ (Finset.univ : Finset (C × V)).filter (fun iv => bad iv.1 iv.2), dcol p q c iv.1 iv.2 := by
  set BP := (Finset.univ : Finset (C × V)).filter (fun iv => bad iv.1 iv.2) with hBP
  have hfib : ∀ f : E → V, (Finset.univ.filter (fun e => (c e, f e) ∈ BP)).card =
      ∑ iv ∈ BP, (Finset.univ.filter (fun e => c e = iv.1 ∧ f e = iv.2)).card := by
    intro f
    rw [Finset.card_eq_sum_card_fiberwise (f := fun e => (c e, f e)) (t := BP)
      (by intro x hx; simpa using hx)]
    apply Finset.sum_congr rfl; intro iv hiv; congr 1; ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨-, rfl⟩; simp
    · rintro ⟨h1, h2⟩
      have : (c e, f e) = iv := Prod.ext h1 h2
      exact ⟨this ▸ hiv, this⟩
  have hsum : ∑ iv ∈ BP, dcol p q c iv.1 iv.2 =
      (Finset.univ.filter (fun e => (c e, p e) ∈ BP)).card +
        (Finset.univ.filter (fun e => (c e, q e) ∈ BP)).card := by
    rw [hfib p, hfib q, ← Finset.sum_add_distrib]; rfl
  rw [hsum]
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E))
    (p := fun e => ¬ bad (c e) (p e) ∧ ¬ bad (c e) (q e))
  rw [Finset.card_univ] at hsplit
  letI : DecidableEq E := Classical.decEq E
  have hsub : (Finset.univ.filter (fun e => ¬ (¬ bad (c e) (p e) ∧ ¬ bad (c e) (q e)))) ⊆
      (Finset.univ.filter (fun e => (c e, p e) ∈ BP)) ∪
        (Finset.univ.filter (fun e => (c e, q e) ∈ BP)) := by
    intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hBP, Finset.mem_union] at he ⊢
    by_contra hh; push Not at hh; exact he ⟨hh.1, hh.2⟩
  have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  omega

end T7aux
end BinaryThreeLCC.JM

namespace BinaryThreeLCC.JM

end BinaryThreeLCC.JM

open BinaryThreeLCC.JM BinaryThreeLCC.JM.T7aux

open T7aux in
/-- T7: Lemma 5.3 with Fact 3.2 (parity-labelled coloured multigraph). -/
theorem solution {V E C : Type} [Fintype V] [Fintype E] [Fintype C]
    [DecidableEq V] [DecidableEq C] [Nonempty C]
    (p q : E → V) (c : E → C) (φ : C → V → ZMod 2)
    (hφ : ∀ i e, φ i (p e) + φ i (q e) = if c e = i then 1 else 0)
    (hE : 0 < Fintype.card E)
    (hvar : ∑ v, ∑ i, ((((Finset.univ.filter (fun e => c e = i ∧ p e = v)).card +
        (Finset.univ.filter (fun e => c e = i ∧ q e = v)).card : ℕ) : ℝ) -
        (((Finset.univ.filter (fun e => p e = v)).card +
          (Finset.univ.filter (fun e => q e = v)).card : ℕ) : ℝ) / Fintype.card C) ^ 2 ≤
      (Fintype.card V : ℝ) * Fintype.card C *
        ((Fintype.card E : ℝ) / (Fintype.card C * Fintype.card V)) ^ 2) :
    (Fintype.card C : ℝ) ≤ 60 * Real.logb 2 (Fintype.card V) := by
  have hvar' : ∑ v, ∑ i, ((dcol p q c i v : ℝ) - (dtot p q v : ℝ) / Fintype.card C) ^ 2 ≤
      (Fintype.card V : ℝ) * Fintype.card C *
        ((Fintype.card E : ℝ) / (Fintype.card C * Fintype.card V)) ^ 2 := hvar
  have hC : 0 < Fintype.card C := Fintype.card_pos
  obtain ⟨e0⟩ : Nonempty E := Fintype.card_pos_iff.mp hE
  have hV : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨p e0⟩
  have hbs := bad_sum_le p q c hV hC hvar'
  have hdel := deleted_le p q c
    (fun i v => 10 * (dtot p q v : ℝ) < (Fintype.card C : ℝ) * dcol p q c i v)
  beta_reduce at hdel
  set K : ℝ := (Fintype.card C : ℝ) with hKdef
  have hK : 0 < K := by rw [hKdef]; exact_mod_cast hC
  set ER : ℝ := (Fintype.card E : ℝ) with hER
  have hERp : 0 < ER := by rw [hER]; exact_mod_cast hE
  set E' := Finset.univ.filter (fun e => ¬ (10 * (dtot p q (p e) : ℝ) < K * dcol p q c (c e) (p e))
    ∧ ¬ (10 * (dtot p q (q e) : ℝ) < K * dcol p q c (c e) (q e))) with hE'
  have hE'card : ER / 2 ≤ (E'.card : ℝ) := by
    have h1 : (Fintype.card E : ℝ) ≤ (E'.card : ℝ) + ((∑ iv ∈ (Finset.univ : Finset (C × V)).filter
        (fun iv => 10 * (dtot p q iv.2 : ℝ) < K * dcol p q c iv.1 iv.2),
          dcol p q c iv.1 iv.2 : ℕ) : ℝ) := by exact_mod_cast hdel
    push_cast at h1
    linarith
  have hgood : ∀ e ∈ E', K * dcol p q c (c e) (p e) ≤ 10 * (dtot p q (p e) : ℝ) ∧
      K * dcol p q c (c e) (q e) ≤ 10 * (dtot p q (q e) : ℝ) := by
    intro e he
    rw [hE', Finset.mem_filter] at he
    exact ⟨not_lt.mp he.2.1, not_lt.mp he.2.2⟩
  classical
  set P := Finset.univ.filter (fun v => 0 < dtot p q v) with hP
  set f : Finset V → ℝ := fun S => ((E'.filter (fun e => p e ∈ S ∧ q e ∈ S)).card : ℝ) -
    ∑ v ∈ S, (dtot p q v : ℝ) / 6 with hf
  obtain ⟨S, hSP, hmax⟩ := Finset.exists_max_image P.powerset f ⟨P, Finset.mem_powerset_self P⟩
  have hSP' : S ⊆ P := Finset.mem_powerset.mp hSP
  have hfP : ER / 6 ≤ f P := by
    have h1 : E'.filter (fun e => p e ∈ P ∧ q e ∈ P) = E' := by
      apply Finset.filter_true_of_mem
      intro e _
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · unfold dtot
        have : 0 < (Finset.univ.filter (fun e' => p e' = p e)).card :=
          Finset.card_pos.mpr ⟨e, by simp⟩
        omega
      · unfold dtot
        have : 0 < (Finset.univ.filter (fun e' => q e' = q e)).card :=
          Finset.card_pos.mpr ⟨e, by simp⟩
        omega
    have h2 : ∑ v ∈ P, (dtot p q v : ℝ) / 6 = ∑ v, (dtot p q v : ℝ) / 6 := by
      rw [hP]; apply Finset.sum_filter_of_ne
      intro v _ hv
      by_contra h0
      apply hv; simp only [not_lt, Nat.le_zero] at h0; simp [h0]
    have h3 : ∑ v, (dtot p q v : ℝ) = 2 * ER := by
      rw [hER]; exact_mod_cast sum_dtot p q
    simp only [hf]
    rw [h1, h2, ← Finset.sum_div, h3]
    linarith
  have hfS : ER / 6 ≤ f S := le_trans hfP (hmax P (Finset.mem_powerset_self P))
  have hSne : S.Nonempty := by
    by_contra h0
    rw [Finset.not_nonempty_iff_eq_empty] at h0
    simp only [hf, h0] at hfS
    simp at hfS
    linarith
  have hdeg : ∀ v ∈ S, (dtot p q v : ℝ) / 6 ≤
      ((E'.filter (fun e => p e ∈ S ∧ q e ∈ S ∧ (p e = v ∨ q e = v))).card : ℝ) := by
    intro v hv
    have hm := hmax (S.erase v) (Finset.mem_powerset.mpr ((Finset.erase_subset v S).trans hSP'))
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := E'.filter (fun e => p e ∈ S ∧ q e ∈ S)) (p := fun e => p e = v ∨ q e = v)
    have e1 : (E'.filter (fun e => p e ∈ S ∧ q e ∈ S)).filter (fun e => p e = v ∨ q e = v) =
        E'.filter (fun e => p e ∈ S ∧ q e ∈ S ∧ (p e = v ∨ q e = v)) := by
      ext e; simp only [Finset.mem_filter]; tauto
    have e2 : (E'.filter (fun e => p e ∈ S ∧ q e ∈ S)).filter (fun e => ¬ (p e = v ∨ q e = v)) =
        E'.filter (fun e => p e ∈ S.erase v ∧ q e ∈ S.erase v) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
    rw [e1, e2] at hsplit
    have hsum := Finset.add_sum_erase S (fun v => (dtot p q v : ℝ) / 6) hv
    simp only [hf] at hm
    have hcast : ((E'.filter (fun e => p e ∈ S ∧ q e ∈ S)).card : ℝ) =
        ((E'.filter (fun e => p e ∈ S ∧ q e ∈ S ∧ (p e = v ∨ q e = v))).card : ℝ) +
        ((E'.filter (fun e => p e ∈ S.erase v ∧ q e ∈ S.erase v)).card : ℝ) := by
      exact_mod_cast hsplit.symm
    linarith
  have hcols : ∀ v ∈ S, K ≤ 60 * ((Finset.univ.filter (fun i => ∃ e ∈ E', c e = i ∧ p e ∈ S ∧
      q e ∈ S ∧ (p e = v ∨ q e = v))).card : ℝ) := by
    intro v hv
    set cols := Finset.univ.filter (fun i => ∃ e ∈ E', c e = i ∧ p e ∈ S ∧
      q e ∈ S ∧ (p e = v ∨ q e = v)) with hcolsdef
    have hdpos : (0 : ℝ) < dtot p q v := by
      have := hSP' hv
      rw [hP, Finset.mem_filter] at this
      exact_mod_cast this.2
    have hinc : (E'.filter (fun e => p e ∈ S ∧ q e ∈ S ∧ (p e = v ∨ q e = v))).card ≤
        ∑ i ∈ cols, dcol p q c i v := by
      calc (E'.filter (fun e => p e ∈ S ∧ q e ∈ S ∧ (p e = v ∨ q e = v))).card
          ≤ (cols.biUnion (fun i => Finset.univ.filter (fun e => c e = i ∧ p e = v) ∪
              Finset.univ.filter (fun e => c e = i ∧ q e = v))).card := by
            apply Finset.card_le_card
            intro e he
            rw [Finset.mem_filter] at he
            rw [Finset.mem_biUnion]
            refine ⟨c e, ?_, ?_⟩
            · rw [hcolsdef, Finset.mem_filter]
              exact ⟨Finset.mem_univ _, e, he.1, rfl, he.2⟩
            · rcases he.2.2.2 with h | h <;> simp [h]
        _ ≤ ∑ i ∈ cols, (Finset.univ.filter (fun e => c e = i ∧ p e = v) ∪
              Finset.univ.filter (fun e => c e = i ∧ q e = v)).card := Finset.card_biUnion_le
        _ ≤ ∑ i ∈ cols, dcol p q c i v := by
            apply Finset.sum_le_sum; intro i _
            unfold dcol; exact Finset.card_union_le _ _
    have hcolbound : ∀ i ∈ cols, (dcol p q c i v : ℝ) ≤ 10 * dtot p q v / K := by
      intro i hi
      rw [hcolsdef, Finset.mem_filter] at hi
      obtain ⟨e, heE', hce, -, -, hinc⟩ := hi.2
      have hg := hgood e heE'
      rw [le_div_iff₀ hK]
      rcases hinc with h | h
      · have := hg.1; rw [hce, h] at this; linarith
      · have := hg.2; rw [hce, h] at this; linarith
    have hsumle : ((∑ i ∈ cols, dcol p q c i v : ℕ) : ℝ) ≤ cols.card * (10 * dtot p q v / K) := by
      push_cast
      calc ∑ i ∈ cols, (dcol p q c i v : ℝ) ≤ ∑ i ∈ cols, (10 * dtot p q v / K) :=
            Finset.sum_le_sum hcolbound
        _ = cols.card * (10 * dtot p q v / K) := by rw [Finset.sum_const, nsmul_eq_mul]
    have h1 : (dtot p q v : ℝ) / 6 ≤ cols.card * (10 * dtot p q v / K) := by
      have := hdeg v hv
      have h' : ((E'.filter (fun e => p e ∈ S ∧ q e ∈ S ∧ (p e = v ∨ q e = v))).card : ℝ) ≤
          ((∑ i ∈ cols, dcol p q c i v : ℕ) : ℝ) := by exact_mod_cast hinc
      linarith
    have h2 : K * ((dtot p q v : ℝ) / 6) ≤ K * (cols.card * (10 * dtot p q v / K)) :=
      mul_le_mul_of_nonneg_left h1 hK.le
    have h3 : K * (cols.card * (10 * dtot p q v / K)) = (60 * cols.card) * (dtot p q v / 6) := by
      field_simp; ring
    rw [h3] at h2
    have h4 := le_of_mul_le_mul_right h2 (by positivity : (0:ℝ) < dtot p q v / 6)
    linarith
  set k' : ℕ := ⌈K / 60⌉₊ with hk'
  have hT : ∀ v ∈ S, ∃ T : Finset C, k' ≤ T.card ∧ ∀ i ∈ T, ∃ e ∈ E', c e = i ∧ p e ∈ S ∧
      q e ∈ S ∧ (p e = v ∨ q e = v) := by
    intro v hv
    refine ⟨Finset.univ.filter (fun i => ∃ e ∈ E', c e = i ∧ p e ∈ S ∧
      q e ∈ S ∧ (p e = v ∨ q e = v)), ?_, ?_⟩
    · rw [hk', Nat.ceil_le]
      have := hcols v hv
      linarith
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have h2k := fact32 p q c φ hφ E' k' S hSne hT
  have hScard : S.card ≤ Fintype.card V := Finset.card_le_univ S
  have hlog : (k' : ℝ) ≤ Real.logb 2 (Fintype.card V) := by
    rw [Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast hV), Real.rpow_natCast]
    exact_mod_cast h2k.trans hScard
  have hceil : K / 60 ≤ (k' : ℝ) := Nat.le_ceil _
  linarith


namespace BinaryThreeLCC.JM

end BinaryThreeLCC.JM
