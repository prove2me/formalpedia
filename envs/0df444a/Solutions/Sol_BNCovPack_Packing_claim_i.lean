-- Prove2me | solution 1 for BNCovPack.Packing.claim_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-21T22:01:32.151753+00:00
-- url     : https://prove2.me/submissions/ec404588-3a01-451f-8098-1a07b6446fcb

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMax
import Definitions.Def_OnlinePrimalDual_GeneralPacking_aMin
import Definitions.Def_BNCovPack_Packing_Scheme



namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

section aux

variable {I : Type*} [Fintype I] {m : ℕ} (inst : GeneralInstance I (Fin m))

lemma le_prefixMax (i : I) {k j : Fin m} (h : k ≤ j) : inst.a i k ≤ prefixMax inst i j := by
  unfold prefixMax
  exact Finset.le_sup' (inst.a i) (Finset.mem_filter.mpr ⟨Finset.mem_univ k, h⟩)

lemma prefixMax_nonneg (i : I) (j : Fin m) : 0 ≤ prefixMax inst i j :=
  (inst.ha_nonneg i j).trans (le_prefixMax inst i le_rfl)

lemma prefixMax_mono (i : I) {j j' : Fin m} (h : j ≤ j') :
    prefixMax inst i j ≤ prefixMax inst i j' := by
  refine Finset.sup'_le _ _ (fun k hk => ?_)
  have hk2 : k ≤ j := (Finset.mem_filter.mp hk).2
  exact le_prefixMax inst i (le_trans hk2 h)

lemma increment_nonneg {B : ℝ} (hB : 0 < B) {y : Fin m → ℝ} (hy : ∀ k, 0 ≤ y k)
    (j : Fin m) (i : I) : 0 ≤ increment inst B y j i := by
  unfold increment
  apply mul_nonneg
  · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) (prefixMax_nonneg inst i j))
  · have : 0 ≤ B / (2 * inst.c i) *
        ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k := by
      apply mul_nonneg
      · exact div_nonneg hB.le (by have := inst.hc_pos i; positivity)
      · exact Finset.sum_nonneg fun k _ => mul_nonneg (inst.ha_nonneg i k) (hy k)
    linarith [Real.one_le_exp this]

lemma increment_update_of_lt (B : ℝ) (y : Fin m → ℝ) {j j' : Fin m} (h : j' < j) (t : ℝ)
    (i : I) :
    increment inst B (Function.update y j t) j' i = increment inst B y j' i := by
  have hs : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j'),
      inst.a i k * Function.update y j t k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j'), inst.a i k * y k := by
    apply Finset.sum_congr rfl
    intro k hk
    have : k ≠ j := ne_of_lt (lt_of_le_of_lt (Finset.mem_filter.mp hk).2 h)
    rw [Function.update_of_ne this]
  unfold increment
  rw [hs]

lemma sum_update_linear (y : Fin m → ℝ) (j : Fin m) (t : ℝ) (i : I) :
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * Function.update y j t k =
    ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * Function.update y j 0 k
      + inst.a i j * t := by
  have h : ∀ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
      inst.a i k * Function.update y j t k =
      inst.a i k * Function.update y j 0 k + (if k = j then inst.a i j * t else 0) := by
    intro k _
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk, Function.update_of_ne hk]
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma increment_update_eq (B : ℝ) (y : Fin m → ℝ) (j : Fin m) (t : ℝ) (i : I) :
    increment inst B (Function.update y j t) j i =
    1 / ((Fintype.card I : ℝ) * prefixMax inst i j) *
      (Real.exp (B / (2 * inst.c i) *
        (∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
            inst.a i k * Function.update y j 0 k + inst.a i j * t)) - 1) := by
  unfold increment
  rw [sum_update_linear]

lemma increment_mono_j [Nonempty I] {B : ℝ} (hB : 0 < B) {y : Fin m → ℝ} (hy : ∀ k, 0 ≤ y k)
    {j j' : Fin m} (hjj : j ≤ j') (hz : ∀ k : Fin m, j < k → y k = 0) (i : I) :
    increment inst B y j' i ≤ increment inst B y j i := by
  have hs : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j'), inst.a i k * y k =
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k := by
    symm
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, (Finset.mem_filter.mp hk).2.trans hjj⟩
    · intro k _ hk
      have : j < k := by
        by_contra hc
        exact hk (Finset.mem_filter.mpr ⟨Finset.mem_univ k, not_lt.mp hc⟩)
      rw [hz k this, mul_zero]
  have hnpos : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hE : 0 ≤ Real.exp (B / (2 * inst.c i) *
      ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k) - 1 := by
    have : 0 ≤ B / (2 * inst.c i) *
        ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k := by
      apply mul_nonneg
      · exact div_nonneg hB.le (by have := inst.hc_pos i; positivity)
      · exact Finset.sum_nonneg fun k _ => mul_nonneg (inst.ha_nonneg i k) (hy k)
    linarith [Real.one_le_exp this]
  unfold increment
  rw [hs]
  rcases (prefixMax_nonneg inst i j).eq_or_lt with h0 | hpos
  · -- prefixMax = 0: sum is zero
    have hS : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * y k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have h1 := le_prefixMax inst i (Finset.mem_filter.mp hk).2
      have h2 := inst.ha_nonneg i k
      have : inst.a i k = 0 := by rw [← h0] at h1; linarith
      rw [this, zero_mul]
    rw [hS]; simp
  · have hpm' : prefixMax inst i j ≤ prefixMax inst i j' := prefixMax_mono inst i hjj
    apply mul_le_mul_of_nonneg_right _ hE
    apply one_div_le_one_div_of_le (mul_pos hnpos hpos)
    exact mul_le_mul_of_nonneg_left hpm' hnpos.le

end aux

structure Inv {I : Type*} [Fintype I] {m : ℕ} (inst : GeneralInstance I (Fin m)) (B : ℝ)
    (s : State I m) (r : ℕ) : Prop where
  x_nn : ∀ i, 0 ≤ s.x i
  y_nn : ∀ k, 0 ≤ s.y k
  y_zero : ∀ k : Fin m, r ≤ (k : ℕ) → s.y k = 0
  inc_le : ∀ j : Fin m, (j : ℕ) < r → ∀ i, increment inst B s.y j i ≤ s.x i

section round

variable {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} (inst : GeneralInstance I (Fin m))

lemma inv_key0 {B : ℝ} (hB : 0 < B) {s : State I m} (j : Fin m) (hs : Inv inst B s j) (i : I) :
    increment inst B s.y j i ≤ s.x i := by
  rcases Nat.eq_zero_or_pos (j : ℕ) with h0 | hpos
  · have hy : ∀ k : Fin m, s.y k = 0 := fun k => hs.y_zero k (by omega)
    have : increment inst B s.y j i = 0 := by
      unfold increment
      have hS : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i k * s.y k = 0 :=
        Finset.sum_eq_zero fun k _ => by rw [hy k, mul_zero]
      rw [hS]; simp
    rw [this]; exact hs.x_nn i
  · let j' : Fin m := ⟨(j : ℕ) - 1, by omega⟩
    have hj'j : j' ≤ j := by show (j : ℕ) - 1 ≤ (j : ℕ); omega
    have h1 := hs.inc_le j' (by show (j : ℕ) - 1 < (j : ℕ); omega) i
    have h2 := increment_mono_j inst hB hs.y_nn hj'j
      (fun k hk => hs.y_zero k (by
        have : ((j' : Fin m) : ℕ) < (k : ℕ) := hk
        have h3 : ((j' : Fin m) : ℕ) = (j : ℕ) - 1 := rfl
        omega)) i
    linarith

lemma key_est {α b g t : ℝ} (hα : 0 ≤ α) :
    α * (Real.exp (b + g * t) - 1) - α * (Real.exp b - 1) ≤
      g * t * (α * (Real.exp (b + g * t) - 1) + α) := by
  have h1 : Real.exp b = Real.exp (b + g * t) * Real.exp (-(g * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 := Real.add_one_le_exp (-(g * t))
  have hE := Real.exp_pos (b + g * t)
  have h3 : Real.exp (b + g * t) - Real.exp b ≤ g * t * Real.exp (b + g * t) := by
    rw [h1]; nlinarith [mul_le_mul_of_nonneg_left h2 hE.le]
  nlinarith [mul_le_mul_of_nonneg_left h3 hα]

noncomputable def fcol {B : ℝ} (s : State I m) (j : Fin m) (t : ℝ) : ℝ :=
  ∑ i, inst.a i j * primalAt inst B s j t i

lemma update_zero_self {B : ℝ} {s : State I m} (j : Fin m) (hs : Inv inst B s j) :
    Function.update s.y j 0 = s.y :=
  Function.update_eq_self_iff.mpr (hs.y_zero j le_rfl).symm

lemma fcol_zero {B : ℝ} (hB : 0 < B) {s : State I m} (j : Fin m) (hs : Inv inst B s j) :
    fcol inst (B := B) s j 0 = ∑ i, inst.a i j * s.x i := by
  unfold fcol
  apply Finset.sum_congr rfl
  intro i _
  unfold primalAt
  rw [update_zero_self inst j hs, max_eq_left (inv_key0 inst hB j hs i)]

lemma fcol_continuous {B : ℝ} (s : State I m) (j : Fin m) :
    Continuous (fcol inst (B := B) s j) := by
  unfold fcol
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul continuous_const
  show Continuous fun t => max (s.x i) (increment inst B (Function.update s.y j t) j i)
  apply Continuous.max continuous_const
  simp only [increment_update_eq]
  fun_prop

lemma roundValue_spec {B : ℝ} (hB : 0 < B) {s : State I m} (j : Fin m) (hs : Inv inst B s j)
    (hj : ∃ i, 0 < inst.a i j) (h1 : ¬ 1 ≤ ∑ i, inst.a i j * s.x i) :
    0 < roundValue inst B s j ∧ fcol inst (B := B) s j (roundValue inst B s j) = 1 := by
  have hcont := fcol_continuous inst (B := B) s j
  have hf0 := fcol_zero inst hB j hs
  have hf0' : fcol inst (B := B) s j 0 < 1 := by rw [hf0]; exact not_le.mp h1
  have hupd := update_zero_self inst j hs
  have hne : ∃ t, t ∈ {t : ℝ | 0 ≤ t ∧ 1 ≤ fcol inst (B := B) s j t} := by
    obtain ⟨i0, hi0⟩ := hj
    have hpm : 0 < prefixMax inst i0 j := lt_of_lt_of_le hi0 (le_prefixMax inst i0 le_rfl)
    have hn : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
    have hc := inst.hc_pos i0
    set A := inst.a i0 j with hA
    set α : ℝ := 1 / ((Fintype.card I : ℝ) * prefixMax inst i0 j) with hα
    have hαpos : 0 < α := by rw [hα]; positivity
    set κ : ℝ := B / (2 * inst.c i0) with hκ
    have hκpos : 0 < κ := by rw [hκ]; positivity
    set S := ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j), inst.a i0 k * s.y k with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => mul_nonneg (inst.ha_nonneg _ _) (hs.y_nn k)
    set t0 : ℝ := 1 / (A * A * α * κ) with ht0
    have ht0pos : 0 < t0 := by rw [ht0]; positivity
    refine ⟨t0, ht0pos.le, ?_⟩
    have hinc : increment inst B (Function.update s.y j t0) j i0 =
        α * (Real.exp (κ * (S + A * t0)) - 1) := by
      rw [increment_update_eq, hupd]
    have hexp := Real.add_one_le_exp (κ * (S + A * t0))
    have hge : α * (κ * (A * t0)) ≤ increment inst B (Function.update s.y j t0) j i0 := by
      rw [hinc]
      apply mul_le_mul_of_nonneg_left _ hαpos.le
      nlinarith [mul_nonneg hκpos.le hS0]
    have hterm : inst.a i0 j * increment inst B (Function.update s.y j t0) j i0 ≤
        fcol inst (B := B) s j t0 := by
      unfold fcol
      calc inst.a i0 j * increment inst B (Function.update s.y j t0) j i0
          ≤ inst.a i0 j * primalAt inst B s j t0 i0 := by
            apply mul_le_mul_of_nonneg_left (le_max_right _ _) (inst.ha_nonneg _ _)
        _ ≤ _ := Finset.single_le_sum (f := fun i => inst.a i j * primalAt inst B s j t0 i)
            (fun i _ => mul_nonneg (inst.ha_nonneg _ _)
              (le_trans (hs.x_nn i) (le_max_left _ _))) (Finset.mem_univ i0)
    have h1' : 1 = A * (α * (κ * (A * t0))) := by
      rw [ht0]; field_simp
    calc (1 : ℝ) = A * (α * (κ * (A * t0))) := h1'
      _ ≤ A * increment inst B (Function.update s.y j t0) j i0 :=
          mul_le_mul_of_nonneg_left hge hi0.le
      _ ≤ _ := hterm
  have hbdd : BddBelow {t : ℝ | 0 ≤ t ∧ 1 ≤ fcol inst (B := B) s j t} := ⟨0, fun t ht => ht.1⟩
  have hclosed : IsClosed {t : ℝ | 0 ≤ t ∧ 1 ≤ fcol inst (B := B) s j t} :=
    (isClosed_Ici (a := (0 : ℝ))).inter (isClosed_le continuous_const hcont)
  have hmem := hclosed.csInf_mem hne hbdd
  have hT : roundValue inst B s j = sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ fcol inst (B := B) s j t} := rfl
  rw [hT]
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = sInf {t : ℝ | 0 ≤ t ∧ 1 ≤ fcol inst (B := B) s j t} := ⟨_, rfl⟩
  rw [← hτ] at hmem ⊢
  obtain ⟨hτ0, hτ1⟩ := hmem
  have hτne : τ ≠ 0 := by
    rintro rfl
    linarith
  have hτpos : 0 < τ := lt_of_le_of_ne hτ0 (Ne.symm hτne)
  refine ⟨hτpos, ?_⟩
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hτ0 hcont.continuousOn
    (show (1 : ℝ) ∈ Set.Icc (fcol inst (B := B) s j 0) (fcol inst (B := B) s j τ) from
      ⟨hf0'.le, hτ1⟩)
  have hle : τ ≤ t := by
    rw [hτ]
    exact csInf_le hbdd ⟨ht.1, hft.ge⟩
  have : t = τ := le_antisymm ht.2 hle
  rw [← this]; exact hft

lemma alpha_sum_le (j : Fin m) :
    ∑ i, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j)) ≤ 1 := by
  have hn : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have h : ∀ i : I, inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j)) ≤
      1 / (Fintype.card I : ℝ) := by
    intro i
    have hle := le_prefixMax inst i (le_refl j)
    rcases (prefixMax_nonneg inst i j).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · rw [mul_one_div, div_le_iff₀ (by positivity)]
      have : 1 / (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) * prefixMax inst i j) =
          prefixMax inst i j := by field_simp
      rw [this]; exact hle
  calc _ ≤ ∑ _i : I, 1 / (Fintype.card I : ℝ) := Finset.sum_le_sum fun i _ => h i
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

lemma round_spec {B : ℝ} (hB : 0 < B) {s : State I m} (j : Fin m) (hs : Inv inst B s j)
    (hj : ∃ i, 0 < inst.a i j) :
    Inv inst B (runRound inst B s j) ((j : ℕ) + 1) ∧
    (∀ i, s.x i ≤ (runRound inst B s j).x i) ∧
    1 ≤ ∑ i, inst.a i j * (runRound inst B s j).x i ∧
    ∑ i, inst.c i * (runRound inst B s j).x i ≤
      ∑ i, inst.c i * s.x i + B * (runRound inst B s j).y j ∧
    (∀ k, k ≠ j → (runRound inst B s j).y k = s.y k) ∧
    (∀ i, (runRound inst B s j).x i ≤ s.x i ∨
      (0 < inst.a i j ∧ (runRound inst B s j).x i ≤ 1 / inst.a i j)) := by
  have hupd := update_zero_self inst j hs
  by_cases h1 : 1 ≤ ∑ i, inst.a i j * s.x i
  · have hr : runRound inst B s j = ⟨s.x, s.y⟩ := by
      unfold runRound; rw [if_pos h1, hupd]
    rw [hr]
    refine ⟨⟨hs.x_nn, hs.y_nn, fun k hk => hs.y_zero k (by omega), ?_⟩, fun i => le_rfl, h1,
      by simp [hs.y_zero j le_rfl], fun k _ => rfl, fun i => Or.inl le_rfl⟩
    intro j' hj' i
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | heq
    · exact hs.inc_le j' hlt i
    · have : j' = j := Fin.ext heq
      subst this
      exact inv_key0 inst hB j' hs i
  · obtain ⟨hτpos, hfτ⟩ := roundValue_spec inst hB j hs hj h1
    have hr : runRound inst B s j = ⟨primalAt inst B s j (roundValue inst B s j),
        Function.update s.y j (roundValue inst B s j)⟩ := by
      unfold runRound; rw [if_neg h1]
    rw [hr]
    generalize roundValue inst B s j = τ at hτpos hfτ ⊢
    have hynn : ∀ k, 0 ≤ Function.update s.y j τ k := by
      intro k
      by_cases hk : k = j
      · subst hk; simp [hτpos.le]
      · rw [Function.update_of_ne hk]; exact hs.y_nn k
    have hn : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
    -- per-coordinate estimate
    have hUV : ∀ i, increment inst B (Function.update s.y j τ) j i - increment inst B s.y j i ≤
        B / (2 * inst.c i) * inst.a i j * τ *
          (increment inst B (Function.update s.y j τ) j i +
            1 / ((Fintype.card I : ℝ) * prefixMax inst i j)) := by
      intro i
      have hα : 0 ≤ 1 / ((Fintype.card I : ℝ) * prefixMax inst i j) :=
        div_nonneg zero_le_one (mul_nonneg hn.le (prefixMax_nonneg inst i j))
      have e1 := increment_update_eq inst B s.y j τ i
      have e0 := increment_update_eq inst B s.y j 0 i
      rw [hupd] at e1 e0
      have := key_est (α := 1 / ((Fintype.card I : ℝ) * prefixMax inst i j))
        (b := B / (2 * inst.c i) * ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
            inst.a i k * s.y k)
        (g := B / (2 * inst.c i) * inst.a i j) (t := τ) hα
      have e1' : increment inst B (Function.update s.y j τ) j i =
          1 / ((Fintype.card I : ℝ) * prefixMax inst i j) *
          (Real.exp (B / (2 * inst.c i) * ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
            inst.a i k * s.y k + B / (2 * inst.c i) * inst.a i j * τ) - 1) := by
        rw [e1]; congr 3; ring
      have e0' : increment inst B s.y j i =
          1 / ((Fintype.card I : ℝ) * prefixMax inst i j) *
          (Real.exp (B / (2 * inst.c i) * ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ j),
            inst.a i k * s.y k) - 1) := rfl
      rw [e1', e0']
      exact this
    set U : I → ℝ := fun i => increment inst B (Function.update s.y j τ) j i with hU
    have hU0 : ∀ i, 0 ≤ U i := fun i => increment_nonneg inst hB hynn j i
    have hX : ∀ i, inst.c i * primalAt inst B s j τ i ≤
        inst.c i * s.x i + B / 2 * τ *
          (inst.a i j * U i + inst.a i j * (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) := by
      intro i
      have hc := inst.hc_pos i
      have hα : 0 ≤ 1 / ((Fintype.card I : ℝ) * prefixMax inst i j) :=
        div_nonneg zero_le_one (mul_nonneg hn.le (prefixMax_nonneg inst i j))
      have hv := inv_key0 inst hB j hs i
      have hUVi := hUV i
      have hai := inst.ha_nonneg i j
      have key : inst.c i * (B / (2 * inst.c i) * inst.a i j * τ *
          (U i + 1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) =
          B / 2 * τ * (inst.a i j * U i + inst.a i j *
            (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) := by
        field_simp
      show inst.c i * max (s.x i) (U i) ≤ _
      rcases le_total (U i) (s.x i) with h | h
      · rw [max_eq_left h]
        have : 0 ≤ B / 2 * τ * (inst.a i j * U i + inst.a i j *
            (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) :=
          mul_nonneg (mul_nonneg (by linarith) hτpos.le)
            (add_nonneg (mul_nonneg hai (hU0 i)) (mul_nonneg hai hα))
        linarith
      · rw [max_eq_right h]
        have h3 := mul_le_mul_of_nonneg_left hUVi hc.le
        have h4 : 0 ≤ inst.c i * (s.x i - increment inst B s.y j i) :=
          mul_nonneg hc.le (sub_nonneg.2 hv)
        rw [key] at h3
        nlinarith
    have hu_sum : ∑ i, inst.a i j * U i ≤ 1 := by
      calc ∑ i, inst.a i j * U i ≤ ∑ i, inst.a i j * primalAt inst B s j τ i :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (le_max_right _ _) (inst.ha_nonneg i j)
        _ = 1 := hfτ
    have hα_sum := alpha_sum_le inst j
    have hsum : ∑ i, inst.c i * primalAt inst B s j τ i ≤
        ∑ i, inst.c i * s.x i + B * τ := by
      calc ∑ i, inst.c i * primalAt inst B s j τ i
          ≤ ∑ i, (inst.c i * s.x i + B / 2 * τ *
            (inst.a i j * U i + inst.a i j *
              (1 / ((Fintype.card I : ℝ) * prefixMax inst i j)))) :=
            Finset.sum_le_sum fun i _ => hX i
        _ = ∑ i, inst.c i * s.x i + B / 2 * τ * (∑ i, inst.a i j * U i + ∑ i, inst.a i j *
              (1 / ((Fintype.card I : ℝ) * prefixMax inst i j))) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ ∑ i, inst.c i * s.x i + B / 2 * τ * 2 := by
            have : 0 ≤ B / 2 * τ := mul_nonneg (by linarith) hτpos.le
            nlinarith
        _ = _ := by ring
    refine ⟨⟨?_, hynn, ?_, ?_⟩, fun i => le_max_left _ _, le_of_eq hfτ.symm, ?_, ?_, ?_⟩
    · intro i; exact le_trans (hs.x_nn i) (le_max_left _ _)
    · intro k hk
      have hkj : k ≠ j := fun h => by subst h; omega
      show Function.update s.y j τ k = 0
      rw [Function.update_of_ne hkj]; exact hs.y_zero k (by omega)
    · intro j' hj' i
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hlt | heq
      · show increment inst B (Function.update s.y j τ) j' i ≤ max (s.x i) _
        rw [increment_update_of_lt inst B s.y (show j' < j from hlt)]
        exact le_trans (hs.inc_le j' hlt i) (le_max_left _ _)
      · have : j' = j := Fin.ext heq
        subst this
        exact le_max_right _ _
    · show _ ≤ _ + B * Function.update s.y j τ j
      rw [Function.update_self]; exact hsum
    · intro k hk
      exact Function.update_of_ne hk _ _
    · intro i
      show max (s.x i) (U i) ≤ s.x i ∨ (0 < inst.a i j ∧ max (s.x i) (U i) ≤ 1 / inst.a i j)
      by_cases hu : U i ≤ s.x i
      · exact Or.inl (max_le le_rfl hu)
      · right
        have hux : s.x i < U i := not_le.mp hu
        have hv := inv_key0 inst hB j hs i
        have hpos : 0 < inst.a i j := by
          rcases (inst.ha_nonneg i j).eq_or_lt with h0 | h0
          · exfalso
            have := hUV i
            rw [← h0] at this
            simp at this
            linarith
          · exact h0
        refine ⟨hpos, ?_⟩
        rw [max_eq_right hux.le, le_div_iff₀ hpos]
        have := Finset.single_le_sum (f := fun i => inst.a i j * U i)
          (fun i _ => mul_nonneg (inst.ha_nonneg i j) (hU0 i)) (Finset.mem_univ i)
        nlinarith

lemma aMin_nonneg (i : I) : 0 ≤ aMin inst i := by
  unfold aMin
  split_ifs with h
  · apply Finset.le_min'
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact inst.ha_nonneg i k
  · exact le_rfl

lemma aMin_spec (i : I) (j : Fin m) (h : 0 < inst.a i j) :
    0 < aMin inst i ∧ aMin inst i ≤ inst.a i j := by
  unfold aMin
  have hj : inst.a i j ∈ (Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i) :=
    Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.ne'⟩, rfl⟩
  have hne : ((Finset.univ.filter (fun k => inst.a i k ≠ 0)).image (inst.a i)).Nonempty :=
    ⟨_, hj⟩
  rw [dif_pos hne]
  constructor
  · obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
    rw [← hkeq]
    exact lt_of_le_of_ne (inst.ha_nonneg i k) (Ne.symm (Finset.mem_filter.mp hk).2)
  · exact Finset.min'_le _ _ hj

lemma stateAfter_succ {B : ℝ} (r : ℕ) (h : r < m) :
    stateAfter inst B (r + 1) = runRound inst B (stateAfter inst B r) ⟨r, h⟩ := by
  rw [stateAfter, dif_pos h]

lemma master {B : ℝ} (hB : 0 < B) (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ r : ℕ, r ≤ m → Inv inst B (stateAfter inst B r) r ∧
      (∀ k : Fin m, (k : ℕ) < r → 1 ≤ ∑ i, inst.a i k * (stateAfter inst B r).x i) ∧
      primalValue inst B r ≤ B * dualValue inst B r ∧
      (∀ i, (stateAfter inst B r).x i ≤ 1 / aMin inst i) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro i; simp [stateAfter, initState]
    · intro k; simp [stateAfter, initState]
    · intro k _; simp [stateAfter, initState]
    · intro j hj; omega
    · intro k hk; omega
    · simp [primalValue, dualValue, stateAfter, initState]
    · intro i
      simp only [stateAfter, initState]
      exact div_nonneg zero_le_one (aMin_nonneg inst i)
  | succ r ih =>
    intro hr
    have hrm : r < m := hr
    obtain ⟨hI, hcols, hPV, hbd⟩ := ih hrm.le
    obtain ⟨hI', hmono, hcolj, hX, hy, hbound⟩ :=
      round_spec inst hB (s := stateAfter inst B r) ⟨r, hrm⟩ hI (hcol _)
    have hst := stateAfter_succ inst (B := B) r hrm
    rw [hst]
    refine ⟨hI', ?_, ?_, ?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
      · calc (1 : ℝ) ≤ ∑ i, inst.a i k * (stateAfter inst B r).x i := hcols k hlt
          _ ≤ _ := Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hmono i) (inst.ha_nonneg i k)
      · have : k = ⟨r, hrm⟩ := Fin.ext heq
        subst this; exact hcolj
    · -- primal ≤ B * dual
      have hfil : Finset.univ.filter (fun k : Fin m => (k : ℕ) < r + 1) =
          insert (⟨r, hrm⟩ : Fin m) (Finset.univ.filter (fun k : Fin m => (k : ℕ) < r)) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hk
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (h | h)
          · rw [h]; show r < r + 1; omega
          · omega
      have hnot : (⟨r, hrm⟩ : Fin m) ∉ Finset.univ.filter (fun k : Fin m => (k : ℕ) < r) := by
        simp
      have hdual : dualValue inst B (r + 1) = dualValue inst B r +
          (runRound inst B (stateAfter inst B r) ⟨r, hrm⟩).y ⟨r, hrm⟩ := by
        unfold dualValue
        rw [hst, hfil, Finset.sum_insert hnot, add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        have hkr : (k : ℕ) < r := (Finset.mem_filter.mp hk).2
        exact hy k (fun h => by rw [h] at hkr; exact lt_irrefl r hkr)
      unfold primalValue at hPV ⊢
      rw [hst, hdual]
      nlinarith
    · intro i
      rcases hbound i with h | ⟨hpos, h⟩
      · exact le_trans h (hbd i)
      · obtain ⟨h1, h2⟩ := aMin_spec inst i ⟨r, hrm⟩ hpos
        exact le_trans h (one_div_le_one_div_of_le h1 h2)

end round

theorem claim_i_core {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ r : ℕ, r ≤ m → primalValue inst B r ≤ B * dualValue inst B r :=
  fun r hr => (master inst hB hcol r hr).2.2.1

theorem claim_ii_core {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    (∀ r : ℕ, r ≤ m →
      (∀ i, 0 ≤ (stateAfter inst B r).x i) ∧
      (∀ k : Fin m, (k : ℕ) < r → 1 ≤ ∑ i, inst.a i k * (stateAfter inst B r).x i)) ∧
    (∀ r : ℕ, ∀ i, (stateAfter inst B r).x i ≤ (stateAfter inst B (r + 1)).x i) := by
  refine ⟨fun r hr => ⟨(master inst hB hcol r hr).1.x_nn, (master inst hB hcol r hr).2.1⟩, ?_⟩
  intro r i
  by_cases h : r < m
  · have hI := (master inst hB hcol r h.le).1
    obtain ⟨-, hmono, -⟩ := round_spec inst hB (s := stateAfter inst B r) ⟨r, h⟩ hI (hcol _)
    rw [stateAfter_succ inst r h]
    exact hmono i
  · rw [stateAfter, dif_neg h]

theorem claim_iii_core {I : Type*} [Fintype I] [Nonempty I] {m : ℕ} [NeZero m]
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ i : I, ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k ≤
      inst.c i * (2 * Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i)) / B := by
  intro i
  obtain ⟨hI, -, -, hbd⟩ := master inst hB hcol m le_rfl
  have hmpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  let last : Fin m := ⟨m - 1, by omega⟩
  have hlast : ∀ k : Fin m, k ≤ last := fun k => by
    show (k : ℕ) ≤ m - 1
    have := k.2; omega
  have hinc := hI.inc_le last (by show m - 1 < m; omega) i
  have hpm : prefixMax inst i last = aMax inst i := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun k _ => Finset.le_sup' (inst.a i) (Finset.mem_univ k)
    · exact Finset.sup'_le _ _ fun k _ => le_prefixMax inst i (hlast k)
  have hsum : ∑ k ∈ Finset.univ.filter (fun k : Fin m => k ≤ last),
      inst.a i k * (stateAfter inst B m).y k = ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k := by
    rw [Finset.filter_true_of_mem (fun k _ => hlast k)]
  unfold increment at hinc
  rw [hpm, hsum] at hinc
  have hn : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hc := inst.hc_pos i
  have hai : ∀ k, inst.a i k ≤ aMax inst i := fun k => Finset.le_sup' (inst.a i) (Finset.mem_univ k)
  rcases (show 0 ≤ aMax inst i from (inst.ha_nonneg i ⟨0, hmpos⟩).trans (hai _)).eq_or_lt with h0 | hpos
  · have : ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have : inst.a i k = 0 := le_antisymm (by rw [h0]; exact hai k) (inst.ha_nonneg i k)
      rw [this, zero_mul]
    rw [this, ← h0]
    simp
  · obtain ⟨k0, hk0⟩ : ∃ k, 0 < inst.a i k := by
      by_contra hcon
      push_neg at hcon
      have : aMax inst i ≤ 0 := Finset.sup'_le _ _ fun k _ => hcon k
      linarith
    obtain ⟨hmin, hmin2⟩ := aMin_spec inst i k0 hk0
    have hmax : inst.a i k0 ≤ aMax inst i := hai k0
    have hx := hbd i
    set S := ∑ k : Fin m, inst.a i k * (stateAfter inst B m).y k with hS
    set D : ℝ := (Fintype.card I : ℝ) * aMax inst i with hD
    have hDpos : 0 < D := mul_pos hn hpos
    have hE : Real.exp (B / (2 * inst.c i) * S) - 1 ≤ D * (1 / aMin inst i) := by
      have h1 : Real.exp (B / (2 * inst.c i) * S) - 1 =
          D * (1 / D * (Real.exp (B / (2 * inst.c i) * S) - 1)) := by
        field_simp
      rw [h1]
      exact mul_le_mul_of_nonneg_left (le_trans hinc hx) hDpos.le
    have hE2 : Real.exp (B / (2 * inst.c i) * S) ≤
        1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i := by
      have : D * (1 / aMin inst i) = (Fintype.card I : ℝ) * aMax inst i / aMin inst i := by
        rw [hD]; ring
      linarith
    have hL : B / (2 * inst.c i) * S ≤
        Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      exact hE2
    have hS2 : S = (2 * inst.c i / B) * (B / (2 * inst.c i) * S) := by
      field_simp
    calc S = (2 * inst.c i / B) * (B / (2 * inst.c i) * S) := hS2
      _ ≤ (2 * inst.c i / B) * Real.log (1 + (Fintype.card I : ℝ) * aMax inst i / aMin inst i) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
      _ = _ := by ring

end BNCovPack.Packing

open BNCovPack.Packing
open OnlinePrimalDual.GeneralPacking

theorem solution {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    ∀ r : ℕ, r ≤ m → primalValue inst B r ≤ B * dualValue inst B r := by
  exact claim_i_core inst B hB hcol
