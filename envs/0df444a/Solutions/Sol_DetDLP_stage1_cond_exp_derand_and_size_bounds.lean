-- Prove2me | solution 1 for DetDLP.stage1_cond_exp_derand_and_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T11:52:51.66116+00:00
-- url     : https://prove2.me/submissions/5810790a-9f69-4259-970a-a89fa9ec5460

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

/-! ### Part 1: Conditional expectation identity (eq. 3.5) and greedy bit-fixing derandomization -/

private lemma cond_exp_identity {α : Type} [DecidableEq α] (Ω : Finset α)
    (W C : α → ℕ) (gord : ℕ) (μ : ℝ) (_hΩ : Ω.Nonempty) (_hμ : μ ≠ 0) :
    (∑ S ∈ Ω, ((gord : ℝ) * (C S : ℝ) + 64 * ((W S : ℝ) - μ) ^ 2) / μ ^ 2) / (Ω.card : ℝ) =
      ((gord : ℝ) * ((∑ S ∈ Ω, C S : ℕ) : ℝ) +
        64 * ((∑ S ∈ Ω, (W S) ^ 2 : ℕ) : ℝ) -
        128 * μ * ((∑ S ∈ Ω, W S : ℕ) : ℝ) +
        64 * μ ^ 2 * (Ω.card : ℝ)) / (μ ^ 2 * (Ω.card : ℝ)) := by
  have hsum_num :
      (∑ S ∈ Ω, ((gord : ℝ) * (C S : ℝ) + 64 * ((W S : ℝ) - μ) ^ 2)) =
        (gord : ℝ) * ((∑ S ∈ Ω, C S : ℕ) : ℝ) +
        64 * ((∑ S ∈ Ω, (W S) ^ 2 : ℕ) : ℝ) -
        128 * μ * ((∑ S ∈ Ω, W S : ℕ) : ℝ) +
        64 * μ ^ 2 * (Ω.card : ℝ) := by
    have hexpand : ∀ S ∈ Ω,
        (gord : ℝ) * (C S : ℝ) + 64 * ((W S : ℝ) - μ) ^ 2 =
          (gord : ℝ) * (C S : ℝ) + 64 * ((W S : ℝ) ^ 2) - 128 * μ * (W S : ℝ) + 64 * μ ^ 2 := by
      intro S _; ring
    rw [Finset.sum_congr rfl hexpand]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, nsmul_eq_mul]
    push_cast
    ring
  rw [← Finset.sum_div, div_div, hsum_num]

private lemma branch_avg_le {α : Type} [DecidableEq α]
    (P0 P1 : Finset α) (f : α → ℝ) (hdisj : Disjoint P0 P1)
    (h0 : P0.Nonempty) (h1 : P1.Nonempty)
    (hle : (∑ x ∈ P0, f x) / (P0.card : ℝ) ≤ (∑ x ∈ P1, f x) / (P1.card : ℝ)) :
    (∑ x ∈ P0, f x) / (P0.card : ℝ) ≤ (∑ x ∈ (P0 ∪ P1), f x) / ((P0 ∪ P1).card : ℝ) := by
  have hc0 : (0 : ℝ) < (P0.card : ℝ) := by exact_mod_cast h0.card_pos
  have hc1 : (0 : ℝ) < (P1.card : ℝ) := by exact_mod_cast h1.card_pos
  have hcard : ((P0 ∪ P1).card : ℝ) = (P0.card : ℝ) + (P1.card : ℝ) := by
    exact_mod_cast Finset.card_union_of_disjoint hdisj
  have hcU : (0 : ℝ) < ((P0 ∪ P1).card : ℝ) := by linarith
  have hsum : ∑ x ∈ (P0 ∪ P1), f x = ∑ x ∈ P0, f x + ∑ x ∈ P1, f x :=
    Finset.sum_union hdisj
  rw [div_le_div_iff₀ hc0 hcU]
  have hcross : (∑ x ∈ P0, f x) * (P1.card : ℝ) ≤ (∑ x ∈ P1, f x) * (P0.card : ℝ) := by
    rw [div_le_div_iff₀ hc0 hc1] at hle
    exact hle
  rw [hcard, hsum]
  linarith

private noncomputable def greedySlice {α : Type} [DecidableEq α] (L : ℕ)
    (enc : α → Fin L → Bool) (f : α → ℝ) (Ω : Finset α) : ℕ → Finset α
  | 0 => Ω
  | k + 1 =>
    if hk : k < L then
      let Prev := greedySlice L enc f Ω k
      let P0 := Prev.filter (fun x => enc x ⟨k, hk⟩ = false)
      let P1 := Prev.filter (fun x => enc x ⟨k, hk⟩ = true)
      if P0.Nonempty ∧ (¬P1.Nonempty ∨
          (∑ x ∈ P0, f x) / (P0.card : ℝ) ≤ (∑ x ∈ P1, f x) / (P1.card : ℝ)) then P0 else P1
    else
      greedySlice L enc f Ω k

private lemma greedySlice_subset_succ {α : Type} [DecidableEq α] (L : ℕ)
    (enc : α → Fin L → Bool) (f : α → ℝ) (Ω : Finset α) (k : ℕ) :
    greedySlice L enc f Ω (k + 1) ⊆ greedySlice L enc f Ω k := by
  dsimp only [greedySlice]
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.rfl

private lemma greedySlice_subset_of_le {α : Type} [DecidableEq α] (L : ℕ)
    (enc : α → Fin L → Bool) (f : α → ℝ) (Ω : Finset α) {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    greedySlice L enc f Ω k₂ ⊆ greedySlice L enc f Ω k₁ := by
  induction hle with
  | refl => exact Finset.Subset.rfl
  | @step m _ ih => exact Finset.Subset.trans (greedySlice_subset_succ L enc f Ω m) ih

private lemma greedySlice_step_props {α : Type} [DecidableEq α] (L : ℕ)
    (enc : α → Fin L → Bool) (f : α → ℝ) (Ω : Finset α) (k : ℕ)
    (hne : (greedySlice L enc f Ω k).Nonempty) :
    (greedySlice L enc f Ω (k + 1)).Nonempty ∧
    (∑ x ∈ greedySlice L enc f Ω (k + 1), f x) / ((greedySlice L enc f Ω (k + 1)).card : ℝ) ≤
      (∑ x ∈ greedySlice L enc f Ω k, f x) / ((greedySlice L enc f Ω k).card : ℝ) := by
  dsimp only [greedySlice]
  split_ifs with hk hcond
  · set Prev := greedySlice L enc f Ω k
    set P0 := Prev.filter (fun x => enc x ⟨k, hk⟩ = false)
    set P1 := Prev.filter (fun x => enc x ⟨k, hk⟩ = true)
    have h0 : P0.Nonempty := hcond.1
    refine ⟨h0, ?_⟩
    have hdisj : Disjoint P0 P1 := Finset.disjoint_filter.mpr fun x _ hx0 hx1 => by
      rw [hx0] at hx1; cases hx1
    have hunion : P0 ∪ P1 = Prev := by
      ext x
      simp only [Finset.mem_union, P0, P1, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        cases h : enc x ⟨k, hk⟩
        · exact Or.inl ⟨hx, rfl⟩
        · exact Or.inr ⟨hx, rfl⟩
    by_cases h1 : P1.Nonempty
    · rcases hcond.2 with h1_not | havg
      · exact absurd h1 h1_not
      · rw [← hunion]
        exact branch_avg_le P0 P1 f hdisj h0 h1 havg
    · have h1_eq : P1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h1
      have hP0_eq : P0 = Prev := by rw [← hunion, h1_eq, Finset.union_empty]
      rw [hP0_eq]
  · set Prev := greedySlice L enc f Ω k
    set P0 := Prev.filter (fun x => enc x ⟨k, hk⟩ = false)
    set P1 := Prev.filter (fun x => enc x ⟨k, hk⟩ = true)
    have hdisj : Disjoint P1 P0 := Finset.disjoint_filter.mpr fun x _ hx1 hx0 => by
      rw [hx0] at hx1; cases hx1
    have hunion : P1 ∪ P0 = Prev := by
      ext x
      simp only [Finset.mem_union, P0, P1, Finset.mem_filter]
      constructor
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
      · intro hx
        cases h : enc x ⟨k, hk⟩
        · exact Or.inr ⟨hx, rfl⟩
        · exact Or.inl ⟨hx, rfl⟩
    by_cases h0 : P0.Nonempty
    · have hnot : ¬(¬P1.Nonempty ∨
          (∑ x ∈ P0, f x) / (P0.card : ℝ) ≤ (∑ x ∈ P1, f x) / (P1.card : ℝ)) :=
        fun h => hcond ⟨h0, h⟩
      push Not at hnot
      obtain ⟨h1, hlt⟩ := hnot
      refine ⟨h1, ?_⟩
      rw [← hunion]
      exact branch_avg_le P1 P0 f hdisj h1 h0 (le_of_lt hlt)
    · have h0_eq : P0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0
      have hP1_eq : P1 = Prev := by rw [← hunion, h0_eq, Finset.union_empty]
      rw [hP1_eq]
      exact ⟨hne, le_refl _⟩
  · exact ⟨hne, le_refl _⟩

private lemma greedySlice_prefix_props {α : Type} [DecidableEq α] (L : ℕ)
    (enc : α → Fin L → Bool) (f : α → ℝ) (Ω : Finset α) (hΩ : Ω.Nonempty) :
    ∀ k : ℕ,
      (greedySlice L enc f Ω k).Nonempty ∧
      (∑ x ∈ greedySlice L enc f Ω k, f x) / ((greedySlice L enc f Ω k).card : ℝ) ≤
        (∑ x ∈ Ω, f x) / (Ω.card : ℝ) ∧
      ∀ x ∈ greedySlice L enc f Ω k, ∀ y ∈ greedySlice L enc f Ω k,
        ∀ j : Fin L, j.val < k → enc x j = enc y j := by
  intro k
  induction k with
  | zero =>
    refine ⟨hΩ, le_refl _, fun x _ y _ j hj => False.elim (Nat.not_lt_zero j.val hj)⟩
  | succ k ih =>
    obtain ⟨hne_k, havg_k, hbit_k⟩ := ih
    obtain ⟨hne_succ, havg_step⟩ := greedySlice_step_props L enc f Ω k hne_k
    refine ⟨hne_succ, le_trans havg_step havg_k, fun x hx y hy j hj => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
    · exact hbit_k x (greedySlice_subset_succ _ _ _ _ _ hx)
        y (greedySlice_subset_succ _ _ _ _ _ hy) j hj_lt
    · have hkL : k < L := by rw [← hj_eq]; exact j.isLt
      have hx' := hx
      have hy' := hy
      dsimp only [greedySlice] at hx' hy'
      rw [dif_pos hkL] at hx' hy'
      have hj_fin : j = ⟨k, hkL⟩ := Fin.ext hj_eq
      rw [hj_fin]
      split_ifs at hx' hy' with hcond
      · simp only [Finset.mem_filter] at hx' hy'
        rw [hx'.2, hy'.2]
      · simp only [Finset.mem_filter] at hx' hy'
        rw [hx'.2, hy'.2]

private lemma greedy_bit_fix {α : Type} [DecidableEq α] (L : ℕ) (enc : α → Fin L → Bool)
    (henc : Function.Injective enc) (Ω : Finset α) (f : α → ℝ) (hΩ : Ω.Nonempty) :
    ∃ S ∈ Ω,
      (∀ k : ℕ, k ≤ L →
        ∃ Ωk : Finset α,
          Ωk.Nonempty ∧ Ωk ⊆ Ω ∧ S ∈ Ωk ∧
          (∀ x ∈ Ωk, ∀ j : Fin L, j.val < k → enc x j = enc S j) ∧
          (∑ x ∈ Ωk, f x) / (Ωk.card : ℝ) ≤ (∑ x ∈ Ω, f x) / (Ω.card : ℝ)) ∧
      f S ≤ (∑ x ∈ Ω, f x) / (Ω.card : ℝ) := by
  have hL := greedySlice_prefix_props L enc f Ω hΩ L
  obtain ⟨S, hSL⟩ := hL.1
  have hS_in_Ω : S ∈ Ω := greedySlice_subset_of_le L enc f Ω (Nat.zero_le L) hSL
  refine ⟨S, hS_in_Ω, fun k hk => ?_, ?_⟩
  · have hk_props := greedySlice_prefix_props L enc f Ω hΩ k
    have hS_k : S ∈ greedySlice L enc f Ω k :=
      greedySlice_subset_of_le L enc f Ω hk hSL
    refine ⟨greedySlice L enc f Ω k, hk_props.1,
      greedySlice_subset_of_le L enc f Ω (Nat.zero_le k), hS_k,
      fun x hx j hj => hk_props.2.2 x hx S hS_k j hj, hk_props.2.1⟩
  · have hsingleton : greedySlice L enc f Ω L = {S} := by
      ext x
      simp only [Finset.mem_singleton]
      constructor
      · intro hxL
        exact henc (funext fun j => hL.2.2 x hxL S hSL j j.isLt)
      · intro hxS
        subst hxS
        exact hSL
    have havg_L := hL.2.1
    rw [hsingleton] at havg_L
    simpa using havg_L

/-! ### Part 2: Native-address injectivity and exact block cardinality bounds -/

private lemma zmod_affine_inj {p : ℕ} [Fact p.Prime] (a : Fin (p - 1)) (b : Fin p) :
    Function.Injective (fun x : ZMod p => ((a.val + 1) * x.val + b.val) % p) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  intro x₁ x₂ hmod
  have hcast : ((((a.val + 1) * x₁.val + b.val) % p : ℕ) : ZMod p) =
      ((((a.val + 1) * x₂.val + b.val) % p : ℕ) : ZMod p) := congrArg Nat.cast hmod
  rw [ZMod.natCast_mod, ZMod.natCast_mod] at hcast
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, ZMod.natCast_zmod_val] at hcast
  have hmul : ((a.val + 1 : ℕ) : ZMod p) * x₁ = ((a.val + 1 : ℕ) : ZMod p) * x₂ := by
    push_cast
    exact add_right_cancel hcast
  have ha_ne : ((a.val + 1 : ℕ) : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ a.val + 1 := (ZMod.natCast_eq_zero_iff (a.val + 1) p).mp h0
    have hlt : a.val + 1 < p := by omega
    exact absurd (Nat.le_of_dvd (by omega) hdvd) (not_le.mpr hlt)
  exact mul_left_cancel₀ ha_ne hmul

private lemma fpFactorBlock_inj_and_card {p m T : ℕ} [Fact p.Prime] (S : FpSeed p m) (i : Fin m) :
    Set.InjOn
      (fun a : (ZMod p)ˣ => (((S i).1.val + 1) * (a : ZMod p).val + (S i).2.val) % p)
      (fpFactorBlock (p := p) T S i) ∧
    (fpFactorBlock (p := p) T S i).card ≤ T := by
  have hinj : Function.Injective
      (fun a : (ZMod p)ˣ => (((S i).1.val + 1) * (a : ZMod p).val + (S i).2.val) % p) := by
    intro a₁ a₂ h
    exact Units.ext (zmod_affine_inj (S i).1 (S i).2 h)
  refine ⟨hinj.injOn, ?_⟩
  have hle := Finset.card_le_card_of_injOn
    (fun a : (ZMod p)ˣ => (((S i).1.val + 1) * (a : ZMod p).val + (S i).2.val) % p)
    (s := fpFactorBlock (p := p) T S i) (t := Finset.range T)
    (fun a ha => by
      simp only [fpFactorBlock, fpFactorMem, Finset.mem_coe, Finset.mem_filter,
        Finset.mem_univ, true_and, decide_eq_true_eq] at ha
      rw [Finset.mem_coe, Finset.mem_range]
      exact ha)
    hinj.injOn
  simpa using hle

private lemma ec_point_x_fiber_le_two {p : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) (x : ZMod p)
    (B : Finset E.toAffine.Point)
    (hB : ∀ P ∈ B, ∃ y h, P = WeierstrassCurve.Affine.Point.some x y h) :
    B.card ≤ 2 := by
  by_cases h0 : B = ∅
  · simp [h0]
  · obtain ⟨P₁, hP₁⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    by_cases h1 : (B.erase P₁) = ∅
    · have hsub : B ⊆ {P₁} := fun P hP => by
        by_cases he : P = P₁
        · simp [he]
        · have : P ∈ B.erase P₁ := Finset.mem_erase.mpr ⟨he, hP⟩
          rw [h1] at this; exact False.elim (Finset.notMem_empty P this)
      calc B.card ≤ ({P₁} : Finset _).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton P₁
        _ ≤ 2 := by omega
    · obtain ⟨P₂, hP₂_er⟩ := Finset.nonempty_iff_ne_empty.mpr h1
      have hne12 : P₂ ≠ P₁ := (Finset.mem_erase.mp hP₂_er).1
      have hP₂ : P₂ ∈ B := (Finset.mem_erase.mp hP₂_er).2
      obtain ⟨y₁, h₁, rfl⟩ := hB P₁ hP₁
      obtain ⟨y₂, h₂, rfl⟩ := hB P₂ hP₂
      have hy_ne12 : y₂ ≠ y₁ := fun heq => hne12 (by subst heq; rfl)
      have heq1 : y₁ ^ 2 + E.a₁ * x * y₁ + E.a₃ * y₁ =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
        simpa using (E.toAffine.equation_iff x y₁).mp h₁.1
      have heq2 : y₂ ^ 2 + E.a₁ * x * y₂ + E.a₃ * y₂ =
          x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
        simpa using (E.toAffine.equation_iff x y₂).mp h₂.1
      have hfac12 : (y₂ - y₁) * (y₂ + y₁ + E.a₁ * x + E.a₃) = 0 := by
        linear_combination heq2 - heq1
      have hsum12 : y₂ + y₁ + E.a₁ * x + E.a₃ = 0 :=
        (mul_eq_zero.mp hfac12).resolve_left (sub_ne_zero.mpr hy_ne12)
      have hsub : B ⊆ {.some x y₁ h₁, .some x y₂ h₂} := by
        intro P₃ hP₃
        obtain ⟨y₃, h₃, rfl⟩ := hB P₃ hP₃
        have heq3 : y₃ ^ 2 + E.a₁ * x * y₃ + E.a₃ * y₃ =
            x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
          simpa using (E.toAffine.equation_iff x y₃).mp h₃.1
        have hfac13 : (y₃ - y₁) * (y₃ + y₁ + E.a₁ * x + E.a₃) = 0 := by
          linear_combination heq3 - heq1
        rcases mul_eq_zero.mp hfac13 with h31 | hsum13
        · have hy31 : y₃ = y₁ := sub_eq_zero.mp h31
          simp [hy31]
        · have hy32 : y₃ = y₂ := by linear_combination hsum13 - hsum12
          simp [hy32]
      calc B.card ≤ ({WeierstrassCurve.Affine.Point.some x y₁ h₁,
            WeierstrassCurve.Affine.Point.some x y₂ h₂} : Finset E.toAffine.Point).card :=
          Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two

private noncomputable def ecPointTag {p : ℕ} [NeZero p] {E : WeierstrassCurve (ZMod p)}
    {m : ℕ} (S : ECSeed p m) (i : Fin m) : E.toAffine.Point → Bool × ℕ
  | .zero => (false, 0)
  | .some x y _ =>
    let ε : Bool := decide (y.val % 2 = 1)
    let ab := S i ε
    (ε, ((ab.1.val + 1) * x.val + ab.2.val) % p)

private lemma ecFactorBlock_card_bounds {p m T : ℕ} [Fact p.Prime]
    (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m) :
    (ecFactorBlock E T S i).card ≤ 4 * T ∧
    (2 < p → E.a₁ = 0 → E.a₃ = 0 → (ecFactorBlock E T S i).card ≤ 2 * T) := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  let B := ecFactorBlock E T S i
  let Target : Finset (Bool × ℕ) := (Finset.univ : Finset Bool) ×ˢ Finset.range T
  have hTarget_card : Target.card = 2 * T := by
    simp [Target, Finset.card_product]
  have hmaps : ∀ P ∈ B, ecPointTag S i P ∈ Target := by
    intro P hP
    simp only [B, ecFactorBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hP
    cases P with
    | zero => simp [ecFactorMem] at hP
    | some x y h =>
      simp only [ecFactorMem] at hP
      simp only [ecPointTag, Target, Finset.mem_product, Finset.mem_univ,
        Finset.mem_range, true_and, decide_eq_true_eq] at hP ⊢
      exact hP
  have hfib_sum : B.card = ∑ t ∈ Target, (B.filter fun P => ecPointTag S i P = t).card :=
    Finset.card_eq_sum_card_fiberwise (f := ecPointTag S i) (s := B) (t := Target)
      (fun P hP => hmaps P hP)
  have hfib_x : ∀ t ∈ Target,
      ∃ x : ZMod p, ∀ P ∈ B.filter (fun P => ecPointTag S i P = t),
        ∃ y h, P = WeierstrassCurve.Affine.Point.some x y h ∧ decide (y.val % 2 = 1) = t.1 := by
    intro t _
    by_cases hemp : (B.filter fun P => ecPointTag S i P = t) = ∅
    · exact ⟨0, fun P hP => by rw [hemp] at hP; exact False.elim (Finset.notMem_empty P hP)⟩
    · obtain ⟨P₀, hP₀⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      rw [Finset.mem_filter] at hP₀
      have hP₀B := hP₀.1
      simp only [B, ecFactorBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hP₀B
      cases P₀ with
      | zero => simp [ecFactorMem] at hP₀B
      | some x₀ y₀ h₀ =>
        refine ⟨x₀, fun P hP => ?_⟩
        rw [Finset.mem_filter] at hP
        have hPB := hP.1
        simp only [B, ecFactorBlock, Finset.mem_filter, Finset.mem_univ, true_and] at hPB
        cases P with
        | zero => simp [ecFactorMem] at hPB
        | some x y h =>
          have htag : ecPointTag S i (.some x y h) = ecPointTag S i (.some x₀ y₀ h₀) :=
            hP.2.trans hP₀.2.symm
          have htag0 : ecPointTag S i (.some x₀ y₀ h₀) = t := hP₀.2
          simp only [ecPointTag, Prod.mk.injEq] at htag
          have htag0_fst : (decide (y₀.val % 2 = 1)) = t.1 := by
            have := congrArg Prod.fst htag0
            simpa [ecPointTag] using this
          have hε : decide (y.val % 2 = 1) = decide (y₀.val % 2 = 1) := htag.1
          have hmod := htag.2
          rw [hε] at hmod
          have hxeq := zmod_affine_inj (S i (decide (y₀.val % 2 = 1))).1
            (S i (decide (y₀.val % 2 = 1))).2 hmod
          subst hxeq
          exact ⟨y, h, rfl, htag.1.trans htag0_fst⟩
  refine ⟨?_, ?_⟩
  · have hle : ∑ t ∈ Target, (B.filter fun P => ecPointTag S i P = t).card ≤ ∑ _t ∈ Target, 2 := by
      refine Finset.sum_le_sum fun t ht => ?_
      obtain ⟨x, hx⟩ := hfib_x t ht
      exact ec_point_x_fiber_le_two E x _ fun P hP => by
        obtain ⟨y, h, rfl, _⟩ := hx P hP
        exact ⟨y, h, rfl⟩
    calc B.card
        = ∑ t ∈ Target, (B.filter fun P => ecPointTag S i P = t).card := hfib_sum
      _ ≤ ∑ _t ∈ Target, 2 := hle
      _ = Target.card * 2 := by simp
      _ = 4 * T := by rw [hTarget_card]; ring
  · intro hp2 ha1 ha3
    have hpodd : p % 2 = 1 := by
      have := hp.eq_two_or_odd
      omega
    have hle : ∑ t ∈ Target, (B.filter fun P => ecPointTag S i P = t).card ≤ ∑ _t ∈ Target, 1 := by
      refine Finset.sum_le_sum fun t ht => ?_
      obtain ⟨x, hx⟩ := hfib_x t ht
      refine Finset.card_le_one.mpr fun P₁ hP₁ P₂ hP₂ => ?_
      obtain ⟨y₁, h₁, rfl, hpar1⟩ := hx P₁ hP₁
      obtain ⟨y₂, h₂, rfl, hpar2⟩ := hx P₂ hP₂
      have heq1 : y₁ ^ 2 = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
        have := (E.toAffine.equation_iff x y₁).mp h₁.1
        simpa [ha1, ha3] using this
      have heq2 : y₂ ^ 2 = x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆ := by
        have := (E.toAffine.equation_iff x y₂).mp h₂.1
        simpa [ha1, ha3] using this
      have hfac : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination heq1 - heq2
      rcases mul_eq_zero.mp hfac with hsub | hadd
      · have hy : y₁ = y₂ := sub_eq_zero.mp hsub
        subst hy; rfl
      · by_cases hy0 : y₁ = 0
        · have hy20 : y₂ = 0 := by rw [hy0, zero_add] at hadd; exact hadd
          subst hy0; subst hy20; rfl
        · have hval_sum_mod : (y₁.val + y₂.val) % p = 0 := by
            have hval_add := ZMod.val_add y₁ y₂
            rw [hadd, ZMod.val_zero] at hval_add
            exact hval_add.symm
          have hv1_pos : 0 < y₁.val := Nat.pos_of_ne_zero (fun hv => hy0 ((ZMod.val_eq_zero y₁).mp hv))
          have hv1_lt : y₁.val < p := ZMod.val_lt y₁
          have hv2_lt : y₂.val < p := ZMod.val_lt y₂
          have hdvd : p ∣ y₁.val + y₂.val := Nat.dvd_of_mod_eq_zero hval_sum_mod
          have hge_p : p ≤ y₁.val + y₂.val := Nat.le_of_dvd (by omega) hdvd
          have hlt_2p : y₁.val + y₂.val < 2 * p := by omega
          have hsum_eq_p : y₁.val + y₂.val = p := by
            rcases hdvd with ⟨k, hk⟩
            have hk_pos : 1 ≤ k := by nlinarith
            have hk_lt : k < 2 := by nlinarith
            have hk1 : k = 1 := by omega
            rw [hk, hk1, mul_one]
          have hpar_eq : decide (y₁.val % 2 = 1) = decide (y₂.val % 2 = 1) := hpar1.trans hpar2.symm
          have hmod : y₁.val % 2 = 1 ↔ y₂.val % 2 = 1 := by
            simpa [decide_eq_decide] using hpar_eq
          by_cases h1 : y₁.val % 2 = 1
          · have h2 := hmod.mp h1; omega
          · have h2 : y₂.val % 2 ≠ 1 := fun ht => h1 (hmod.mpr ht); omega
    calc B.card
        = ∑ t ∈ Target, (B.filter fun P => ecPointTag S i P = t).card := hfib_sum
      _ ≤ ∑ _t ∈ Target, 1 := hle
      _ = Target.card * 1 := by simp
      _ = 2 * T := by rw [hTarget_card]; ring

/-! ### Part 3: Total factor-base size bounds in both regimes -/

private lemma qStar_le {m gord : ℕ} (hm : 2 ≤ m) (hg : 1 ≤ gord) :
    (qStar m gord : ℝ) ≤ 4096 * (m : ℝ) + 5 * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
  unfold qStar
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm_ge2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hg1 : (1 : ℝ) ≤ (gord : ℝ) := by exact_mod_cast hg
  have h16_le : (16 : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤ 4 := by
    have hpow : (16 : ℝ) ^ ((1 : ℝ) / (m : ℝ)) ≤ (16 : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (one_div_le_one_div_of_le (by norm_num) hm_ge2)
    have h4 : (16 : ℝ) ^ ((1 : ℝ) / 2) = 4 := by
      have h16eq : (16 : ℝ) = (4 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [h16eq, ← Real.rpow_mul (by norm_num)]
      norm_num
    linarith
  have hg_ge1 : 1 ≤ (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) :=
    Real.one_le_rpow hg1 (by positivity)
  have hmul_le : (16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ)) ≤ 4 * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    exact mul_le_mul_of_nonneg_right h16_le (by positivity)
  have hceil_le : (Nat.ceil ((16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) : ℝ) ≤
      5 * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by
    have hlt := Nat.ceil_lt_add_one (a := (16 * (gord : ℝ)) ^ ((1 : ℝ) / (m : ℝ))) (by positivity)
    linarith
  push_cast
  exact max_le
    (le_add_of_le_of_nonneg (le_refl _) (by positivity))
    (le_add_of_nonneg_of_le (by positivity) hceil_le)

private lemma hasse_implies_p_le_two_n {p gord : ℕ} (hg64 : 64 ≤ gord)
    (hhasse : |(gord : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ)) :
    (p : ℝ) ≤ 2 * ((gord - 1 : ℕ) : ℝ) := by
  by_contra hlt
  push Not at hlt
  have hlt_nat : 2 * (gord - 1) < p := by
    have hcast : ((2 * (gord - 1) : ℕ) : ℝ) < (p : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
      exact hlt
    exact_mod_cast hcast
  have hp_ge : (p : ℝ) ≥ 2 * (gord : ℝ) - 1 := by
    have hnat : 2 * gord - 1 ≤ p := by omega
    have hcast : ((2 * gord - 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hnat
    have hsub : ((2 * gord - 1 : ℕ) : ℝ) = 2 * (gord : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * gord)]; norm_num
    linarith
  set d : ℝ := (p : ℝ) - (2 * (gord : ℝ) - 1)
  have hd : 0 ≤ d := by linarith
  have hp_eq : (p : ℝ) = 2 * (gord : ℝ) - 1 + d := by dsimp only [d]; ring
  have hsq : ((p : ℝ) + 1 - (gord : ℝ)) ^ 2 ≤ 4 * (p : ℝ) := by
    have h1 : |(p : ℝ) + 1 - (gord : ℝ)| ≤ 2 * Real.sqrt (p : ℝ) := by
      rw [abs_sub_comm]; exact hhasse
    have h2 : |(p : ℝ) + 1 - (gord : ℝ)| ^ 2 ≤ (2 * Real.sqrt (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg p)] at h2
    linarith
  have hid : ((p : ℝ) + 1 - (gord : ℝ)) ^ 2 - 4 * (p : ℝ) =
      (gord : ℝ) * ((gord : ℝ) - 8) + 2 * ((gord : ℝ) - 2) * d + d ^ 2 + 4 := by
    rw [hp_eq]; ring
  have hgR : (64 : ℝ) ≤ (gord : ℝ) := by exact_mod_cast hg64
  have hpos : 0 < (gord : ℝ) * ((gord : ℝ) - 8) + 2 * ((gord : ℝ) - 2) * d + d ^ 2 + 4 := by
    nlinarith
  linarith

private lemma fp_total_size_bound :
    ∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
      2 ≤ m → (∀ i : Fin m, (F i).Nodup) →
      ((¬(64 ≤ p - 1 ∧ 4096 * m ≤ p - 1) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
       (64 ≤ p - 1 ∧ 4096 * m ≤ p - 1 ∧
         ∃ S : FpSeed p m,
           ∀ i : Fin m, (F i).toFinset =
             fpFactorBlock (p := p) (hashThreshold p (p - 1) m (p - 1)) S i)) →
      ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
        (8193 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
  intro p m _ F hm hnodup hreg
  have hcard_len : ∀ i : Fin m, (F i).length = (F i).toFinset.card :=
    fun i => (List.toFinset_card_of_nodup (hnodup i)).symm
  have hnonneg : (0 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by positivity
  rcases hreg with ⟨hnot, huniv⟩ | ⟨hg64, _, S, hblk⟩
  · have hlt : p - 1 ≤ 4096 * m := by
      by_contra hgt
      have hgt' : 4096 * m < p - 1 := Nat.lt_of_not_le hgt
      exact hnot ⟨by omega, by omega⟩
    have hsum : (∑ i : Fin m, (F i).length : ℕ) = m * (p - 1) := by
      calc ∑ i : Fin m, (F i).length
          = ∑ i : Fin m, (F i).toFinset.card := Finset.sum_congr rfl fun i _ => hcard_len i
        _ = ∑ _i : Fin m, Fintype.card (ZMod p)ˣ :=
            Finset.sum_congr rfl fun i _ => by rw [huniv i, Finset.card_univ]
        _ = m * (p - 1) := by simp [Nat.totient_prime Fact.out]
    rw [hsum]
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmulR : ((m * (p - 1) : ℕ) : ℝ) ≤ 4096 * (m : ℝ) ^ 2 := by
      have hnat : m * (p - 1) ≤ 4096 * m * m := by nlinarith
      have : ((m * (p - 1) : ℕ) : ℝ) ≤ ((4096 * m * m : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this ⊢
      linarith
    nlinarith
  · set T := hashThreshold p (p - 1) m (p - 1)
    have hT_le : (T : ℝ) ≤ 8193 * ((m : ℝ) + ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
      have hn_pos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < p - 1)
      have hp_le_2n : (p : ℝ) ≤ 2 * ((p - 1 : ℕ) : ℝ) := by
        have hnat : p ≤ 2 * (p - 1) := by omega
        exact_mod_cast hnat
      have hpdiv : (p : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 2 := (div_le_iff₀ hn_pos).mpr hp_le_2n
      have hqstar := qStar_le hm (by omega : 1 ≤ p - 1)
      have hceil_lt : (T : ℝ) < (p : ℝ) * (qStar m (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ) + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      have hprod : (p : ℝ) * (qStar m (p - 1) : ℝ) / ((p - 1 : ℕ) : ℝ) ≤ 2 * (qStar m (p - 1) : ℝ) := by
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right hpdiv (Nat.cast_nonneg _)
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      nlinarith
    have hsum : ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ (m : ℝ) * (T : ℝ) := by
      have hnat : ∑ i : Fin m, (F i).length ≤ ∑ _i : Fin m, T := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hcard_len i, hblk i]
        exact (fpFactorBlock_inj_and_card S i).2
      have hnat2 : ∑ i : Fin m, (F i).length ≤ m * T := by simpa using hnat
      have : ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ ((m * T : ℕ) : ℝ) := by exact_mod_cast hnat2
      simpa using this
    calc ((∑ i : Fin m, (F i).length : ℕ) : ℝ)
        ≤ (m : ℝ) * (T : ℝ) := hsum
      _ ≤ (m : ℝ) * (8193 * ((m : ℝ) + ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left hT_le (Nat.cast_nonneg m)
      _ = (8193 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by ring

private lemma ec_total_size_bound :
    ∀ (p m : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
      (F : Fin m → List E.toAffine.Point),
      3 < p → 2 ≤ m → (∀ i : Fin m, (F i).Nodup) →
      letI := ecPointFintype E
      let gord := Fintype.card E.toAffine.Point
      let n := gord - 1
      |(gord : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) →
      ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
       (64 ≤ gord ∧ 4096 * m ≤ n ∧
         ∃ S : ECSeed p m,
           ∀ i : Fin m, (F i).toFinset =
             ecFactorBlock E (hashThreshold p n m gord) S i)) →
      ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
        (32772 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
  intro p m _ E _ F hp3 hm hnodup
  let _ := ecPointFintype E
  dsimp only
  intro hhasse hreg
  set gord := Fintype.card E.toAffine.Point
  set n := gord - 1
  have hcard_len : ∀ i : Fin m, (F i).length = (F i).toFinset.card :=
    fun i => (List.toFinset_card_of_nodup (hnodup i)).symm
  have hnonneg : (0 : ℝ) ≤ (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ)) := by positivity
  rcases hreg with ⟨hnot, huniv⟩ | ⟨hg64, hn4096, S, hblk⟩
  · have hg_le : gord ≤ 4096 * m := by
      by_contra hgt
      have hgt' : 4096 * m < gord := Nat.lt_of_not_le hgt
      have : 64 ≤ gord ∧ 4096 * m ≤ n := ⟨by omega, by dsimp [n]; omega⟩
      exact hnot this
    have hsum : (∑ i : Fin m, (F i).length : ℕ) = m * gord := by
      calc ∑ i : Fin m, (F i).length
          = ∑ i : Fin m, (F i).toFinset.card := Finset.sum_congr rfl fun i _ => hcard_len i
        _ = ∑ _i : Fin m, Fintype.card E.toAffine.Point :=
            Finset.sum_congr rfl fun i _ => by rw [huniv i, Finset.card_univ]
        _ = m * gord := by simp [gord]
    rw [hsum]
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hmulR : ((m * gord : ℕ) : ℝ) ≤ 4096 * (m : ℝ) ^ 2 := by
      have hnat : m * gord ≤ 4096 * m * m := by nlinarith
      have : ((m * gord : ℕ) : ℝ) ≤ ((4096 * m * m : ℕ) : ℝ) := by exact_mod_cast hnat
      push_cast at this ⊢
      linarith
    nlinarith
  · set T := hashThreshold p n m gord
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hp_le_2n : (p : ℝ) ≤ 2 * (n : ℝ) := hasse_implies_p_le_two_n hg64 hhasse
    have hpdiv : (p : ℝ) / (n : ℝ) ≤ 2 := (div_le_iff₀ hn_pos).mpr hp_le_2n
    have hqstar := qStar_le hm (by omega : 1 ≤ gord)
    have hceil_lt : (T : ℝ) < (p : ℝ) * (qStar m gord : ℝ) / (n : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hprod : (p : ℝ) * (qStar m gord : ℝ) / (n : ℝ) ≤ 2 * (qStar m gord : ℝ) := by
      rw [mul_div_right_comm]
      exact mul_le_mul_of_nonneg_right hpdiv (Nat.cast_nonneg _)
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
    have hT_le : (T : ℝ) ≤ 8193 * ((m : ℝ) + (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by
      nlinarith
    have hsum : ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ (m : ℝ) * (4 * (T : ℝ)) := by
      have hnat : ∑ i : Fin m, (F i).length ≤ ∑ _i : Fin m, 4 * T := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hcard_len i, hblk i]
        exact (ecFactorBlock_card_bounds E S i).1
      have hnat2 : ∑ i : Fin m, (F i).length ≤ m * (4 * T) := by simpa using hnat
      have : ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤ ((m * (4 * T) : ℕ) : ℝ) := by
        exact_mod_cast hnat2
      push_cast at this ⊢
      exact this
    calc ((∑ i : Fin m, (F i).length : ℕ) : ℝ)
        ≤ (m : ℝ) * (4 * (T : ℝ)) := hsum
      _ ≤ (m : ℝ) * (4 * (8193 * ((m : ℝ) + (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))))) :=
          mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg m)
      _ = (32772 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))) := by ring

theorem solution :
    (∀ {α : Type} [DecidableEq α] (Ω : Finset α) (W C : α → ℕ) (gord : ℕ) (μ : ℝ),
      Ω.Nonempty → μ ≠ 0 →
      (∑ S ∈ Ω, ((gord : ℝ) * (C S : ℝ) + 64 * ((W S : ℝ) - μ) ^ 2) / μ ^ 2) / (Ω.card : ℝ) =
        ((gord : ℝ) * ((∑ S ∈ Ω, C S : ℕ) : ℝ) +
          64 * ((∑ S ∈ Ω, (W S) ^ 2 : ℕ) : ℝ) -
          128 * μ * ((∑ S ∈ Ω, W S : ℕ) : ℝ) +
          64 * μ ^ 2 * (Ω.card : ℝ)) / (μ ^ 2 * (Ω.card : ℝ))) ∧
    (∀ {α : Type} [DecidableEq α] (L : ℕ) (enc : α → Fin L → Bool),
      Function.Injective enc →
      ∀ (Ω : Finset α) (f : α → ℝ), Ω.Nonempty →
        ∃ S ∈ Ω,
          (∀ k : ℕ, k ≤ L →
            ∃ Ωk : Finset α,
              Ωk.Nonempty ∧ Ωk ⊆ Ω ∧ S ∈ Ωk ∧
              (∀ x ∈ Ωk, ∀ j : Fin L, j.val < k → enc x j = enc S j) ∧
              (∑ x ∈ Ωk, f x) / (Ωk.card : ℝ) ≤ (∑ x ∈ Ω, f x) / (Ω.card : ℝ)) ∧
          f S ≤ (∑ x ∈ Ω, f x) / (Ω.card : ℝ)) ∧
    ((∀ (p m T : ℕ) [Fact p.Prime] (S : FpSeed p m) (i : Fin m),
        Set.InjOn
          (fun a : (ZMod p)ˣ => (((S i).1.val + 1) * (a : ZMod p).val + (S i).2.val) % p)
          (fpFactorBlock (p := p) T S i) ∧
        (fpFactorBlock (p := p) T S i).card ≤ T) ∧
     (∀ (p m T : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) (S : ECSeed p m) (i : Fin m),
        (ecFactorBlock E T S i).card ≤ 4 * T ∧
        (2 < p → E.a₁ = 0 → E.a₃ = 0 → (ecFactorBlock E T S i).card ≤ 2 * T))) ∧
    ((∀ (p m : ℕ) [Fact p.Prime] (F : Fin m → List (ZMod p)ˣ),
        2 ≤ m → (∀ i : Fin m, (F i).Nodup) →
        ((¬(64 ≤ p - 1 ∧ 4096 * m ≤ p - 1) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
         (64 ≤ p - 1 ∧ 4096 * m ≤ p - 1 ∧
           ∃ S : FpSeed p m,
             ∀ i : Fin m, (F i).toFinset =
               fpFactorBlock (p := p) (hashThreshold p (p - 1) m (p - 1)) S i)) →
        ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
          (8193 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * ((p - 1 : ℕ) : ℝ) ^ ((1 : ℝ) / (m : ℝ)))) ∧
     (∀ (p m : ℕ) [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) [E.IsElliptic]
        (F : Fin m → List E.toAffine.Point),
        3 < p → 2 ≤ m → (∀ i : Fin m, (F i).Nodup) →
        letI := ecPointFintype E
        let gord := Fintype.card E.toAffine.Point
        let n := gord - 1
        |(gord : ℝ) - ((p : ℝ) + 1)| ≤ 2 * Real.sqrt (p : ℝ) →
        ((¬(64 ≤ gord ∧ 4096 * m ≤ n) ∧ ∀ i : Fin m, (F i).toFinset = Finset.univ) ∨
         (64 ≤ gord ∧ 4096 * m ≤ n ∧
           ∃ S : ECSeed p m,
             ∀ i : Fin m, (F i).toFinset =
               ecFactorBlock E (hashThreshold p n m gord) S i)) →
        ((∑ i : Fin m, (F i).length : ℕ) : ℝ) ≤
          (32772 : ℝ) * ((m : ℝ) ^ 2 + (m : ℝ) * (gord : ℝ) ^ ((1 : ℝ) / (m : ℝ))))) :=
  ⟨fun Ω W C gord μ hΩ hμ => cond_exp_identity Ω W C gord μ hΩ hμ,
   fun L enc henc Ω f hΩ => greedy_bit_fix L enc henc Ω f hΩ,
   ⟨fun _p _m _T _ S i => fpFactorBlock_inj_and_card S i,
    fun _p _m _T _ E S i => ecFactorBlock_card_bounds E S i⟩,
   ⟨fp_total_size_bound, ec_total_size_bound⟩⟩
