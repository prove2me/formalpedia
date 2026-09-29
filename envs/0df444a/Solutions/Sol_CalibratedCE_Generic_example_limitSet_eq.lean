-- Prove2me | solution 1 for CalibratedCE.Generic.example_limitSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:08:40.554986+00:00
-- url     : https://prove2.me/submissions/8fe162c0-3523-4397-8ada-d0d74815c62e

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet
import Definitions.Def_CalibratedCE_Generic_Example

namespace CalibratedCE.Generic

open Finset in
theorem aux_exl_key {k : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (P : (Fin k → ℝ) → Prop)
    [DecidablePred P] (j : Fin k) (t : ℕ) :
    |∑ s ∈ range t, (if P (f s) then ((if z s = j then (1:ℝ) else 0) - f s j) else 0)|
      ≤ t * Shared.calibScore f z j t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have hmaps : ∀ s ∈ range t, f s ∈ (range t).image f := fun s hs => mem_image_of_mem f hs
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  unfold Shared.calibScore
  rw [Finset.mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have htR : (0:ℝ) < t := by exact_mod_cast ht
  obtain ⟨s₀, hs₀, hfs₀⟩ := mem_image.1 hp
  have hNpos : 0 < Shared.N f p t := by
    unfold Shared.N
    exact card_pos.2 ⟨s₀, mem_filter.2 ⟨hs₀, hfs₀⟩⟩
  have hNR : (0:ℝ) < Shared.N f p t := by exact_mod_cast hNpos
  have hrho : Shared.rho f z p j t
      = ((((range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)) / (Shared.N f p t : ℝ) := by
    unfold Shared.rho
    rw [if_neg hNpos.ne']
  rw [hrho]
  have hsum : ∑ s ∈ range t with f s = p,
      (if P (f s) then ((if z s = j then (1:ℝ) else 0) - f s j) else 0)
      = if P p then ((((range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
          - (Shared.N f p t : ℝ) * p j) else 0 := by
    rw [Finset.sum_congr rfl (g := fun s => if P p then ((if z s = j then (1:ℝ) else 0) - p j) else 0)
      (fun s hs => by rw [(mem_filter.1 hs).2])]
    split_ifs with hP
    · rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.natCast_card_filter,
        Finset.filter_filter]
      rfl
    · simp
  rw [hsum]
  have hkey : (t:ℝ) * (|(((range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
      / (Shared.N f p t : ℝ) - p j| * (Shared.N f p t : ℝ) / t)
      = |(((range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
          - (Shared.N f p t : ℝ) * p j| := by
    set C : ℝ := (((range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ)
    set NN : ℝ := (Shared.N f p t : ℝ)
    have h1 : (C / NN - p j) * NN = C - NN * p j := by field_simp
    calc (t:ℝ) * (|C / NN - p j| * NN / t) = |C / NN - p j| * NN := by field_simp
      _ = |(C / NN - p j) * NN| := by rw [abs_mul, abs_of_pos hNR]
      _ = |C - NN * p j| := by rw [h1]
  rw [hkey]
  split_ifs
  · exact le_rfl
  · simp

theorem aux_exl_br1 (R₁ : (Fin 3 → ℝ) → Fin 3) (hR₁ : IsBestReply₁ exU₁ R₁) (p : Fin 3 → ℝ)
    (hp : IsDist p) (h : R₁ p ≠ 2) : p = ![1, 0, 0] := by
  have h1 := hR₁ p hp 2
  obtain ⟨hnn, hsum⟩ := hp
  simp only [Fin.sum_univ_three] at hsum h1
  have hnn1 := hnn 1
  have hnn2 := hnn 2
  rcases (by decide : ∀ r : Fin 3, r ≠ 2 → r = 0 ∨ r = 1) (R₁ p) h with hr | hr <;>
  · rw [hr] at h1
    simp [exU₁, Matrix.cons_val] at h1
    have e1 : p 1 = 0 := by linarith
    have e2 : p 2 = 0 := by linarith
    funext i
    fin_cases i <;> simp <;> linarith

theorem aux_exl_br2a (R₂ : (Fin 3 → ℝ) → Fin 3) (hR₂ : IsBestReply₂ exU₂ R₂) (q : Fin 3 → ℝ)
    (hq : IsDist q) (h : R₂ q = 0) : q 0 = 1/2 ∧ q 1 = 1/2 := by
  have h1 := hR₂ q hq 1
  have h2 := hR₂ q hq 2
  obtain ⟨hnn, hsum⟩ := hq
  simp only [Fin.sum_univ_three] at hsum h1 h2
  rw [h] at h1 h2
  simp [exU₂, Matrix.cons_val] at h1 h2
  have hnn2 := hnn 2
  constructor <;> linarith

theorem aux_exl_br2b (R₂ : (Fin 3 → ℝ) → Fin 3) (hR₂ : IsBestReply₂ exU₂ R₂) (q : Fin 3 → ℝ)
    (hq : IsDist q) (h : R₂ q = 2) : 1/3 ≤ q 1 := by
  have h1 := hR₂ q hq 1
  obtain ⟨hnn, hsum⟩ := hq
  simp only [Fin.sum_univ_three] at hsum h1
  rw [h] at h1
  simp [exU₂, Matrix.cons_val] at h1
  have hnn0 := hnn 0
  have hnn2 := hnn 2
  linarith

open Finset in
theorem aux_exl_count (R₁ : (Fin 3 → ℝ) → Fin 3) (R₂ : (Fin 3 → ℝ) → Fin 3)
    (hR₁ : IsBestReply₁ exU₁ R₁) (hR₂ : IsBestReply₂ exU₂ R₂)
    (f₁ f₂ : ℕ → Fin 3 → ℝ) (x y : ℕ → Fin 3)
    (hx : ∀ s, x s = R₁ (f₁ s)) (hy : ∀ s, y s = R₂ (f₂ s))
    (hd₁ : ∀ s, IsDist (f₁ s)) (hd₂ : ∀ s, IsDist (f₂ s)) (t : ℕ) :
    ∑ s ∈ range t, (if x s = 2 ∧ y s = 1 then (0:ℝ) else 1)
      ≤ 4 * (t * Shared.calibScore f₁ y 0 t) + 10 * (t * Shared.calibScore f₂ x 0 t)
        + 13 * (t * Shared.calibScore f₂ x 1 t) := by
  have hxe : ∀ s, x s ≠ 2 → f₁ s = ![1,0,0] := fun s hs =>
    aux_exl_br1 R₁ hR₁ (f₁ s) (hd₁ s) (by rw [← hx s]; exact hs)
  have hy0 : ∀ s, y s = 0 → f₂ s 0 = 1/2 ∧ f₂ s 1 = 1/2 := fun s hs =>
    aux_exl_br2a R₂ hR₂ (f₂ s) (hd₂ s) (by rw [← hy s]; exact hs)
  have hy2 : ∀ s, y s = 2 → 1/3 ≤ f₂ s 1 := fun s hs =>
    aux_exl_br2b R₂ hR₂ (f₂ s) (hd₂ s) (by rw [← hy s]; exact hs)
  have hj : ∃ j : Fin 3, (j = 0 ∨ j = 1) ∧ ∀ s, x s ≠ j := by
    by_cases h0 : R₁ ![1,0,0] = 0
    · refine ⟨1, Or.inr rfl, fun s hs => ?_⟩
      have h2 : x s ≠ 2 := by rw [hs]; decide
      have := hx s
      rw [hxe s h2, h0, hs] at this
      exact absurd this (by decide)
    · refine ⟨0, Or.inl rfl, fun s hs => ?_⟩
      have h2 : x s ≠ 2 := by rw [hs]; decide
      have := hx s
      rw [hxe s h2, hs] at this
      exact h0 this.symm
  obtain ⟨j, hj01, hjx⟩ := hj
  have K1 := aux_exl_key f₁ y (fun p => p = ![1,0,0]) 0 t
  have K2j := aux_exl_key f₂ x (fun q => q 0 = 1/2 ∧ q 1 = 1/2) j t
  have K20 := aux_exl_key f₂ x (fun q => q 0 = 1/2 ∧ q 1 = 1/2) 0 t
  have K21 := aux_exl_key f₂ x (fun q => q 0 = 1/2 ∧ q 1 = 1/2) 1 t
  have K3 := aux_exl_key f₂ x (fun _ => True) 1 t
  beta_reduce at K1 K2j K20 K21 K3
  simp only [if_true] at K3
  -- pointwise bounds
  have Pa : ∀ s ∈ range t, (if y s = 0 then (1:ℝ) else 0) ≤
      -2 * (if f₂ s 0 = 1/2 ∧ f₂ s 1 = 1/2 then ((if x s = j then (1:ℝ) else 0) - f₂ s j) else 0) := by
    intro s _
    have hxj := hjx s
    have hfj : f₂ s 0 = 1/2 ∧ f₂ s 1 = 1/2 → f₂ s j = 1/2 := by
      rcases hj01 with rfl | rfl
      · exact fun h => h.1
      · exact fun h => h.2
    by_cases hy0' : y s = 0
    · have hP := hy0 s hy0'
      rw [if_pos hy0', if_pos hP, if_neg hxj, hfj hP]; norm_num
    · rw [if_neg hy0']
      have := (hd₂ s).1 j
      split_ifs <;> linarith
  have Pb : ∀ s ∈ range t, (if x s = 2 then (0:ℝ) else 1) ≤
      -(if f₁ s = ![1,0,0] then ((if y s = 0 then (1:ℝ) else 0) - f₁ s 0) else 0)
        + (if y s = 0 then (1:ℝ) else 0) := by
    intro s _
    have hf0 : f₁ s 0 ≤ 1 := by
      obtain ⟨hnn, hsum⟩ := hd₁ s
      simp only [Fin.sum_univ_three] at hsum
      linarith [hnn 1, hnn 2]
    have hf0' : 0 ≤ f₁ s 0 := (hd₁ s).1 0
    by_cases hx2 : x s = 2
    · rw [if_pos hx2]
      split_ifs <;> linarith
    · have he := hxe s hx2
      rw [if_neg hx2, if_pos he, he]
      split_ifs <;> simp
  have Pc : ∀ s ∈ range t, (if y s = 2 then (1:ℝ) else 0) ≤
      3 * (if x s = 2 then (0:ℝ) else 1) - 3 * ((if x s = 1 then (1:ℝ) else 0) - f₂ s 1) := by
    intro s _
    have hnn := (hd₂ s).1 1
    have hxx : x s = 1 → x s ≠ 2 := fun h => by rw [h]; decide
    by_cases hy2' : y s = 2
    · have h3 := hy2 s hy2'
      rw [if_pos hy2']
      by_cases hx1 : x s = 1
      · rw [if_neg (hxx hx1), if_pos hx1]; linarith
      · rw [if_neg hx1]; split_ifs <;> linarith
    · rw [if_neg hy2']
      by_cases hx1 : x s = 1
      · rw [if_neg (hxx hx1), if_pos hx1]; linarith
      · rw [if_neg hx1]; split_ifs <;> linarith
  have Pd : ∀ s ∈ range t, (if x s = 2 ∧ y s = 1 then (0:ℝ) else 1) ≤
      (if x s = 2 then (0:ℝ) else 1) + (if y s = 0 then (1:ℝ) else 0)
        + (if y s = 2 then (1:ℝ) else 0) := by
    intro s _
    rcases (by decide : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2) (y s) with h | h | h <;>
    by_cases hx2 : x s = 2 <;> simp [h, hx2]
  have Sa := Finset.sum_le_sum Pa
  have Sb := Finset.sum_le_sum Pb
  have Sc := Finset.sum_le_sum Pc
  have Sd := Finset.sum_le_sum Pd
  rw [← Finset.mul_sum] at Sa
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib] at Sb
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at Sc
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at Sd
  have hT2 : t * Shared.calibScore f₂ x j t ≤
      t * Shared.calibScore f₂ x 0 t + t * Shared.calibScore f₂ x 1 t := by
    have h0 := (abs_nonneg _).trans K20
    have h1 := (abs_nonneg _).trans K21
    rcases hj01 with rfl | rfl <;> linarith
  obtain ⟨K1l, K1u⟩ := abs_le.1 K1
  obtain ⟨K2l, K2u⟩ := abs_le.1 K2j
  obtain ⟨K3l, K3u⟩ := abs_le.1 K3
  have h1 := (abs_nonneg _).trans K21
  linarith

open Filter Topology Finset in
theorem aux_exl_sub (D : Fin 3 → Fin 3 → ℝ) (hD : D ∈ LimitSet exU₁ exU₂) : D = exDelta := by
  obtain ⟨R₁, R₂, π₁, π₂, hR₁, hR₂, hπ₁, hπ₂, hc₁, hc₂, hlim⟩ := hD
  set x := play₁ R₁ R₂ π₁ π₂ with hxdef
  set y := play₂ R₁ R₂ π₁ π₂ with hydef
  set f₁ := forecast₁ R₁ R₂ π₁ π₂ with hf₁def
  set f₂ := forecast₂ R₁ R₂ π₁ π₂ with hf₂def
  have hB := aux_exl_count R₁ R₂ hR₁ hR₂ f₁ f₂ x y (fun s => rfl) (fun s => rfl)
    (fun s => hπ₁ _) (fun s => hπ₂ _)
  set bad : ℕ → ℝ := fun t => ∑ s ∈ range t, (if x s = 2 ∧ y s = 1 then (0:ℝ) else 1)
    with hbad
  have hbad0 : ∀ t, 0 ≤ bad t := fun t =>
    Finset.sum_nonneg (fun s _ => by split_ifs <;> norm_num)
  have hlimbad : Tendsto (fun t : ℕ => bad t / t) atTop (𝓝 0) := by
    have hu : Tendsto (fun t : ℕ => 4 * Shared.calibScore f₁ y 0 t
        + 10 * Shared.calibScore f₂ x 0 t + 13 * Shared.calibScore f₂ x 1 t) atTop (𝓝 0) := by
      have := (((hc₁ 0).const_mul 4).add ((hc₂ 0).const_mul 10)).add ((hc₂ 1).const_mul 13)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · exact Eventually.of_forall fun t => div_nonneg (hbad0 t) (Nat.cast_nonneg t)
    · filter_upwards [eventually_ge_atTop 1] with t ht
      have htR : (0:ℝ) < t := by exact_mod_cast ht
      rw [div_le_iff₀ htR]
      have := hB t
      linarith
  have hemp : ∀ t a b, empDist x y t a b
      = (∑ s ∈ range t, if x s = a ∧ y s = b then (1:ℝ) else 0) / t := by
    intro t a b
    unfold empDist
    rw [Finset.natCast_card_filter]
  have hsmall : ∀ a b, ¬(a = 2 ∧ b = 1) →
      Tendsto (fun t => empDist x y t a b) atTop (𝓝 0) := by
    intro a b hab
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimbad ?_ ?_
    · intro t
      dsimp only
      rw [hemp]
      exact div_nonneg (sum_nonneg fun s _ => by split_ifs <;> norm_num) (Nat.cast_nonneg _)
    · intro t
      dsimp only
      rw [hemp]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro s _
      split_ifs with h1 h2 <;> try norm_num
      exact hab ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
  have hone : Tendsto (fun t => empDist x y t 2 1) atTop (𝓝 1) := by
    have h1 : Tendsto (fun t : ℕ => 1 - bad t / t) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1:ℝ))).sub hlimbad
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htR : (t:ℝ) ≠ 0 := by positivity
    rw [hemp]
    have hs : (∑ s ∈ range t, if x s = 2 ∧ y s = 1 then (1:ℝ) else 0) = t - bad t := by
      rw [hbad]
      simp only
      rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (g := fun _ => (1:ℝ)) (fun s _ => by split_ifs <;> norm_num)]
      simp
    rw [hs]
    field_simp
  funext a b
  unfold exDelta
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact tendsto_nhds_unique (hlim 2 1) hone
  · exact tendsto_nhds_unique (hlim a b) (hsmall a b h)

theorem aux_exl_const_calib {k : ℕ} (p : Fin k → ℝ) (c : Fin k)
    (hp : ∀ j, p j = if c = j then 1 else 0) (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k)
    (hf : ∀ s, f s = p) (hz : ∀ s, z s = c) : Shared.Calibrated f z := by
  intro j
  have h0 : ∀ t, Shared.calibScore f z j t = 0 := by
    intro t
    unfold Shared.calibScore
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hq
    rw [hf s]
    have ht : t ≠ 0 := by have := Finset.mem_range.1 hs; omega
    have hN : Shared.N f p t = t := by
      unfold Shared.N
      rw [Finset.filter_true_of_mem (fun s _ => hf s), Finset.card_range]
    have hrho : Shared.rho f z p j t = p j := by
      unfold Shared.rho
      rw [hN, if_neg ht, hp j]
      by_cases hcj : c = j
      · rw [if_pos hcj, Finset.filter_true_of_mem (fun s _ => ⟨hf s, (hz s).trans hcj⟩),
          Finset.card_range]
        have : (t:ℝ) ≠ 0 := by exact_mod_cast ht
        field_simp
      · rw [if_neg hcj, Finset.filter_false_of_mem (fun s _ h => hcj ((hz s).symm.trans h.2))]
        simp
    rw [hrho, sub_self, abs_zero, zero_mul, zero_div]
  simp only [h0]
  exact tendsto_const_nhds

open Filter Topology in
theorem aux_exl_sup : exDelta ∈ LimitSet exU₁ exU₂ := by
  have hex : ∀ q : Fin 3 → ℝ, ∃ b : Fin 3, (q = ![0,0,1] → b = 1) ∧
      ∀ b', ∑ a, q a * exU₂ a b' ≤ ∑ a, q a * exU₂ a b := by
    intro q
    by_cases hq : q = ![0,0,1]
    · refine ⟨1, fun _ => rfl, fun b' => ?_⟩
      subst hq
      simp only [Fin.sum_univ_three]
      fin_cases b' <;> simp [exU₂, Matrix.cons_val]
    · obtain ⟨b, _, hb⟩ := Finset.exists_max_image Finset.univ
        (fun b => ∑ a, q a * exU₂ a b) Finset.univ_nonempty
      exact ⟨b, fun h => absurd h hq, fun b' => hb b' (Finset.mem_univ _)⟩
  choose R₂ hR₂e hR₂b using hex
  have hy : ∀ s, play₂ (fun _ => (2 : Fin 3)) R₂ (fun _ => ![0,1,0]) (fun _ => ![0,0,1]) s = 1 :=
    fun s => hR₂e ![0,0,1] rfl
  have hx : ∀ s, play₁ (fun _ => (2 : Fin 3)) R₂ (fun _ => ![0,1,0]) (fun _ => ![0,0,1]) s = 2 :=
    fun s => rfl
  refine ⟨fun _ => 2, R₂, fun _ => ![0,1,0], fun _ => ![0,0,1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp a'
    obtain ⟨hnn, _⟩ := hp
    simp only [Fin.sum_univ_three]
    have := hnn 1
    have := hnn 2
    fin_cases a' <;> simp [exU₁, Matrix.cons_val] <;> linarith
  · intro q _ b'
    exact hR₂b q b'
  · intro h
    exact ⟨fun a => by fin_cases a <;> simp, by simp [Fin.sum_univ_three]⟩
  · intro h
    exact ⟨fun a => by fin_cases a <;> simp, by simp [Fin.sum_univ_three]⟩
  · exact aux_exl_const_calib ![0,1,0] 1 (by intro j; fin_cases j <;> simp) _ _
      (fun s => rfl) hy
  · exact aux_exl_const_calib ![0,0,1] 2 (by intro j; fin_cases j <;> simp) _ _
      (fun s => rfl) hx
  · intro a b
    unfold empDist
    simp only [hx, hy]
    unfold exDelta
    by_cases hab : a = 2 ∧ b = 1
    · obtain ⟨rfl, rfl⟩ := hab
      simp only [and_self, if_true, Finset.filter_true, Finset.card_range]
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 1] with t ht
      have : (t:ℝ) ≠ 0 := by positivity
      field_simp
    · rw [if_neg hab]
      have h0 : ∀ t, ((Finset.range t).filter (fun _ => (2 : Fin 3) = a ∧ (1 : Fin 3) = b)).card = 0 := by
        intro t
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro s _ h
        exact hab ⟨h.1.symm, h.2.symm⟩
      simp only [h0, Nat.cast_zero, zero_div]
      exact tendsto_const_nhds

end CalibratedCE.Generic

open CalibratedCE.Generic

theorem solution : LimitSet exU₁ exU₂ = {exDelta} := by
  ext D
  constructor
  · intro hD
    exact aux_exl_sub D hD
  · intro hD
    rw [Set.mem_singleton_iff] at hD
    subst hD
    exact aux_exl_sup
