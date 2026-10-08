-- Prove2me | solution 2 for BondarevaShapley.core_nonempty_iff_balanced
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T20:41:08.103656+00:00
-- url     : https://prove2.me/submissions/a9cb9eb3-978a-429c-ba96-a8f5536b8099

import Mathlib

theorem solution {N : Type*} [Fintype N] [DecidableEq N] [Nonempty N]
    (v : Finset N → ℝ) (hv : v ∅ = 0) :
    (∃ x : N → ℝ, ∑ i, x i = v Finset.univ ∧ ∀ S : Finset N, v S ≤ ∑ i ∈ S, x i) ↔
      ∀ (B : Finset (Finset N)) (δ : Finset N → ℝ),
        ∅ ∉ B → (∀ S ∈ B, 0 < δ S) →
        (∀ i : N, ∑ S ∈ B.filter (fun S => i ∈ S), δ S = 1) →
        ∑ S ∈ B, δ S * v S ≤ v Finset.univ := by
  constructor
  · rintro ⟨x, hxN, hx⟩ B δ _ hpos hbal
    calc ∑ S ∈ B, δ S * v S ≤ ∑ S ∈ B, δ S * ∑ i ∈ S, x i :=
          Finset.sum_le_sum fun S hS => mul_le_mul_of_nonneg_left (hx S) (hpos S hS).le
      _ = ∑ i, x i * ∑ S ∈ B.filter (fun S => i ∈ S), δ S := by
          simp only [Finset.mul_sum, Finset.sum_filter]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun S _ => ?_
          simp [mul_ite, Finset.sum_ite_mem, mul_comm]
      _ = v Finset.univ := by simp [hbal, hxN]
  · intro hbal
    have step1 : ∀ ε > 0, ∃ x : N → ℝ, (∀ S : Finset N, v S - ε < ∑ i ∈ S, x i) ∧
        ∑ i, x i < v Finset.univ + ε := by
      intro ε hε
      let a : Option (Finset N) → (Option N → ℝ) := fun k => match k with
        | none => fun j => j.elim (v Finset.univ + ε) (fun _ => -1)
        | some S => fun j => j.elim (-(v S - ε)) (fun i => if i ∈ S then 1 else 0)
      let L : (Option (Finset N) → ℝ) →ₗ[ℝ] (Option N → ℝ) := Fintype.linearCombination ℝ a
      let K := L '' stdSimplex ℝ (Option (Finset N))
      have hKc : IsCompact K := (isCompact_stdSimplex ℝ _).image L.continuous_of_finiteDimensional
      have hKv : Convex ℝ K := (convex_stdSimplex ℝ _).linear_image L
      have h0 : (0 : Option N → ℝ) ∉ K := by
        rintro ⟨w, ⟨hw0, hw1⟩, hLw⟩
        have hcoord : ∀ j, ∑ k, w k * a k j = 0 := fun j => by
          have := congrFun hLw j
          simpa [L, Fintype.linearCombination_apply, Finset.sum_apply] using this
        have hi : ∀ i : N, ∑ S, (if i ∈ S then w (some S) else 0) = w none := by
          intro i; have := hcoord (some i); simp [a, Fintype.sum_option] at this; linarith
        have hn : ∑ S, w (some S) * (v S - ε) = w none * (v Finset.univ + ε) := by
          have := hcoord none; simp [a, Fintype.sum_option] at this
          have h' : ∑ S, w (some S) * (v S - ε) = -∑ S, w (some S) * (ε - v S) := by
            rw [← Finset.sum_neg_distrib]; congr 1; ext; ring
          linarith
        have hw1' : w none + ∑ S, w (some S) = 1 := by simpa [Fintype.sum_option] using hw1
        rcases (hw0 none).lt_or_eq with hpos | hzero
        · set B := Finset.univ.filter (fun S : Finset N => S ≠ ∅ ∧ 0 < w (some S)) with hB
          have key := hbal B (fun S => w (some S) / w none) (by simp [B])
            (fun S hS => div_pos (Finset.mem_filter.1 hS).2.2 hpos) (by
              intro i
              rw [← Finset.sum_div, div_eq_one_iff_eq hpos.ne', ← hi i, Finset.filter_filter,
                Finset.sum_filter]
              refine Finset.sum_congr rfl fun S _ => ?_
              by_cases hiS : i ∈ S
              · have hS : S ≠ ∅ := Finset.ne_empty_of_mem hiS
                by_cases hw : 0 < w (some S)
                · simp [hiS, hS, hw]
                · simp [hiS, hS, le_antisymm (not_lt.1 hw) (hw0 _)]
              · simp [hiS])
          have hsum : ∑ S ∈ B, w (some S) / w none * v S = (∑ S, w (some S) * v S) / w none := by
            rw [Finset.sum_div, hB, Finset.sum_filter]
            refine Finset.sum_congr rfl fun S _ => ?_
            by_cases hS : S = ∅
            · simp [hS, hv]
            by_cases hw : 0 < w (some S)
            · simp [hS, hw]; ring
            · simp [hS, le_antisymm (not_lt.1 hw) (hw0 _)]
          have hvw : ∑ S, w (some S) * v S = w none * (v Finset.univ + ε) + ε * ∑ S, w (some S) := by
            rw [← hn, Finset.mul_sum, ← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun S _ => ?_
            ring
          have hnn : 0 ≤ ∑ S, w (some S) := Finset.sum_nonneg fun S _ => hw0 _
          rw [hsum, div_le_iff₀ hpos, hvw] at key
          nlinarith
        · have hS : ∀ S : Finset N, S ≠ ∅ → w (some S) = 0 := by
            intro S hS
            obtain ⟨i, hiS⟩ := Finset.nonempty_iff_ne_empty.2 hS
            have h := hi i
            rw [← hzero] at h
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun T _ => by
              split_ifs
              · exact hw0 _
              · exact le_rfl)).1 h S (Finset.mem_univ _)
            simpa [hiS] using this
          have hn' : ∑ S, w (some S) * (v S - ε) = w (some ∅) * (v ∅ - ε) :=
            Finset.sum_eq_single ∅ (fun S _ hS' => by simp [hS S hS']) (by simp)
          rw [hn', ← hzero, hv] at hn
          have he : w (some ∅) = 0 := by nlinarith
          have : ∑ S, w (some S) = 0 := Finset.sum_eq_zero fun S _ => by
            by_cases h : S = ∅
            · rw [h, he]
            · exact hS S h
          linarith
      obtain ⟨f, u, v', hfu, huv, hv'⟩ := geometric_hahn_banach_compact_closed hKv hKc
        (convex_singleton 0) isClosed_singleton (Set.disjoint_singleton_right.2 h0)
      have hneg : ∀ k, f (a k) < 0 := by
        intro k
        have hmem : a k ∈ K := ⟨Pi.single k 1, single_mem_stdSimplex ℝ k, by
          simp [L, Fintype.linearCombination_apply, Pi.single_apply]⟩
        have := hv' 0 rfl
        simp at this
        linarith [hfu _ hmem]
      have hf : ∀ u : Option N → ℝ, f u = u none * f (fun j => if none = j then 1 else 0) +
          ∑ i, u (some i) * f (fun j => if some i = j then 1 else 0) := by
        intro u
        have := LinearMap.pi_apply_eq_sum_univ (f : (Option N → ℝ) →ₗ[ℝ] ℝ) u
        simpa [Fintype.sum_option] using this
      set c := f (fun j => if none = j then 1 else 0)
      set x : N → ℝ := fun i => f (fun j => if some i = j then 1 else 0)
      have hS : ∀ S : Finset N, -(v S - ε) * c + ∑ i ∈ S, x i < 0 := by
        intro S
        have := hneg (some S)
        rw [hf] at this
        simpa [a, Finset.sum_ite_mem] using this
      have hN : (v Finset.univ + ε) * c - ∑ i, x i < 0 := by
        have := hneg none
        rw [hf] at this
        simpa [a, sub_eq_add_neg] using this
      have hc : c < 0 := by
        have := hS ∅
        simp [hv] at this
        nlinarith
      refine ⟨fun i => x i / c, fun S => ?_, ?_⟩
      · rw [← Finset.sum_div, lt_div_iff_of_neg hc]
        linarith [hS S]
      · rw [← Finset.sum_div, div_lt_iff_of_neg hc]
        linarith
    set M : ℝ := (Fintype.card (Finset N) : ℝ) + 1 with hM
    set C : ℝ := |v Finset.univ| + 1 + ∑ j, (|v {j}| + 1) with hC
    set box : Set (N → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-C) C) with hbox_def
    have hbox : IsCompact box := isCompact_univ_pi fun _ => isCompact_Icc
    set φ : (N → ℝ) → ℝ := fun x =>
      ∑ S, max (v S - ∑ i ∈ S, x i) 0 + max (∑ i, x i - v Finset.univ) 0 with hφ
    have hφc : Continuous φ := by fun_prop
    have hinbox : ∀ ε, ε ≤ 1 → ∀ x : N → ℝ, (∀ S : Finset N, v S - ε < ∑ i ∈ S, x i) →
        ∑ i, x i < v Finset.univ + ε → x ∈ box := by
      intro ε hε1 x hxS hxN i _
      have hj : ∀ j, -(|v {j}| + 1) < x j := by
        intro j
        have := hxS {j}
        simp at this
        linarith [neg_abs_le (v {j})]
      have hle : |v {i}| + 1 ≤ ∑ j, (|v {j}| + 1) :=
        Finset.single_le_sum (f := fun j => |v {j}| + 1) (fun j _ => by positivity)
          (Finset.mem_univ i)
      have hrest : -∑ j, (|v {j}| + 1) ≤ ∑ j ∈ Finset.univ.erase i, x j := by
        have h1 : ∑ j ∈ Finset.univ.erase i, (|v {j}| + 1) ≤ ∑ j, (|v {j}| + 1) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun j _ _ => by positivity)
        have h2 : ∑ j ∈ Finset.univ.erase i, -(|v {j}| + 1) ≤ ∑ j ∈ Finset.univ.erase i, x j :=
          Finset.sum_le_sum fun j _ => (hj j).le
        rw [Finset.sum_neg_distrib] at h2
        linarith
      have hsplit := Finset.add_sum_erase Finset.univ x (Finset.mem_univ i)
      have habs := le_abs_self (v Finset.univ)
      constructor
      · linarith [hj i, abs_nonneg (v Finset.univ)]
      · linarith
    obtain ⟨x1, hx1S, hx1N⟩ := step1 1 one_pos
    obtain ⟨x0, hx0box, hx0min⟩ :=
      hbox.exists_isMinOn ⟨x1, hinbox 1 le_rfl x1 hx1S hx1N⟩ hφc.continuousOn
    have hφ0 : φ x0 ≤ 0 := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have hMpos : 0 < M := by positivity
      set ε' := min 1 (ε / M) with hε'
      have hε'pos : 0 < ε' := lt_min one_pos (div_pos hε hMpos)
      obtain ⟨x, hxS, hxN⟩ := step1 ε' hε'pos
      have hle : φ x0 ≤ φ x := hx0min (hinbox ε' (min_le_left _ _) x hxS hxN)
      have hφx : φ x ≤ M * ε' := by
        have h1 : ∑ S, max (v S - ∑ i ∈ S, x i) 0 ≤ ∑ _S : Finset N, ε' :=
          Finset.sum_le_sum fun S _ => max_le (by linarith [hxS S]) hε'pos.le
        have h2 : max (∑ i, x i - v Finset.univ) 0 ≤ ε' := max_le (by linarith) hε'pos.le
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
        simp only [φ, hM]
        linarith
      have : M * ε' ≤ ε := by
        calc M * ε' ≤ M * (ε / M) := mul_le_mul_of_nonneg_left (min_le_right _ _) hMpos.le
          _ = ε := by field_simp
      linarith
    have hterm : ∀ S, max (v S - ∑ i ∈ S, x0 i) 0 ≤ φ x0 := by
      intro S
      have h1 : max (v S - ∑ i ∈ S, x0 i) 0 ≤ ∑ T, max (v T - ∑ i ∈ T, x0 i) 0 :=
        Finset.single_le_sum (f := fun T => max (v T - ∑ i ∈ T, x0 i) 0)
          (fun T _ => le_max_right _ _) (Finset.mem_univ S)
      have h2 := le_max_right (∑ i, x0 i - v Finset.univ) 0
      simp only [φ]
      linarith
    have hcore : ∀ S : Finset N, v S ≤ ∑ i ∈ S, x0 i := fun S => by
      linarith [hterm S, le_max_left (v S - ∑ i ∈ S, x0 i) 0]
    have hNle : ∑ i, x0 i ≤ v Finset.univ := by
      have h1 : 0 ≤ ∑ T, max (v T - ∑ i ∈ T, x0 i) 0 :=
        Finset.sum_nonneg fun T _ => le_max_right _ _
      have h2 := le_max_left (∑ i, x0 i - v Finset.univ) 0
      have : φ x0 = ∑ T, max (v T - ∑ i ∈ T, x0 i) 0 + max (∑ i, x0 i - v Finset.univ) 0 := rfl
      linarith
    exact ⟨x0, le_antisymm hNle (hcore Finset.univ), hcore⟩
