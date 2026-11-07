-- Prove2me | solution 1 for GenCMu.HeavyTraffic.eq_46_50_kuhn_tucker
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:52:47.735425+00:00
-- url     : https://prove2.me/submissions/9d57957b-bd6b-44b8-b4dc-5a97e3633d51

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMuKKTAux

open Filter Topology Finset GenCMu.HeavyTraffic

lemma grad_ineq (C : ℝ → ℝ) (hc : ConvexOn ℝ (Set.Ici 0) C)
    (hd : DifferentiableOn ℝ C (Set.Ici 0)) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    C a + derivWithin C (Set.Ici 0) a * (b - a) ≤ C b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h := hc.derivWithin_le_slope (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr hb) hab
      (hd a (Set.mem_Ici.mpr ha))
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hab)] at h
    linarith
  · simp
  · have h := hc.slope_le_derivWithin (Set.mem_Ici.mpr hb) (Set.mem_Ici.mpr ha) hba
      (hd a (Set.mem_Ici.mpr ha))
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hba)] at h
    nlinarith

lemma deriv_nonneg_of_min (ψ : ℝ → ℝ) (D : ℝ) (hψ : HasDerivWithinAt ψ D (Set.Ici 0) 0)
    (ε : ℝ) (hε : 0 < ε) (hmin : ∀ s ∈ Set.Ioo 0 ε, ψ 0 ≤ ψ s) : 0 ≤ D := by
  have h := hasDerivWithinAt_iff_tendsto_slope.mp hψ
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h; exact ⟨h.le, h.ne'⟩
  rw [hset] at h
  refine ge_of_tendsto h ?_
  filter_upwards [Ioo_mem_nhdsGT hε] with s hs
  rw [slope_def_field]
  exact div_nonneg (by linarith [hmin s hs]) (by linarith [hs.1])

end GenCMuKKTAux

open Filter Topology Finset GenCMu.HeavyTraffic GenCMuKKTAux

theorem solution {d : ℕ} (lam rho : Fin d → ℝ) (Cs : Fin d → ℝ → ℝ)
    (hlam : ∀ k, 0 < lam k) (hrho : ∀ k, 0 < rho k)
    (hconv : ∀ k, ConvexOn ℝ (Set.Ici 0) (Cs k)) (hC1 : ∀ k, ContDiffOn ℝ 1 (Cs k) (Set.Ici 0))
    (y : ℝ) (x : Fin d → ℝ) (hx : ∀ k, 0 ≤ x k) (hsum : ∑ k, x k = y) :
    (IsMin43 lam rho Cs y x ↔
      ∃ α₀ : ℝ, ∃ α : Fin d → ℝ, (∀ k, 0 ≤ α k) ∧
        (∀ k, lam k / rho k * mc Cs k (x k / rho k) - α k = α₀) ∧ (∀ k, α k * x k = 0)) ∧
    ((∀ k, 0 < x k) →
      (IsMin43 lam rho Cs y x ↔ ∃ α₀ : ℝ, ∀ k, lam k / rho k * mc Cs k (x k / rho k) = α₀)) := by
  classical
  have hdiff : ∀ k, DifferentiableOn ℝ (Cs k) (Set.Ici 0) := fun k =>
    (hC1 k).differentiableOn one_ne_zero
  set f' : Fin d → ℝ := fun k => lam k / rho k * mc Cs k (x k / rho k) with hf'
  -- sufficiency
  have suff : (∃ α₀ : ℝ, ∃ α : Fin d → ℝ, (∀ k, 0 ≤ α k) ∧
        (∀ k, f' k - α k = α₀) ∧ (∀ k, α k * x k = 0)) → IsMin43 lam rho Cs y x := by
    rintro ⟨α₀, α, hα, hK, hcs⟩
    refine ⟨hx, hsum, fun x' hx' hsum' => ?_⟩
    unfold obj43
    have hterm : ∀ k, lam k * Cs k (x k / rho k) + (α₀ + α k) * (x' k - x k)
        ≤ lam k * Cs k (x' k / rho k) := by
      intro k
      have hg := grad_ineq (Cs k) (hconv k) (hdiff k) (x k / rho k) (x' k / rho k)
        (div_nonneg (hx k) (hrho k).le) (div_nonneg (hx' k) (hrho k).le)
      have hl := hlam k
      have hr := hrho k
      have e : (α₀ + α k) * (x' k - x k) =
          lam k * (derivWithin (Cs k) (Set.Ici 0) (x k / rho k) * (x' k / rho k - x k / rho k)) := by
        have := hK k
        simp only [hf', mc] at this
        rw [show α₀ + α k = lam k / rho k * derivWithin (Cs k) (Set.Ici 0) (x k / rho k) by
          linarith]
        field_simp
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hg hl.le]
    have hsumt := Finset.sum_le_sum fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => hterm k
    rw [Finset.sum_add_distrib] at hsumt
    have hnn : 0 ≤ ∑ k, (α₀ + α k) * (x' k - x k) := by
      have e : ∑ k, (α₀ + α k) * (x' k - x k) =
          α₀ * (∑ k, x' k - ∑ k, x k) + ∑ k, α k * x' k - ∑ k, α k * x k := by
        simp only [add_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        ring
      rw [e, hsum, hsum', sub_self, mul_zero, zero_add]
      have h1 : ∑ k, α k * x k = 0 := Finset.sum_eq_zero fun k _ => hcs k
      rw [h1, sub_zero]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (hα k) (hx' k)
    linarith
  -- necessity
  have nec_pair : IsMin43 lam rho Cs y x → ∀ k l, 0 < x k → f' k ≤ f' l := by
    intro hmin k l hk
    by_cases hkl : k = l
    · subst hkl; exact le_rfl
    set ψ : ℝ → ℝ := fun s => lam l * Cs l ((x l + s) / rho l) +
      lam k * Cs k ((x k - s) / rho k) with hψ
    have hl := hlam l
    have hrl := hrho l
    have hkk := hlam k
    have hrk := hrho k
    have hdl : HasDerivWithinAt (fun s => Cs l ((x l + s) / rho l))
        (mc Cs l (x l / rho l) * (1 / rho l)) (Set.Ici 0) 0 := by
      have hCl : HasDerivWithinAt (Cs l) (mc Cs l (x l / rho l)) (Set.Ici 0) (x l / rho l) :=
        (hdiff l _ (Set.mem_Ici.mpr (div_nonneg (hx l) hrl.le))).hasDerivWithinAt
      have hh : HasDerivWithinAt (fun s : ℝ => (x l + s) / rho l) (1 / rho l) (Set.Ici 0) 0 :=
        (((hasDerivAt_id (0 : ℝ)).const_add (x l)).div_const (rho l)).hasDerivWithinAt
      exact hCl.comp_of_eq 0 hh (fun s hs => Set.mem_Ici.mpr
        (div_nonneg (by linarith [Set.mem_Ici.mp hs, hx l]) hrl.le)) (by simp)
    have hdk : HasDerivAt (fun s => Cs k ((x k - s) / rho k))
        (mc Cs k (x k / rho k) * (-1 / rho k)) 0 := by
      have hCk : HasDerivAt (Cs k) (mc Cs k (x k / rho k)) (x k / rho k) :=
        ((hdiff k _ (Set.mem_Ici.mpr (div_nonneg (hx k) hrk.le))).hasDerivWithinAt).hasDerivAt
          (Ici_mem_nhds (div_pos hk hrk))
      have hh : HasDerivAt (fun s : ℝ => (x k - s) / rho k) (-1 / rho k) 0 := by
        have := ((hasDerivAt_id (0 : ℝ)).const_sub (x k)).div_const (rho k)
        simpa using this
      exact hCk.comp_of_eq 0 hh (by simp)
    have hψd : HasDerivWithinAt ψ (lam l * (mc Cs l (x l / rho l) * (1 / rho l)) +
        lam k * (mc Cs k (x k / rho k) * (-1 / rho k))) (Set.Ici 0) 0 :=
      (hdl.const_mul (lam l)).add ((hdk.const_mul (lam k)).hasDerivWithinAt)
    have hmin' : ∀ s ∈ Set.Ioo 0 (x k), ψ 0 ≤ ψ s := by
      intro s hs
      set x' : Fin d → ℝ := fun j => if j = l then x l + s else if j = k then x k - s else x j
        with hx'
      have hx'l : x' l = x l + s := by simp [hx']
      have hx'k : x' k = x k - s := by simp [hx', hkl]
      have hx'o : ∀ j, j ≠ k ∧ j ≠ l → x' j = x j := by
        intro j hj; simp [hx', hj.1, hj.2]
      have hnn : ∀ j, 0 ≤ x' j := by
        intro j
        by_cases hj1 : j = l
        · subst hj1; rw [hx'l]; linarith [hx j, hs.1]
        by_cases hj2 : j = k
        · subst hj2; rw [hx'k]; linarith [hs.2]
        rw [hx'o j ⟨hj2, hj1⟩]; exact hx j
      have hs' : ∑ j, x' j = y := by
        rw [← hsum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_add_of_mem k l (Finset.mem_univ _) (Finset.mem_univ _) hkl]
        · rw [hx'k, hx'l]; ring
        · intro j _ hj; rw [hx'o j hj, sub_self]
      have hm := hmin.2.2 x' hnn hs'
      unfold obj43 at hm
      have hdiffo : ∑ j, lam j * Cs j (x' j / rho j) - ∑ j, lam j * Cs j (x j / rho j) =
          ψ s - ψ 0 := by
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_add_of_mem k l (Finset.mem_univ _) (Finset.mem_univ _) hkl]
        · rw [hx'k, hx'l]; simp only [hψ, add_zero, sub_zero]; ring
        · intro j _ hj; rw [hx'o j hj, sub_self]
      linarith
    have := deriv_nonneg_of_min ψ _ hψd (x k) hk hmin'
    simp only [hf']
    have e1 : lam l * (mc Cs l (x l / rho l) * (1 / rho l)) = lam l / rho l * mc Cs l (x l / rho l) := by
      field_simp
    have e2 : lam k * (mc Cs k (x k / rho k) * (-1 / rho k)) =
        -(lam k / rho k * mc Cs k (x k / rho k)) := by
      field_simp
    linarith
  have nec : IsMin43 lam rho Cs y x → ∃ α₀ : ℝ, ∃ α : Fin d → ℝ, (∀ k, 0 ≤ α k) ∧
        (∀ k, f' k - α k = α₀) ∧ (∀ k, α k * x k = 0) := by
    intro hmin
    by_cases hex : ∃ k, 0 < x k
    · obtain ⟨k0, hk0⟩ := hex
      refine ⟨f' k0, fun k => f' k - f' k0, fun k => ?_, fun k => by ring, fun k => ?_⟩
      · linarith [nec_pair hmin k0 k hk0]
      · rcases (hx k).lt_or_eq with h | h
        · have := nec_pair hmin k k0 h
          have := nec_pair hmin k0 k hk0
          have : f' k - f' k0 = 0 := by linarith
          show (f' k - f' k0) * x k = 0
          rw [this, zero_mul]
        · rw [← h, mul_zero]
    · push Not at hex
      refine ⟨-(∑ j, |f' j|), fun k => f' k + ∑ j, |f' j|, fun k => ?_, fun k => by ring,
        fun k => ?_⟩
      · have := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
          abs_nonneg (f' j)) (Finset.mem_univ k)
        linarith [neg_abs_le (f' k)]
      · rw [le_antisymm (hex k) (hx k), mul_zero]
  refine ⟨⟨nec, suff⟩, fun hpos => ⟨fun hmin => ?_, fun ⟨α₀, hα₀⟩ => ?_⟩⟩
  · obtain ⟨α₀, α, -, hK, hcs⟩ := nec hmin
    refine ⟨α₀, fun k => ?_⟩
    have h0 : α k = 0 := by
      rcases mul_eq_zero.mp (hcs k) with h | h
      · exact h
      · exact absurd h (hpos k).ne'
    have := hK k
    rw [h0, sub_zero] at this
    exact this
  · exact suff ⟨α₀, fun _ => 0, fun _ => le_rfl, fun k => by simp [hf', hα₀ k],
      fun k => by simp⟩
