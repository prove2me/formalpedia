-- Prove2me | solution 1 for Formalism.ValuationGridEstimates.valuation_ratio_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:00.575582+00:00
-- url     : https://prove2.me/submissions/160545fc-d957-4c5e-9242-d99bedecef82

import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationBoundIndexed
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_SumAdditiveCharacterEqZero
import Definitions.Def_Formalism_TowerValuationBounds_TowerValuationProofs_ValuationRatioIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ValuationGridEstimates
open Finset
namespace Formalism.ValuationGridEstimates
theorem _root_.solution : TowerValuationBoundIndexed := by
  intro G _ v hv a a' d h p q e had hae hdh he ha' T Td Tdp ρ E N0 ε δ σ H1 H2 c0 c00 A A0 A0'
    hc0 hc00 hA ub ua hub hua r hr
  classical
  subst hr
  have hv1 : v 1 = 0 := by
    have h11 := hv 1 1
    rw [one_mul] at h11
    linarith
  have hvinv : ∀ x, v x⁻¹ = - v x := fun x => by
    have h2 := hv x x⁻¹
    rw [mul_inv_cancel, hv1] at h2
    linarith
  have hvdiv : ∀ x y, v (x / y) = v x - v y := fun x y => by
    rw [div_eq_mul_inv, hv, hvinv]; ring
  have hvprod : ∀ {ι : Type} (s : Finset ι) (f : ι → G),
      v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
    intro ι s f
    induction s using Finset.induction_on with
    | empty => simp [hv1]
    | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, hv, ih]
  have hvA := congrArg v hA
  rw [hvdiv, hvprod] at hvA
  simp only [hv, hvinv, hvdiv, hvprod]
  obtain ⟨U, hU⟩ : ∃ U : ℕ, U = h - (p + q) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = e + q - p := ⟨_, rfl⟩
  have hUz : (h : ℤ) - (p + q) = (U : ℤ) := by omega
  have hPz : (e : ℤ) + q - p = (P : ℤ) := by omega
  rw [hUz, hPz] at hvA
  rw [hPz] at H2
  have I1 : ∑ s ∈ Finset.Icc (1 - (P : ℤ)) (U : ℤ), v (ρ s) =
      ∑ s ∈ Finset.Icc (1 - (P : ℤ)) 0, v (ρ s) + ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have I2 : ∑ s ∈ Finset.Icc (1 - (P : ℤ)) 0, v (ρ s) = ∑ s ∈ Finset.Icc (1 : ℤ) P, v (ρ s) := by
    refine Finset.sum_nbij' (fun s => 1 - s) (fun t => 1 - t) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x _; ring
    · intro x _; ring
    · intro s hs
      simp only [Finset.mem_Icc] at hs
      obtain ⟨h1, h2⟩ := H2 s hs.1 hs.2
      rw [h1, hv, h2, zero_add]
  have I3 : ∑ k ∈ Finset.Icc 1 p, v (ρ ((e : ℤ) + q - k + 1)) =
      ∑ t ∈ Finset.Icc ((P : ℤ) + 1) ((e : ℤ) + q), v (ρ t) := by
    refine Finset.sum_nbij' (fun k : ℕ => (e : ℤ) + q - k + 1)
      (fun t : ℤ => ((e : ℤ) + q + 1 - t).toNat) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro k _; rfl
  have I4 : ∑ k ∈ Finset.Icc 1 q, v (ρ ((e : ℤ) + k)) =
      ∑ t ∈ Finset.Icc ((e : ℤ) + 1) ((e : ℤ) + q), v (ρ t) := by
    refine Finset.sum_nbij' (fun k : ℕ => (e : ℤ) + k) (fun t : ℤ => (t - e).toNat) ?_ ?_ ?_ ?_ ?_
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro x hx; simp only [Finset.mem_Icc, Finset.mem_coe] at *; omega
    · intro k _; rfl
  have ShiftFormula : ∑ t ∈ Finset.Icc (1 : ℤ) P, v (ρ t) +
      ∑ t ∈ Finset.Icc ((P : ℤ) + 1) ((e : ℤ) + q), v (ρ t) =
      ∑ t ∈ Finset.Icc (1 : ℤ) ((e : ℤ) + q), v (ρ t) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have I5b : ∑ t ∈ Finset.Icc (1 : ℤ) e, v (ρ t) +
      ∑ t ∈ Finset.Icc ((e : ℤ) + 1) ((e : ℤ) + q), v (ρ t) =
      ∑ t ∈ Finset.Icc (1 : ℤ) ((e : ℤ) + q), v (ρ t) := by
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have hF : ∀ s ∈ Finset.Icc (1 : ℤ) h, v (ρ s) ≤ |v (Td s)| + |v (T s)| + ε := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    obtain ⟨_, hρ, _, hup⟩ := H1 s hs.1 hs.2
    rw [hρ, hvdiv]
    have := le_abs_self (v (Td s))
    have := neg_abs_le (v (T s))
    linarith
  have hε : ∀ s ∈ Finset.Icc (1 : ℤ) h, -ε ≤ |v (Td s)| + N0 s := by
    intro s hs
    simp only [Finset.mem_Icc] at hs
    obtain ⟨_, _, hlo, hup⟩ := H1 s hs.1 hs.2
    have := le_abs_self (v (Td s))
    linarith
  have hN : ∀ s ∈ Finset.Icc (1 : ℤ) h, 0 ≤ N0 s := fun s hs => by
    simp only [Finset.mem_Icc] at hs
    exact (H1 s hs.1 hs.2).1
  have hcard : ∀ (lo hi : ℤ) (n : ℕ), hi + 1 - lo = n → ((Finset.Icc lo hi).card : ℝ) = n := by
    intro lo hi n hn
    rw [Int.card_Icc, hn]
    simp
  let C : ℤ → ℝ := fun s => |v (Td s)| + |v (T s)| + N0 s
  have hsub : ∀ {lo hi : ℤ}, 1 ≤ lo → hi ≤ h → Finset.Icc lo hi ⊆ Finset.Icc (1 : ℤ) h := by
    intro lo hi h1 h2 x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hCnn : ∀ s ∈ Finset.Icc (1 : ℤ) h, 0 ≤ C s := fun s hs => by
    have := hN s hs
    have := abs_nonneg (v (Td s))
    have := abs_nonneg (v (T s))
    simp only [C]
    linarith
  have Be : ∑ s ∈ Finset.Icc (1 : ℤ) e, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s + e * ε := by
    have hs1 : Finset.Icc (1 : ℤ) e ⊆ Finset.Icc (1 : ℤ) h := hsub le_rfl (by omega)
    calc ∑ s ∈ Finset.Icc (1 : ℤ) e, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) e, (C s + ε) :=
          Finset.sum_le_sum fun s hs => by
            have := hF s (hs1 hs)
            have := hN s (hs1 hs)
            simp only [C]
            linarith
      _ = ∑ s ∈ Finset.Icc (1 : ℤ) e, C s + e * ε := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard 1 e e (by ring)]
      _ ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s + e * ε :=
          add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hs1 (fun s hs _ => hCnn s hs)) le_rfl
  have BU : ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + U * ε := by
    have hs1 : Finset.Icc (1 : ℤ) U ⊆ Finset.Icc (1 : ℤ) h := hsub le_rfl (by omega)
    calc ∑ s ∈ Finset.Icc (1 : ℤ) U, v (ρ s) ≤ ∑ s ∈ Finset.Icc (1 : ℤ) U, (C s + ε) :=
          Finset.sum_le_sum fun s hs => by
            have := hF s (hs1 hs)
            have := hN s (hs1 hs)
            simp only [C]
            linarith
      _ = ∑ s ∈ Finset.Icc (1 : ℤ) U, C s + U * ε := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hcard 1 U U (by ring)]
  have Bq : -(q * ε) ≤ ∑ s ∈ Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q), C s := by
    have hs1 : Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q) ⊆ Finset.Icc (1 : ℤ) h :=
      hsub (by omega) (by omega)
    have h3 := Finset.sum_le_sum (s := Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q))
      (f := fun _ => -ε) (g := C) (fun s hs => by
        have := hε s (hs1 hs)
        have := abs_nonneg (v (T s))
        simp only [C]
        linarith)
    rw [Finset.sum_const, nsmul_eq_mul, hcard _ _ q (by ring)] at h3
    linarith
  have hUq : ∑ s ∈ Finset.Icc (1 : ℤ) U, C s +
      ∑ s ∈ Finset.Icc ((U : ℤ) + 1) ((U : ℤ) + q), C s ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, C s := by
    rw [← Finset.sum_union]
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hCnn s hs)
      intro x hx
      simp only [Finset.mem_union, Finset.mem_Icc] at hx ⊢
      omega
    · rw [Finset.disjoint_left]; intro x hx hx'; simp only [Finset.mem_Icc] at hx hx'; omega
  have hCsum : ∑ s ∈ Finset.Icc (1 : ℤ) h, C s = ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (Td s)| +
      ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (T s)| + ∑ s ∈ Finset.Icc (1 : ℤ) h, N0 s := by
    simp only [C, Finset.sum_add_distrib]
  have hTnn : 0 ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, |v (T s)| :=
    Finset.sum_nonneg fun s _ => abs_nonneg _
  have hNnn : 0 ≤ ∑ s ∈ Finset.Icc (1 : ℤ) h, N0 s := Finset.sum_nonneg hN
  have hσq : ∑ j ∈ Finset.range q, v (ub j) ≤ q * σ := by
    have h3 := Finset.sum_le_sum (s := Finset.range q) (f := fun j => v (ub j)) (g := fun _ => σ)
      (fun j hj => hub j (Finset.mem_range.1 hj))
    simpa using h3
  have hσp : ∑ i ∈ Finset.range p, v (ua i) ≤ p * σ := by
    have h3 := Finset.sum_le_sum (s := Finset.range p) (f := fun i => v (ua i)) (g := fun _ => σ)
      (fun i hi => hua i (Finset.mem_range.1 hi))
    simpa using h3
  have hε2 : ((a : ℝ) - p) * ε = e * ε + U * ε + q * ε := by
    have ha : a = e + U + q + p := by omega
    rw [ha]
    push_cast
    ring
  have hpq : ((p + q : ℕ) : ℝ) * σ = p * σ + q * σ := by
    push_cast
    ring
  linarith [hvA, I1, I2, I3, I4, ShiftFormula, I5b, Be, BU, Bq, hUq, hσq, hσp, hc0, hc00, hCsum, hTnn, hNnn,
    hε2, hpq]
end Formalism.ValuationGridEstimates
