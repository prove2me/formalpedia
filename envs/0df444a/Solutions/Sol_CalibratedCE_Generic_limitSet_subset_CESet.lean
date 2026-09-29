-- Prove2me | solution 1 for CalibratedCE.Generic.limitSet_subset_CESet
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:17:44.888312+00:00
-- url     : https://prove2.me/submissions/bbb300a9-6ec9-4542-b5de-c09230bec7e5

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game
import Definitions.Def_CalibratedCE_Shared_Calibration
import Definitions.Def_CalibratedCE_Generic_LimitSet

namespace CalibratedCE.Generic

open Filter Topology

lemma aux_lsc_emp_sum {m n : ℕ} (x : ℕ → Fin m) (y : ℕ → Fin n) (t : ℕ)
    (G : Fin m → Fin n → ℝ) :
    ∑ a, ∑ b, empDist x y t a b * G a b = (∑ s ∈ Finset.range t, G (x s) (y s)) / t := by
  classical
  simp only [empDist, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  have key : ∀ a b, (((Finset.range t).filter (fun s => x s = a ∧ y s = b)).card : ℝ) * G a b
      = ∑ s ∈ Finset.range t, if x s = a ∧ y s = b then G a b else 0 := by
    intro a b
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp_rw [key]
  rw [show (∑ a, ∑ b, ∑ s ∈ Finset.range t, if x s = a ∧ y s = b then G a b else 0)
      = ∑ a, ∑ s ∈ Finset.range t, ∑ b, (if x s = a ∧ y s = b then G a b else 0) from
      Finset.sum_congr rfl (fun a _ => Finset.sum_comm), Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [ite_and]

lemma aux_lsc_main {k l : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (R : (Fin k → ℝ) → Fin l)
    (h : Fin l → Fin k → ℝ) (K : ℝ) (hK : ∀ r j, |h r j| ≤ K)
    (hbr : ∀ s, ∑ j, f s j * h (R (f s)) j ≤ 0) (t : ℕ) :
    ∑ s ∈ Finset.range t, h (R (f s)) (z s) ≤
      K * ∑ j, ∑ p ∈ (Finset.range t).image f,
        |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range t) (t := (Finset.range t).image f)
    (g := f) (fun s hs => Finset.mem_image_of_mem f hs)]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨s₀, hs₀, hfs₀⟩ := Finset.mem_image.mp hp
  have hbr' : ∑ j, p j * h (R p) j ≤ 0 := hfs₀ ▸ hbr s₀
  set F := (Finset.range t).filter (fun s => f s = p) with hF
  have hN : (Shared.N f p t : ℝ) = F.card := rfl
  have hNpos : Shared.N f p t ≠ 0 := by
    unfold Shared.N
    rw [← Nat.pos_iff_ne_zero, Finset.card_pos]
    exact ⟨s₀, Finset.mem_filter.mpr ⟨hs₀, hfs₀⟩⟩
  set M : Fin k → ℝ := fun j =>
    (((Finset.range t).filter (fun s => f s = p ∧ z s = j)).card : ℝ) with hM
  have h1 : ∑ s ∈ F, h (R (f s)) (z s) = ∑ j, M j * h (R p) j := by
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2])]
    rw [← Finset.sum_fiberwise (s := F) (g := z)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
      Finset.sum_const, nsmul_eq_mul, hF, Finset.filter_filter]
  have h2 : ∀ j, |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ)
      = |M j - (Shared.N f p t : ℝ) * p j| := by
    intro j
    have hNr : (Shared.N f p t : ℝ) ≠ 0 := by exact_mod_cast hNpos
    have hNnn : (0:ℝ) ≤ Shared.N f p t := Nat.cast_nonneg _
    rw [Shared.rho, if_neg hNpos, ← abs_of_nonneg hNnn, ← abs_mul, abs_of_nonneg hNnn]
    congr 1
    field_simp
    ring
  rw [h1, Finset.mul_sum]
  simp_rw [h2]
  have h3 : ∑ j, M j * h (R p) j
      = ∑ j, (M j - (Shared.N f p t : ℝ) * p j) * h (R p) j
        + (Shared.N f p t : ℝ) * ∑ j, p j * h (R p) j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h3]
  have h4 : (Shared.N f p t : ℝ) * ∑ j, p j * h (R p) j ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hbr'
  have h5 : ∑ j, (M j - (Shared.N f p t : ℝ) * p j) * h (R p) j
      ≤ ∑ j, K * |M j - (Shared.N f p t : ℝ) * p j| := by
    apply Finset.sum_le_sum
    intro j _
    calc (M j - (Shared.N f p t : ℝ) * p j) * h (R p) j
        ≤ |(M j - (Shared.N f p t : ℝ) * p j) * h (R p) j| := le_abs_self _
      _ = |M j - (Shared.N f p t : ℝ) * p j| * |h (R p) j| := abs_mul _ _
      _ ≤ |M j - (Shared.N f p t : ℝ) * p j| * K :=
          mul_le_mul_of_nonneg_left (hK _ _) (abs_nonneg _)
      _ = K * |M j - (Shared.N f p t : ℝ) * p j| := mul_comm _ _
  linarith

lemma aux_lsc_limit {k l : ℕ} (f : ℕ → Fin k → ℝ) (z : ℕ → Fin k) (R : (Fin k → ℝ) → Fin l)
    (h : Fin l → Fin k → ℝ) (hbr : ∀ s, ∑ j, f s j * h (R (f s)) j ≤ 0)
    (hcal : Shared.Calibrated f z) (w : ℕ → ℝ) (L : ℝ) (hw : Tendsto w atTop (𝓝 L))
    (hweq : ∀ t : ℕ, 0 < t → w t = (∑ s ∈ Finset.range t, h (R (f s)) (z s)) / t) :
    L ≤ 0 := by
  set K : ℝ := ∑ r, ∑ j, |h r j| with hKdef
  have hK : ∀ r j, |h r j| ≤ K := by
    intro r j
    calc |h r j| ≤ ∑ j', |h r j'| :=
          Finset.single_le_sum (f := fun j' => |h r j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ K := Finset.single_le_sum (f := fun r' => ∑ j', |h r' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ r)
  have hlim : Tendsto (fun t => K * ∑ j, Shared.calibScore f z j t) atTop (𝓝 0) := by
    have := (tendsto_finsetSum (Finset.univ : Finset (Fin k))
      fun j _ => hcal j).const_mul K
    simpa using this
  refine le_of_tendsto_of_tendsto hw hlim ?_
  filter_upwards [eventually_ge_atTop 1] with t ht
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [hweq t ht]
  have hcs : K * ∑ j, Shared.calibScore f z j t
      = (K * ∑ j, ∑ p ∈ (Finset.range t).image f,
        |Shared.rho f z p j t - p j| * (Shared.N f p t : ℝ)) / t := by
    simp only [Shared.calibScore, Finset.sum_div, mul_div_assoc]
  rw [hcs]
  exact div_le_div_of_nonneg_right (aux_lsc_main f z R h K hK hbr t) htpos.le

end CalibratedCE.Generic

open CalibratedCE.Generic Filter Topology

theorem solution {m n : ℕ} (u₁ u₂ : Fin m → Fin n → ℝ) :
    LimitSet u₁ u₂ ⊆ CESet u₁ u₂ := by
  rintro D ⟨R₁, R₂, π₁, π₂, hR₁, hR₂, hπ₁, hπ₂, hc₁, hc₂, hD⟩
  have hconv : ∀ G : Fin m → Fin n → ℝ,
      Tendsto (fun t => ∑ a, ∑ b,
        empDist (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t a b * G a b) atTop
        (𝓝 (∑ a, ∑ b, D a b * G a b)) := fun G =>
    tendsto_finsetSum _ fun a _ => tendsto_finsetSum _ fun b _ => (hD a b).mul_const _
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a b
    exact ge_of_tendsto' (hD a b) fun t => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · have h1 := hconv (fun _ _ => 1)
    simp only [mul_one] at h1
    refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop 1] with t ht
    have htpos : (t : ℝ) ≠ 0 := by
      have : (0 : ℝ) < t := by exact_mod_cast ht
      exact this.ne'
    have := aux_lsc_emp_sum (play₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) t (fun _ _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    rw [this, div_self htpos]
  · intro Φ
    have key := aux_lsc_limit (forecast₁ R₁ R₂ π₁ π₂) (play₂ R₁ R₂ π₁ π₂) R₁
      (fun r j => u₁ (Φ r) j - u₁ r j) ?_ hc₁ _ _ (hconv fun a b => u₁ (Φ a) b - u₁ a b)
      (fun t _ => by rw [aux_lsc_emp_sum]; rfl)
    · simp only [mul_sub, Finset.sum_sub_distrib] at key
      linarith
    · intro s
      have := hR₁ (forecast₁ R₁ R₂ π₁ π₂ s) (hπ₁ _) (Φ (R₁ (forecast₁ R₁ R₂ π₁ π₂ s)))
      simp only [mul_sub, Finset.sum_sub_distrib]
      unfold forecast₁ at this ⊢
      linarith
  · intro Φ
    have key := aux_lsc_limit (forecast₂ R₁ R₂ π₁ π₂) (play₁ R₁ R₂ π₁ π₂) R₂
      (fun r a => u₂ a (Φ r) - u₂ a r) ?_ hc₂ _ _ (hconv fun a b => u₂ a (Φ b) - u₂ a b)
      (fun t _ => by rw [aux_lsc_emp_sum]; rfl)
    · simp only [mul_sub, Finset.sum_sub_distrib] at key
      linarith
    · intro s
      have := hR₂ (forecast₂ R₁ R₂ π₁ π₂ s) (hπ₂ _) (Φ (R₂ (forecast₂ R₁ R₂ π₁ π₂ s)))
      simp only [mul_sub, Finset.sum_sub_distrib]
      unfold forecast₂ at this ⊢
      linarith
