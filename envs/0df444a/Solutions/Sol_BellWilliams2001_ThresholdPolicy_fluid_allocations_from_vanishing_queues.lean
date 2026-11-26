-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.fluid_allocations_from_vanishing_queues
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:30:35.699319+00:00
-- url     : https://prove2.me/submissions/ad7dbff3-58c8-4af5-9a10-cf7d62748016

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_primitive_fluid_limits_in_prob
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_allocation_balance_bound

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology Set
open scoped ENNReal

private theorem clock_range {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (n : ℕ) (T : Allocation Ω) (hA : M.IsAdmissible n T) (ω : Ω) (j : Fin 3)
    (s : ℝ) (hs : 0 ≤ s) : 0 ≤ M.Tbar n T ω s j ∧ M.Tbar n T ω s j ≤ s := by
  let R := M.r n^2
  have hR : 0 < R := pow_pos (zero_lt_one.trans_le (M.r_ge n)) _
  have h0 : (0:ℝ) ∈ Ici (0:ℝ) := mem_Ici.mpr le_rfl
  have hu : R*s ∈ Ici (0:ℝ) := mul_nonneg hR.le hs
  have hNon (i : Fin 3) : 0 ≤ T ω i (R*s) := by
    have h := hA.alloc_mono ω i h0 hu hu
    rwa [hA.alloc_zero] at h
  refine ⟨div_nonneg (hNon j) hR.le, ?_⟩
  change T ω j (R*s) / R ≤ s
  rw [div_le_iff₀ hR, mul_comm s]
  have h0 := hA.idle_mono ω 0 h0 hu hu
  have h1 := hA.idle_mono ω 1 (show (0:ℝ) ∈ Ici 0 from mem_Ici.mpr le_rfl) hu hu
  rw [hA.idle_zero] at h0 h1
  simp only [SystemSequence.idle,if_true, show (1:Fin 2) ≠ 0 by decide,if_false] at h0 h1
  fin_cases j <;> simp at *
  · linarith
  · linarith [hNon 2]
  · linarith [hNon 1]

private theorem point_of_supDist {m : ℕ} {f g : ℝ → Fin m → ℝ} {H e s : ℝ} (he : 0 < e)
    (hs : s ∈ Icc 0 H) (h : supDist f g H < ENNReal.ofReal e) (i : Fin m) :
    |f s i - g s i| ≤ e := by
  have hsum : |f s i - g s i| ≤ ∑ j, |f s j-g s j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (f s j-g s j)) (Finset.mem_univ i)
  have h₁ : ENNReal.ofReal (∑ j,|f s j-g s j|) ≤ supDist f g H :=
    le_iSup_of_le s (le_iSup_of_le hs le_rfl)
  exact ((ENNReal.ofReal_lt_ofReal_iff he).1 ((ENNReal.ofReal_le_ofReal hsum).trans_lt (h₁.trans_lt h))).le

set_option maxHeartbeats 1500000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (T : ℕ → Allocation Ω)
    (hT : ∀ᶠ n in atTop, M.IsAdmissible (φ n) (T n))
    (hq : UocInProb M.P (fun n ω t => M.Qbar (φ n) (T n) ω t) (fun _ => 0)) :
    UocInProb M.P (fun n ω t => M.Tbar (φ n) (T n) ω t) M.fluidAllocation ∧
    UocInProb M.P (fun n ω t => M.Ibar (φ n) (T n) ω t) (fun _ => 0) := by
  obtain ⟨hA,hS⟩ := primitive_fluid_limits_in_prob M
  obtain ⟨C,hC,hBal⟩ := fluid_allocation_balance_bound M
  have hBoth (H : ℝ) (hH : 0 ≤ H) (ε : ℝ) (hε : 0 < ε) :
      let E₁ (n : ℕ) : Set Ω := {ω | ENNReal.ofReal ε ≤
        supDist (M.Tbar (φ n) (T n) ω) M.fluidAllocation H}
      let E₂ (n : ℕ) : Set Ω := {ω | ENNReal.ofReal ε ≤
        supDist (M.Ibar (φ n) (T n) ω) (fun _ => 0) H}
      Tendsto (fun n => M.P (E₁ n)) atTop (𝓝 0) ∧ Tendsto (fun n => M.P (E₂ n)) atTop (𝓝 0) := by
    intro E₁ E₂
    let δ := ε/(2*C)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδs : C*δ < ε := by
      have heq : C*δ = ε/2 := by dsimp [δ]; field_simp
      rw [heq]
      linarith
    let EA (n : ℕ) : Set Ω := {ω | ENNReal.ofReal δ ≤
      supDist (M.Abar (φ n) ω) (fun t k => M.lam k*t) H}
    let ES (n : ℕ) : Set Ω := {ω | ENNReal.ofReal δ ≤
      supDist (M.Sbar (φ n) ω) (fun t j => M.mu j*t) H}
    let EQ (n : ℕ) : Set Ω := {ω | ENNReal.ofReal δ ≤
      supDist (M.Qbar (φ n) (T n) ω) (fun _ => 0) H}
    have hTa : Tendsto (fun n => M.P (EA n)) atTop (𝓝 0) := (hA H hH δ hδ).comp hφ
    have hTs : Tendsto (fun n => M.P (ES n)) atTop (𝓝 0) := (hS H hH δ hδ).comp hφ
    have hTq : Tendsto (fun n => M.P (EQ n)) atTop (𝓝 0) := hq H hH δ hδ
    have hsum : Tendsto (fun n => M.P (EA n) + M.P (ES n) + M.P (EQ n)) atTop (𝓝 0) := by
      simpa using (hTa.add hTs).add hTq
    have hMass : ∀ᶠ n in atTop,
        M.P (E₁ n) ≤ M.P (EA n)+M.P (ES n)+M.P (EQ n) ∧
        M.P (E₂ n) ≤ M.P (EA n)+M.P (ES n)+M.P (EQ n) := by
      filter_upwards [hT] with n hn
      let E := (EA n ∪ ES n) ∪ EQ n
      have hUnion : M.P E ≤ M.P (EA n)+M.P (ES n)+M.P (EQ n) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      have hg (ω : Ω) (hω : ω ∉ E) : ω ∉ E₁ n ∧ ω ∉ E₂ n := by
        have h1 : supDist (M.Abar (φ n) ω) (fun t k => M.lam k*t) H < ENNReal.ofReal δ :=
          lt_of_not_ge (fun h => hω (Or.inl (Or.inl h)))
        have h2 : supDist (M.Sbar (φ n) ω) (fun t j => M.mu j*t) H < ENNReal.ofReal δ :=
          lt_of_not_ge (fun h => hω (Or.inl (Or.inr h)))
        have h3 : supDist (M.Qbar (φ n) (T n) ω) (fun _ => 0) H < ENNReal.ofReal δ :=
          lt_of_not_ge (fun h => hω (Or.inr h))
        have hb (s : ℝ) (hs : s ∈ Icc 0 H) := hBal (φ n) (T n) hn ω s δ hs.1 hδ.le
          (point_of_supDist hδ hs h1)
          (fun j => by
            have hclock := clock_range M (φ n) (T n) hn ω j s hs.1
            exact point_of_supDist hδ ⟨hclock.1,hclock.2.trans hs.2⟩ h2 j)
          (fun k => by simpa using point_of_supDist hδ hs h3 k)
        have hB₁ : supDist (M.Tbar (φ n) (T n) ω) M.fluidAllocation H ≤ ENNReal.ofReal (C*δ) := by
          refine iSup_le fun s => iSup_le fun hs => ENNReal.ofReal_le_ofReal ?_
          exact (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans (hb s hs)
        have hB₂ : supDist (M.Ibar (φ n) (T n) ω) (fun _ => 0) H ≤ ENNReal.ofReal (C*δ) := by
          refine iSup_le fun s => iSup_le fun hs => ENNReal.ofReal_le_ofReal ?_
          simp only [Pi.zero_apply,sub_zero]
          exact (le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).trans (hb s hs)
        have hLT := (ENNReal.ofReal_lt_ofReal_iff hε).2 hδs
        exact ⟨(hB₁.trans_lt hLT).not_ge,(hB₂.trans_lt hLT).not_ge⟩
      exact ⟨(measure_mono (fun ω hw => by by_contra hh; exact (hg ω hh).1 hw)).trans hUnion,
        (measure_mono (fun ω hw => by by_contra hh; exact (hg ω hh).2 hw)).trans hUnion⟩
    exact ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall (fun _ => bot_le)) (hMass.mono (fun _ hn => hn.1)),
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
        (Eventually.of_forall (fun _ => bot_le)) (hMass.mono (fun _ hn => hn.2))⟩
  exact ⟨fun H hH e he => (hBoth H hH e he).1,fun H hH e he => (hBoth H hH e he).2⟩
