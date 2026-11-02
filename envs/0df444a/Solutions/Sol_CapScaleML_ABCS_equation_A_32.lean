-- Prove2me | solution 1 for CapScaleML.ABCS.equation_A_32
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T19:10:23.495756+00:00
-- url     : https://prove2.me/submissions/b8d2f2bb-3d28-4ca5-86b2-72e9d0c54a24

import Mathlib
import Definitions.Def_CapScaleML_ABCS_Defs

open MeasureTheory Set
open scoped ENNReal

namespace CapScaleML.ABCS.A32Aux

/-- The "first exit" comparison argument: if `D = D 0 + ∫ k` on `[0,T]`, `D 0 ≤ 0`, and `k ≤ 0`
wherever `D > 0`, then `D ≤ 0` on `[0,T]`. -/
lemma nonpos_of_integral (T : ℝ) (D k : ℝ → ℝ) (hD0 : D 0 ≤ 0)
    (hk : IntervalIntegrable k volume 0 T)
    (hDeq : ∀ t ∈ Icc 0 T, D t = D 0 + ∫ s in (0:ℝ)..t, k s)
    (hneg : ∀ s ∈ Icc 0 T, 0 < D s → k s ≤ 0) : ∀ t ∈ Icc 0 T, D t ≤ 0 := by
  intro t ht
  by_contra hcon
  push_neg at hcon
  have hT : 0 ≤ T := ht.1.trans ht.2
  -- continuity of D on [0,T]
  have hcont : ContinuousOn D (Icc 0 T) := by
    have hI : IntegrableOn k (uIcc 0 T) volume := by
      rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hk
    have hc := (intervalIntegral.continuousOn_primitive_interval hI).const_add (D 0)
    rw [uIcc_of_le hT] at hc
    exact hc.congr (fun x hx => hDeq x hx)
  set S := {u ∈ Icc 0 t | D u ≤ 0} with hS
  have hSsub : S ⊆ Icc 0 T := fun u hu => ⟨hu.1.1, hu.1.2.trans ht.2⟩
  have hScl : IsClosed S := by
    have hc' : ContinuousOn D (Icc 0 t) := hcont.mono (Icc_subset_Icc le_rfl ht.2)
    exact hc'.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨0, ⟨le_rfl, ht.1⟩, hD0⟩
  have hSbdd : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  set s := sSup S
  have hsS : s ∈ S := hScl.csSup_mem hSne hSbdd
  have hst : s < t := by
    rcases lt_or_eq_of_le hsS.1.2 with h | h
    · exact h
    · exfalso; have := hsS.2; rw [h] at this; linarith
  have hpos : ∀ u ∈ Ioc s t, 0 < D u := by
    intro u hu
    by_contra hle; push_neg at hle
    have : u ≤ s := le_csSup hSbdd ⟨⟨by linarith [hsS.1.1, hu.1], hu.2⟩, hle⟩
    linarith [hu.1]
  have hs0 : 0 ≤ s := hsS.1.1
  have hint : ∫ x in s..t, k x ≤ 0 := by
    have hkst : IntervalIntegrable k volume s t := hk.mono_set (by
      rw [uIcc_of_le hst.le, uIcc_of_le hT]; exact Icc_subset_Icc hs0 ht.2)
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (f := k)
      (g := fun _ => (0:ℝ)) hst.le hkst intervalIntegrable_const (fun x hx =>
        hneg x ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩ (hpos x ⟨hx.1, hx.2.le⟩))
    simpa using this
  have h1 := hDeq t ⟨ht.1, ht.2⟩
  have h2 := hDeq s (hSsub hsS)
  have hadd : ∫ x in (0:ℝ)..t, k x = (∫ x in (0:ℝ)..s, k x) + ∫ x in s..t, k x :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hk.mono_set (by rw [uIcc_of_le hs0, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl (hsS.1.2.trans ht.2)))
      (hk.mono_set (by rw [uIcc_of_le hst.le, uIcc_of_le hT]; exact Icc_subset_Icc hs0 ht.2))).symm
  have := hsS.2
  linarith

/-- The workload integrand dominates the net input. -/
lemma integrand_ge (q lam m : ℝ) :
    lam - m ≤ (if 0 < q ∨ m ≤ lam then lam - m else 0) := by
  split_ifs with h
  · exact le_rfl
  · push_neg at h; linarith [h.2]

/-- Workloads are nonnegative. -/
lemma workload_nonneg (T : ℝ) (lam m q : ℝ → ℝ) (hq : IsWorkload T lam m q) :
    ∀ t ∈ Icc 0 T, 0 ≤ q t := by
  obtain ⟨hI, heq⟩ := hq
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hq0 : q 0 = 0 := by rw [heq 0 ⟨le_rfl, hT⟩]; simp
  have := nonpos_of_integral T (fun u => - q u)
    (fun s => -(if 0 < q s ∨ m s ≤ lam s then lam s - m s else 0)) (by simp [hq0]) hI.neg
    (fun u hu => by
      simp only [hq0, neg_zero, zero_add]
      rw [heq u hu, intervalIntegral.integral_neg])
    (fun s _ hs => by
      have hqs : q s < 0 := by linarith
      simp only [neg_nonpos]
      split_ifs with h
      · rcases h with h | h
        · linarith
        · linarith
      · exact le_rfl) t ht
  linarith

lemma workload_cont (T : ℝ) (hT : 0 ≤ T) (lam m q : ℝ → ℝ) (hq : IsWorkload T lam m q) :
    ContinuousOn q (Icc 0 T) := by
  obtain ⟨hI, heq⟩ := hq
  have hI' : IntegrableOn (fun s => if 0 < q s ∨ m s ≤ lam s then lam s - m s else 0)
      (uIcc 0 T) volume := by
    rw [uIcc_of_le hT]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hI
  have hc := intervalIntegral.continuousOn_primitive_interval hI'
  rw [uIcc_of_le hT] at hc
  exact hc.congr (fun x hx => heq x hx)

lemma aemeas_of_contOn (T : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 T)) :
    AEMeasurable (fun s => ENNReal.ofReal (f s)) (volume.restrict (Icc 0 T)) :=
  (hf.aemeasurable measurableSet_Icc).ennreal_ofReal

lemma aemeas_of_ii (T : ℝ) (hT : 0 ≤ T) (f : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 T) :
    AEMeasurable (fun s => ENNReal.ofReal (f s)) (volume.restrict (Icc 0 T)) := by
  have h := ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mp hf).aestronglyMeasurable
  exact h.aemeasurable.ennreal_ofReal

lemma limsup_add_le_ennreal {ι : Type*} (f : Filter ι) (u v : ι → ℝ≥0∞) :
    Filter.limsup (u + v) f ≤ Filter.limsup u f + Filter.limsup v f := by
  refine ENNReal.le_of_forall_pos_le_add (fun ε hε hlt => ?_)
  have hu : Filter.limsup u f ≠ ⊤ := ne_top_of_le_ne_top hlt.ne le_self_add
  have hv : Filter.limsup v f ≠ ⊤ := ne_top_of_le_ne_top hlt.ne le_add_self
  have hε2 : ((ε : ℝ≥0∞) / 2) ≠ 0 := by
    simp [ENNReal.div_eq_top]; exact hε.ne'
  have h1 : Filter.limsup u f < Filter.limsup u f + (ε : ℝ≥0∞) / 2 := ENNReal.lt_add_right hu hε2
  have h2 : Filter.limsup v f < Filter.limsup v f + (ε : ℝ≥0∞) / 2 := ENNReal.lt_add_right hv hε2
  have e1 := Filter.eventually_lt_of_limsup_lt h1
  have e2 := Filter.eventually_lt_of_limsup_lt h2
  have : Filter.limsup (u + v) f ≤
      (Filter.limsup u f + (ε : ℝ≥0∞) / 2) + (Filter.limsup v f + (ε : ℝ≥0∞) / 2) := by
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [e1, e2] with x hx1 hx2
    exact add_le_add hx1.le hx2.le
  calc Filter.limsup (u + v) f ≤ _ := this
    _ = Filter.limsup u f + Filter.limsup v f + ((ε : ℝ≥0∞) / 2 + (ε : ℝ≥0∞) / 2) := by ring
    _ = _ := by rw [ENNReal.add_halves]

lemma switching_add_le (t : ℝ) (m₁ m₂ : ℝ → ℝ) :
    switching t (fun x => m₁ x + m₂ x) ≤ switching t m₁ + switching t m₂ := by
  unfold switching
  calc Filter.limsup (fun δ => switchSum t δ (fun x => m₁ x + m₂ x)) (nhdsWithin 0 (Ioi 0))
      ≤ Filter.limsup ((fun δ => switchSum t δ m₁) + (fun δ => switchSum t δ m₂))
          (nhdsWithin 0 (Ioi 0)) :=
        Filter.limsup_le_limsup (Filter.Eventually.of_forall (fun δ => ?_))
    _ ≤ _ := limsup_add_le_ennreal _ _ _
  show switchSum t δ (fun x => m₁ x + m₂ x) ≤ (switchSum t δ m₁ + switchSum t δ m₂)
  unfold switchSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [show m₁ (min ((i + 1) * δ) t) + m₂ (min ((i + 1) * δ) t) - (m₁ (i * δ) + m₂ (i * δ)) =
      (m₁ (min ((i + 1) * δ) t) - m₁ (i * δ)) + (m₂ (min ((i + 1) * δ) t) - m₂ (i * δ)) by ring]
  exact ENNReal.ofReal_add_le

end CapScaleML.ABCS.A32Aux

open CapScaleML.ABCS CapScaleML.ABCS.A32Aux in
theorem solution (ω β θ T : ℝ) (hω : 0 < ω) (hβ : 0 < β)
    (hθ : 0 ≤ θ) (hT : 0 < T) (lam lamHat m₁ q₁ q₂ q : ℝ → ℝ)
    (hlam : ∀ t ∈ Icc 0 T, 0 ≤ lam t)
    (hlamHat : ∀ t ∈ Icc 0 T, 0 ≤ lamHat t)
    (hlamI : IntervalIntegrable lam volume 0 T)
    (hlamHatI : IntervalIntegrable lamHat volume 0 T)
    (hm₁ : Admissible T m₁) (hq₁ : IsWorkload T lamHat m₁ q₁)
    (hq₂ : IsWorkload T (deltaLam lam lamHat) (apOnline ω β lam lamHat) q₂)
    (hq : IsWorkload T lam (fun t => m₁ t + apOnline ω β lam lamHat t) q) :
    cost ω β θ T (fun t => m₁ t + apOnline ω β lam lamHat t) q ≤
      cost ω β θ T m₁ q₁ + cost ω β θ T (apOnline ω β lam lamHat) q₂ := by
  have hT' : 0 ≤ T := hT.le
  set m₂ := apOnline ω β lam lamHat with hm₂def
  set Δ := deltaLam lam lamHat with hΔdef
  -- Step 1: workload comparison q ≤ q₁ + q₂
  have hq1n := workload_nonneg T lamHat m₁ q₁ hq₁
  have hq2n := workload_nonneg T Δ m₂ q₂ hq₂
  have hcomp : ∀ t ∈ Icc 0 T, q t ≤ q₁ t + q₂ t := by
    have key := nonpos_of_integral T (fun u => q u - (q₁ u + q₂ u))
      (fun s => (if 0 < q s ∨ m₁ s + m₂ s ≤ lam s then lam s - (m₁ s + m₂ s) else 0) -
        ((if 0 < q₁ s ∨ m₁ s ≤ lamHat s then lamHat s - m₁ s else 0) +
         (if 0 < q₂ s ∨ m₂ s ≤ Δ s then Δ s - m₂ s else 0)))
      (by
        rw [hq.2 0 ⟨le_rfl, hT'⟩, hq₁.2 0 ⟨le_rfl, hT'⟩, hq₂.2 0 ⟨le_rfl, hT'⟩]
        simp)
      (hq.1.sub (hq₁.1.add hq₂.1))
      (fun u hu => by
        have e0 : q 0 - (q₁ 0 + q₂ 0) = 0 := by
          rw [hq.2 0 ⟨le_rfl, hT'⟩, hq₁.2 0 ⟨le_rfl, hT'⟩, hq₂.2 0 ⟨le_rfl, hT'⟩]; simp
        rw [e0, zero_add, intervalIntegral.integral_sub
          (hq.1.mono_set (by rw [uIcc_of_le hu.1, uIcc_of_le hT']; exact Icc_subset_Icc le_rfl hu.2))
          ((hq₁.1.add hq₂.1).mono_set (by rw [uIcc_of_le hu.1, uIcc_of_le hT']; exact Icc_subset_Icc le_rfl hu.2)),
          intervalIntegral.integral_add
          (hq₁.1.mono_set (by rw [uIcc_of_le hu.1, uIcc_of_le hT']; exact Icc_subset_Icc le_rfl hu.2))
          (hq₂.1.mono_set (by rw [uIcc_of_le hu.1, uIcc_of_le hT']; exact Icc_subset_Icc le_rfl hu.2)),
          ← hq.2 u hu, ← hq₁.2 u hu, ← hq₂.2 u hu])
      (fun s hs hD => by
        have hqpos : 0 < q s := by linarith [hq1n s hs, hq2n s hs]
        rw [if_pos (Or.inl hqpos)]
        have g1 := integrand_ge (q₁ s) (lamHat s) (m₁ s)
        have g2 := integrand_ge (q₂ s) (Δ s) (m₂ s)
        have hΔ : lam s - lamHat s ≤ Δ s := by
          simp only [hΔdef, deltaLam, if_pos hs.1]; exact le_max_left _ _
        linarith)
    intro t ht
    have := key t ht
    linarith
  -- Step 2: the three cost components
  have hqc := workload_cont T hT' _ _ _ hq₁
  have hq2c := workload_cont T hT' _ _ _ hq₂
  have hpow : ∫⁻ s in Icc 0 T, ENNReal.ofReal (m₁ s + m₂ s) ≤
      (∫⁻ s in Icc 0 T, ENNReal.ofReal (m₁ s)) + ∫⁻ s in Icc 0 T, ENNReal.ofReal (m₂ s) := by
    rw [← lintegral_add_left' (aemeas_of_ii T hT' m₁ hm₁.2.2)]
    refine setLIntegral_mono' measurableSet_Icc (fun s _ => ?_)
    exact ENNReal.ofReal_add_le
  have hsw := switching_add_le T m₁ m₂
  set P₁ := ∫⁻ s in Icc 0 T, ENNReal.ofReal (m₁ s)
  set P₂ := ∫⁻ s in Icc 0 T, ENNReal.ofReal (m₂ s)
  set S₁ := switching T m₁
  set S₂ := switching T m₂
  unfold cost
  rw [← mul_add]
  refine mul_le_mul' le_rfl ?_
  have hAE : AEMeasurable (fun s => ENNReal.ofReal (q₁ s) + ENNReal.ofReal β * S₁ +
      ENNReal.ofReal θ * P₁) (volume.restrict (Icc 0 T)) :=
    ((aemeas_of_contOn T q₁ hqc).add aemeasurable_const).add aemeasurable_const
  rw [← lintegral_add_left' hAE]
  refine setLIntegral_mono' measurableSet_Icc (fun s hs => ?_)
  have h1 : ENNReal.ofReal (q s) ≤ ENNReal.ofReal (q₁ s) + ENNReal.ofReal (q₂ s) :=
    (ENNReal.ofReal_le_ofReal (hcomp s hs)).trans ENNReal.ofReal_add_le
  calc ENNReal.ofReal (q s) + ENNReal.ofReal β * switching T (fun t => m₁ t + m₂ t) +
        ENNReal.ofReal θ * ∫⁻ s in Icc 0 T, ENNReal.ofReal (m₁ s + m₂ s)
      ≤ (ENNReal.ofReal (q₁ s) + ENNReal.ofReal (q₂ s)) + ENNReal.ofReal β * (S₁ + S₂) +
        ENNReal.ofReal θ * (P₁ + P₂) :=
        add_le_add (add_le_add h1 (mul_le_mul' le_rfl hsw)) (mul_le_mul' le_rfl hpow)
    _ = _ := by ring
