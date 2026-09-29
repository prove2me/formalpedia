-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8d93c2cd-9256-5d5f-901d-072b0334d18a

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero

set_option autoImplicit false

open IsLocalRing

theorem solution
    (W : Type) [CommRing W] [IsDomain W] (π : W) (hπ : π ≠ 0)
    (f u v : MvPowerSeries (Fin 2) W) (hv : IsUnit v) (hf : MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) f = 0)
    (e : ℕ) (g g₁ r : MvPowerSeries (Fin 2) W)
    (hg : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e → MvPowerSeries.coeff n g = 0)
    (hg₁ : ∀ n : Fin 2 →₀ ℕ, n 0 + n 1 < e + 1 → MvPowerSeries.coeff n g₁ = 0)
    (hrel : g = g₁ + (MvPowerSeries.C π * v - f * u) * r)
    (n : Fin 2 →₀ ℕ) (hn : n 0 + n 1 = e) :
    MvPowerSeries.coeff n g ∈ Ideal.span {π} := by
  classical

  let P : ℕ → MvPowerSeries (Fin 2) W → Prop := fun d a => ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 < d → MvPowerSeries.coeff m a = 0
  have hmul : ∀ d d' (a b : MvPowerSeries (Fin 2) W), P d a → P d' b → P (d + d') (a * b) := by
    intro d d' a b ha hb m hm
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have h0 : p.1 0 + p.2 0 = m 0 := by rw [← Finsupp.add_apply, hp]
    have h1 : p.1 1 + p.2 1 = m 1 := by rw [← Finsupp.add_apply, hp]
    by_cases hlt : p.1 0 + p.1 1 < d
    · rw [ha p.1 hlt, zero_mul]
    · have : p.2 0 + p.2 1 < d' := by omega
      rw [hb p.2 this, mul_zero]
  have hP0 : ∀ a : MvPowerSeries (Fin 2) W, P 0 a := fun a m hm => by omega
  have hPf : P 1 f := by
    intro m hm
    have : m = 0 := by
      ext j; fin_cases j <;> simp <;> omega
    rw [this]; exact hf
  have hmulL : ∀ d (a b : MvPowerSeries (Fin 2) W), P d b → P d (a * b) := by
    intro d a b hb
    have := hmul 0 d a b (hP0 a) hb
    rwa [zero_add] at this
  have hmul1 : ∀ d (b : MvPowerSeries (Fin 2) W), P d b → P (d + 1) (f * b) := by
    intro d b hb
    have := hmul 1 d f b hPf hb
    rwa [add_comm] at this

  obtain ⟨vU, rfl⟩ := hv
  set s : MvPowerSeries (Fin 2) W := (vU : MvPowerSeries (Fin 2) W) * r with hs
  have hr : r = ((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) * s := by
    rw [hs, ← mul_assoc, Units.inv_mul, one_mul]

  have hcoef : ∀ m : Fin 2 →₀ ℕ, MvPowerSeries.coeff m g =
      MvPowerSeries.coeff m g₁ + (π * MvPowerSeries.coeff m s -
        MvPowerSeries.coeff m (f * (u * (((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) * s)))) := by
    intro m
    rw [hrel, map_add, sub_mul, map_sub, mul_assoc, MvPowerSeries.coeff_C_mul, ← hs, mul_assoc, ← hr]

  have hPs : ∀ d, d ≤ e → P d s := by
    intro d
    induction d with
    | zero => intro _; exact hP0 s
    | succ d ih =>
      intro hd m hm
      have ih' := ih (by omega)
      rcases Nat.lt_or_ge (m 0 + m 1) d with hlt | hge
      · exact ih' m hlt
      · have hdeg : m 0 + m 1 = d := by omega

        have hfur : MvPowerSeries.coeff m (f * (u * (((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) * s))) = 0 := by
          have h1 : P d (u * (((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) * s)) :=
            hmulL d u _ (hmulL d _ s ih')
          exact hmul1 d _ h1 m (by omega)
        have h := hcoef m
        rw [hg m (by omega), hg₁ m (by omega), hfur, sub_zero, zero_add] at h
        have : π * MvPowerSeries.coeff m s = 0 := h.symm
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hπ
        · exact h0

  have hfur : MvPowerSeries.coeff n (f * (u * (((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) * s))) = 0 := by
    have h1 : P e (u * (((vU⁻¹ : (MvPowerSeries (Fin 2) W)ˣ) : MvPowerSeries (Fin 2) W) * s)) :=
      hmulL e u _ (hmulL e _ s (hPs e le_rfl))
    exact hmul1 e _ h1 n (by omega)
  rw [hcoef n, hg₁ n (by omega), hfur, sub_zero, zero_add]
  exact Ideal.mem_span_singleton.mpr (dvd_mul_right π _)

end S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_coeff_mem_span_of_eq_add_rel_mul_of_forall_coeff_eq_zero (solution)
