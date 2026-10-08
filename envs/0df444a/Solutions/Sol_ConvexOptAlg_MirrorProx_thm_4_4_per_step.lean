-- Prove2me | solution 1 for ConvexOptAlg.MirrorProx.thm_4_4_per_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T00:58:52.923989+00:00
-- url     : https://prove2.me/submissions/a77e2c15-4dee-4acb-99ba-b167486c88a4

import Mathlib
import Definitions.Def_ConvexOptAlg_MirrorProx_Defs

set_option autoImplicit false

namespace P3dd31818

open ConvexOptAlg.MirrorProx

lemma proj_foc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X D : Set E) (hXconv : Convex ℝ X) (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ)
    (hΦ : IsMirrorMap D Φ Φ') (y z : E) (hp : IsBregmanProj X D Φ Φ' y z)
    (w : E) (hw : w ∈ X ∩ D) : 0 ≤ (Φ' z - Φ' y) (w - z) := by
  obtain ⟨hz, hmin⟩ := hp
  have hconv : Convex ℝ (X ∩ D) := hXconv.inter hΦ.2.1
  have hder : HasFDerivAt (fun v => bregman Φ Φ' v y) (Φ' z - Φ' y) z := by
    unfold bregman
    have h1 := hΦ.2.2.2.1 z hz.2
    have heq : (fun v => Φ' y (v - y)) = fun v => Φ' y v - Φ' y y := by
      funext v; simp [map_sub]
    have h2 : HasFDerivAt (fun v => Φ' y (v - y)) (Φ' y) z := by
      rw [heq]; exact (Φ' y).hasFDerivAt.sub_const _
    exact (h1.sub_const (Φ y)).sub h2
  have hloc : IsLocalMinOn (fun v => bregman Φ Φ' v y) (X ∩ D) z :=
    IsMinOn.localize (fun v hv => hmin v hv)
  exact hloc.hasFDerivWithinAt_nonneg hder.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset (hconv.segment_subset hz hw))

lemma conv_grad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (g : E →L[ℝ] ℝ) (hf : ConvexOn ℝ X f) (c u : E)
    (hc : c ∈ X) (hu : u ∈ X) (hd : HasFDerivWithinAt f g X c) :
    f c - f u ≤ g (c - u) := by
  set L : ℝ → E := fun s => c + s • (u - c) with hLdef
  have hL : HasDerivWithinAt L (u - c) (Set.Icc 0 1) 0 := by
    have := ((hasDerivAt_id' (0:ℝ)).smul_const (u - c)).const_add c
    convert this.hasDerivWithinAt using 1
    simp
  have hmaps : Set.MapsTo L (Set.Icc 0 1) X := by
    intro s hs
    exact hf.1.add_smul_sub_mem hc hu hs
  have hL0 : L 0 = c := by simp [L]
  have hcomp : HasDerivWithinAt (f ∘ L) (g (u - c)) (Set.Icc 0 1) 0 := by
    have hd' : HasFDerivWithinAt f g X (L 0) := by rw [hL0]; exact hd
    exact hd'.comp_hasDerivWithinAt 0 hL hmaps
  set φ : ℝ → ℝ := fun s => f c + s * (f u - f c) - f (L s) with hφdef
  have hφ : HasDerivWithinAt φ ((f u - f c) - g (u - c)) (Set.Icc 0 1) 0 := by
    have h1 : HasDerivWithinAt (fun s : ℝ => f c + s * (f u - f c)) (f u - f c)
        (Set.Icc 0 1) 0 := by
      have := ((hasDerivAt_id' (0:ℝ)).mul_const (f u - f c)).const_add (f c)
      simpa using this.hasDerivWithinAt
    exact h1.sub hcomp
  have hmin : IsLocalMinOn φ (Set.Icc 0 1) 0 := by
    apply IsMinOn.localize
    intro s hs
    simp only [Set.mem_setOf_eq]
    have hconv := hf.2 hc hu (by linarith [hs.2] : (0:ℝ) ≤ 1 - s) hs.1 (by ring)
    have hLs : L s = (1 - s) • c + s • u := by
      simp only [L]; module
    have h0 : φ 0 = 0 := by simp [φ, hL0]
    rw [h0]
    simp only [φ, hLs]
    simp only [smul_eq_mul] at hconv
    nlinarith [hconv]
  have hpos : (1:ℝ) ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    rw [zero_add, segment_eq_Icc zero_le_one]
  have := hmin.hasFDerivWithinAt_nonneg hφ.hasFDerivWithinAt hpos
  simp at this
  rw [map_sub]
  linarith

end P3dd31818

open ConvexOptAlg.MirrorProx in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X D : Set E) (hXc : IsCompact X) (hXconv : Convex ℝ X) (hXD : X ⊆ closure D)
    (hXDne : (X ∩ D).Nonempty)
    (Φ : E → ℝ) (Φ' : E → E →L[ℝ] ℝ) (hΦ : IsMirrorMap D Φ Φ')
    (ρ : ℝ) (hρ : 0 < ρ) (hsc : IsStronglyConvexWRT (X ∩ D) Φ Φ' ρ)
    (f : E → ℝ) (f' : E → E →L[ℝ] ℝ) (hf : ConvexOn ℝ X f)
    (β : ℝ) (hβ : 0 < β) (hsm : IsSmoothWRT X f f' β)
    (x y y' x' : ℕ → E) (hrun : IsMirrorProxRun X D Φ Φ' f' (ρ / β) x y y' x')
    (t : ℕ) (ht : 1 ≤ t) (u : E) (hu : u ∈ X ∩ D) :
    f (y (t + 1)) - f u
      ≤ (bregman Φ Φ' u (x t) - bregman Φ Φ' u (x (t + 1))) / (ρ / β) := by
  have hη : 0 < ρ / β := div_pos hρ hβ
  have hηβ : ρ / β * β = ρ := by field_simp
  obtain ⟨-, hy'eq, hpy, -, hx'eq, hpx⟩ := hrun.2 t ht
  have ha : x t ∈ X ∩ D := by
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; exact hrun.1
    · exact ((hrun.2 k hk).2.2.2.2.2).1
  have hb : x (t+1) ∈ X ∩ D := hpx.1
  have hc : y (t+1) ∈ X ∩ D := hpy.1
  have hA := P3dd31818.conv_grad X f (f' (y (t+1))) hf (y (t+1)) u hc.1 hu.1 (hsm.1 _ hc.1)
  have hB := P3dd31818.proj_foc X D hXconv Φ Φ' hΦ _ _ hpx u hu
  have hC := P3dd31818.proj_foc X D hXconv Φ Φ' hΦ _ _ hpy (x (t+1)) hb
  rw [hx'eq] at hB
  rw [hy'eq] at hC
  have hD : (f' (y (t+1)) - f' (x t)) (y (t+1) - x (t+1))
      ≤ β * ‖y (t+1) - x t‖ * ‖y (t+1) - x (t+1)‖ := by
    calc _ ≤ ‖f' (y (t+1)) - f' (x t)‖ * ‖y (t+1) - x (t+1)‖ :=
          le_trans (le_abs_self _) ((f' (y (t+1)) - f' (x t)).le_opNorm _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hsm.2 _ hc.1 _ ha.1) (norm_nonneg _)
  have hE1 := hsc _ ha _ hc
  have hE2 := hsc _ hc _ hb
  have hn : ‖y (t+1) - x t‖ = ‖x t - y (t+1)‖ := norm_sub_rev _ _
  have hAM : ρ * (‖y (t+1) - x t‖ * ‖y (t+1) - x (t+1)‖)
      ≤ ρ / 2 * ‖x t - y (t+1)‖ ^ 2 + ρ / 2 * ‖y (t+1) - x (t+1)‖ ^ 2 := by
    rw [← hn]
    nlinarith [sq_nonneg (‖y (t+1) - x t‖ - ‖y (t+1) - x (t+1)‖)]
  have hD' : ρ / β * (f' (y (t+1)) - f' (x t)) (y (t+1) - x (t+1))
      ≤ ρ * (‖y (t+1) - x t‖ * ‖y (t+1) - x (t+1)‖) := by
    calc _ ≤ ρ / β * (β * ‖y (t+1) - x t‖ * ‖y (t+1) - x (t+1)‖) :=
          mul_le_mul_of_nonneg_left hD hη.le
      _ = _ := by
          rw [show ρ / β * (β * ‖y (t+1) - x t‖ * ‖y (t+1) - x (t+1)‖)
              = (ρ / β * β) * (‖y (t+1) - x t‖ * ‖y (t+1) - x (t+1)‖) by ring, hηβ]
  have hA' : ρ / β * (f (y (t+1)) - f u) ≤ ρ / β * f' (y (t+1)) (y (t+1) - u) :=
    mul_le_mul_of_nonneg_left hA hη.le
  rw [le_div_iff₀ hη]
  unfold bregman
  simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul] at hA' hB hC hD' hE1 hE2 ⊢
  generalize ρ / β = η at *
  linarith
