-- Prove2me | solution 1 for DirS.asym_sid_graphon
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:54:54.910525+00:00
-- url     : https://prove2.me/submissions/e14189db-0264-48dd-99f2-2b1a3d9775b1

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw
open DirS

theorem g73t_limit (a t : ℝ) (e : ℕ) (d h : ℕ → ℝ) (hd0 : ∀ k, 0 ≤ d k)
    (hd : ∀ k : ℕ, 0 < k → a - 1 / (k : ℝ) ≤ d k) (hle : ∀ k, 0 < k → d k ^ e ≤ h k)
    (hh : ∀ k : ℕ, 0 < k → h k ≤ t + e * (1 / (k : ℝ))) (ha : 0 ≤ a) : a ^ e ≤ t := by
  have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hg : Filter.Tendsto (fun k : ℕ => (max (a - 1 / (k : ℝ)) 0) ^ e) Filter.atTop
      (nhds ((max (a - 0) 0) ^ e)) :=
    ((tendsto_const_nhds.sub h0).max tendsto_const_nhds).pow e
  have hH : Filter.Tendsto (fun k : ℕ => t + e * (1 / (k : ℝ))) Filter.atTop
      (nhds (t + e * 0)) := tendsto_const_nhds.add (tendsto_const_nhds.mul h0)
  rw [sub_zero, max_eq_left ha] at hg
  rw [mul_zero, add_zero] at hH
  refine le_of_tendsto_of_tendsto hg hH ?_
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  have hk' : 0 < k := hk
  calc (max (a - 1 / (k : ℝ)) 0) ^ e ≤ d k ^ e :=
        pow_le_pow_left₀ (le_max_right _ _) (max_le (hd k hk') (hd0 k)) e
    _ ≤ h k := hle k hk'
    _ ≤ _ := hh k hk'

theorem g73t_dirDens_nonneg {n : ℕ} (G : OriGraph n) : 0 ≤ G.dirDens := by
  unfold OriGraph.dirDens; positivity

theorem g73t_bipDens_nonneg {m n : ℕ} (G : BipGraph m n) : 0 ≤ G.bipDens := by
  unfold BipGraph.bipDens; positivity

theorem g73t_abs_le {d μ : ℝ} {k : ℕ} (hd : 0 ≤ d) (h : |d - μ| ≤ 1 / (k : ℝ)) :
    |μ| - 1 / (k : ℝ) ≤ d := by
  have := abs_sub_abs_le_abs_sub μ d
  rw [abs_sub_comm] at h
  rw [abs_of_nonneg hd] at this
  linarith

theorem solution {mA nA : ℕ} (A : BipGraph mA nA) (_w : GraphWorld) :
    AsymSidorenko A ↔ AsymSidW A := by
  constructor
  · intro h dg
    rw [Real.rpow_natCast]
    refine g73t_limit _ _ A.bipEdgeCount (fun k => (_w.approxB k dg).2.bipDens)
      (fun k => A.bipHomDens (_w.approxB k dg).2) (fun k => g73t_bipDens_nonneg _)
      (fun k hk => g73t_abs_le (g73t_bipDens_nonneg _) (_w.approxB_mean dg k hk))
      (fun k _ => by
        have := h _ _ (_w.approxB k dg).2
        rwa [Real.rpow_natCast] at this)
      (fun k hk => by
        have := _w.approxB_t dg mA nA A k hk
        have h2 := (abs_le.mp this).2
        rw [mul_one_div]
        linarith) (abs_nonneg _)
  · intro h m n G
    have h' := h (_w.graphonOfBip m n G)
    rwa [_w.wof_bip, _w.wof_bip_mean, abs_of_nonneg (g73t_bipDens_nonneg G)] at h'
