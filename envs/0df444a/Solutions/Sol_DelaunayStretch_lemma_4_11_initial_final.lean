-- Prove2me | solution 1 for DelaunayStretch.lemma_4_11_initial_final
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:48:12.438944+00:00
-- url     : https://prove2.me/submissions/dbfab90e-8685-4e59-8f54-05c49b387376
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DelaunayStretch_lemma_4_2_range_of_coordinates
import Definitions.Def_DelaunayStretch_IsNextDisk
import Definitions.Def_DelaunayStretch_SatisfiesH0toH4

open DelaunayStretch

theorem clip_sub_abs (h t : ℝ) (hh : 0 ≤ h) : |clip h t - t| = max (|t| - h) 0 := by
  unfold clip
  rcases le_total t h with h1 | h1 <;> rcases le_total (-h) t with h2 | h2
  · rw [min_eq_right h1, max_eq_right h2, sub_self, abs_zero]
    have : |t| ≤ h := abs_le.mpr ⟨h2, h1⟩
    rw [max_eq_right (by linarith)]
  · rw [min_eq_right h1, max_eq_left h2]
    rw [abs_of_nonpos (by linarith : t ≤ 0), abs_of_nonneg (by linarith : 0 ≤ -h - t)]
    rw [max_eq_left (by linarith)]; ring
  · rw [min_eq_left h1, max_eq_right (by linarith)]
    rw [abs_of_nonneg (by linarith : 0 ≤ t), abs_of_nonpos (by linarith : h - t ≤ 0)]
    rw [max_eq_left (by linarith)]; ring
  · have e1 : h = 0 := by linarith
    have e2 : t = 0 := by linarith
    subst e1; subst e2; simp

theorem abs_clip_le (h t : ℝ) (hh : 0 ≤ h) : |clip h t| ≤ h := by
  unfold clip
  rw [abs_le]; constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem radius_pos_of_mem (O : Disk) (a b : ℂ) (ha : a ∈ O.boundary) (hb : b ∈ O.boundary)
    (hab : a ≠ b) : 0 < O.radius := by
  unfold Disk.boundary at ha hb
  rw [Metric.mem_sphere] at ha hb
  rcases lt_or_ge 0 O.radius with h | h
  · exact h
  · exfalso
    have h1 : dist a O.center = 0 := le_antisymm (ha ▸ h) dist_nonneg
    have h2 : dist b O.center = 0 := le_antisymm (hb ▸ h) dist_nonneg
    rw [dist_eq_zero] at h1 h2
    exact hab (h1.trans h2.symm)

theorem solution (U : ℝ) (H : R4 → ℝ) (h1 : CondH1 H) (h3 : CondH3 U H) :
    (∀ (O₁ O₂ : Disk) (a₁ b₁ : ℂ), IsInitialPair O₁ O₂ a₁ b₁ →
      (⟨O₁, a₁, b₁, initialDiff O₁ a₁ b₁⟩ : GateState).IsGateState ∧
        initialCost O₁ a₁ b₁ - U * initialProgress O₁ a₁ b₁ +
          potential H U ⟨O₁, a₁, b₁, initialDiff O₁ a₁ b₁⟩ ≤ 0) ∧
    (∀ s : GateState, s.IsGateState →
      finalCost s - U * finalProgress s - potential H U s ≤ 0) := by
  obtain ⟨hSig, -, -, hcoord⟩ := lemma_4_2_range_of_coordinates
  constructor
  · intro O₁ O₂ a₁ b₁ hip
    obtain ⟨hint, ha, hb, -⟩ := hip
    have haO : a₁ ∈ O₁.boundary := (show a₁ ∈ O₁.boundary ∩ O₂.boundary by rw [hint]; simp).1
    have hbO : b₁ ∈ O₁.boundary := (show b₁ ∈ O₁.boundary ∩ O₂.boundary by rw [hint]; simp).1
    have hab : a₁ ≠ b₁ := by intro h; rw [h] at ha; linarith
    have hr := radius_pos_of_mem O₁ a₁ b₁ haO hbO hab
    set s : GateState := ⟨O₁, a₁, b₁, initialDiff O₁ a₁ b₁⟩ with hs
    have hgs : s.IsGateState := by
      refine ⟨hr, haO, hbO, ha, hb, ?_⟩
      exact abs_clip_le _ _ dist_nonneg
    refine ⟨hgs, ?_⟩
    obtain ⟨-, -, hα, hβ, -, hwm, -, hcr⟩ := hcoord s hgs
    have hz := hSig s hgs
    -- notation
    set r := O₁.radius
    set γ := s.gammaCoord
    set φ := s.phiCoord
    set θ := s.thetaCoord
    set G := dist a₁ b₁
    have hα' : O₁.upperArcLength O₁.wMinus a₁ = r * (θ + γ - φ) := hα
    have hβ' : O₁.lowerArcLength O₁.wMinus b₁ = r * (θ - γ + φ) := hβ
    set δ := initialDiff O₁ a₁ b₁ with hδ
    have hδ' : δ = clip G (2 * r * (γ - φ)) := by
      rw [hδ, initialDiff, moveNewDiff, hα', hβ']; congr 1; ring
    have hcost : initialCost O₁ a₁ b₁ = (2 * r * θ - max (|2 * r * (γ - φ)| - G) 0) / 2 := by
      rw [initialCost, moveCost, hα', hβ']
      congr 2
      · ring
      · congr 2; ring_nf
    have hprog : initialProgress O₁ a₁ b₁ = (s.crossing.re - O₁.center.re) + r * Real.cos γ := by
      rw [initialProgress, hwm]; simp only [GateState.crossing, s]; ring
    have hpot : potential H U s = r * (Real.pi / 2 - θ - H (γ, φ, θ, s.psiCoord)) +
        U * (s.crossing.re - O₁.center.re) := rfl
    have hψ : s.psiCoord = φ + δ / (2 * r) := rfl
    -- (H1) and (H3)
    have hΩ : (γ, φ, θ) ∈ OmegaSet := hz.1
    have hH1 := h1 γ φ θ hΩ s.psiCoord γ
    have hH3 := (h3 γ φ θ hΩ).1
    have hω : |s.psiCoord - γ| = max (|2 * r * (γ - φ)| - G) 0 / (2 * r) := by
      rw [hψ, hδ', ← clip_sub_abs G _ dist_nonneg]
      rw [show φ + clip G (2 * r * (γ - φ)) / (2 * r) - γ =
          (clip G (2 * r * (γ - φ)) - 2 * r * (γ - φ)) / (2 * r) by field_simp; ring]
      rw [abs_div, abs_of_pos (by linarith : 0 < 2 * r)]
    rw [hcost, hprog, hpot]
    have hle : H (γ, φ, θ, γ) - max (|2 * r * (γ - φ)| - G) 0 / (2 * r) ≤
        H (γ, φ, θ, s.psiCoord) := by
      have := abs_le.mp hH1; rw [hω] at this; linarith [this.1]
    have key : r * (H (γ, φ, θ, γ) - max (|2 * r * (γ - φ)| - G) 0 / (2 * r)) ≤
        r * H (γ, φ, θ, s.psiCoord) := mul_le_mul_of_nonneg_left hle hr.le
    have e : r * (max (|2 * r * (γ - φ)| - G) 0 / (2 * r)) = max (|2 * r * (γ - φ)| - G) 0 / 2 := by
      field_simp
    rw [mul_sub, e] at key
    have k3 : r * (Real.pi / 2 - U * Real.cos γ) ≤ r * H (γ, φ, θ, γ) :=
      mul_le_mul_of_nonneg_left hH3 hr.le
    nlinarith
  · intro s hs
    obtain ⟨hU0, hL0, hα, hβ, -, -, hwp, -⟩ := hcoord s hs
    have hz := hSig s hs
    have hr := hs.1
    set r := s.O.radius
    set γ := s.gammaCoord
    set φ := s.phiCoord
    set θ := s.thetaCoord
    set ψ := s.psiCoord
    have hαe : s.O.upperArcLength s.aG s.O.wPlus = r * (Real.pi + 2 * γ) - r * (θ + γ - φ) := by
      rw [← hU0, ← hα]; unfold Disk.upperArcLength; ring
    have hβe : s.O.lowerArcLength s.bG s.O.wPlus = r * (Real.pi - 2 * γ) - r * (θ - γ + φ) := by
      rw [← hL0, ← hβ]; unfold Disk.lowerArcLength; ring
    have hδ : s.δ = 2 * r * (ψ - φ) := by
      have e : ψ = φ + s.δ / (2 * r) := rfl
      rw [e]; field_simp; ring
    have hκ : finalCost s = r * (Real.pi - θ - |ψ + γ|) := by
      rw [finalCost, hαe, hβe, hδ]
      have e1 : 2 * r * (ψ - φ) / 2 + (r * (Real.pi + 2 * γ) - r * (θ + γ - φ)) =
          r * (Real.pi - θ) + r * (ψ + γ) := by ring
      have e2 : -(2 * r * (ψ - φ)) / 2 + (r * (Real.pi - 2 * γ) - r * (θ - γ + φ)) =
          r * (Real.pi - θ) - r * (ψ + γ) := by ring
      rw [e1, e2]
      rcases le_total 0 (ψ + γ) with h | h
      · rw [abs_of_nonneg h, min_eq_right (by nlinarith)]; ring
      · rw [abs_of_nonpos h, min_eq_left (by nlinarith)]; ring
    have hprog : finalProgress s = (s.O.center.re - s.crossing.re) + r * Real.cos γ := by
      rw [finalProgress, hwp]; ring
    have hpot : potential H U s = r * (Real.pi / 2 - θ - H (γ, φ, θ, ψ)) +
        U * (s.crossing.re - s.O.center.re) := rfl
    have hΩ : (γ, φ, θ) ∈ OmegaSet := hz.1
    have hH1 := h1 γ φ θ hΩ ψ (-γ)
    have hH3 := (h3 γ φ θ hΩ).2
    rw [hκ, hprog, hpot]
    have hle : H (γ, φ, θ, ψ) ≤ H (γ, φ, θ, -γ) + |ψ + γ| := by
      have := abs_le.mp hH1; rw [sub_neg_eq_add] at this; linarith [this.2]
    have k : r * H (γ, φ, θ, ψ) ≤ r * (-(Real.pi / 2) + U * Real.cos γ + |ψ + γ|) :=
      mul_le_mul_of_nonneg_left (by linarith) hr.le
    nlinarith
