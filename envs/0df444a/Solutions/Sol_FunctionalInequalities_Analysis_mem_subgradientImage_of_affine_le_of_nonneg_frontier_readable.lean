-- Prove2me | solution 1 for FunctionalInequalities.Analysis.mem_subgradientImage_of_affine_le_of_nonneg_frontier_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:59.597005+00:00
-- url     : https://prove2.me/submissions/f2c2625b-a692-4e66-aea3-367ca520fda9

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11C2AlexandrovSliding
open Set Metric
open scoped RealInnerProductSpace
/-- **Sliding lemma for the Alexandrov maximum principle** (weak Letwin route, Caffarelli's argument):
if `u` is convex, `u ≥ 0` on the frontier of a bounded open `Ω`, `u x₀ < 0` at some `x₀ ∈ Ω`, and the
affine function `x ↦ u x₀ + ⟪p, x − x₀⟫` is `≤ 0` on `closure Ω`, then `p` is a subgradient of `u` at
some point of `Ω`. In particular, `closedBall 0 (-u x₀ / diam Ω) ⊆ ∂u(Ω)`, and the cone over the ball
with apex in the direction of a nearest boundary point is contained in `∂u(Ω)`. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hfr : ∀ x ∈ frontier Ω, 0 ≤ u x) {x₀ : E} (hx₀ : x₀ ∈ Ω) (hneg : u x₀ < 0)
    {p : E} (hp : ∀ x ∈ closure Ω, u x₀ + ⟪p, x - x₀⟫ ≤ 0) : p ∈ FunctionalInequalities.Analysis.subgradientImage u Ω := by
  have _hneg : u x₀ < 0 := hneg
  let ell : E → ℝ := fun x => u x₀ + ⟪p, x - x₀⟫
  let w : E → ℝ := fun x => u x - ell x
  have hu : Continuous u := by
    exact continuousOn_univ.mp (ConvexOn.continuousOn isOpen_univ hconv)
  have hconst : Continuous (fun _ : E => x₀) := continuous_const
  have hinner : Continuous (fun x : E => ⟪p, x - x₀⟫) := by
    exact
      (continuous_const : Continuous (fun _ : E => p)).inner
        (continuous_id.sub hconst)
  have hell_cont : Continuous ell := by
    change Continuous (fun x : E => u x₀ + ⟪p, x - x₀⟫)
    have h :=
      (continuous_const : Continuous (fun _ : E => u x₀)).add hinner
    exact h.congr (fun x => rfl)
  have hw : Continuous w := by
    change Continuous (fun x : E => u x - ell x)
    exact (hu.sub hell_cont).congr (fun x => rfl)
  have hcomp : IsCompact (closure Ω) := hb.isCompact_closure
  have hne : (closure Ω).Nonempty := ⟨x₀, subset_closure hx₀⟩
  obtain ⟨x₁, hx₁, hmin₁⟩ :=
    hcomp.exists_isMinOn hne hw.continuousOn
  have hw₀ : w x₀ = 0 := by
    simp [w, ell]
  have hle₁ : w x₁ ≤ 0 := by
    calc
      w x₁ ≤ w x₀ := hmin₁ (subset_closure hx₀)
      _ = 0 := hw₀
  have hfront : ∀ x ∈ frontier Ω, 0 ≤ w x := by
    intro x hx
    change 0 ≤ u x - ell x
    exact
      sub_nonneg.mpr
        (le_trans
          (by simpa [ell] using hp x (frontier_subset_closure hx))
          (hfr x hx))
  have hex : ∃ x₂ ∈ Ω, IsMinOn w (closure Ω) x₂ := by
    by_cases h₁fr : x₁ ∈ frontier Ω
    · have hw₁ : w x₁ = 0 := le_antisymm hle₁ (hfront x₁ h₁fr)
      have hmin₀ : IsMinOn w (closure Ω) x₀ := by
        intro z hz
        calc
          w x₀ = w x₁ := hw₀.trans hw₁.symm
          _ ≤ w z := hmin₁ hz
      exact ⟨x₀, hx₀, hmin₀⟩
    · have hx₁union : x₁ ∈ Ω ∪ frontier Ω := by
        rw [← closure_eq_self_union_frontier]
        exact hx₁
      exact ⟨x₁, hx₁union.resolve_right h₁fr, hmin₁⟩
  obtain ⟨x₂, hx₂, hmin₂⟩ := hex
  refine ⟨x₂, hx₂, ?_⟩
  intro y
  have htouch (z : E) :
      ell z + w x₂ = u x₂ + ⟪p, z - x₂⟫ := by
    have hi :
        ⟪p, z - x₀⟫ - ⟪p, x₂ - x₀⟫ = ⟪p, z - x₂⟫ := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      ring
    dsimp [w, ell]
    calc
      (u x₀ + ⟪p, z - x₀⟫) +
          (u x₂ - (u x₀ + ⟪p, x₂ - x₀⟫)) =
          u x₂ + (⟪p, z - x₀⟫ - ⟪p, x₂ - x₀⟫) := by ring
      _ = u x₂ + ⟪p, z - x₂⟫ := by rw [hi]
  have hwle : w x₂ ≤ w y := by
    by_contra hnot
    have hlt : w y < w x₂ := lt_of_not_ge hnot
    have hy : y ≠ x₂ := by
      intro hxy
      subst y
      exact (lt_irrefl _ hlt)
    have hdn : 0 < ‖y - x₂‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨ε, hε, hball⟩ :=
      Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx₂)
    set t : ℝ := min (1 / 2) (ε / (2 * ‖y - x₂‖)) with ht
    have htpos : 0 < t := by
      rw [ht]
      exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hdn))
    have htle : t ≤ 1 / 2 := by
      rw [ht]
      exact min_le_left _ _
    have htleone : t ≤ 1 := by
      linarith
    have htdiv : t ≤ ε / (2 * ‖y - x₂‖) := by
      rw [ht]
      exact min_le_right _ _
    have hcone : t * ‖y - x₂‖ < ε := by
      have hmul :=
        mul_le_mul_of_nonneg_right htdiv (le_of_lt hdn)
      calc
        t * ‖y - x₂‖ ≤ (ε / (2 * ‖y - x₂‖)) * ‖y - x₂‖ := hmul
        _ = ε / 2 := by field_simp [ne_of_gt hdn]
        _ < ε := by linarith
    let z : E := (1 - t) • x₂ + t • y
    have hzsub : z - x₂ = t • (y - x₂) := by
      dsimp [z]
      module
    have hzball : z ∈ ball x₂ ε := by
      rw [mem_ball, dist_eq_norm]
      rw [hzsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact hcone
    have hzΩ : z ∈ Ω := hball hzball
    have hzcl : z ∈ closure Ω := subset_closure hzΩ
    have hconv' :
        ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
          u (a • x₂ + b • y) ≤ a • u x₂ + b • u y :=
      hconv.2 (mem_univ x₂) (mem_univ y)
    have huv' :
        u ((1 - t) • x₂ + t • y) ≤
          (1 - t) • u x₂ + t • u y :=
      hconv' (a := 1 - t) (b := t)
        (sub_nonneg.mpr htleone) (le_of_lt htpos) (by ring)
    have huv : u z ≤ (1 - t) * u x₂ + t * u y := by
      dsimp [z]
      simpa only [smul_eq_mul] using huv'
    have hzlin :
        z - x₀ = (1 - t) • (x₂ - x₀) + t • (y - x₀) := by
      dsimp [z]
      module
    have hell :
        ell z = (1 - t) * ell x₂ + t * ell y := by
      dsimp [ell]
      rw [hzlin, inner_add_right, inner_smul_right, inner_smul_right]
      ring
    have hwz : w z ≤ (1 - t) * w x₂ + t * w y := by
      calc
        w z = u z - ell z := rfl
        _ ≤ ((1 - t) * u x₂ + t * u y) - ell z :=
          sub_le_sub_right huv _
        _ = (1 - t) * w x₂ + t * w y := by
          rw [hell]
          dsimp [w]
          ring
    have hminz : w x₂ ≤ w z := hmin₂ hzcl
    have hmul : t * w x₂ ≤ t * w y := by
      nlinarith [hminz, hwz]
    have hltmul : t * w y < t * w x₂ :=
      (mul_lt_mul_of_pos_left hlt htpos)
    exact (not_lt_of_ge hmul) hltmul
  calc
    u x₂ + ⟪p, y - x₂⟫ = ell y + w x₂ := (htouch y).symm
    _ ≤ ell y + w y := by linarith
    _ = u y := by
      dsimp [w]
      ring
