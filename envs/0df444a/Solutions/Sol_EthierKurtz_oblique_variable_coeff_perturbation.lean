-- Prove2me | solution 1 for EthierKurtz.oblique_variable_coeff_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-29T22:24:10.708167+00:00
-- url     : https://prove2.me/submissions/ae34addd-aa61-4358-b698-eafd3d69a64d

import Mathlib

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory Real Set Filter
open scoped Topology

namespace ObliqueLib
/-- Euclidean space of dimension `d`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

section ModelDef

variable {d : ℕ}

/-- Half-space model: on `{⟪x, e⟫ ≥ 0}` the resolvent `(lam - Δ/2) u = h` with the oblique condition
`Du · (b - e) = 0` on `⟪x, e⟫ = 0`, with all Schauder bounds (`C` independent of `lam`, `h`). -/
def HalfModel (d : ℕ) (μ : ℝ) : Prop :=
  ∀ e b : Eu d, ‖e‖ = 1 → inner ℝ b e = 0 → ∃ C : ℝ, 0 ≤ C ∧
  ∀ lam : ℝ, 0 < lam → ∀ h : Eu d → ℝ,
    (∃ Hh : ℝ, ∀ y z : Eu d, 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
    (∃ M0 : ℝ, ∀ y : Eu d, 0 ≤ inner ℝ y e → |h y| ≤ M0) →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x : Eu d, 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          = h x) ∧
      (∀ x : Eu d, inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      ∀ M0 Hh : ℝ, 0 ≤ M0 → 0 ≤ Hh → (∀ y : Eu d, 0 ≤ inner ℝ y e → |h y| ≤ M0) →
        (∀ y z : Eu d, 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
      (∀ x : Eu d, 0 ≤ inner ℝ x e → ∀ v w : Eu d,
        |u x| ≤ C * M0 * (1 / lam) ∧
        |u1 x v| ≤ C * M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖ ∧
        |u2 x v w| ≤ C * Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : Eu d,
        |u x - u x'| ≤ C * M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)

end ModelDef

noncomputable local instance instL2NO (d : ℕ) : NormedAddCommGroup (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance instL2SO (d : ℕ) : NormedSpace ℝ (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section Series

variable {d : ℕ}

/-- `f` is bounded by `M` and `μ`-Hölder with constant `H` on `X`. -/
def HB (X : Set (Eu d)) (μ M H : ℝ) (f : Eu d → ℝ) : Prop :=
  0 ≤ M ∧ 0 ≤ H ∧ (∀ x ∈ X, |f x| ≤ M) ∧ ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ H * ‖x - y‖ ^ μ

lemma tsum_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : ℕ → E} {c q N : ℝ}
    (hc : 0 ≤ c) (hq0 : 0 ≤ q) (hq1 : q < 1) (hN : 0 ≤ N) (hf : ∀ k, ‖f k‖ ≤ c * (q ^ k * N)) :
    Summable f ∧ ‖∑' k, f k‖ ≤ c * N / (1 - q) := by
  have hg : Summable (fun k : ℕ => c * (q ^ k * N)) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_right N).mul_left c
  have hn : Summable (fun k => ‖f k‖) := hg.of_nonneg_of_le (fun k => norm_nonneg _) hf
  refine ⟨hn.of_norm, ?_⟩
  calc ‖∑' k, f k‖ ≤ ∑' k, ‖f k‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' k, c * (q ^ k * N) := hn.tsum_le_tsum hf hg
    _ = c * N / (1 - q) := by
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]; ring

lemma tsum_telescope {f : ℕ → ℝ} (hf : Summable f) : ∑' k, (f k - f (k + 1)) = f 0 := by
  have h1 : Summable (fun k => f (k + 1)) := (summable_nat_add_iff 1).mpr hf
  rw [hf.tsum_sub h1, hf.tsum_eq_zero_add]; ring

theorem series_solve {X Xo Bd : Set (Eu d)} (hXo : IsOpen Xo) (hXoX : Xo ⊆ X) (hBd : Bd ⊆ X)
    {μ w q lam : ℝ} (hw : 0 < w) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (cf : Eu d → Eu d) (p1 : Eu d → (Eu d →L[ℝ] ℝ) →L[ℝ] ℝ)
    (p2 : Eu d → (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ)
    (R0 : (Eu d → ℝ) → Eu d → ℝ) (R1 : (Eu d → ℝ) → Eu d → Eu d →L[ℝ] ℝ)
    (R2 : (Eu d → ℝ) → Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ)
    {c0 c1 c2 c3 c4 c5 : ℝ} (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3)
    (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5)
    (hR : ∀ (g : Eu d → ℝ) (M H : ℝ), HB X μ M H g →
      (∀ x ∈ Xo, HasFDerivAt (R0 g) (R1 g x) x ∧ HasFDerivAt (R1 g) (R2 g x) x) ∧
      (∀ x ∈ Bd, R1 g x (cf x) = 0) ∧
      (∀ x ∈ X, |R0 g x| ≤ c0 * (w * M + H) ∧ ‖R1 g x‖ ≤ c1 * (w * M + H) ∧
        ‖R2 g x‖ ≤ c2 * (w * M + H)) ∧
      (∀ x ∈ X, ∀ x' ∈ X, |R0 g x - R0 g x'| ≤ c3 * (w * M + H) * ‖x - x'‖ ^ μ ∧
        ‖R1 g x - R1 g x'‖ ≤ c4 * (w * M + H) * ‖x - x'‖ ^ μ ∧
        ‖R2 g x - R2 g x'‖ ≤ c5 * (w * M + H) * ‖x - x'‖ ^ μ) ∧
      ∃ M' H' : ℝ, HB X μ M' H'
          (fun x => g x - (lam * R0 g x - p1 x (R1 g x) - p2 x (R2 g x))) ∧
        w * M' + H' ≤ q * (w * M + H))
    {g : Eu d → ℝ} {M H : ℝ} (hg : HB X μ M H g) :
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x ∈ Xo, HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x ∈ Bd, u1 x (cf x) = 0) ∧
      (∀ x ∈ X, lam * u x - p1 x (u1 x) - p2 x (u2 x) = g x) ∧
      (∀ x ∈ X, |u x| ≤ c0 * (w * M + H) / (1 - q) ∧ ‖u1 x‖ ≤ c1 * (w * M + H) / (1 - q) ∧
        ‖u2 x‖ ≤ c2 * (w * M + H) / (1 - q)) ∧
      (∀ x ∈ X, ∀ x' ∈ X, |u x - u x'| ≤ c3 * ‖x - x'‖ ^ μ * (w * M + H) / (1 - q) ∧
        ‖u1 x - u1 x'‖ ≤ c4 * ‖x - x'‖ ^ μ * (w * M + H) / (1 - q) ∧
        ‖u2 x - u2 x'‖ ≤ c5 * ‖x - x'‖ ^ μ * (w * M + H) / (1 - q)) := by
  obtain ⟨gs, hgs0, hgs1⟩ : ∃ gs : ℕ → Eu d → ℝ, gs 0 = g ∧ ∀ k x, gs (k + 1) x =
      gs k x - (lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) :=
    ⟨fun k => Nat.rec g (fun _ f x => f x - (lam * R0 f x - p1 x (R1 f x) - p2 x (R2 f x))) k,
      rfl, fun _ _ => rfl⟩
  have hN0p : 0 ≤ w * M + H := by have := hg.1; have := hg.2.1; positivity
  have claim : ∀ k : ℕ, ∃ Mk Hk : ℝ, HB X μ Mk Hk (gs k) ∧ w * Mk + Hk ≤ q ^ k * (w * M + H) := by
    intro k
    induction k with
    | zero => exact ⟨M, H, hgs0 ▸ hg, by simp⟩
    | succ k ih =>
      obtain ⟨Mk, Hk, hk, hkN⟩ := ih
      obtain ⟨M', H', h1, h2⟩ := (hR _ Mk Hk hk).2.2.2.2
      refine ⟨M', H', ?_, ?_⟩
      · have : gs (k + 1) = fun x =>
            gs k x - (lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) := funext (hgs1 k)
        rw [this]; exact h1
      · calc w * M' + H' ≤ q * (w * Mk + Hk) := h2
          _ ≤ q * (q ^ k * (w * M + H)) := mul_le_mul_of_nonneg_left hkN hq0
          _ = q ^ (k + 1) * (w * M + H) := by ring
  choose Mk Hk hk hkN using claim
  have hRk := fun k => hR (gs k) (Mk k) (Hk k) (hk k)
  have hcN : ∀ {c : ℝ}, 0 ≤ c → ∀ k, c * (w * Mk k + Hk k) ≤ c * (q ^ k * (w * M + H)) :=
    fun hc k => mul_le_mul_of_nonneg_left (hkN k) hc
  have hcNt : ∀ {c t : ℝ}, 0 ≤ c → 0 ≤ t → ∀ k,
      c * (w * Mk k + Hk k) * t ≤ (c * t) * (q ^ k * (w * M + H)) := fun {c t} hc ht k => by
    calc c * (w * Mk k + Hk k) * t = (c * t) * (w * Mk k + Hk k) := by ring
      _ ≤ (c * t) * (q ^ k * (w * M + H)) := mul_le_mul_of_nonneg_left (hkN k) (mul_nonneg hc ht)
  have S0 : ∀ x ∈ X, Summable (fun k => R0 (gs k) x) ∧
      ‖∑' k, R0 (gs k) x‖ ≤ c0 * (w * M + H) / (1 - q) :=
    fun x hx => tsum_bound hc0 hq0 hq1 hN0p fun k => by
      rw [Real.norm_eq_abs]; exact ((hRk k).2.2.1 x hx).1.trans (hcN hc0 k)
  have S1 : ∀ x ∈ X, Summable (fun k => R1 (gs k) x) ∧
      ‖∑' k, R1 (gs k) x‖ ≤ c1 * (w * M + H) / (1 - q) :=
    fun x hx => tsum_bound hc1 hq0 hq1 hN0p fun k => ((hRk k).2.2.1 x hx).2.1.trans (hcN hc1 k)
  have S2 : ∀ x ∈ X, Summable (fun k => R2 (gs k) x) ∧
      ‖∑' k, R2 (gs k) x‖ ≤ c2 * (w * M + H) / (1 - q) :=
    fun x hx => tsum_bound hc2 hq0 hq1 hN0p fun k => ((hRk k).2.2.1 x hx).2.2.trans (hcN hc2 k)
  have hgeo : ∀ {c : ℝ}, Summable (fun k : ℕ => c * (q ^ k * (w * M + H))) := fun {c} =>
    ((summable_geometric_of_lt_one hq0 hq1).mul_right _).mul_left c
  refine ⟨fun x => ∑' k, R0 (gs k) x, fun x => ∑' k, R1 (gs k) x, fun x => ∑' k, R2 (gs k) x,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hXo x hx
    have hbX : Metric.ball x r ⊆ X := hball.trans hXoX
    have hpc : IsPreconnected (Metric.ball x r) := (convex_ball x r).isPreconnected
    have hx0 : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    exact ⟨hasFDerivAt_tsum_of_isPreconnected hgeo Metric.isOpen_ball hpc
        (fun k y hy => ((hRk k).1 y (hball hy)).1)
        (fun k y hy => ((hRk k).2.2.1 y (hbX hy)).2.1.trans (hcN hc1 k)) hx0 (S0 x (hXoX hx)).1 hx0,
      hasFDerivAt_tsum_of_isPreconnected hgeo Metric.isOpen_ball hpc
        (fun k y hy => ((hRk k).1 y (hball hy)).2)
        (fun k y hy => ((hRk k).2.2.1 y (hbX hy)).2.2.trans (hcN hc2 k)) hx0 (S1 x (hXoX hx)).1 hx0⟩
  · intro x hx
    have hm := (ContinuousLinearMap.apply ℝ ℝ (cf x)).map_tsum (S1 x (hBd hx)).1
    simp only [ContinuousLinearMap.apply_apply] at hm
    show (∑' k, R1 (gs k) x) (cf x) = 0
    have h0 : ∀ k, R1 (gs k) x (cf x) = 0 := fun k => (hRk k).2.1 x hx
    rw [hm]; simp only [h0, tsum_zero]
  · intro x hx
    have e1 := (S0 x hx).1
    have e2 := (S1 x hx).1
    have e3 := (S2 x hx).1
    have hs1 : Summable (fun k => p1 x (R1 (gs k) x)) := e2.mapL (p1 x)
    have hs2 : Summable (fun k => p2 x (R2 (gs k) x)) := e3.mapL (p2 x)
    have hgsum : Summable (fun k => gs k x) := (tsum_bound (c := 1 / w) (by positivity) hq0 hq1 hN0p
      fun k => by
        rw [Real.norm_eq_abs]
        refine ((hk k).2.2.1 x hx).trans ?_
        rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hw]
        have := (hk k).2.1; have := hkN k; linarith).1
    have hsplit : ∑' k, (lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) =
        lam * ∑' k, R0 (gs k) x - ∑' k, p1 x (R1 (gs k) x) - ∑' k, p2 x (R2 (gs k) x) := by
      rw [((e1.mul_left lam).sub hs1).tsum_sub hs2, (e1.mul_left lam).tsum_sub hs1, tsum_mul_left]
    have htel : (fun k => lam * R0 (gs k) x - p1 x (R1 (gs k) x) - p2 x (R2 (gs k) x)) =
        fun k => gs k x - gs (k + 1) x := funext fun k => by rw [hgs1]; ring
    show lam * (∑' k, R0 (gs k) x) - p1 x (∑' k, R1 (gs k) x) - p2 x (∑' k, R2 (gs k) x) = g x
    rw [(p1 x).map_tsum e2, (p2 x).map_tsum e3, ← hsplit, htel, tsum_telescope hgsum, hgs0]
  · intro x hx
    exact ⟨by rw [← Real.norm_eq_abs]; exact (S0 x hx).2, (S1 x hx).2, (S2 x hx).2⟩
  · intro x hx x' hx'
    have ht : 0 ≤ ‖x - x'‖ ^ μ := by positivity
    refine ⟨?_, ?_, ?_⟩
    · have hb := tsum_bound (f := fun k => R0 (gs k) x - R0 (gs k) x') (mul_nonneg hc3 ht) hq0 hq1
        hN0p fun k => by
          rw [Real.norm_eq_abs]; exact ((hRk k).2.2.2.1 x hx x' hx').1.trans (hcNt hc3 ht k)
      show |(∑' k, R0 (gs k) x) - ∑' k, R0 (gs k) x'| ≤ _
      rw [← (S0 x hx).1.tsum_sub (S0 x' hx').1, ← Real.norm_eq_abs]; exact hb.2
    · have hb := tsum_bound (f := fun k => R1 (gs k) x - R1 (gs k) x') (mul_nonneg hc4 ht) hq0 hq1
        hN0p fun k => ((hRk k).2.2.2.1 x hx x' hx').2.1.trans (hcNt hc4 ht k)
      show ‖(∑' k, R1 (gs k) x) - ∑' k, R1 (gs k) x'‖ ≤ _
      rw [← (S1 x hx).1.tsum_sub (S1 x' hx').1]; exact hb.2
    · have hb := tsum_bound (f := fun k => R2 (gs k) x - R2 (gs k) x') (mul_nonneg hc5 ht) hq0 hq1
        hN0p fun k => ((hRk k).2.2.2.1 x hx x' hx').2.2.trans (hcNt hc5 ht k)
      show ‖(∑' k, R2 (gs k) x) - ∑' k, R2 (gs k) x'‖ ≤ _
      rw [← (S2 x hx).1.tsum_sub (S2 x' hx').1]; exact hb.2

end Series

section VarM

variable {d : ℕ}

/-- Variable-coefficient half-space solvability with Schauder bounds. -/
def VarModel (d : ℕ) (μ : ℝ) : Prop :=
  ∀ e b : Eu d, ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
  ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
  ∀ (α : Eu d → Fin d → Fin d → ℝ) (β : Eu d → Fin d → ℝ),
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
    (∀ x : Eu d, 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
    (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
      ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
    ∀ (g : Eu d → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : Eu d, 0 ≤ inner ℝ y e → |g y| ≤ M) →
    (∀ y z : Eu d, 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
    ∃ (u : Eu d → ℝ) (u1 : Eu d → Eu d →L[ℝ] ℝ) (u2 : Eu d → Eu d →L[ℝ] Eu d →L[ℝ] ℝ),
      (∀ x : Eu d, 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e →
        lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
          - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
          - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
      (∀ x : Eu d, inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
      (∀ x : Eu d, 0 ≤ inner ℝ x e → ∀ v w : Eu d,
        |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
        |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
        |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
      (∀ x x' : Eu d, 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : Eu d,
        |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
        |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
        |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)

/-- evaluation of a bilinear form at `(v, w)` as a continuous linear functional. -/
noncomputable def evB (v w : Eu d) : (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ (Eu d →L[ℝ] ℝ) v)

lemma evB_apply (v w : Eu d) (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) : evB v w B = B v w := rfl

noncomputable def pLv (β : Eu d → Fin d → ℝ) (x : Eu d) : (Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ∑ i, β x i • ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))

noncomputable def pBv (α : Eu d → Fin d → Fin d → ℝ) (x : Eu d) :
    (Eu d →L[ℝ] Eu d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • ∑ i, evB (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i 1) +
    ∑ i, ∑ j, α x i j • evB (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j 1)

lemma pLv_apply (β : Eu d → Fin d → ℝ) (x : Eu d) (L : Eu d →L[ℝ] ℝ) :
    pLv β x L = ∑ i, β x i * L (EuclideanSpace.single i 1) := by
  simp [pLv, ContinuousLinearMap.sum_apply]

lemma pBv_apply (α : Eu d → Fin d → Fin d → ℝ) (x : Eu d) (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) :
    pBv α x B = (1 / 2 : ℝ) * ∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) +
      ∑ i, ∑ j, α x i j * B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  simp [pBv, ContinuousLinearMap.sum_apply, evB_apply]

lemma opn1 {L : Eu d →L[ℝ] ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ v, |L v| ≤ c * ‖v‖) : ‖L‖ ≤ c :=
  L.opNorm_le_bound hc fun v => by rw [Real.norm_eq_abs]; exact h v

lemma opn2 {B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ} {c : ℝ} (hc : 0 ≤ c) (h : ∀ v w, |B v w| ≤ c * ‖v‖ * ‖w‖) :
    ‖B‖ ≤ c :=
  B.opNorm_le_bound₂ hc fun v w => by rw [Real.norm_eq_abs]; exact h v w

lemma abs_app1' (L : Eu d →L[ℝ] ℝ) (v : Eu d) : |L v| ≤ ‖L‖ * ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact L.le_opNorm v

lemma abs_app2' (B : Eu d →L[ℝ] Eu d →L[ℝ] ℝ) (v w : Eu d) : |B v w| ≤ ‖B‖ * ‖v‖ * ‖w‖ := by
  rw [← Real.norm_eq_abs]; exact B.le_opNorm₂ v w

lemma norm_single1 (i : Fin d) : ‖(EuclideanSpace.single i (1 : ℝ) : Eu d)‖ = 1 := by
  rw [EuclideanSpace.norm_single, norm_one]

lemma ssum_le {a b : Fin d → ℝ} {A B : ℝ} (hA : ∑ i, |a i| ≤ A) (hb : ∀ i, |b i| ≤ B) (hB : 0 ≤ B) :
    |∑ i, a i * b i| ≤ A * B := by
  calc |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| * B := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb i) (abs_nonneg _)
    _ = (∑ i, |a i|) * B := by rw [Finset.sum_mul]
    _ ≤ A * B := mul_le_mul_of_nonneg_right hA hB

lemma dsum_le {a b : Fin d → Fin d → ℝ} {A B : ℝ} (hA : ∑ i, ∑ j, |a i j| ≤ A)
    (hb : ∀ i j, |b i j| ≤ B) (hB : 0 ≤ B) : |∑ i, ∑ j, a i j * b i j| ≤ A * B := by
  calc |∑ i, ∑ j, a i j * b i j| ≤ ∑ i, |∑ j, a i j * b i j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (∑ j, |a i j|) * B := Finset.sum_le_sum fun i _ => by
        calc |∑ j, a i j * b i j| ≤ ∑ j, |a i j * b i j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j, |a i j| * B := Finset.sum_le_sum fun j _ => by
              rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb i j) (abs_nonneg _)
          _ = (∑ j, |a i j|) * B := by rw [Finset.sum_mul]
    _ = (∑ i, ∑ j, |a i j|) * B := by rw [Finset.sum_mul]
    _ ≤ A * B := mul_le_mul_of_nonneg_right hA hB

lemma ssum_hol {a a' b b' : Fin d → ℝ} {A A' B1 B2 : ℝ} (hA : ∑ i, |a i| ≤ A)
    (hA' : ∑ i, |a i - a' i| ≤ A') (hb1 : ∀ i, |b i - b' i| ≤ B1) (hb2 : ∀ i, |b' i| ≤ B2)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) : |∑ i, a i * b i - ∑ i, a' i * b' i| ≤ A * B1 + A' * B2 := by
  have e : ∑ i, a i * b i - ∑ i, a' i * b' i = ∑ i, a i * (b i - b' i) + ∑ i, (a i - a' i) * b' i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (ssum_le hA hb1 hB1) (ssum_le hA' hb2 hB2))

lemma dsum_hol {a a' b b' : Fin d → Fin d → ℝ} {A A' B1 B2 : ℝ} (hA : ∑ i, ∑ j, |a i j| ≤ A)
    (hA' : ∑ i, ∑ j, |a i j - a' i j| ≤ A') (hb1 : ∀ i j, |b i j - b' i j| ≤ B1)
    (hb2 : ∀ i j, |b' i j| ≤ B2) (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) :
    |∑ i, ∑ j, a i j * b i j - ∑ i, ∑ j, a' i j * b' i j| ≤ A * B1 + A' * B2 := by
  have e : ∑ i, ∑ j, a i j * b i j - ∑ i, ∑ j, a' i j * b' i j =
      ∑ i, ∑ j, a i j * (b i j - b' i j) + ∑ i, ∑ j, (a i j - a' i j) * b' i j := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  exact (abs_add_le _ _).trans (add_le_add (dsum_le hA hb1 hB1) (dsum_le hA' hb2 hB2))

set_option maxHeartbeats 3000000 in
theorem varModel {μ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hHM : HalfModel d μ) : VarModel d μ := by
  intro e b he hb
  obtain ⟨C, hC, hsol⟩ := hHM e b he hb
  refine ⟨1 / (8 * (C + 1)), by positivity, fun K hK => ?_⟩
  refine ⟨max 1 ((6 * K * C + 1) ^ (2 / μ)), 2 * C, le_max_left _ _, by positivity, ?_⟩
  intro lam hlam α β hα hαH hβ hβH g M H hM hH hgM hgH
  have hlam1 : 1 ≤ lam := (le_max_left _ _).trans hlam
  have hlam0 : 0 < lam := by linarith
  -- exponent bookkeeping: ℓ = 1/lam, s = ℓ^(1/2), E = ℓ^(μ/2), w = lam^(μ/2)
  have hℓ0 : 0 < 1 / lam := by positivity
  have hℓ1 : 1 / lam ≤ 1 := by rw [div_le_one hlam0]; exact hlam1
  have hwE : lam ^ (μ / 2) * (1 / lam) ^ (μ / 2) = 1 := by
    rw [← mul_rpow hlam0.le hℓ0.le, mul_one_div_cancel hlam0.ne', one_rpow]
  have hw1 : 1 ≤ lam ^ (μ / 2) := one_le_rpow hlam1 (by linarith)
  have hE0 : 0 < (1 / lam) ^ (μ / 2) := rpow_pos_of_pos hℓ0 _
  have hs0 : 0 < (1 / lam) ^ (1 / 2 : ℝ) := rpow_pos_of_pos hℓ0 _
  have hℓs : 1 / lam ≤ (1 / lam) ^ (1 / 2 : ℝ) := by
    calc 1 / lam = (1 / lam) ^ (1 : ℝ) := (rpow_one _).symm
      _ ≤ (1 / lam) ^ (1 / 2 : ℝ) := rpow_le_rpow_of_exponent_ge hℓ0 hℓ1 (by norm_num)
  have hsE : (1 / lam) ^ (1 / 2 : ℝ) ≤ (1 / lam) ^ (μ / 2) :=
    rpow_le_rpow_of_exponent_ge hℓ0 hℓ1 (by linarith)
  have hF5 : (1 / lam) ^ ((1 - μ) / 2) * (1 / lam) ^ (μ / 2) = (1 / lam) ^ (1 / 2 : ℝ) := by
    rw [← rpow_add hℓ0]; congr 1; ring
  have hF6 : (1 / lam) ^ (1 - μ / 2) * (1 / lam) ^ (μ / 2) = 1 / lam := by
    rw [← rpow_add hℓ0, show 1 - μ / 2 + μ / 2 = (1 : ℝ) by ring, rpow_one]
  have hF8 : (1 / lam) ^ ((1 - μ) / 2) = lam ^ (μ / 2) * (1 / lam) ^ (1 / 2 : ℝ) := by
    rw [← hF5]
    calc (1 / lam) ^ ((1 - μ) / 2) = (1 / lam) ^ ((1 - μ) / 2) * (lam ^ (μ / 2) * (1 / lam) ^ (μ / 2)) := by
          rw [hwE, mul_one]
      _ = _ := by ring
  have hw6 : 6 * K * C + 1 ≤ lam ^ (μ / 2) := by
    have h1 : (6 * K * C + 1) ^ (2 / μ) ≤ lam := (le_max_right _ _).trans hlam
    have h2 := rpow_le_rpow (by positivity) h1 (by linarith : (0 : ℝ) ≤ μ / 2)
    rwa [← rpow_mul (by positivity), show 2 / μ * (μ / 2) = (1 : ℝ) by field_simp, rpow_one] at h2
  have hKCE : K * C * (1 / lam) ^ (μ / 2) ≤ 1 / 6 := by
    have := mul_le_mul_of_nonneg_right hw6 hE0.le
    rw [hwE] at this
    linarith [hE0]
  have hδC : 1 / (8 * (C + 1)) * C ≤ 1 / 8 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set ℓ := 1 / lam with hℓdef
  set s := ℓ ^ (1 / 2 : ℝ) with hsdef
  set E := ℓ ^ (μ / 2) with hEdef
  set w := lam ^ (μ / 2) with hwdef
  set δ := 1 / (8 * (C + 1)) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  -- the selected half-space solution operator
  choose! R0 R1 R2 hR using hsol lam hlam0
  have hXo : IsOpen {x : Eu d | 0 < inner ℝ x e} := isOpen_lt continuous_const (by fun_prop)
  have hXoX : {x : Eu d | 0 < inner ℝ x e} ⊆ {x : Eu d | 0 ≤ inner ℝ x e} := fun x hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢; exact hx.le
  have hBdX : {x : Eu d | inner ℝ x e = 0} ⊆ {x : Eu d | 0 ≤ inner ℝ x e} := fun x hx => by
    simp only [Set.mem_setOf_eq] at hx ⊢; rw [hx]
  have hgHB : HB {x : Eu d | 0 ≤ inner ℝ x e} μ M H g := ⟨hM, hH, hgM, fun y hy z hz => hgH y z hy hz⟩
  have hsr := series_solve hXo hXoX hBdX (μ := μ) (w := w) (q := 1 / 2) (lam := lam)
    (by positivity) (by norm_num) (by norm_num) (fun _ => b - e) (pLv β) (pBv α) R0 R1 R2
    (c0 := C * ℓ * E) (c1 := C * s * E) (c2 := C * E) (c3 := C * ℓ) (c4 := C * s) (c5 := C)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hC ?hR hgHB
  -- the hypothesis of `series_solve`
  case hR =>
    intro g' M' H' hg'
    obtain ⟨hM', hH', hgs, hgh⟩ := hg'
    obtain ⟨hdR, heqR, hbcR, hbnd⟩ :=
      hR g' ⟨H', fun y z hy hz => hgh y hy z hz⟩ ⟨M', hgs⟩
    have hb := hbnd M' H' hM' hH' hgs (fun y z hy hz => hgh y hy z hz)
    have hN : 0 ≤ w * M' + H' := by positivity
    have hMN : M' ≤ E * (w * M' + H') := by
      have : M' = E * (w * M') := by rw [← mul_assoc, mul_comm E w, hwE, one_mul]
      linarith [mul_nonneg hE0.le hH']
    have hHN : H' ≤ w * M' + H' := by linarith [mul_nonneg (by positivity : (0 : ℝ) ≤ w) hM']
    have hCM : C * M' ≤ C * (E * (w * M' + H')) := mul_le_mul_of_nonneg_left hMN hC
    have hCH : C * H' ≤ C * (w * M' + H') := mul_le_mul_of_nonneg_left hHN hC
    refine ⟨hdR, hbcR, fun x hx => ?_, fun x hx x' hx' => ?_, ?_⟩
    · obtain ⟨b0, -, -⟩ := hb.1 x hx 0 0
      refine ⟨?_, ?_, ?_⟩
      · refine b0.trans ?_
        linarith [mul_le_mul_of_nonneg_right hCM hℓ0.le]
      · refine opn1 (by positivity) fun v => ((hb.1 x hx v 0).2.1).trans ?_
        linarith [mul_le_mul_of_nonneg_right hCM (by positivity : 0 ≤ s * ‖v‖)]
      · refine opn2 (by positivity) fun v w' => ((hb.1 x hx v w').2.2).trans ?_
        linarith [mul_le_mul_of_nonneg_right hCH (by positivity : 0 ≤ E * ‖v‖ * ‖w'‖)]
    · have ht : 0 ≤ ‖x - x'‖ ^ μ := by positivity
      obtain ⟨b0, -, -⟩ := hb.2 x x' hx hx' 0 0
      refine ⟨?_, ?_, ?_⟩
      · refine b0.trans ?_
        have h1 : C * M' * ℓ ^ (1 - μ / 2) ≤ C * (w * M' + H') * ℓ := by
          calc C * M' * ℓ ^ (1 - μ / 2) ≤ C * (E * (w * M' + H')) * ℓ ^ (1 - μ / 2) :=
                mul_le_mul_of_nonneg_right hCM (by positivity)
            _ = C * (w * M' + H') * (ℓ ^ (1 - μ / 2) * E) := by ring
            _ = C * (w * M' + H') * ℓ := by rw [hF6]
        linarith [mul_le_mul_of_nonneg_right h1 ht]
      · refine opn1 (by positivity) fun v => ?_
        rw [ContinuousLinearMap.sub_apply]
        refine ((hb.2 x x' hx hx' v 0).2.1).trans ?_
        have h1 : C * M' * ℓ ^ ((1 - μ) / 2) ≤ C * (w * M' + H') * s := by
          calc C * M' * ℓ ^ ((1 - μ) / 2) ≤ C * (E * (w * M' + H')) * ℓ ^ ((1 - μ) / 2) :=
                mul_le_mul_of_nonneg_right hCM (by positivity)
            _ = C * (w * M' + H') * (ℓ ^ ((1 - μ) / 2) * E) := by ring
            _ = C * (w * M' + H') * s := by rw [hF5]
        linarith [mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ ‖x - x'‖ ^ μ * ‖v‖)]
      · refine opn2 (by positivity) fun v w' => ?_
        rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply]
        refine ((hb.2 x x' hx hx' v w').2.2).trans ?_
        linarith [mul_le_mul_of_nonneg_right hCH (by positivity : 0 ≤ ‖x - x'‖ ^ μ * ‖v‖ * ‖w'‖)]
    -- residual: on the half-space it is Σ α R2 + Σ β R1
    · have hres : ∀ x, 0 ≤ inner ℝ x e →
          g' x - (lam * R0 g' x - pLv β x (R1 g' x) - pBv α x (R2 g' x)) =
          ∑ i, ∑ j, α x i j * R2 g' x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, β x i * R1 g' x (EuclideanSpace.single i 1) := by
        intro x hx
        have h1 := heqR x hx
        rw [pLv_apply, pBv_apply]
        linarith
      have b2s : ∀ x, 0 ≤ inner ℝ x e → ∀ i j : Fin d,
          |R2 g' x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ C * H' * E := by
        intro x hx i j
        have := (hb.1 x hx (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).2.2
        rwa [norm_single1, norm_single1, mul_one, mul_one] at this
      have b1s : ∀ x, 0 ≤ inner ℝ x e → ∀ i : Fin d,
          |R1 g' x (EuclideanSpace.single i 1)| ≤ C * M' * s := by
        intro x hx i
        have := (hb.1 x hx (EuclideanSpace.single i 1) 0).2.1
        rwa [norm_single1, mul_one] at this
      refine ⟨δ * (C * H' * E) + K * (C * M' * s),
        δ * (C * H') + K * (C * H' * E) +
          (K * (C * M' * ℓ ^ ((1 - μ) / 2)) + K * (C * M' * s)), ⟨by positivity, by positivity, ?_, ?_⟩, ?_⟩
      · intro x hx
        beta_reduce
        rw [hres x hx]
        exact (abs_add_le _ _).trans (add_le_add
          (dsum_le (hα x hx) (b2s x hx) (by positivity)) (ssum_le (hβ x hx) (b1s x hx) (by positivity)))
      · intro x hx x' hx'
        beta_reduce
        rw [hres x hx, hres x' hx']
        have ht : 0 ≤ ‖x - x'‖ ^ μ := by positivity
        have h2d : ∀ i j : Fin d, |R2 g' x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
            R2 g' x' (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ C * H' * ‖x - x'‖ ^ μ := by
          intro i j
          have := (hb.2 x x' hx hx' (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).2.2
          rwa [norm_single1, norm_single1, mul_one, mul_one] at this
        have h1d : ∀ i : Fin d, |R1 g' x (EuclideanSpace.single i 1) - R1 g' x' (EuclideanSpace.single i 1)|
            ≤ C * M' * ℓ ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ := by
          intro i
          have := (hb.2 x x' hx hx' (EuclideanSpace.single i 1) 0).2.1
          rwa [norm_single1, mul_one] at this
        have hA := dsum_hol (hα x hx) (hαH x x' hx hx') h2d (b2s x' hx') (by positivity) (by positivity)
        have hB := ssum_hol (hβ x hx) (hβH x x' hx hx') h1d (b1s x' hx') (by positivity) (by positivity)
        have e : (∑ i, ∑ j, α x i j * R2 g' x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, β x i * R1 g' x (EuclideanSpace.single i 1)) -
            (∑ i, ∑ j, α x' i j * R2 g' x' (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
            ∑ i, β x' i * R1 g' x' (EuclideanSpace.single i 1)) =
            (∑ i, ∑ j, α x i j * R2 g' x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) -
              ∑ i, ∑ j, α x' i j * R2 g' x' (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
            (∑ i, β x i * R1 g' x (EuclideanSpace.single i 1) -
              ∑ i, β x' i * R1 g' x' (EuclideanSpace.single i 1)) := by ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        have := add_le_add hA hB
        linarith
      · -- contraction: w M'' + H'' ≤ ½ (w M' + H')
        rw [hF8]
        have hw0 : 0 ≤ w := by positivity
        have k1 : K * (C * H' * E) ≤ (1 / 6) * H' := by linarith [mul_le_mul_of_nonneg_right hKCE hH']
        have k2 : K * (C * M' * (w * s)) ≤ (1 / 6) * (w * M') := by
          have h3 : K * (C * M' * (w * s)) ≤ K * C * E * (w * M') := by
            have := mul_le_mul_of_nonneg_left hsE (by positivity : 0 ≤ K * C * M' * w)
            linarith [this]
          linarith [mul_le_mul_of_nonneg_right hKCE (by positivity : 0 ≤ w * M')]
        have k3 : K * (C * M' * s) ≤ K * (C * M' * (w * s)) := by
          have := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ K * C * M' * s)
          linarith [this]
        have k4 : δ * (C * H') ≤ (1 / 8) * H' := by linarith [mul_le_mul_of_nonneg_right hδC hH']
        have k5 : w * (δ * (C * H' * E)) = δ * (C * H') := by
          calc w * (δ * (C * H' * E)) = δ * (C * H') * (w * E) := by ring
            _ = δ * (C * H') := by rw [hwE, mul_one]
        linarith [k1, k2, k3, k4, k5]
  obtain ⟨u, u1, u2, hd, hbc, heq, hsup, hhol⟩ := hsr
  refine ⟨u, u1, u2, hd, fun x hx => ?_, hbc, fun x hx v w' => ?_, fun x x' hx hx' v w' => ?_⟩
  · have h1 := heq x hx
    rw [pLv_apply, pBv_apply] at h1
    linarith
  · obtain ⟨b0, b1, b2⟩ := hsup x hx
    refine ⟨b0.trans_eq (by ring), ?_, ?_⟩
    · refine (abs_app1' _ v).trans ?_
      have := mul_le_mul_of_nonneg_right b1 (norm_nonneg v)
      exact this.trans_eq (by ring)
    · refine (abs_app2' _ v w').trans ?_
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right b2 (norm_nonneg v)) (norm_nonneg w')
      exact this.trans_eq (by ring)
  · obtain ⟨b0, b1, b2⟩ := hhol x hx x' hx'
    refine ⟨b0.trans_eq (by ring), ?_, ?_⟩
    · rw [← ContinuousLinearMap.sub_apply]
      refine (abs_app1' _ v).trans ?_
      have := mul_le_mul_of_nonneg_right b1 (norm_nonneg v)
      exact this.trans_eq (by ring)
    · rw [← ContinuousLinearMap.sub_apply, ← ContinuousLinearMap.sub_apply]
      refine (abs_app2' _ v w').trans ?_
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right b2 (norm_nonneg v)) (norm_nonneg w')
      exact this.trans_eq (by ring)

end VarM

end ObliqueLib

theorem solution (d : ℕ) (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hHM : ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ lam : ℝ, 0 < lam → ∀ h : EuclideanSpace ℝ (Fin d) → ℝ,
        (∃ Hh : ℝ, ∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
        (∃ M0 : ℝ, ∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |h y| ≤ M0) →
        ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
          (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
            lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
              = h x) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
          ∀ M0 Hh : ℝ, 0 ≤ M0 → 0 ≤ Hh → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |h y| ≤ M0) →
            (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |h y - h z| ≤ Hh * ‖y - z‖ ^ μ) →
          (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
            |u x| ≤ C * M0 * (1 / lam) ∧
            |u1 x v| ≤ C * M0 * (1 / lam) ^ (1 / 2 : ℝ) * ‖v‖ ∧
            |u2 x v w| ≤ C * Hh * (1 / lam) ^ (μ / 2) * ‖v‖ * ‖w‖) ∧
          (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
            |u x - u x'| ≤ C * M0 * (1 / lam) ^ (1 - μ / 2) * ‖x - x'‖ ^ μ ∧
            |u1 x v - u1 x' v| ≤ C * M0 * (1 / lam) ^ ((1 - μ) / 2) * ‖x - x'‖ ^ μ * ‖v‖ ∧
            |u2 x v w - u2 x' v w| ≤ C * Hh * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖)) :
    ∀ e b : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 → inner ℝ b e = 0 → ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℝ, 0 ≤ K →
      ∃ lam0 C : ℝ, 1 ≤ lam0 ∧ 0 ≤ C ∧ ∀ lam : ℝ, lam0 ≤ lam →
      ∀ (α : EuclideanSpace ℝ (Fin d) → Fin d → Fin d → ℝ) (β : EuclideanSpace ℝ (Fin d) → Fin d → ℝ),
        (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, ∑ j, |α x i j| ≤ δ) →
        (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
          ∑ i, ∑ j, |α x i j - α x' i j| ≤ K * ‖x - x'‖ ^ μ) →
        (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∑ i, |β x i| ≤ K) →
        (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e →
          ∑ i, |β x i - β x' i| ≤ K * ‖x - x'‖ ^ μ) →
        ∀ (g : EuclideanSpace ℝ (Fin d) → ℝ) (M H : ℝ), 0 ≤ M → 0 ≤ H → (∀ y : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → |g y| ≤ M) →
        (∀ y z : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ y e → 0 ≤ inner ℝ z e → |g y - g z| ≤ H * ‖y - z‖ ^ μ) →
        ∃ (u : EuclideanSpace ℝ (Fin d) → ℝ) (u1 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (u2 : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ),
          (∀ x : EuclideanSpace ℝ (Fin d), 0 < inner ℝ x e → HasFDerivAt u (u1 x) x ∧ HasFDerivAt u1 (u2 x) x) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e →
            lam * u x - (1 / 2 : ℝ) * ∑ i, u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
              - ∑ i, ∑ j, α x i j * u2 x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
              - ∑ i, β x i * u1 x (EuclideanSpace.single i 1) = g x) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), inner ℝ x e = 0 → u1 x (b - e) = 0) ∧
          (∀ x : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → ∀ v w : EuclideanSpace ℝ (Fin d),
            |u x| ≤ C * (1 / lam) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) ∧
            |u1 x v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ ∧
            |u2 x v w| ≤ C * (1 / lam) ^ (μ / 2) * (lam ^ (μ / 2) * M + H) * ‖v‖ * ‖w‖) ∧
          (∀ x x' : EuclideanSpace ℝ (Fin d), 0 ≤ inner ℝ x e → 0 ≤ inner ℝ x' e → ∀ v w : EuclideanSpace ℝ (Fin d),
            |u x - u x'| ≤ C * (1 / lam) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ ∧
            |u1 x v - u1 x' v| ≤ C * (1 / lam) ^ (1 / 2 : ℝ) * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ ∧
            |u2 x v w - u2 x' v w| ≤ C * (lam ^ (μ / 2) * M + H) * ‖x - x'‖ ^ μ * ‖v‖ * ‖w‖) := by
  exact ObliqueLib.varModel hμ0 hμ1 hHM
