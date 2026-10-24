-- Prove2me | solution 1 for FirstOrderOpt.OperatorSliding.ps_procedure_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T08:36:55.423602+00:00
-- url     : https://prove2.me/submissions/3935de73-adef-4d5a-a201-4cf7c92d1d8c

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox Filter Topology

namespace PS88

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma three_point {X : Set E} (ν : DistanceGeneratingFunction X) (x xp u : E) :
    ν.V x u - ν.V xp u - ν.V x xp = ν.dω xp (u - xp) - ν.dω x (u - xp) := by
  simp only [DistanceGeneratingFunction.V]
  have : u - x = (u - xp) + (xp - x) := by abel
  rw [this, map_add]; ring

lemma slope_lim {X : Set E} (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    {xp u : E} (hxp : xp ∈ X) (hu : u ∈ X) :
    Tendsto (fun t : ℝ => t⁻¹ * (ν.ω (xp + t • (u - xp)) - ν.ω xp)) (𝓝[Set.Ioc 0 1] 0)
      (𝓝 (ν.dω xp (u - xp))) := by
  have hmap : Set.MapsTo (fun t : ℝ => xp + t • (u - xp)) (Set.Icc 0 1) X := by
    intro t ht
    have := hXconv.add_smul_sub_mem hxp hu ht
    simpa using this
  have hl : HasDerivWithinAt (fun t : ℝ => xp + t • (u - xp)) (u - xp) (Set.Icc 0 1) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const (u - xp)).const_add xp
    simpa using this.hasDerivWithinAt
  have hd : HasDerivWithinAt (fun t : ℝ => ν.ω (xp + t • (u - xp))) (ν.dω xp (u - xp))
      (Set.Icc 0 1) 0 := by
    have h0 : HasFDerivWithinAt ν.ω (ν.dω xp) X (xp + (0:ℝ) • (u - xp)) := by
      simpa using ν.hasFDerivWithinAt xp hxp
    exact h0.comp_hasDerivWithinAt 0 hl hmap
  have := hasDerivWithinAt_iff_tendsto_slope.1 hd
  have hs : Set.Icc (0:ℝ) 1 \ {0} = Set.Ioc 0 1 := by
    ext t; simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨lt_of_le_of_ne h1 (Ne.symm h3), h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1.ne'⟩
  rw [hs] at this
  refine this.congr (fun t => ?_)
  simp [slope_def_field, div_eq_inv_mul]

lemma tp_gen {X : Set E} (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    (ψ : E → ℝ) (hψ : ConvexOn ℝ X ψ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (x y z : E) (hz : z ∈ X)
    (hmin : ∀ w ∈ X, ψ z + a * ν.V x z + b * ν.V y z ≤ ψ w + a * ν.V x w + b * ν.V y w)
    (w : E) (hw : w ∈ X) :
    ψ z + a * ν.V x z + b * ν.V y z + (a + b) * ν.V z w ≤
      ψ w + a * ν.V x w + b * ν.V y w := by
  set d := w - z with hd
  have key : 0 ≤ (ψ w - ψ z) + (a + b) * ν.dω z d - a * ν.dω x d - b * ν.dω y d := by
    have hF : ∀ t ∈ Set.Ioc (0:ℝ) 1, 0 ≤ (ψ w - ψ z) +
        (a + b) * (t⁻¹ * (ν.ω (z + t • d) - ν.ω z)) - a * ν.dω x d - b * ν.dω y d := by
      rintro t ⟨ht0, ht1⟩
      have hut : z + t • d ∈ X := by
        have := hXconv.add_smul_sub_mem hz hw ⟨ht0.le, ht1⟩; simpa [hd] using this
      have h1 := hmin _ hut
      have hconv : ψ (z + t • d) ≤ (1 - t) * ψ z + t * ψ w := by
        have := hψ.2 hz hw (by linarith : 0 ≤ 1 - t) ht0.le (by ring)
        have e : (1 - t) • z + t • w = z + t • d := by
          simp only [hd, smul_sub, sub_smul, one_smul]; abel
        simpa [e, smul_eq_mul] using this
      have hV : ∀ q : E, ν.V q (z + t • d) - ν.V q z =
          ν.ω (z + t • d) - ν.ω z - t * ν.dω q d := by
        intro q
        simp only [DistanceGeneratingFunction.V]
        have : z + t • d - q = (z - q) + t • d := by abel
        rw [this, map_add, map_smul, smul_eq_mul]; ring
      have hx1 := hV x
      have hy1 := hV y
      have hmain : 0 ≤ t * (ψ w - ψ z) + (a + b) * (ν.ω (z + t • d) - ν.ω z)
          - t * a * ν.dω x d - t * b * ν.dω y d := by
        have e1 : a * ν.V x (z + t • d) - a * ν.V x z =
            a * (ν.ω (z + t • d) - ν.ω z - t * ν.dω x d) := by rw [← hx1]; ring
        have e2 : b * ν.V y (z + t • d) - b * ν.V y z =
            b * (ν.ω (z + t • d) - ν.ω z - t * ν.dω y d) := by rw [← hy1]; ring
        nlinarith
      have e : (ψ w - ψ z) + (a + b) * (t⁻¹ * (ν.ω (z + t • d) - ν.ω z))
          - a * ν.dω x d - b * ν.dω y d =
          t⁻¹ * (t * (ψ w - ψ z) + (a + b) * (ν.ω (z + t • d) - ν.ω z)
            - t * a * ν.dω x d - t * b * ν.dω y d) := by
        field_simp
      rw [e]; exact mul_nonneg (inv_nonneg.2 ht0.le) hmain
    have hlim : Tendsto (fun t : ℝ => (ψ w - ψ z) +
        (a + b) * (t⁻¹ * (ν.ω (z + t • d) - ν.ω z)) - a * ν.dω x d - b * ν.dω y d)
        (𝓝[Set.Ioc 0 1] 0)
        (𝓝 ((ψ w - ψ z) + (a + b) * ν.dω z d - a * ν.dω x d - b * ν.dω y d)) := by
      have := slope_lim hXconv ν hz hw
      exact ((tendsto_const_nhds.add (this.const_mul _)).sub tendsto_const_nhds).sub
        tendsto_const_nhds
    have : (𝓝[Set.Ioc (0:ℝ) 1] 0).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc (by norm_num)]
      exact ⟨le_rfl, zero_le_one⟩
    exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hF)
  have htx := three_point ν x z w
  have hty := three_point ν y z w
  rw [← hd] at htx hty
  linear_combination key - a * htx - b * hty

end PS88

namespace PS88

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma V_conv {X : Set E} (hXconv : Convex ℝ X) (ν : DistanceGeneratingFunction X)
    (x a b : E) (ha : a ∈ X) (hb : b ∈ X) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    ν.V x ((1 - θ) • a + θ • b) ≤ (1 - θ) * ν.V x a + θ * ν.V x b := by
  set z := (1 - θ) • a + θ • b with hzdef
  have hz : z ∈ X := hXconv ha hb (by linarith) h0 (by ring)
  have sa := ν.strongConvex z hz a ha
  have sb := ν.strongConvex z hz b hb
  have hna : 0 ≤ (1 / 2 : ℝ) * ‖a - z‖ ^ 2 := by positivity
  have hnb : 0 ≤ (1 / 2 : ℝ) * ‖b - z‖ ^ 2 := by positivity
  have e0 : (1 - θ) • (a - z) + θ • (b - z) = 0 := by
    simp only [hzdef, smul_sub, sub_smul, one_smul, smul_add, smul_smul]; module
  have e1 : (1 - θ) * ν.dω z (a - z) + θ * ν.dω z (b - z) = 0 := by
    have := congrArg (ν.dω z) e0
    rw [map_add, map_smul, map_smul, map_zero] at this
    simpa [smul_eq_mul] using this
  have e2 : z - x = (1 - θ) • (a - x) + θ • (b - x) := by
    simp only [hzdef, smul_sub, sub_smul, one_smul]; module
  have e3 : ν.dω x (z - x) = (1 - θ) * ν.dω x (a - x) + θ * ν.dω x (b - x) := by
    rw [e2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  simp only [DistanceGeneratingFunction.V]
  rw [e3]
  have h1' : 0 ≤ 1 - θ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left (by linarith : ν.ω z + ν.dω z (a - z) ≤ ν.ω a) h1',
    mul_le_mul_of_nonneg_left (by linarith : ν.ω z + ν.dω z (b - z) ≤ ν.ω b) h0]

end PS88


theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (g : E → ℝ) (lg : E →L[ℝ] ℝ) (cg : ℝ) (hg : ∀ u, g u = lg u + cg)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h) (h' : E → E →L[ℝ] ℝ)
    (hh' : ∀ y ∈ X, ∀ z ∈ X, h y + (h' y) (z - y) ≤ h z)
    (lh : E → E → ℝ) (hlh : ∀ y z, lh y z = h y + (h' y) (z - y))
    (chi : E → ℝ) (hchiconv : ConvexOn ℝ X chi)
    (x : E) (hx : x ∈ X) (β M : ℝ) (hβ : 0 < β) (hM : 0 < M)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ lh y z + M * ‖z - y‖)
    (Φ : E → ℝ) (hΦ : ∀ u, Φ u = g u + h u + β * ν.V x u + chi u)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t)
    (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (u ũ : ℕ → E) (hu0 : u 0 = x) (hũ0 : ũ 0 = x) (hmem : ∀ t, u t ∈ X)
    (huMin : ∀ t : ℕ, 1 ≤ t → ∀ w ∈ X,
      g (u t) + lh (u (t - 1)) (u t) + β * ν.V x (u t) + β * p t * ν.V (u (t - 1)) (u t)
          + chi (u t) ≤
        g w + lh (u (t - 1)) w + β * ν.V x w + β * p t * ν.V (u (t - 1)) w + chi w)
    (hũrec : ∀ t : ℕ, 1 ≤ t → ũ t = (1 - θ t) • ũ (t - 1) + θ t • u t)
    (t : ℕ) (ht : 1 ≤ t) (w : E) (hw : w ∈ X) :
    β * (1 - P t)⁻¹ * ν.V (u t) w + (Φ (ũ t) - Φ w) ≤
      P t * (1 - P t)⁻¹ *
        (β * ν.V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 t, (p i ^ 2 * P (i - 1))⁻¹) := by
  -- scalar facts
  have hPs : ∀ n, P (n + 1) = p (n + 1) * (1 + p (n + 1))⁻¹ * P n := fun n => by
    simpa using hPrec (n + 1) (by omega)
  have hPpos : ∀ n, 0 < P n ∧ P n ≤ 1 := by
    intro n
    induction n with
    | zero => rw [hP0]; norm_num
    | succ n ih =>
      have hpn := hp (n + 1)
      rw [hPs n]
      refine ⟨by have := ih.1; positivity, ?_⟩
      have : p (n + 1) * (1 + p (n + 1))⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
      nlinarith [ih.1, ih.2]
  have hPlt : ∀ n, P (n + 1) < 1 := by
    intro n
    have hpn := hp (n + 1)
    have := hPpos n
    rw [hPs n]
    have : p (n + 1) * (1 + p (n + 1))⁻¹ < 1 := by
      rw [← div_eq_mul_inv, div_lt_one (by linarith)]; linarith
    nlinarith
  -- step inequality (*)
  have hstep : ∀ n, Φ (u (n + 1)) + β * (1 + p (n + 1)) * ν.V (u (n + 1)) w ≤
      Φ w + β * p (n + 1) * ν.V (u n) w + M ^ 2 / (2 * β * p (n + 1)) := by
    intro n
    set y := u n
    set z := u (n + 1)
    set pt := p (n + 1)
    have hpt : 0 < pt := hp (n + 1)
    have hy : y ∈ X := hmem n
    have hz : z ∈ X := hmem (n + 1)
    have hmin := huMin (n + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hmin
    let ψ : E → ℝ := fun v => g v + lh y v + chi v
    have hψ : ConvexOn ℝ X ψ := by
      refine ⟨hXconv, fun a ha b hb s r hs hr hsr => ?_⟩
      have hc := hchiconv.2 ha hb hs hr hsr
      simp only [ψ, hg, hlh, map_add, map_smul, smul_eq_mul, map_sub] at hc ⊢
      have : s * cg + r * cg = cg := by rw [← add_mul, hsr, one_mul]
      have : s * h y + r * h y = h y := by rw [← add_mul, hsr, one_mul]
      have : s * (h' y) y + r * (h' y) y = (h' y) y := by rw [← add_mul, hsr, one_mul]
      nlinarith
    have key := PS88.tp_gen hXconv ν ψ hψ β (β * pt) hβ.le (by positivity) x y z hz
      (fun v hv => by have := hmin v hv; simp only [ψ]; linarith) w hw
    simp only [ψ] at key
    have hL := hMLip y hy z hz
    have hh2 := hh' y hy w hw
    rw [← hlh] at hh2
    have hsc := ν.strongConvex y hy z hz
    have hVyz : (1 / 2) * ‖z - y‖ ^ 2 ≤ ν.V y z := by
      simp only [DistanceGeneratingFunction.V]; linarith
    have hq : M * ‖z - y‖ - β * pt * ((1 / 2) * ‖z - y‖ ^ 2) ≤ M ^ 2 / (2 * β * pt) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (β * pt * ‖z - y‖ - M)]
    have hm := mul_le_mul_of_nonneg_left hVyz (by positivity : (0:ℝ) ≤ β * pt)
    rw [hΦ, hΦ]
    nlinarith
  -- Jensen for Φ
  have hJ : ∀ a ∈ X, ∀ b ∈ X, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      Φ ((1 - s) • a + s • b) ≤ (1 - s) * Φ a + s * Φ b := by
    intro a ha b hb s h0 h1
    have h1' : 0 ≤ 1 - s := by linarith
    have hhc := hhconv.2 ha hb h1' h0 (by ring)
    have hcc := hchiconv.2 ha hb h1' h0 (by ring)
    have hVc := PS88.V_conv hXconv ν x a b ha hb s h0 h1
    have hVc' := mul_le_mul_of_nonneg_left hVc hβ.le
    simp only [smul_eq_mul] at hhc hcc
    rw [hΦ, hΦ, hΦ, hg, hg, hg, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  -- main induction
  have main : ∀ n, ũ n ∈ X ∧ β / P n * ν.V (u n) w + (1 - P n) / P n * (Φ (ũ n) - Φ w) ≤
      β * ν.V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 n, (p i ^ 2 * P (i - 1))⁻¹ := by
    intro n
    induction n with
    | zero =>
      refine ⟨by rw [hũ0]; exact hx, ?_⟩
      simp [hP0, hu0]
    | succ n ih =>
      obtain ⟨hmn, ih⟩ := ih
      have hrec := hũrec (n + 1) (by omega)
      have hth := hθ (n + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hrec hth
      set q := P n with hq
      set r := P (n + 1) with hr
      set pp := p (n + 1) with hpp
      set th := θ (n + 1) with hthdef
      have hpp0 : 0 < pp := hp (n + 1)
      have hq0 := (hPpos n).1
      have hq1 := (hPpos n).2
      have hr0 := (hPpos (n + 1)).1
      have hr1 : r < 1 := hPlt n
      have hrq : r = pp * (1 + pp)⁻¹ * q := hPs n
      have h1r : 1 - r ≠ 0 := by linarith
      have hq' : q ≠ 0 := hq0.ne'
      have hpp' : pp ≠ 0 := hpp0.ne'
      have h1pp : 1 + pp ≠ 0 := by linarith
      have hr' : r * (1 + pp) = pp * q := by rw [hrq]; field_simp
      have hqe : q = r * (1 + pp) / pp := by rw [hr']; field_simp
      have hth' : th = 1 / ((1 + pp) * (1 - r)) := by
        rw [hth, div_eq_div_iff (mul_ne_zero h1r hq') (mul_ne_zero h1pp h1r)]
        linear_combination (-(1 - r)) * hr'
      have h1r' : 0 < 1 - r := by linarith
      have hth0 : 0 ≤ th := by rw [hth']; positivity
      have hth1 : th ≤ 1 := by
        rw [hth', div_le_one (by positivity)]
        nlinarith [mul_nonneg hpp0.le (by linarith : (0:ℝ) ≤ 1 - q)]
      have hmem' : ũ (n + 1) ∈ X := by
        rw [hrec]; exact hXconv hmn (hmem _) (by linarith) hth0 (by ring)
      refine ⟨hmem', ?_⟩
      have hJ1 := hJ _ hmn _ (hmem (n + 1)) th hth0 hth1
      rw [← hrec] at hJ1
      have hS := hstep n
      rw [← hpp] at hS
      have c1 : (1 - r) / r * th = 1 / (pp * q) := by
        rw [hth', hqe]; field_simp
      have c2 : (1 - r) / r * (1 - th) = (1 - q) / q := by
        rw [hth', hqe]; field_simp; ring
      have c3 : 1 / (pp * q) * (β * pp * ν.V (u n) w - β * (1 + pp) * ν.V (u (n + 1)) w
          + M ^ 2 / (2 * β * pp)) = β / q * ν.V (u n) w - β / r * ν.V (u (n + 1)) w
          + M ^ 2 / (2 * β) * (pp ^ 2 * q)⁻¹ := by
        rw [hqe]; field_simp
      have hc0 : 0 ≤ (1 - r) / r := by
        have : 0 ≤ 1 - r := by linarith
        positivity
      have d1 : (1 - r) / r * (Φ (ũ (n + 1)) - Φ w) ≤
          (1 - r) / r * ((1 - th) * (Φ (ũ n) - Φ w) + th * (Φ (u (n + 1)) - Φ w)) :=
        mul_le_mul_of_nonneg_left (by linear_combination hJ1) hc0
      have d2 : (1 - r) / r * ((1 - th) * (Φ (ũ n) - Φ w) + th * (Φ (u (n + 1)) - Φ w)) =
          (1 - q) / q * (Φ (ũ n) - Φ w) + 1 / (pp * q) * (Φ (u (n + 1)) - Φ w) := by
        rw [← c1, ← c2]; ring
      have d3 : 1 / (pp * q) * (Φ (u (n + 1)) - Φ w) ≤ 1 / (pp * q) *
          (β * pp * ν.V (u n) w - β * (1 + pp) * ν.V (u (n + 1)) w + M ^ 2 / (2 * β * pp)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
      simp only [Nat.add_sub_cancel]
      rw [← hq, ← hpp, mul_add]
      linarith
  obtain ⟨_, hmain⟩ := main t
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  have hr0 := (hPpos (n + 1)).1
  have hr1 := hPlt n
  have hpos : 0 ≤ P (n + 1) * (1 - P (n + 1))⁻¹ := by
    have : 0 < 1 - P (n + 1) := by linarith
    positivity
  have := mul_le_mul_of_nonneg_left hmain hpos
  have e : P (n + 1) * (1 - P (n + 1))⁻¹ * (β / P (n + 1) * ν.V (u (n + 1)) w +
      (1 - P (n + 1)) / P (n + 1) * (Φ (ũ (n + 1)) - Φ w)) =
      β * (1 - P (n + 1))⁻¹ * ν.V (u (n + 1)) w + (Φ (ũ (n + 1)) - Φ w) := by
    have : (1 - P (n + 1)) ≠ 0 := by linarith
    field_simp
  linarith
