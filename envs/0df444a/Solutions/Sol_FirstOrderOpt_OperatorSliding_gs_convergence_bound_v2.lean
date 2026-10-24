-- Prove2me | solution 1 for FirstOrderOpt.OperatorSliding.gs_convergence_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T09:27:15.224002+00:00
-- url     : https://prove2.me/submissions/f848ef51-5cf0-4bbb-89e3-c9cf419aca4b

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox Filter Topology

namespace GS88

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma descent (X : Set E) (hXconv : Convex ℝ X) (f : E → ℝ) (fGrad : E → E →L[ℝ] ℝ) (L : ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (a b : E) (ha : a ∈ X) (hb : b ∈ X) :
    f b ≤ f a + fGrad a (b - a) + L / 2 * ‖b - a‖ ^ 2 := by
  set d := b - a with hd
  let φ : ℝ → ℝ := fun t => f (a + t • d) - t * fGrad a d - L / 2 * t ^ 2 * ‖d‖ ^ 2
  let φ' : ℝ → ℝ := fun t => fGrad (a + t • d) d - fGrad a d - L * t * ‖d‖ ^ 2
  have hmap : Set.MapsTo (fun t : ℝ => a + t • d) (Set.Icc 0 1) X := by
    intro t ht
    have := hXconv.add_smul_sub_mem ha hb ht
    simpa [hd] using this
  have hder : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivWithinAt φ (φ' t) (Set.Icc 0 1) t := by
    intro t ht
    have hl : HasDerivWithinAt (fun t : ℝ => a + t • d) d (Set.Icc 0 1) t := by
      have := ((hasDerivAt_id t).smul_const d).const_add a
      simpa using this.hasDerivWithinAt
    have h1 : HasDerivWithinAt (fun t : ℝ => f (a + t • d)) (fGrad (a + t • d) d)
        (Set.Icc 0 1) t :=
      (hGrad _ (hmap ht)).comp_hasDerivWithinAt t hl hmap
    have h2 : HasDerivWithinAt (fun t : ℝ => t * fGrad a d) (1 * fGrad a d) (Set.Icc 0 1) t :=
      ((hasDerivAt_id t).mul_const _).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun t : ℝ => L / 2 * t ^ 2 * ‖d‖ ^ 2)
        (L / 2 * (↑2 * t ^ (2 - 1)) * ‖d‖ ^ 2) (Set.Icc 0 1) t :=
      (((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const _).hasDerivWithinAt
    have := (h1.sub h2).sub h3
    have e : φ' t = fGrad (a + t • d) d - 1 * fGrad a d - L / 2 * (↑2 * t ^ (2 - 1)) * ‖d‖ ^ 2 := by
      simp only [φ']; norm_num; left; ring
    rw [e]; exact this
  have hanti : AntitoneOn φ (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · exact fun t ht => (hder t ht).continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht ⊢
      exact (hder t (Set.Ioo_subset_Icc_self ht)).mono Set.Ioo_subset_Icc_self
    · intro t ht
      rw [interior_Icc] at ht
      have hz := hmap (Set.Ioo_subset_Icc_self ht)
      have hs := hSmooth _ hz a ha
      have e : fGrad (a + t • d) d - fGrad a d = (fGrad (a + t • d) - fGrad a) d := by
        simp
      have hn : (fGrad (a + t • d) - fGrad a) d ≤ ‖fGrad (a + t • d) - fGrad a‖ * ‖d‖ :=
        le_trans (le_abs_self _) (by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _)
      have hn2 : ‖a + t • d - a‖ = t * ‖d‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hn2] at hs
      have := mul_le_mul_of_nonneg_right hs (norm_nonneg d)
      simp only [φ']
      nlinarith
  have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    zero_le_one
  simp only [φ] at this
  simp at this
  rw [hd] at this ⊢
  have e : a + (b - a) = b := by abel
  rw [e] at this
  linarith

end GS88


open scoped RealInnerProductSpace
open FirstOrderOpt.Prox Filter Topology

namespace GS88

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

end GS88

namespace GS88

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

end GS88


namespace GS88

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem ps_bound
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
    (T : ℕ)
    (huMin : ∀ t : ℕ, 1 ≤ t → t ≤ T → ∀ w ∈ X,
      g (u t) + lh (u (t - 1)) (u t) + β * ν.V x (u t) + β * p t * ν.V (u (t - 1)) (u t)
          + chi (u t) ≤
        g w + lh (u (t - 1)) w + β * ν.V x w + β * p t * ν.V (u (t - 1)) w + chi w)
    (hũrec : ∀ t : ℕ, 1 ≤ t → t ≤ T → ũ t = (1 - θ t) • ũ (t - 1) + θ t • u t)
    (t : ℕ) (ht : 1 ≤ t) (htT : t ≤ T) (w : E) (hw : w ∈ X) :
    ũ t ∈ X ∧ β * (1 - P t)⁻¹ * ν.V (u t) w + (Φ (ũ t) - Φ w) ≤
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
  have hstep : ∀ n, n + 1 ≤ T → Φ (u (n + 1)) + β * (1 + p (n + 1)) * ν.V (u (n + 1)) w ≤
      Φ w + β * p (n + 1) * ν.V (u n) w + M ^ 2 / (2 * β * p (n + 1)) := by
    intro n hnT
    set y := u n
    set z := u (n + 1)
    set pt := p (n + 1)
    have hpt : 0 < pt := hp (n + 1)
    have hy : y ∈ X := hmem n
    have hz : z ∈ X := hmem (n + 1)
    have hmin := huMin (n + 1) (by omega) hnT
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
    have key := GS88.tp_gen hXconv ν ψ hψ β (β * pt) hβ.le (by positivity) x y z hz
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
    have hVc := GS88.V_conv hXconv ν x a b ha hb s h0 h1
    have hVc' := mul_le_mul_of_nonneg_left hVc hβ.le
    simp only [smul_eq_mul] at hhc hcc
    rw [hΦ, hΦ, hΦ, hg, hg, hg, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    nlinarith
  -- main induction
  have main : ∀ n, n ≤ T → ũ n ∈ X ∧ β / P n * ν.V (u n) w + (1 - P n) / P n * (Φ (ũ n) - Φ w) ≤
      β * ν.V x w + (M ^ 2 / (2 * β)) * ∑ i ∈ Finset.Icc 1 n, (p i ^ 2 * P (i - 1))⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨by rw [hũ0]; exact hx, ?_⟩
      simp [hP0, hu0]
    | succ n ih =>
      intro hnT
      obtain ⟨hmn, ih⟩ := ih (by omega)
      have hrec := hũrec (n + 1) (by omega) hnT
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
      have hS := hstep n hnT
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
  obtain ⟨hmt, hmain⟩ := main t htT
  obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by omega⟩
  refine ⟨hmt, ?_⟩
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

end GS88


open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

namespace GS88

lemma P_facts (p P : ℕ → ℝ) (hp : ∀ t, 0 < p t) (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1)) :
    ∀ n, 1 ≤ n → 0 < P n ∧ P n < 1 := by
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
  intro n hn
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨(hPpos _).1, ?_⟩
  have hpn := hp (n + 1)
  have := hPpos n
  rw [hPs n]
  have : p (n + 1) * (1 + p (n + 1))⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by linarith)]; linarith
  nlinarith

end GS88


open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

set_option maxHeartbeats 1000000 in
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hfconv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) ≤ f y)
    (hhconv : ConvexOn ℝ X h) (h' : E → E →L[ℝ] ℝ)
    (hh' : ∀ y ∈ X, ∀ z ∈ X, h y + (h' y) (z - y) ≤ h z)
    (hMLip : ∀ y ∈ X, ∀ z ∈ X, h z ≤ h y + (h' y) (z - y) + M * ‖z - y‖)
    (hchiconv : ConvexOn ℝ X chi)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (p θ P : ℕ → ℝ) (hp : ∀ t, 0 < p t) (hP0 : P 0 = 1)
    (hPrec : ∀ t : ℕ, 1 ≤ t → P t = p t * (1 + p t)⁻¹ * P (t - 1))
    (hθ : ∀ t : ℕ, 1 ≤ t → θ t = (P (t - 1) - P t) / ((1 - P t) * P (t - 1)))
    (β γ : ℕ → ℝ) (T : ℕ → ℕ) (hTpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ T k)
    (hβpos : ∀ k : ℕ, 1 ≤ k → 0 < β k)
    (hγ1 : γ 1 = 1) (hγpos : ∀ k : ℕ, 2 ≤ k → 0 < γ k) (hγlt : ∀ k : ℕ, 2 ≤ k → γ k < 1)
    (hβγ : ∀ k : ℕ, 1 ≤ k → L * γ k ≤ β k)
    (Γ : ℕ → ℝ) (hΓ1 : Γ 1 = 1) (hΓrec : ∀ k : ℕ, 2 ≤ k → Γ k = (1 - γ k) * Γ (k - 1))
    (hMono : ∀ k : ℕ, 2 ≤ k →
      γ k * β k / (Γ k * (1 - P (T k))) ≤ γ (k - 1) * β (k - 1) / (Γ (k - 1) * (1 - P (T (k - 1)))))
    (x xbar xunder xtilde : ℕ → E) (hx0eq : x 0 = x0) (hxbar0 : xbar 0 = x0)
    (hxunder : ∀ k : ℕ, 1 ≤ k → xunder k = (1 - γ k) • xbar (k - 1) + γ k • x (k - 1))
    (u ũ : ℕ → ℕ → E)
    (hu0 : ∀ k : ℕ, 1 ≤ k → u k 0 = x (k - 1)) (hũ0 : ∀ k : ℕ, 1 ≤ k → ũ k 0 = x (k - 1))
    (humem : ∀ k t, u k t ∈ X)
    (huMin : ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ T k → ∀ w ∈ X,
      (f (xunder k) + (fGrad (xunder k)) (u k t - xunder k))
          + (h (u k (t - 1)) + (h' (u k (t - 1))) (u k t - u k (t - 1)))
          + β k * ν.V (x (k - 1)) (u k t) + β k * p t * ν.V (u k (t - 1)) (u k t) + chi (u k t) ≤
        (f (xunder k) + (fGrad (xunder k)) (w - xunder k))
          + (h (u k (t - 1)) + (h' (u k (t - 1))) (w - u k (t - 1)))
          + β k * ν.V (x (k - 1)) w + β k * p t * ν.V (u k (t - 1)) w + chi w)
    (hũrec : ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ, 1 ≤ t → t ≤ T k →
      ũ k t = (1 - θ t) • ũ k (t - 1) + θ t • u k t)
    (hxk : ∀ k : ℕ, 1 ≤ k → x k = u k (T k)) (hxtilde : ∀ k : ℕ, 1 ≤ k → xtilde k = ũ k (T k))
    (hxbar : ∀ k : ℕ, 1 ≤ k → xbar k = (1 - γ k) • xbar (k - 1) + γ k • xtilde k)
    (N : ℕ) (hN : 1 ≤ N) :
    Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * ν.V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) := by
  -- notation
  have hPf := GS88.P_facts p P hp hP0 hPrec
  have hγ01 : ∀ k, 1 ≤ k → 0 ≤ γ k ∧ γ k ≤ 1 := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · obtain rfl : k = 1 := by omega
      rw [hγ1]; norm_num
    · exact ⟨(hγpos k h2).le, (hγlt k h2).le⟩
  have hVnn : ∀ a ∈ X, ∀ b ∈ X, 0 ≤ ν.V a b := by
    intro a ha b hb
    have := ν.strongConvex a ha b hb
    simp only [DistanceGeneratingFunction.V]
    nlinarith [sq_nonneg ‖b - a‖]
  -- one outer step
  have key : ∀ k, 1 ≤ k → xbar (k - 1) ∈ X → x (k - 1) ∈ X → xbar k ∈ X ∧
      Ψ (xbar k) - Ψ xstar ≤ (1 - γ k) * (Ψ (xbar (k - 1)) - Ψ xstar) +
        γ k * (β k * (1 - P (T k))⁻¹ * (ν.V (x (k - 1)) xstar - ν.V (x k) xstar) +
          P (T k) * (1 - P (T k))⁻¹ *
            (M ^ 2 / (2 * β k) * ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹)) := by
    intro k hk hxb hxp
    obtain ⟨hg0, hg1⟩ := hγ01 k hk
    have hβk := hβpos k hk
    have hxu : xunder k ∈ X := by
      rw [hxunder k hk]; exact hXconv hxb hxp (by linarith) hg0 (by ring)
    have hPS := GS88.ps_bound X hXconv hXclosed ν
      (fun v => f (xunder k) + (fGrad (xunder k)) (v - xunder k)) (fGrad (xunder k))
      (f (xunder k) - (fGrad (xunder k)) (xunder k))
      (fun v => by simp only [map_sub]; ring)
      h hhconv h' hh' (fun y z => h y + (h' y) (z - y)) (fun _ _ => rfl) chi hchiconv
      (x (k - 1)) hxp (β k) M hβk hM hMLip
      (fun v => (f (xunder k) + (fGrad (xunder k)) (v - xunder k)) + h v
        + β k * ν.V (x (k - 1)) v + chi v) (fun _ => rfl)
      p θ P hp hP0 hPrec hθ (u k) (ũ k) (hu0 k hk) (hũ0 k hk) (humem k) (T k)
      (huMin k hk) (hũrec k hk) (T k) (hTpos k hk) le_rfl xstar hxstar
    rw [← hxk k hk, ← hxtilde k hk] at hPS
    obtain ⟨hxt, hPS⟩ := hPS
    have hxbk : xbar k ∈ X := by
      rw [hxbar k hk]; exact hXconv hxb hxt (by linarith) hg0 (by ring)
    refine ⟨hxbk, ?_⟩
    obtain ⟨hP0', hP1'⟩ := hPf (T k) (hTpos k hk)
    set c := (1 - P (T k))⁻¹ with hc
    have hc1 : c * (1 - P (T k)) = 1 := by
      have : 1 - P (T k) ≠ 0 := by linarith
      rw [hc, inv_mul_cancel₀ this]
    have hdiff : xbar k - xunder k = γ k • (xtilde k - x (k - 1)) := by
      rw [hxbar k hk, hxunder k hk]; module
    have hdiff2 : xbar k - xunder k = (1 - γ k) • (xbar (k - 1) - xunder k)
        + γ k • (xtilde k - xunder k) := by
      rw [hxbar k hk]; module
    set xu := xunder k
    set xt := xtilde k
    set xp := x (k - 1)
    set xb := xbar (k - 1)
    set g := γ k
    set S := ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹
    have hdes := GS88.descent X hXconv f fGrad L hGrad hSmooth xu (xbar k) hxu hxbk
    have hlin : (fGrad xu) (xbar k - xu) =
        (1 - g) * (fGrad xu) (xb - xu) + g * (fGrad xu) (xt - xu) := by
      rw [hdiff2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hnorm : ‖xbar k - xu‖ ^ 2 = g ^ 2 * ‖xt - xp‖ ^ 2 := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hfb := hfconv xu hxu xb hxb
    have hfs := hfconv xu hxu xstar hxstar
    have hhc := hhconv.2 hxb hxt (by linarith : 0 ≤ 1 - g) hg0 (by ring)
    have hcc := hchiconv.2 hxb hxt (by linarith : 0 ≤ 1 - g) hg0 (by ring)
    rw [← hxbar k hk, smul_eq_mul, smul_eq_mul] at hhc hcc
    have hVt : (1 / 2) * ‖xt - xp‖ ^ 2 ≤ ν.V xp xt := by
      have := ν.strongConvex xp hxp xt hxt
      simp only [DistanceGeneratingFunction.V]; linarith
    have hq : L / 2 * (g ^ 2 * ‖xt - xp‖ ^ 2) ≤ g * (β k * ν.V xp xt) := by
      have h1 : L * g * g ≤ β k * g := mul_le_mul_of_nonneg_right (hβγ k hk) hg0
      have h2 := mul_le_mul_of_nonneg_left hVt (mul_nonneg hg0 hβk.le)
      nlinarith [sq_nonneg ‖xt - xp‖]
    -- inner bound
    have hin : (f xu + (fGrad xu) (xt - xu) + h xt + β k * ν.V xp xt + chi xt) - Ψ xstar ≤
        β k * c * (ν.V xp xstar - ν.V (x k) xstar) + P (T k) * c * (M ^ 2 / (2 * β k) * S) := by
      have e : β k * c * ν.V xp xstar = β k * ν.V xp xstar + P (T k) * c * (β k * ν.V xp xstar) := by
        linear_combination (β k * ν.V xp xstar) * hc1
      rw [hΨ xstar]
      linarith
    have hin2 := mul_le_mul_of_nonneg_left hin hg0
    have hm1 := mul_le_mul_of_nonneg_left hfb (by linarith : 0 ≤ 1 - g)
    rw [hΨ xstar] at hin2
    rw [hΨ, hΨ, hΨ]
    rw [hlin, hnorm] at hdes
    nlinarith
  -- memberships
  have hmem : ∀ n, xbar n ∈ X ∧ x n ∈ X := by
    intro n
    induction n with
    | zero => rw [hxbar0, hx0eq]; exact ⟨hx0, hx0⟩
    | succ n ih =>
      have := (key (n + 1) (by omega) (by simpa using ih.1) (by simpa using ih.2)).1
      refine ⟨this, ?_⟩
      rw [hxk (n + 1) (by omega)]; exact humem _ _
  have hΓpos : ∀ k, 1 ≤ k → 0 < Γ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; rw [hΓ1]; norm_num
      · rw [hΓrec (n + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
        have := hγlt (n + 1) (by omega)
        exact mul_pos (by linarith) (ih h0)
  -- weights
  set w : ℕ → ℝ := fun k => γ k * β k / (Γ k * (1 - P (T k))) with hw
  set cc : ℕ → ℝ := fun k => M ^ 2 / 2 * ∑ i ∈ Finset.Icc 1 (T k),
    γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) with hcc
  have hident : ∀ k, 1 ≤ k → ∀ A B : ℝ,
      γ k * (β k * (1 - P (T k))⁻¹ * (A - B) + P (T k) * (1 - P (T k))⁻¹ *
        (M ^ 2 / (2 * β k) * ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹)) =
      Γ k * (w k * (A - B) + cc k) := by
    intro k hk A B
    have hΓ := (hΓpos k hk).ne'
    have hs : ∑ i ∈ Finset.Icc 1 (T k),
        γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) =
        γ k / Γ k * P (T k) * (1 - P (T k))⁻¹ * (β k)⁻¹ *
          ∑ i ∈ Finset.Icc 1 (T k), (p i ^ 2 * P (i - 1))⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      simp only [mul_inv]
      ring
    simp only [hw, hcc]
    rw [hs]
    field_simp
  -- telescoping
  have tele : ∀ n, 1 ≤ n → Ψ (xbar n) - Ψ xstar ≤
      Γ n * (w 1 * ν.V x0 xstar - w n * ν.V (x n) xstar + ∑ k ∈ Finset.Icc 1 n, cc k) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        have := (key 1 le_rfl (by simpa using (hmem 0).1) (by simpa using (hmem 0).2)).2
        rw [hident 1 le_rfl, hγ1] at this
        simp only [Nat.sub_self, hx0eq, sub_self, zero_mul, zero_add] at this
        simp only [zero_add, Finset.Icc_self, Finset.sum_singleton]
        rw [hΓ1] at this ⊢
        linarith
      · have ih := ih h0
        have hk := key (n + 1) (by omega) (by rw [Nat.add_sub_cancel]; exact (hmem n).1)
          (by rw [Nat.add_sub_cancel]; exact (hmem n).2)
        simp only [Nat.add_sub_cancel] at hk
        have hk := hk.2
        rw [hident (n + 1) (by omega)] at hk
        have hΓk := hΓrec (n + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hΓk
        have hg := hγlt (n + 1) (by omega)
        have f1 := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ 1 - γ (n + 1))
        rw [← mul_assoc, ← hΓk] at f1
        have hmono := hMono (n + 1) (by omega)
        simp only [Nat.add_sub_cancel] at hmono
        have hVn := hVnn _ (hmem n).2 _ hxstar
        have f4 : Γ (n + 1) * (w (n + 1) * ν.V (x n) xstar) ≤ Γ (n + 1) * (w n * ν.V (x n) xstar) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hVn)
            (hΓpos (n + 1) (by omega)).le
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
        linear_combination hk + f1 + f4
  have hfin := tele N hN
  have hwN : 0 ≤ w N * ν.V (x N) xstar := by
    have := hγ01 N hN
    have := hΓpos N hN
    have := hβpos N hN
    have := (hPf (T N) (hTpos N hN)).2
    have := hVnn _ (hmem N).2 _ hxstar
    simp only [hw]
    refine mul_nonneg (div_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg (by linarith) (by linarith))) (by assumption)
  have hΓN := (hΓpos N hN).le
  have e1 : w 1 = β 1 / (1 - P (T 1)) := by simp only [hw, hγ1, hΓ1, one_mul]
  have e2 : M ^ 2 * Γ N / 2 * ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
      γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1)) =
      Γ N * ∑ k ∈ Finset.Icc 1 N, cc k := by
    simp only [hcc, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun i _ => ?_))
    ring
  rw [e2]
  have := mul_le_mul_of_nonneg_left hwN hΓN
  rw [e1] at hfin
  linear_combination hfin + this
