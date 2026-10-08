-- Prove2me | solution 1 for GabayMercier.DualAlgorithm.eq_3_20
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:07:18.168059+00:00
-- url     : https://prove2.me/submissions/0abf9720-02e1-4675-8388-278138c5482e

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

set_option autoImplicit false

open Filter Topology InertialFB.IFB

namespace P2M2618e210

open GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- real value of an extended function at a finite point -/
lemma ereal_eq_coe {x : EReal} (h1 : x ≠ ⊤) (h2 : x ≠ ⊥) : ∃ c : ℝ, x = (c : EReal) :=
  ⟨x.toReal, (EReal.coe_toReal h1 h2).symm⟩

/-- Saddle point consequences. -/
lemma saddle_facts (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∃ c : ℝ, f₂ ys = (c : EReal) ∧ A vs = ys ∧ (∀ w, inner ℝ ls (A w) = b w) ∧
      ∀ z : Y, ∀ cz : ℝ, f₂ z = (cz : EReal) → c + inner ℝ (ls - f₁' ys) (z - ys) ≤ cz := by
  obtain ⟨hbot, z0, hz0⟩ := h.f₂_proper
  -- f₂ ys finite
  have htop : f₂ ys ≠ ⊤ := by
    intro hys
    have h1 := hsp.2 vs z0
    obtain ⟨c0, hc0⟩ := ereal_eq_coe hz0 (hbot z0)
    simp only [lagrangian, hys, hc0, EReal.coe_add_top] at h1
    rw [← EReal.coe_add] at h1
    exact EReal.coe_ne_top _ (top_le_iff.mp h1)
  obtain ⟨c, hc⟩ := ereal_eq_coe htop (hbot ys)
  refine ⟨c, hc, ?_, ?_, ?_⟩
  · -- A vs = ys
    have h1 := hsp.1 (ls + (A vs - ys))
    simp only [lagrangian, hc, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [inner_add_left] at h1
    have : inner ℝ (A vs - ys) (A vs - ys) ≤ 0 := by linarith
    have h0 : A vs - ys = 0 := by
      have := real_inner_self_nonneg (x := A vs - ys)
      exact inner_self_eq_zero.mp (le_antisymm (by linarith) this)
    exact sub_eq_zero.mp h0
  · -- linear part
    have key : ∀ w, inner ℝ ls (A vs) - b vs ≤ inner ℝ ls (A w) - b w := by
      intro w
      have h1 := hsp.2 w ys
      simp only [lagrangian, hc, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      rw [inner_sub_right, inner_sub_right] at h1
      linarith
    intro w
    have h1 := key (vs + w)
    have h2 := key (vs - w)
    simp only [map_add, map_sub, inner_add_right, inner_sub_right] at h1 h2
    linarith
  · -- subgradient
    have hAvs : A vs = ys := by
      have h1 := hsp.1 (ls + (A vs - ys))
      simp only [lagrangian, hc, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      rw [inner_add_left] at h1
      have : inner ℝ (A vs - ys) (A vs - ys) ≤ 0 := by linarith
      have h0 : A vs - ys = 0 := by
        have := real_inner_self_nonneg (x := A vs - ys)
        exact inner_self_eq_zero.mp (le_antisymm (by linarith) this)
      exact sub_eq_zero.mp h0
    -- minimality in z
    have hmin : ∀ z : Y, ∀ cz : ℝ, f₂ z = (cz : EReal) →
        f₁ ys + c ≤ f₁ z + inner ℝ ls (ys - z) + cz := by
      intro z cz hcz
      have h1 := hsp.2 vs z
      simp only [lagrangian, hc, hcz, hAvs, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      simp only [sub_self, inner_zero_right] at h1
      linarith
    intro z cz hcz
    set hd : Y := z - ys with hhd
    set K : ℝ := c - cz + inner ℝ ls hd with hK
    -- K ≤ slope for t ∈ (0,1]
    have hslope : ∀ t : ℝ, 0 < t → t ≤ 1 → K ≤ t⁻¹ * (f₁ (ys + t • hd) - f₁ ys) := by
      intro t ht0 ht1
      have hconv := h.f₂_convex
      have hmem1 : ((ys, c) : Y × ℝ) ∈ {p : Y × ℝ | f₂ p.1 ≤ (p.2 : EReal)} := by
        simp [hc]
      have hmem2 : ((z, cz) : Y × ℝ) ∈ {p : Y × ℝ | f₂ p.1 ≤ (p.2 : EReal)} := by
        simp [hcz]
      have hcomb := hconv hmem1 hmem2 (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      simp only [Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at hcomb
      have hpt : (1 - t) • ys + t • z = ys + t • hd := by
        rw [hhd, smul_sub, sub_smul, one_smul]; abel
      rw [hpt] at hcomb
      have hne : f₂ (ys + t • hd) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hcomb
      obtain ⟨ct, hct⟩ := ereal_eq_coe hne (hbot _)
      rw [hct, EReal.coe_le_coe_iff] at hcomb
      have hm := hmin (ys + t • hd) ct hct
      have hin : inner ℝ ls (ys - (ys + t • hd)) = - t * inner ℝ ls hd := by
        rw [sub_add_cancel_left, inner_neg_right, inner_smul_right]; ring
      rw [hin] at hm
      rw [le_inv_mul_iff₀ ht0]
      nlinarith
    -- derivative along the line
    have hder : HasDerivAt (fun t : ℝ => f₁ (ys + t • hd)) (inner ℝ (f₁' ys) hd) 0 := by
      have hf : HasFDerivAt f₁ (InnerProductSpace.toDual ℝ Y (f₁' ys)) (ys + (0:ℝ) • hd) := by
        simpa using hasGradientAt_iff_hasFDerivAt.mp (h.f₁_hasGradient ys)
      have hl : HasDerivAt (fun t : ℝ => ys + t • hd) hd 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const hd).const_add ys
      have h3 := hf.comp_hasDerivAt (0:ℝ) hl
      simp only [InnerProductSpace.toDual_apply_apply] at h3
      exact h3
    have ht := hder.tendsto_slope_zero_right
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), K ≤ t⁻¹ • ((fun t : ℝ => f₁ (ys + t • hd)) (0 + t) -
        (fun t : ℝ => f₁ (ys + t • hd)) 0) := by
      have : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [this] with t htt
      simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
      exact hslope t htt.1 htt.2.le
    have hle := ge_of_tendsto ht hev
    rw [inner_sub_left]
    linarith

/-- the orthogonal splitting of an inner product -/
lemma inner_split (K : Submodule ℝ Y) [K.HasOrthogonalProjection] (x y : Y) :
    inner ℝ x y = inner ℝ (K.starProjection x) (K.starProjection y)
      + inner ℝ (x - K.starProjection x) (y - K.starProjection y) := by
  have h1 : inner ℝ (K.starProjection x) (y - K.starProjection y) = 0 := by
    rw [real_inner_comm]; exact K.starProjection_inner_eq_zero y _ (K.starProjection_apply_mem x)
  have h2 : inner ℝ (x - K.starProjection x) (K.starProjection y) = 0 :=
    K.starProjection_inner_eq_zero x _ (K.starProjection_apply_mem y)
  have : inner ℝ x y = inner ℝ (K.starProjection x + (x - K.starProjection x))
      (K.starProjection y + (y - K.starProjection y)) := by
    simp only [add_sub_cancel]
  rw [this, inner_add_left, inner_add_right, inner_add_right, h1, h2]
  ring

/-- the final algebra of (3.19) -/
lemma algebra (K : Submodule ℝ Y) [K.HasOrthogonalProjection] (a e d u g : Y) (γ r ρ : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ)
    (F1 : 0 ≤ inner ℝ d e + r * inner ℝ u e - r * inner ℝ e e - inner ℝ g e)
    (F2 : γ * ‖e‖ ^ 2 ≤ inner ℝ g e)
    (F3 : r * inner ℝ u (K.starProjection e)
      - (r * inner ℝ a (K.starProjection e) - inner ℝ d (K.starProjection e)) = 0)
    (F4 : K.starProjection u = u) :
    γ * ‖e‖ ^ 2 + (r - ρ / 2) * ‖e - K.starProjection e‖ ^ 2 + r / 2 * ‖K.starProjection e‖ ^ 2
      + 1 / (2 * ρ) * ‖d + ρ • (u - e) - K.starProjection (d + ρ • (u - e))‖ ^ 2
    ≤ r / 2 * ‖K.starProjection a‖ ^ 2 + 1 / (2 * ρ) * ‖d - K.starProjection d‖ ^ 2 := by
  set P := K.starProjection with hPdef
  have hPP : P (P e) = P e := K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem e)
  have S1 := inner_split K e e
  have S2 := inner_split K d e
  have S3 := inner_split K u e
  have S4 := inner_split K a (P e)
  have S5 := inner_split K d (P e)
  rw [← hPdef] at S1 S2 S3 S4 S5
  rw [hPP, sub_self, inner_zero_right, add_zero] at S4 S5
  rw [F4, sub_self, inner_zero_left, add_zero] at S3
  have hvec : d + ρ • (u - e) - P (d + ρ • (u - e)) = (d - P d) - ρ • (e - P e) := by
    rw [map_add, map_smul, map_sub, F4]; simp only [smul_sub]; abel
  have N1 : ‖d + ρ • (u - e) - P (d + ρ • (u - e))‖ ^ 2
      = ‖d - P d‖ ^ 2 - 2 * ρ * inner ℝ (d - P d) (e - P e) + ρ ^ 2 * ‖e - P e‖ ^ 2 := by
    rw [hvec, norm_sub_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [N1]
  have N2 : 1 / (2 * ρ) * (‖d - P d‖ ^ 2 - 2 * ρ * inner ℝ (d - P d) (e - P e)
      + ρ ^ 2 * ‖e - P e‖ ^ 2) = 1 / (2 * ρ) * ‖d - P d‖ ^ 2 - inner ℝ (d - P d) (e - P e)
      + ρ / 2 * ‖e - P e‖ ^ 2 := by
    field_simp
  rw [N2]
  simp only [← real_inner_self_eq_norm_sq] at F2 ⊢
  have hPa := real_inner_self_nonneg (x := P a - P e)
  rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm (P a) (P e)] at hPa
  have hrPa : r * (2 * inner ℝ (P a) (P e)) ≤ r * (inner ℝ (P a) (P a) + inner ℝ (P e) (P e)) :=
    mul_le_mul_of_nonneg_left (by linarith) hr.le
  have R3 : r * inner ℝ u e = r * inner ℝ u (P e) := by rw [S3]
  have R4 : r * inner ℝ a (P e) = r * inner ℝ (P a) (P e) := by rw [S4]
  have R1 : r * inner ℝ e e = r * inner ℝ (P e) (P e) + r * inner ℝ (e - P e) (e - P e) := by
    rw [S1]; ring
  linarith

/-- (3.19) -/
lemma step (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ n : ℕ,
      γ * ‖y (n + 1) - ys‖ ^ 2
        + (r - ρ / 2) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (y (n + 1) - ys)‖ ^ 2
        + r / 2 * ‖projRange A (y (n + 1) - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam (n + 1) - ls)‖ ^ 2
      ≤ r / 2 * ‖projRange A (y n - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam n - ls)‖ ^ 2 := by
  intro n
  obtain ⟨c, hc, hAvs, hb, hsub⟩ := saddle_facts A f₁ f₁' f₂ b γ α h vs ys ls hsp
  obtain ⟨s1, s2, s3⟩ := hrun n
  set K := (LinearMap.range (A : V →ₗ[ℝ] Y)).topologicalClosure with hKdef
  have hP : ∀ x, projRange A x = K.starProjection x := fun x => rfl
  have hQ : ∀ x, (ContinuousLinearMap.id ℝ Y - projRange A) x = x - K.starProjection x := by
    intro x; simp [hP]
  simp only [hQ, hP]
  set P := K.starProjection with hPdef
  set a := y n - ys with ha
  set e := y (n + 1) - ys with he
  set d := lam n - ls with hd
  set u := A (v (n + 1)) - ys with hu
  set g := f₁' (y (n + 1)) - f₁' ys with hg
  -- F1 monotonicity
  have F1 : 0 ≤ inner ℝ d e + r * inner ℝ u e - r * inner ℝ e e - inner ℝ g e := by
    obtain ⟨hne, hsg⟩ := s2
    obtain ⟨c', hc'⟩ := ereal_eq_coe hne (h.f₂_proper.1 _)
    have h1 := hsg ys
    rw [hc', hc, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    have h2 := hsub (y (n + 1)) c' hc'
    have hv : lam n + r • A (v (n + 1)) - r • y (n + 1) - f₁' (y (n + 1)) - (ls - f₁' ys)
        = d + r • (u - e) - g := by
      simp only [hd, hu, he, hg, smul_sub]; abel
    have hsum : 0 ≤ inner ℝ (lam n + r • A (v (n + 1)) - r • y (n + 1) - f₁' (y (n + 1))
        - (ls - f₁' ys)) e := by
      rw [inner_sub_left]
      have : ys - y (n + 1) = -e := by rw [he]; abel
      rw [this, inner_neg_right] at h1
      linarith
    rw [hv] at hsum
    simp only [inner_sub_left, inner_add_left, inner_smul_left, RCLike.conj_to_real] at hsum
    linarith
  -- F2 strong monotonicity
  have F2 : γ * ‖e‖ ^ 2 ≤ inner ℝ g e := h.strongMono _ _
  -- F3 orthogonality to the range
  have hrange : ∀ w, inner ℝ (r • u - (r • a - d)) (A w) = 0 := by
    intro w
    have h1 := s1 w
    rw [← hb w] at h1
    have h2 : inner ℝ ys (A w) = inner ℝ (A vs) (A w) := by rw [hAvs]
    simp only [hu, ha, hd, inner_sub_left, inner_smul_left, RCLike.conj_to_real] at h1 ⊢
    linarith
  have hKle : K ≤ (innerSL ℝ (r • u - (r • a - d))).ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨w, rfl⟩
      rw [LinearMap.mem_ker]
      exact (innerSL_apply_apply (𝕜 := ℝ) _ _).trans (hrange w)
    · exact ContinuousLinearMap.isClosed_ker _
  have F3 : r * inner ℝ u (P e) - (r * inner ℝ a (P e) - inner ℝ d (P e)) = 0 := by
    have := hKle (K.starProjection_apply_mem e)
    rw [LinearMap.mem_ker] at this
    simp [inner_sub_left, inner_smul_left] at this
    exact this
  -- F4 u in K
  have huK : u ∈ K := by
    apply Submodule.le_topologicalClosure
    refine ⟨v (n + 1) - vs, ?_⟩
    simp [hu, hAvs]
  have F4 : P u = u := K.starProjection_eq_self_iff.mpr huK
  -- F5 multiplier update
  have F5 : lam (n + 1) - ls = d + ρ • (u - e) := by
    rw [s3, hd, hu, he]; simp only [smul_sub]; abel
  rw [F5]
  exact algebra K a e d u g γ r ρ hr hρ F1 F2 F3 F4

end P2M2618e210

open GabayMercier.DualAlgorithm in
theorem solution {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (r ρ : ℝ) (hr : 0 < r)
    (hρ : 0 < ρ) (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (ys ls : Y) (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) :
    ∀ N : ℕ,
      γ * ∑ n ∈ Finset.range (N + 1), ‖y (n + 1) - ys‖ ^ 2
        + (r - ρ / 2) * ∑ n ∈ Finset.range (N + 1),
            ‖(ContinuousLinearMap.id ℝ Y - projRange A) (y (n + 1) - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam (N + 1) - ls)‖ ^ 2
      ≤ r / 2 * ‖projRange A (y 0 - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam 0 - ls)‖ ^ 2 := by
  have hs := P2M2618e210.step A f₁ f₁' f₂ b γ α h r ρ hr hρ v y lam hrun vs ys ls hsp
  have key : ∀ N : ℕ,
      γ * ∑ n ∈ Finset.range (N + 1), ‖y (n + 1) - ys‖ ^ 2
        + (r - ρ / 2) * ∑ n ∈ Finset.range (N + 1),
            ‖(ContinuousLinearMap.id ℝ Y - projRange A) (y (n + 1) - ys)‖ ^ 2
        + r / 2 * ‖projRange A (y (N + 1) - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam (N + 1) - ls)‖ ^ 2
      ≤ r / 2 * ‖projRange A (y 0 - ys)‖ ^ 2
        + 1 / (2 * ρ) * ‖(ContinuousLinearMap.id ℝ Y - projRange A) (lam 0 - ls)‖ ^ 2 := by
    intro N
    induction N with
    | zero => simpa using hs 0
    | succ N ih =>
      rw [Finset.sum_range_succ _ (N + 1), Finset.sum_range_succ _ (N + 1)]
      have := hs (N + 1)
      linarith
  intro N
  have h1 := key N
  have h2 : 0 ≤ r / 2 * ‖projRange A (y (N + 1) - ys)‖ ^ 2 := by positivity
  linarith
