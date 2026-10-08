-- Prove2me | solution 1 for DouglasRachfordPPA.GenDR.generalized_douglas_rachford_convergence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T01:57:46.485001+00:00
-- url     : https://prove2.me/submissions/2cce955e-db83-4e7c-bbea-5f4e097d3ccf

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace ThreeOpSplitting.Convergence
open Filter Topology

namespace DouglasRachfordPPA.GenDR

lemma km_real_ulim {ι : Type*} (f : ι → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ι) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩

lemma km_exists_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (U : Ultrafilter ℕ) :
    ∃ w : H, ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hb : ∀ y k, |inner ℝ (u k) y| ≤ M * ‖y‖ := fun y k =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hex : ∀ y, ∃ a, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 a) :=
    fun y => km_real_ulim _ _ (hb y) U
  set L : H → ℝ := fun y => limUnder (U : Filter ℕ) (fun k => inner ℝ (u k) y) with hL
  have hLt : ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (L y)) :=
    fun y => tendsto_nhds_limUnder (hex y)
  have hadd : ∀ y y', L (y + y') = L y + L y' := by
    intro y y'
    have h1 := hLt (y + y')
    have h2 := (hLt y).add (hLt y')
    simp only [inner_add_right] at h1
    exact tendsto_nhds_unique h1 h2
  have hsmul : ∀ (c : ℝ) y, L (c • y) = c * L y := by
    intro c y
    have h1 := hLt (c • y)
    have h2 := (hLt y).const_mul c
    simp only [real_inner_smul_right] at h1
    exact tendsto_nhds_unique h1 h2
  let Ll : H →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hadd, map_smul' := fun c y => by simp [hsmul] }
  have hbd : ∀ y, ‖Ll y‖ ≤ M * ‖y‖ := by
    intro y
    show |L y| ≤ M * ‖y‖
    have := (hLt y)
    have hmem : ∀ᶠ k in (U : Filter ℕ), inner ℝ (u k) y ∈ Set.Icc (-(M * ‖y‖)) (M * ‖y‖) :=
      Filter.Eventually.of_forall (fun k => abs_le.1 (hb y k))
    exact abs_le.2 (isClosed_Icc.mem_of_tendsto this hmem)
  let Lc : StrongDual ℝ H := Ll.mkContinuous M hbd
  refine ⟨(InnerProductSpace.toDual ℝ H).symm Lc, fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  exact hLt y

lemma km_weak_of_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (w0 : H)
    (h : ∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop → ∀ w : H,
      (∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y))) → w = w0) :
    WeakTendsto u w0 := by
  intro y
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨w, hw⟩ := km_exists_ulim u M hM U
  have := h U hU w hw
  subst this
  exact hw y

lemma km_demiclosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → H) (hT : ∀ u v, ‖T u - T v‖ ≤ ‖u - v‖) (z : ℕ → H) (M : ℝ)
    (hM : ∀ k, ‖z k‖ ≤ M)
    (hr : Tendsto (fun k => ‖T (z k) - z k‖) atTop (𝓝 0)) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (w : H)
    (hw : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U (𝓝 (inner ℝ w y))) : T w = w := by
  set d := w - T w with hd
  have key : ∀ k, ‖d‖ ^ 2 + 2 * (inner ℝ (z k) d - inner ℝ w d) ≤
      ‖T (z k) - z k‖ ^ 2 + 2 * ‖T (z k) - z k‖ * (M + ‖w‖) := by
    intro k
    have e1 : z k - T w = (z k - T (z k)) + (T (z k) - T w) := by abel
    have h1 : ‖z k - T w‖ ≤ ‖T (z k) - z k‖ + ‖z k - w‖ := by
      rw [e1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_sub_rev (z k) (T (z k))]
      linarith [hT (z k) w]
    have e2 : z k - T w = (z k - w) + d := by rw [hd]; abel
    have h2 : ‖z k - T w‖ ^ 2 = ‖z k - w‖ ^ 2 + 2 * inner ℝ (z k - w) d + ‖d‖ ^ 2 := by
      rw [e2, norm_add_sq_real]
    have h3 : ‖z k - w‖ ≤ M + ‖w‖ := (norm_sub_le _ _).trans (by linarith [hM k])
    have h0 : 0 ≤ ‖z k - T w‖ := norm_nonneg _
    have hsq : ‖z k - T w‖ ^ 2 ≤ (‖T (z k) - z k‖ + ‖z k - w‖) ^ 2 :=
      pow_le_pow_left₀ h0 h1 2
    rw [inner_sub_left] at h2
    have hr0 : 0 ≤ ‖T (z k) - z k‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 hr0]
  have hL : Tendsto (fun k => ‖d‖ ^ 2 + 2 * (inner ℝ (z k) d - inner ℝ w d)) U
      (𝓝 (‖d‖ ^ 2 + 2 * (inner ℝ w d - inner ℝ w d))) :=
    tendsto_const_nhds.add ((hw d).sub tendsto_const_nhds |>.const_mul 2)
  have hR : Tendsto (fun k => ‖T (z k) - z k‖ ^ 2 + 2 * ‖T (z k) - z k‖ * (M + ‖w‖)) U
      (𝓝 (0 ^ 2 + 2 * 0 * (M + ‖w‖))) := by
    have := hr.mono_left hU
    exact (this.pow 2).add ((this.const_mul 2).mul_const _)
  have hle := le_of_tendsto_of_tendsto' hL hR key
  simp only [sub_self, mul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul] at hle
  have : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
  rw [norm_eq_zero, hd, sub_eq_zero] at this
  exact this.symm

lemma km_opial_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z : ℕ → H) (w1 w2 : H) (U1 U2 : Ultrafilter ℕ)
    (h1 : (U1 : Filter ℕ) ≤ atTop) (h2 : (U2 : Filter ℕ) ≤ atTop)
    (hw1 : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U1 (𝓝 (inner ℝ w1 y)))
    (hw2 : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U2 (𝓝 (inner ℝ w2 y)))
    (hc1 : ∃ d, Tendsto (fun k => ‖z k - w1‖) atTop (𝓝 d))
    (hc2 : ∃ d, Tendsto (fun k => ‖z k - w2‖) atTop (𝓝 d)) : w1 = w2 := by
  obtain ⟨d1, hd1⟩ := hc1
  obtain ⟨d2, hd2⟩ := hc2
  set v := w1 - w2 with hv
  have hg : Tendsto (fun k => ‖z k - w2‖ ^ 2 - ‖z k - w1‖ ^ 2) atTop (𝓝 (d2 ^ 2 - d1 ^ 2)) :=
    (hd2.pow 2).sub (hd1.pow 2)
  have hid : ∀ k, ‖z k - w2‖ ^ 2 - ‖z k - w1‖ ^ 2 =
      2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2 := by
    intro k
    have e : z k - w2 = (z k - w1) + v := by rw [hv]; abel
    rw [e, norm_add_sq_real, inner_sub_left]; ring
  simp only [hid] at hg
  have g1 : Tendsto (fun k => 2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2) U1
      (𝓝 (2 * inner ℝ w1 v - 2 * inner ℝ w1 v + ‖v‖ ^ 2)) :=
    (((hw1 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have g2 : Tendsto (fun k => 2 * inner ℝ (z k) v - 2 * inner ℝ w1 v + ‖v‖ ^ 2) U2
      (𝓝 (2 * inner ℝ w2 v - 2 * inner ℝ w1 v + ‖v‖ ^ 2)) :=
    (((hw2 v).const_mul 2).sub tendsto_const_nhds).add tendsto_const_nhds
  have e1 := tendsto_nhds_unique g1 (hg.mono_left h1)
  have e2 := tendsto_nhds_unique g2 (hg.mono_left h2)
  have e3 : inner ℝ w2 v - inner ℝ w1 v = -‖v‖ ^ 2 := by
    rw [← inner_sub_left, ← real_inner_self_eq_norm_sq, hv, ← inner_neg_left, neg_sub]
  have : ‖v‖ ^ 2 = 0 := by nlinarith
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  rw [norm_eq_zero, hv, sub_eq_zero] at this
  exact this

lemma km_conv_of_incr (u w : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hw0 : ∀ n, 0 ≤ w n)
    (hw : Summable w) (h : ∀ n, u (n + 1) ≤ u n + w n) : ∃ l, Tendsto u atTop (𝓝 l) := by
  set g : ℕ → ℝ := fun n => u n - ∑ i ∈ Finset.range n, w i with hg
  have hanti : Antitone g := by
    apply antitone_nat_of_succ_le
    intro n; simp only [hg, Finset.sum_range_succ]; linarith [h n]
  have hbdd : BddBelow (Set.range g) := by
    refine ⟨-(∑' i, w i), ?_⟩
    rintro _ ⟨n, rfl⟩
    have := hw.sum_le_tsum (Finset.range n) (fun i _ => hw0 i)
    simp only [hg]; linarith [hu n]
  have hgt := tendsto_atTop_ciInf hanti hbdd
  have hst := hw.hasSum.tendsto_sum_nat
  refine ⟨_, (hgt.add hst).congr (fun n => ?_)⟩
  simp only [hg]; ring

lemma km_convex_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • u + t • v‖ ^ 2 = (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, norm_sub_sq_real, inner_smul_left, inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg (by linarith : 0 ≤ 1 - t),
    RCLike.conj_to_real]
  ring

lemma km_err_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x e : H) :
    ‖x + e‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖e‖ * (2 * ‖x‖ + ‖e‖) := by
  have h := norm_add_le x e
  have h0 := norm_nonneg (x + e)
  nlinarith [norm_nonneg x, norm_nonneg e]

/-- The relaxed step against a fixed point `p`, and against `N c`. -/
lemma km_y_fix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : H → H) (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (z p : H) (hp : N p = p) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((1 - t) • z + t • N z) - p‖ ^ 2 ≤ ‖z - p‖ ^ 2 - t * (1 - t) * ‖z - N z‖ ^ 2 := by
  have e : ((1 - t) • z + t • N z) - p = (1 - t) • (z - p) + t • (N z - p) := by module
  rw [e, km_convex_sq _ _ t ht0 ht1]
  have h1 : ‖N z - p‖ ≤ ‖z - p‖ := by have := hN z p; rwa [hp] at this
  have h2 : ‖N z - p‖ ^ 2 ≤ ‖z - p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 : (z - p) - (N z - p) = z - N z := by abel
  rw [e2]
  nlinarith

lemma km_y_Nc {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : H → H) (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (z c : H) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((1 - t) • z + t • N z) - N c‖ ^ 2 ≤ (1 - t) * ‖z - N c‖ ^ 2 + t * ‖z - c‖ ^ 2 := by
  have e : ((1 - t) • z + t • N z) - N c = (1 - t) • (z - N c) + t • (N z - N c) := by module
  rw [e, km_convex_sq _ _ t ht0 ht1]
  have h2 : ‖N z - N c‖ ^ 2 ≤ ‖z - c‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hN z c) 2
  have : 0 ≤ t * (1 - t) * ‖z - N c - (N z - N c)‖ ^ 2 :=
    mul_nonneg (mul_nonneg ht0 (by linarith)) (sq_nonneg _)
  nlinarith

lemma km_y_Nc_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : H → H) (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (z c : H) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((1 - t) • z + t • N z) - N c‖ ≤ ‖z‖ + ‖N c‖ + ‖c‖ := by
  have e : ((1 - t) • z + t • N z) - N c = (1 - t) • (z - N c) + t • (N z - N c) := by module
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0,
    abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
  have h1 : ‖z - N c‖ ≤ ‖z‖ + ‖N c‖ := norm_sub_le _ _
  have h2 : ‖N z - N c‖ ≤ ‖z‖ + ‖c‖ := (hN z c).trans (norm_sub_le _ _)
  have := norm_nonneg c
  have := norm_nonneg (N c)
  nlinarith

section KMSetup
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem km_weak [CompleteSpace H]
    (N : H → H) (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (t : ℕ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : b < 1) (ht : ∀ k, a ≤ t k ∧ t k ≤ b) (z : ℕ → H) (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hεs : Summable ε) (hz : ∀ k, ‖z (k + 1) - ((1 - t k) • z k + t k • N (z k))‖ ≤ ε k)
    (hfix : ∃ p, N p = p) : ∃ w, N w = w ∧ WeakTendsto z w := by
  have ht0 : ∀ k, 0 ≤ t k := fun k => ha.le.trans (ht k).1
  have ht1 : ∀ k, t k ≤ 1 := fun k => (ht k).2.trans hb.le
  set y : ℕ → H := fun k => (1 - t k) • z k + t k • N (z k)
  have hstep : ∀ p, ∀ k, ‖z (k + 1) - p‖ ≤ ‖y k - p‖ + ε k := by
    intro p k
    have e : z (k + 1) - p = (z (k + 1) - y k) + (y k - p) := by abel
    rw [e]; refine (norm_add_le _ _).trans ?_; linarith [hz k]
  have hyp : ∀ p, N p = p → ∀ k, ‖y k - p‖ ^ 2 ≤ ‖z k - p‖ ^ 2 - t k * (1 - t k) * ‖z k - N (z k)‖ ^ 2 :=
    fun p hp k => km_y_fix N hN (z k) p hp (t k) (ht0 k) (ht1 k)
  have hyp' : ∀ p, N p = p → ∀ k, ‖y k - p‖ ≤ ‖z k - p‖ := by
    intro p hp k
    have h := hyp p hp k
    have : 0 ≤ t k * (1 - t k) * ‖z k - N (z k)‖ ^ 2 :=
      mul_nonneg (mul_nonneg (ht0 k) (by linarith [ht1 k])) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  have hconv : ∀ p, N p = p → ∃ l, Tendsto (fun k => ‖z k - p‖) atTop (𝓝 l) := by
    intro p hp
    exact km_conv_of_incr _ ε (fun _ => norm_nonneg _) hε0 hεs
      (fun k => (hstep p k).trans (by linarith [hyp' p hp k]))
  obtain ⟨p0, hp0⟩ := hfix
  obtain ⟨l0, hl0⟩ := hconv p0 hp0
  obtain ⟨R, hR⟩ : ∃ R, ∀ k, ‖z k - p0‖ ≤ R := by
    obtain ⟨R, hR⟩ := hl0.bddAbove_range
    exact ⟨R, fun k => hR (Set.mem_range_self k)⟩
  have hM : ∀ k, ‖z k‖ ≤ R + ‖p0‖ := fun k => by
    have : z k = (z k - p0) + p0 := by abel
    rw [this]; exact (norm_add_le _ _).trans (by linarith [hR k])
  -- residual
  have hres : Tendsto (fun k => ‖N (z k) - z k‖) atTop (𝓝 0) := by
    set D := fun k => ‖z k - p0‖
    have hε : Tendsto ε atTop (𝓝 0) := hεs.tendsto_atTop_zero
    have hkey : ∀ k, a * (1 - b) * ‖N (z k) - z k‖ ^ 2 ≤
        D k ^ 2 - D (k + 1) ^ 2 + ε k * (2 * D k + ε k) := by
      intro k
      have h1 := hstep p0 k
      have h2 := hyp p0 hp0 k
      have h3 := hyp' p0 hp0 k
      have hD : 0 ≤ D (k + 1) := norm_nonneg _
      have hsq : D (k + 1) ^ 2 ≤ (‖y k - p0‖ + ε k) ^ 2 := pow_le_pow_left₀ hD h1 2
      have htt : a * (1 - b) ≤ t k * (1 - t k) := by
        have := ht k; nlinarith
      have hr : ‖N (z k) - z k‖ = ‖z k - N (z k)‖ := norm_sub_rev _ _
      rw [hr]
      have hyn := norm_nonneg (y k - p0)
      have := hε0 k
      have hrr := sq_nonneg ‖z k - N (z k)‖
      simp only [D] at *
      nlinarith [mul_le_mul_of_nonneg_right htt hrr]
    have hlimR : Tendsto (fun k => (D k ^ 2 - D (k + 1) ^ 2 + ε k * (2 * D k + ε k)) / (a * (1 - b)))
        atTop (𝓝 ((l0 ^ 2 - l0 ^ 2 + 0 * (2 * l0 + 0)) / (a * (1 - b)))) := by
      refine Tendsto.div_const ?_ _
      exact ((hl0.pow 2).sub ((hl0.comp (tendsto_add_atTop_nat 1)).pow 2)).add
        (hε.mul ((hl0.const_mul 2).add hε))
    simp only [sub_self, zero_mul, add_zero, zero_div] at hlimR
    have hab : 0 < a * (1 - b) := mul_pos ha (by linarith)
    have hsq : Tendsto (fun k => ‖N (z k) - z k‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) hlimR
      rw [le_div_iff₀ hab, mul_comm]; exact hkey k
    have := hsq.sqrt
    simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at this
    exact this
  set U0 : Ultrafilter ℕ := Ultrafilter.of (atTop : Filter ℕ)
  have hU0 : (U0 : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨w0, hw0⟩ := km_exists_ulim z _ hM U0
  have hw0fix : N w0 = w0 := km_demiclosed N hN z _ hM hres U0 hU0 w0 hw0
  refine ⟨w0, hw0fix, ?_⟩
  apply km_weak_of_ulim z _ hM w0
  intro U hU w hw
  have hwfix : N w = w := km_demiclosed N hN z _ hM hres U hU w hw
  exact km_opial_unique z w w0 U U0 hU hU0 hw hw0 (hconv w hwfix) (hconv w0 hw0fix)

lemma km_ls_up (u : ℕ → ℝ) (B : ℝ) (hB : ∀ k, u k ≤ B) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k in atTop, u k < Filter.limsup u atTop + δ :=
  Filter.eventually_lt_of_limsup_lt (by linarith) (isBoundedUnder_of ⟨B, hB⟩)

lemma km_ls_low (u : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ u k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ᶠ k in atTop, Filter.limsup u atTop - δ < u k :=
  Filter.frequently_lt_of_lt_limsup (isCoboundedUnder_le_of_le atTop hB0) (by linarith)

theorem km_bdd_fix [CompleteSpace H]
    (N : H → H) (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (t : ℕ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hb : b < 1) (ht : ∀ k, a ≤ t k ∧ t k ≤ b) (z : ℕ → H) (ε : ℕ → ℝ) (hε0 : ∀ k, 0 ≤ ε k)
    (hεs : Summable ε) (hz : ∀ k, ‖z (k + 1) - ((1 - t k) • z k + t k • N (z k))‖ ≤ ε k)
    (M : ℝ) (hM : ∀ k, ‖z k‖ ≤ M) : ∃ p, N p = p := by
  have ht0 : ∀ k, 0 ≤ t k := fun k => ha.le.trans (ht k).1
  have ht1 : ∀ k, t k ≤ 1 := fun k => (ht k).2.trans hb.le
  set G : H → ℝ := fun y => Filter.limsup (fun k => ‖z k - y‖ ^ 2) atTop with hG
  have hbd : ∀ y k, ‖z k - y‖ ^ 2 ≤ (M + ‖y‖) ^ 2 := fun y k =>
    pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hM k])) 2
  have up : ∀ y δ, 0 < δ → ∀ᶠ k in atTop, ‖z k - y‖ ^ 2 < G y + δ :=
    fun y δ hδ => km_ls_up _ _ (hbd y) δ hδ
  have low : ∀ y δ, 0 < δ → ∃ᶠ k in atTop, G y - δ < ‖z k - y‖ ^ 2 :=
    fun y δ hδ => km_ls_low _ (fun k => sq_nonneg _) δ hδ
  have Gnn : ∀ y, 0 ≤ G y := by
    intro y
    by_contra h; push_neg at h
    obtain ⟨k, hk⟩ := (up y (-G y / 2) (by linarith)).exists
    nlinarith [sq_nonneg ‖z k - y‖]
  -- generic: from `∀ δ>0, X ≤ Y + δ` get `X ≤ Y`
  have le_of_all : ∀ X Y : ℝ, (∀ δ, 0 < δ → X ≤ Y + δ) → X ≤ Y := by
    intro X Y h
    by_contra hc; push_neg at hc
    have := h ((X - Y) / 2) (by linarith); linarith
  -- parallelogram
  have par : ∀ y1 y2 : H, G ((1/2:ℝ) • (y1 + y2)) ≤ (1/2) * G y1 + (1/2) * G y2
      - (1/4) * ‖y1 - y2‖ ^ 2 := by
    intro y1 y2
    apply le_of_all
    intro δ hδ
    obtain ⟨k, hk1, hk2, hk3⟩ :=
      ((low ((1/2:ℝ) • (y1 + y2)) (δ/2) (by linarith)).and_eventually
        ((up y1 (δ/2) (by linarith)).and (up y2 (δ/2) (by linarith)))).exists
    have hid : ‖z k - (1/2:ℝ) • (y1 + y2)‖ ^ 2 = (1/2) * ‖z k - y1‖ ^ 2 + (1/2) * ‖z k - y2‖ ^ 2
        - (1/4) * ‖y1 - y2‖ ^ 2 := by
      have e1 : z k - (1/2:ℝ) • (y1 + y2) = (1/2:ℝ) • ((z k - y1) + (z k - y2)) := by module
      have e2 : y1 - y2 = (z k - y2) - (z k - y1) := by abel
      rw [e1, e2]
      generalize z k - y1 = u
      generalize z k - y2 = v
      rw [norm_smul, mul_pow, norm_add_sq_real, norm_sub_sq_real, real_inner_comm v u]
      norm_num; ring
    linarith
  -- Lipschitz-type bound
  have lip : ∀ y y' : H, G y ≤ G y' + ‖y - y'‖ * (2 * M + 3 * ‖y‖ + 3 * ‖y'‖) := by
    intro y y'
    apply le_of_all
    intro δ hδ
    obtain ⟨k, hk1, hk2⟩ := ((low y (δ/2) (by linarith)).and_eventually
      (up y' (δ/2) (by linarith))).exists
    have hid : ‖z k - y‖ ^ 2 ≤ ‖z k - y'‖ ^ 2 + ‖y - y'‖ * (2 * M + 3 * ‖y‖ + 3 * ‖y'‖) := by
      have e : z k - y = (z k - y') - (y - y') := by abel
      rw [e, norm_sub_sq_real]
      have h1 : ⟪z k - y', y - y'⟫_ℝ ≥ -(‖z k - y'‖ * ‖y - y'‖) := by
        have := abs_real_inner_le_norm (z k - y') (y - y'); linarith [neg_abs_le ⟪z k - y', y - y'⟫_ℝ]
      have h2 : ‖z k - y'‖ ≤ M + ‖y'‖ := (norm_sub_le _ _).trans (by linarith [hM k])
      have h3 : ‖y - y'‖ ≤ ‖y‖ + ‖y'‖ := norm_sub_le _ _
      have := norm_nonneg (y - y')
      nlinarith [mul_le_mul_of_nonneg_left h2 this, mul_le_mul_of_nonneg_left h3 this, norm_nonneg y, norm_nonneg y']
    linarith
  -- G (N c) ≤ G c
  have hε : Tendsto ε atTop (𝓝 0) := hεs.tendsto_atTop_zero
  have hNc : ∀ c, G (N c) ≤ G c := by
    intro c
    by_contra hcon; push_neg at hcon
    set γ := G (N c) - G c
    have hγ : 0 < γ := by simp only [γ]; linarith
    set η := a * γ / 4
    have hη : 0 < η := by positivity
    set R := M + ‖N c‖ + ‖c‖
    have hδ : Tendsto (fun k => ε k * (2 * R + ε k)) atTop (𝓝 0) := by
      have := hε.mul ((tendsto_const_nhds (x := 2 * R)).add hε); simpa using this
    have hrec : ∀ k, ‖z (k + 1) - N c‖ ^ 2 ≤ (1 - t k) * ‖z k - N c‖ ^ 2 + t k * ‖z k - c‖ ^ 2
        + ε k * (2 * R + ε k) := by
      intro k
      set yk := (1 - t k) • z k + t k • N (z k)
      have e : z (k + 1) - N c = (yk - N c) + (z (k + 1) - yk) := by abel
      have h1 := km_err_sq (yk - N c) (z (k + 1) - yk)
      have h2 := km_y_Nc N hN (z k) c (t k) (ht0 k) (ht1 k)
      have h3 := km_y_Nc_norm N hN (z k) c (t k) (ht0 k) (ht1 k)
      have h4 := hz k
      have h5 : ‖yk - N c‖ ≤ R := h3.trans (by simp only [R]; linarith [hM k])
      rw [e]
      have := norm_nonneg (z (k + 1) - yk)
      have := norm_nonneg (yk - N c)
      have := hε0 k
      nlinarith [mul_le_mul h4 (by linarith : 2 * ‖yk - N c‖ + ‖z (k + 1) - yk‖ ≤ 2 * R + ε k)
        (by positivity) (hε0 k)]
    have hev := ((up (N c) η hη).and (up c η hη)).and (hδ.eventually (gt_mem_nhds hη))
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 hev
    obtain ⟨j, hj, hjv⟩ := Filter.frequently_atTop.1 (low (N c) η hη) (K + 1)
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hk := hK k (by omega)
    have hr := hrec k
    have hta := (ht k).1
    have ht1k := ht1 k
    obtain ⟨⟨hA, hB⟩, hD⟩ := hk
    have hA' : (1 - t k) * ‖z k - N c‖ ^ 2 ≤ (1 - t k) * (G (N c) + η) :=
      mul_le_mul_of_nonneg_left hA.le (by linarith)
    have hB' : t k * ‖z k - c‖ ^ 2 ≤ t k * (G c + η) :=
      mul_le_mul_of_nonneg_left hB.le (ht0 k)
    have hγa : a * γ ≤ t k * γ := mul_le_mul_of_nonneg_right hta hγ.le
    simp only [γ, η] at *
    nlinarith
  -- existence of a minimizer of G
  have hbddG : BddBelow (Set.range G) := ⟨0, by rintro _ ⟨y, rfl⟩; exact Gnn y⟩
  set m := ⨅ y, G y
  have hmle : ∀ y, m ≤ G y := fun y => ciInf_le hbddG y
  have hseq : ∀ n : ℕ, ∃ y, G y < m + 1 / ((n:ℝ) + 1) := fun n =>
    exists_lt_of_ciInf_lt (by have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
                              linarith)
  choose ys hys using hseq
  have hcl : ∀ n k, ‖ys n - ys k‖ ^ 2 ≤ 2 * (1 / ((n:ℝ) + 1) + 1 / ((k:ℝ) + 1)) := by
    intro n k
    have h1 := par (ys n) (ys k)
    have h2 := hmle ((1/2:ℝ) • (ys n + ys k))
    have := hys n; have := hys k
    nlinarith
  have hcauchy : CauchySeq ys := by
    rw [Metric.cauchySeq_iff']
    intro e he
    obtain ⟨N0, hN0⟩ := exists_nat_gt (4 / e ^ 2)
    refine ⟨N0, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have h := hcl n N0
    have hn' : 1 / ((n:ℝ) + 1) ≤ 1 / ((N0:ℝ) + 1) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (N0:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hN1 : 4 / ((N0:ℝ) + 1) < e ^ 2 := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ (by positivity)] at hN0
      nlinarith
    have : ‖ys n - ys N0‖ ^ 2 < e ^ 2 := by
      have : 4 / ((N0:ℝ) + 1) = 4 * (1 / ((N0:ℝ) + 1)) := by ring
      nlinarith
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) he.le two_ne_zero).1 this
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  obtain ⟨Kb, hKb⟩ : ∃ Kb, ∀ n, ‖ys n‖ ≤ Kb := by
    obtain ⟨Kb, hKb⟩ := hc.norm.bddAbove_range
    exact ⟨Kb, fun n => hKb (Set.mem_range_self n)⟩
  have hGc : G c ≤ m := by
    have hlim : Tendsto (fun n : ℕ => m + 1 / ((n:ℝ) + 1) + ‖c - ys n‖ * (2 * M + 3 * ‖c‖ + 3 * Kb))
        atTop (𝓝 (m + 0 + 0 * (2 * M + 3 * ‖c‖ + 3 * Kb))) := by
      refine (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat).add ?_
      refine Tendsto.mul_const _ ?_
      have := (tendsto_const_nhds (x := c)).sub hc
      simpa using this.norm
    simp only [add_zero, zero_mul] at hlim
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    have h1 := lip c (ys n)
    have h2 := hys n
    have h3 : ‖c - ys n‖ * (2 * M + 3 * ‖c‖ + 3 * ‖ys n‖) ≤ ‖c - ys n‖ * (2 * M + 3 * ‖c‖ + 3 * Kb) :=
      mul_le_mul_of_nonneg_left (by linarith [hKb n]) (norm_nonneg _)
    linarith
  refine ⟨c, ?_⟩
  have h1 := hNc c
  have h2 := par c (N c)
  have h3 := hmle ((1/2:ℝ) • (c + N c))
  have h4 := hmle c
  have h5 : ‖c - N c‖ ^ 2 ≤ 0 := by nlinarith
  have h6 : ‖c - N c‖ = 0 := by
    have := sq_nonneg ‖c - N c‖
    exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm h5 this)
  exact (sub_eq_zero.1 (norm_eq_zero.1 h6)).symm

end KMSetup

section DR
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma dr_res_fne (A : H → Set H) (hA : IsMonotoneOp A) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam A J) (x y : H) : ‖J x - J y‖ ^ 2 ≤ ⟪J x - J y, x - y⟫_ℝ := by
  have h := hA _ _ _ _ (hJ x) (hJ y)
  rw [← smul_sub, inner_smul_right] at h
  have e : (x - J x) - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h
  have := inv_pos.2 hlam
  nlinarith

lemma dr_res_nonexp (A : H → Set H) (hA : IsMonotoneOp A) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam A J) (x y : H) : ‖J x - J y‖ ≤ ‖x - y‖ := by
  have h := dr_res_fne A hA lam hlam J hJ x y
  have h2 := real_inner_le_norm (J x - J y) (x - y)
  rcases (norm_nonneg (J x - J y)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

lemma dr_refl_nonexp (A : H → Set H) (hA : IsMonotoneOp A) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam A J) (x y : H) :
    ‖((2:ℝ) • J x - x) - ((2:ℝ) • J y - y)‖ ≤ ‖x - y‖ := by
  have h := dr_res_fne A hA lam hlam J hJ x y
  have e : ((2:ℝ) • J x - x) - ((2:ℝ) • J y - y) = (2:ℝ) • (J x - J y) - (x - y) := by module
  have hsq : ‖((2:ℝ) • J x - x) - ((2:ℝ) • J y - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e, norm_sub_sq_real, norm_smul, inner_smul_left, mul_pow, RCLike.conj_to_real]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

lemma dr_res_eq (B : H → Set H) (hB : IsMonotoneOp B) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam B J) (u b : H) (hb : b ∈ B u) : J (u + lam • b) = u := by
  set z := u + lam • b
  have h := hB _ _ _ _ (hJ z) hb
  have e : lam⁻¹ • (z - J z) - b = lam⁻¹ • (u - J z) := by
    simp only [z]
    rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hlam.ne', one_smul]; abel
  rw [e, inner_smul_right, ← neg_sub u (J z), inner_neg_left, real_inner_self_eq_norm_sq] at h
  have hl := inv_pos.2 hlam
  have h2 : ‖u - J z‖ ^ 2 ≤ 0 := by nlinarith
  have h3 : ‖u - J z‖ = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.1
    (le_antisymm h2 (sq_nonneg _))
  exact (sub_eq_zero.1 (norm_eq_zero.1 h3)).symm

lemma dr_fix_iff (A B : H → Set H) (hA : IsMonotoneOp A) (hB : IsMonotoneOp B)
    (lam : ℝ) (hlam : 0 < lam) (JA JB : H → H) (hJA : IsResolvent lam A JA)
    (hJB : IsResolvent lam B JB) (z : H) :
    (2:ℝ) • drMap JA JB z - z = z ↔ z ∈ Zstar lam A B := by
  have hfix : (2:ℝ) • drMap JA JB z - z = z ↔ JA ((2:ℝ) • JB z - z) = JB z := by
    simp only [drMap]
    constructor
    · intro h
      have : (2:ℝ) • (JA ((2:ℝ) • JB z - z) - JB z) = 0 := by
        rw [← sub_eq_zero] at h; rw [← h]; module
      have := (smul_eq_zero.1 this).resolve_left two_ne_zero
      exact sub_eq_zero.1 this
    · intro h; rw [h]; module
  rw [hfix]
  constructor
  · intro h
    refine ⟨JB z, lam⁻¹ • (z - JB z), hJB z, ?_, ?_⟩
    · have hA' := hJA ((2:ℝ) • JB z - z)
      rw [h] at hA'
      have e : lam⁻¹ • ((2:ℝ) • JB z - z - JB z) = -(lam⁻¹ • (z - JB z)) := by module
      rw [← e]; exact hA'
    · rw [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]; abel
  · rintro ⟨u, b, hb, hnb, rfl⟩
    have h1 : JB (u + lam • b) = u := dr_res_eq B hB lam hlam JB hJB u b hb
    rw [h1]
    have e : (2:ℝ) • u - (u + lam • b) = u + lam • (-b) := by module
    rw [e]
    exact dr_res_eq A hA lam hlam JA hJA u (-b) hnb

theorem dr_core [CompleteSpace H]
    (A B : H → Set H) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (lam : ℝ) (hlam : 0 < lam)
    (JA JB : H → H) (hJA : IsResolvent lam A JA) (hJB : IsResolvent lam B JB)
    (z u v : ℕ → H) (α β ρ : ℕ → ℝ)
    (hT1 : ∀ k, ‖u k - JB (z k)‖ ≤ β k)
    (hT2 : ∀ k, ‖v (k + 1) - JA ((2 : ℝ) • u k - z k)‖ ≤ α k)
    (hT3 : ∀ k, z (k + 1) = z k + ρ k • (v (k + 1) - u k))
    (hα_nonneg : ∀ k, 0 ≤ α k) (hβ_nonneg : ∀ k, 0 ≤ β k)
    (hα_sum : Summable α) (hβ_sum : Summable β)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂) :
    ((zer (opAdd A B)).Nonempty → ∃ zs ∈ Zstar lam A B, WeakTendsto z zs) ∧
    (zer (opAdd A B) = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hρk⟩ := hρ
  set N : H → H := fun x => (2:ℝ) • drMap JA JB x - x with hNdef
  have hNe : ∀ x, N x = (2:ℝ) • JA ((2:ℝ) • JB x - x) - ((2:ℝ) • JB x - x) := by
    intro x; simp only [hNdef, drMap]; module
  have hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖ := by
    intro x y
    rw [hNe, hNe]
    exact (dr_refl_nonexp A hA.1 lam hlam JA hJA _ _).trans
      (dr_refl_nonexp B hB.1 lam hlam JB hJB x y)
  set t : ℕ → ℝ := fun k => ρ k / 2
  set ε : ℕ → ℝ := fun k => 2 * (α k + 3 * β k)
  have ht : ∀ k, ρ₁ / 2 ≤ t k ∧ t k ≤ ρ₂ / 2 := fun k =>
    ⟨by simp only [t]; linarith [(hρk k).1], by simp only [t]; linarith [(hρk k).2]⟩
  have hε0 : ∀ k, 0 ≤ ε k := fun k => by
    simp only [ε]; linarith [hα_nonneg k, hβ_nonneg k]
  have hεs : Summable ε := (hα_sum.add (hβ_sum.mul_left 3)).mul_left 2
  have hz : ∀ k, ‖z (k + 1) - ((1 - t k) • z k + t k • N (z k))‖ ≤ ε k := by
    intro k
    have e : z (k + 1) - ((1 - t k) • z k + t k • N (z k)) =
        ρ k • ((v (k + 1) - JA ((2:ℝ) • u k - z k))
          + (JA ((2:ℝ) • u k - z k) - JA ((2:ℝ) • JB (z k) - z k))
          + (JB (z k) - u k)) := by
      rw [hT3, hNe]; simp only [t]; module
    rw [e, norm_smul, Real.norm_eq_abs]
    have hρ0 : 0 ≤ ρ k := hρ₁.le.trans (hρk k).1
    have hρ2 : ρ k ≤ 2 := ((hρk k).2.trans hρ₂.le)
    rw [abs_of_nonneg hρ0]
    have h1 := hT2 k
    have h2 : ‖JA ((2:ℝ) • u k - z k) - JA ((2:ℝ) • JB (z k) - z k)‖ ≤ 2 * β k := by
      refine (dr_res_nonexp A hA.1 lam hlam JA hJA _ _).trans ?_
      have : ((2:ℝ) • u k - z k) - ((2:ℝ) • JB (z k) - z k) = (2:ℝ) • (u k - JB (z k)) := by module
      rw [this, norm_smul]; norm_num; exact hT1 k
    have h3 : ‖JB (z k) - u k‖ ≤ β k := by rw [norm_sub_rev]; exact hT1 k
    set P := v (k + 1) - JA ((2:ℝ) • u k - z k)
    set Q := JA ((2:ℝ) • u k - z k) - JA ((2:ℝ) • JB (z k) - z k)
    set R := JB (z k) - u k
    have hsum : ‖P + Q + R‖ ≤ α k + 3 * β k := by
      have := norm_add_le (P + Q) R
      have := norm_add_le P Q
      linarith
    simp only [ε]
    have := norm_nonneg (P + Q + R)
    nlinarith
  have hfixiff := dr_fix_iff A B hA.1 hB.1 lam hlam JA JB hJA hJB
  have ha : 0 < ρ₁ / 2 := by linarith
  have hb : ρ₂ / 2 < 1 := by linarith
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨a', ha', b', hb', h0⟩ := hx
    have hmem : x + lam • b' ∈ Zstar lam A B := by
      refine ⟨x, b', hb', ?_, rfl⟩
      have : -b' = a' := (eq_neg_of_add_eq_zero_left h0.symm).symm
      rw [this]; exact ha'
    obtain ⟨w, hw, hwk⟩ := km_weak N hN t (ρ₁ / 2) (ρ₂ / 2) ha hb ht z ε hε0 hεs hz
      ⟨_, (hfixiff _).2 hmem⟩
    exact ⟨w, (hfixiff w).1 hw, hwk⟩
  · intro hzer hbdd
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hbdd
    obtain ⟨p, hp⟩ := km_bdd_fix N hN t (ρ₁ / 2) (ρ₂ / 2) ha hb ht z ε hε0 hεs hz M
      (fun k => hM _ (Set.mem_range_self k))
    obtain ⟨u0, b0, hb0, hnb0, -⟩ := (hfixiff p).1 hp
    have : u0 ∈ zer (opAdd A B) := ⟨-b0, hnb0, b0, hb0, by abel⟩
    rw [hzer] at this; exact this

end DR

end DouglasRachfordPPA.GenDR

open DouglasRachfordPPA.GenDR


theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (lam : ℝ) (hlam : 0 < lam)
    (JA JB : H → H) (hJA : IsResolvent lam A JA) (hJB : IsResolvent lam B JB)
    (z u v : ℕ → H) (α β ρ : ℕ → ℝ)
    (hT1 : ∀ k, ‖u k - JB (z k)‖ ≤ β k)
    (hT2 : ∀ k, ‖v (k + 1) - JA ((2 : ℝ) • u k - z k)‖ ≤ α k)
    (hT3 : ∀ k, z (k + 1) = z k + ρ k • (v (k + 1) - u k))
    (hα_nonneg : ∀ k, 0 ≤ α k) (hβ_nonneg : ∀ k, 0 ≤ β k)
    (hα_sum : Summable α) (hβ_sum : Summable β)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂) :
    ((zer (opAdd A B)).Nonempty → ∃ zs ∈ Zstar lam A B, WeakTendsto z zs) ∧
    (zer (opAdd A B) = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by
  exact dr_core A B hA hB lam hlam JA JB hJA hJB z u v α β ρ hT1 hT2 hT3 hα_nonneg hβ_nonneg hα_sum hβ_sum hρ
