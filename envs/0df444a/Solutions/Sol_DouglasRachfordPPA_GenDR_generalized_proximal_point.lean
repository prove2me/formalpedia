-- Prove2me | solution 1 for DouglasRachfordPPA.GenDR.generalized_proximal_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T06:09:26.312864+00:00
-- url     : https://prove2.me/submissions/b7f565b5-86ca-494a-a4ba-dfda1bda4391

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace ThreeOpSplitting.Convergence
open Filter Topology

namespace DouglasRachfordPPA.GenDR

lemma pp_real_ulim {ι : Type*} (f : ι → ℝ) (M : ℝ) (hM : ∀ k, |f k| ≤ M) (U : Ultrafilter ι) :
    ∃ a, Tendsto f U (𝓝 a) := by
  have hc : IsCompact (Set.Icc (-M) M) := isCompact_Icc
  obtain ⟨a, -, ha⟩ := hc.ultrafilter_le_nhds (U.map f) (by
    rw [Filter.le_principal_iff, Ultrafilter.coe_map, Filter.mem_map]
    exact Filter.univ_mem' (fun k => abs_le.1 (hM k)))
  exact ⟨a, ha⟩

lemma pp_exists_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (U : Ultrafilter ℕ) :
    ∃ w : H, ∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y)) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hb : ∀ y k, |inner ℝ (u k) y| ≤ M * ‖y‖ := fun y k =>
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM k) (norm_nonneg _))
  have hex : ∀ y, ∃ a, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 a) :=
    fun y => pp_real_ulim _ _ (hb y) U
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

lemma pp_weak_of_ulim {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (u : ℕ → H) (M : ℝ) (hM : ∀ k, ‖u k‖ ≤ M) (w0 : H)
    (h : ∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop → ∀ w : H,
      (∀ y, Tendsto (fun k => inner ℝ (u k) y) U (𝓝 (inner ℝ w y))) → w = w0) :
    WeakTendsto u w0 := by
  intro y
  rw [tendsto_iff_ultrafilter]
  intro U hU
  obtain ⟨w, hw⟩ := pp_exists_ulim u M hM U
  have := h U hU w hw
  subst this
  exact hw y

lemma pp_demiclosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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

lemma pp_opial_unique {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
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

lemma pp_conv_of_incr (u w : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hw0 : ∀ n, 0 ≤ w n)
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

lemma pp_convex_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • u + t • v‖ ^ 2 = (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 - t * (1 - t) * ‖u - v‖ ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, norm_sub_sq_real, inner_smul_left, inner_smul_right,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ht0, abs_of_nonneg (by linarith : 0 ≤ 1 - t),
    RCLike.conj_to_real]
  ring

lemma pp_err_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (x e : H) :
    ‖x + e‖ ^ 2 ≤ ‖x‖ ^ 2 + ‖e‖ * (2 * ‖x‖ + ‖e‖) := by
  have h := norm_add_le x e
  have h0 := norm_nonneg (x + e)
  nlinarith [norm_nonneg x, norm_nonneg e]

/-- The relaxed step against a fixed point `p`, and against `N c`. -/
lemma pp_y_fix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (N : H → H) (hN : ∀ x y, ‖N x - N y‖ ≤ ‖x - y‖) (z p : H) (hp : N p = p) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((1 - t) • z + t • N z) - p‖ ^ 2 ≤ ‖z - p‖ ^ 2 - t * (1 - t) * ‖z - N z‖ ^ 2 := by
  have e : ((1 - t) • z + t • N z) - p = (1 - t) • (z - p) + t • (N z - p) := by module
  rw [e, pp_convex_sq _ _ t ht0 ht1]
  have h1 : ‖N z - p‖ ≤ ‖z - p‖ := by have := hN z p; rwa [hp] at this
  have h2 : ‖N z - p‖ ^ 2 ≤ ‖z - p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have e2 : (z - p) - (N z - p) = z - N z := by abel
  rw [e2]
  nlinarith

lemma pp_res_fne {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A : H → Set H) (hA : IsMonotoneOp A) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam A J) (x y : H) : ‖J x - J y‖ ^ 2 ≤ ⟪J x - J y, x - y⟫_ℝ := by
  have h := hA _ _ _ _ (hJ x) (hJ y)
  rw [← smul_sub, inner_smul_right] at h
  have e : (x - J x) - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h
  have := inv_pos.2 hlam
  nlinarith

lemma pp_res_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A : H → Set H) (hA : IsMonotoneOp A) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam A J) (x y : H) : ‖J x - J y‖ ≤ ‖x - y‖ := by
  have h := pp_res_fne A hA lam hlam J hJ x y
  have h2 := real_inner_le_norm (J x - J y) (x - y)
  rcases (norm_nonneg (J x - J y)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  · nlinarith

lemma pp_refl_nonexp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A : H → Set H) (hA : IsMonotoneOp A) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
    (hJ : IsResolvent lam A J) (x y : H) :
    ‖((2:ℝ) • J x - x) - ((2:ℝ) • J y - y)‖ ≤ ‖x - y‖ := by
  have h := pp_res_fne A hA lam hlam J hJ x y
  have e : ((2:ℝ) • J x - x) - ((2:ℝ) • J y - y) = (2:ℝ) • (J x - J y) - (x - y) := by module
  have hsq : ‖((2:ℝ) • J x - x) - ((2:ℝ) • J y - y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
    rw [e, norm_sub_sq_real, norm_smul, inner_smul_left, mul_pow, RCLike.conj_to_real]
    norm_num
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

lemma pp_res_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (B : H → Set H) (hB : IsMonotoneOp B) (lam : ℝ) (hlam : 0 < lam) (J : H → H)
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

lemma pp_zero_of_closure {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → Set H) (hT : IsMaximalMonotone T) (w : H)
    (h : ∀ x v, v ∈ T x → ⟪w - x, v⟫_ℝ ≤ 0) : (0 : H) ∈ T w := by
  classical
  obtain ⟨T', hT'⟩ : ∃ T' : H → Set H, ∀ x', T' x' = T x' ∪ {y' | x' = w ∧ y' = 0} :=
    ⟨_, fun _ => rfl⟩
  have hmono : IsMonotoneOp T' := by
    intro x y u v hu hv
    rw [hT'] at hu hv
    simp only [Set.mem_union, Set.mem_setOf_eq] at hu hv
    rcases hu with hu | ⟨hx, hu0⟩ <;> rcases hv with hv | ⟨hy, hv0⟩
    · exact hT.1 x y u v hu hv
    · rw [hy, hv0, sub_zero, ← neg_sub w x, inner_neg_left]
      linarith [h x u hu]
    · rw [hx, hu0, zero_sub, inner_neg_right]
      linarith [h y v hv]
    · rw [hx, hu0, hy, hv0]; simp
  have hEq := hT.2 T' hmono (fun x => by rw [hT']; exact Set.subset_union_left)
  have : (0:H) ∈ T' w := by rw [hT']; exact Or.inr ⟨rfl, rfl⟩
  rw [hEq] at this; exact this

lemma pp_demiclosedT {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H → Set H) (hT : IsMaximalMonotone T) (c : ℕ → ℝ) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hc : ∀ k, c₀ ≤ c k) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z : ℕ → H) (M : ℝ) (hM : ∀ k, ‖z k‖ ≤ M)
    (hr : Tendsto (fun k => ‖J k (z k) - z k‖) atTop (𝓝 0)) (U : Ultrafilter ℕ)
    (hU : (U : Filter ℕ) ≤ atTop) (w : H)
    (hw : ∀ y, Tendsto (fun k => inner ℝ (z k) y) U (𝓝 (inner ℝ w y))) : (0 : H) ∈ T w := by
  apply pp_zero_of_closure T hT w
  intro x v hv
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = ‖J k (z k) - z k‖ := ⟨_, fun _ => rfl⟩
  have hr' : Tendsto r atTop (𝓝 0) := by
    refine hr.congr fun k => ?_
    rw [hr_def]
  have hck : ∀ k, 0 < c k := fun k => hc₀.trans_le (hc k)
  have key : ∀ k, inner ℝ (z k) v - inner ℝ x v ≤
      r k * ‖v‖ + (r k + (M + ‖x‖)) * (c₀⁻¹ * r k) := by
    intro k
    have hm := hT.1 (J k (z k)) x _ v (hJ k (z k)) hv
    rw [inner_sub_right, inner_smul_right] at hm
    have hr0 : 0 ≤ r k := by rw [hr_def]; exact norm_nonneg _
    have h1 : inner ℝ (J k (z k) - x) (z k - J k (z k)) ≤ ‖J k (z k) - x‖ * r k := by
      refine (real_inner_le_norm _ _).trans ?_
      rw [norm_sub_rev (z k) (J k (z k)), hr_def]
    have h2 : ‖J k (z k) - x‖ ≤ r k + (M + ‖x‖) := by
      calc ‖J k (z k) - x‖ = ‖(J k (z k) - z k) + (z k - x)‖ := by congr 1; abel
        _ ≤ ‖J k (z k) - z k‖ + ‖z k - x‖ := norm_add_le _ _
        _ ≤ r k + (M + ‖x‖) := by
          have := norm_sub_le (z k) x; rw [hr_def]; linarith [hM k]
    have h3 : (c k)⁻¹ ≤ c₀⁻¹ := inv_anti₀ hc₀ (hc k)
    have h4 : inner ℝ (J k (z k) - x) v =
        inner ℝ (J k (z k) - z k) v + (inner ℝ (z k) v - inner ℝ x v) := by
      rw [← inner_sub_left, ← inner_add_left]; congr 1; abel
    have h5 : -(r k * ‖v‖) ≤ inner ℝ (J k (z k) - z k) v := by
      have := abs_real_inner_le_norm (J k (z k) - z k) v
      rw [← hr_def] at this
      linarith [neg_abs_le (inner ℝ (J k (z k) - z k) v)]
    have h6 : (c k)⁻¹ * inner ℝ (J k (z k) - x) (z k - J k (z k)) ≤
        c₀⁻¹ * ((r k + (M + ‖x‖)) * r k) := by
      have hp : 0 ≤ ‖J k (z k) - x‖ * r k := mul_nonneg (norm_nonneg _) hr0
      calc (c k)⁻¹ * inner ℝ (J k (z k) - x) (z k - J k (z k))
          ≤ (c k)⁻¹ * (‖J k (z k) - x‖ * r k) :=
            mul_le_mul_of_nonneg_left h1 (inv_pos.2 (hck k)).le
        _ ≤ c₀⁻¹ * (‖J k (z k) - x‖ * r k) := mul_le_mul_of_nonneg_right h3 hp
        _ ≤ c₀⁻¹ * ((r k + (M + ‖x‖)) * r k) := by
            apply mul_le_mul_of_nonneg_left _ (inv_pos.2 hc₀).le
            exact mul_le_mul_of_nonneg_right h2 hr0
    nlinarith
  have hg : Tendsto (fun k => r k * ‖v‖ + (r k + (M + ‖x‖)) * (c₀⁻¹ * r k)) atTop
      (𝓝 (0 * ‖v‖ + (0 + (M + ‖x‖)) * (c₀⁻¹ * 0))) :=
    (hr'.mul_const ‖v‖).add ((hr'.add tendsto_const_nhds).mul (hr'.const_mul c₀⁻¹))
  simp only [zero_mul, mul_zero, add_zero] at hg
  have hl : Tendsto (fun k => inner ℝ (z k) v - inner ℝ x v) U
      (𝓝 (inner ℝ w v - inner ℝ x v)) := (hw v).sub tendsto_const_nhds
  have := le_of_tendsto_of_tendsto' hl (hg.mono_left hU) key
  rw [inner_sub_left]; linarith

/-- The key one-step inequality for the ergodic argument. -/
lemma pp_key {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Z U E V x : H) (ρ cc : ℝ) (hρ0 : 0 ≤ ρ) (hρ2 : ρ ≤ 2) (hc : 0 < cc)
    (hmono : 0 ≤ ⟪(Z - U) - x, cc⁻¹ • U - V⟫_ℝ) :
    ρ * cc * ⟪(Z - U) - x, V⟫_ℝ ≤ (1/2) * (‖Z - x‖ ^ 2 - ‖(Z - ρ • U + E) - x‖ ^ 2)
      + ‖E‖ * (‖Z - x‖ + ‖ρ • U‖ + ‖E‖) := by
  have h1 : ⟪(Z - U) - x, V⟫_ℝ ≤ cc⁻¹ * ⟪(Z - U) - x, U⟫_ℝ := by
    rw [inner_sub_right, inner_smul_right] at hmono; linarith
  have h2 : ρ * cc * ⟪(Z - U) - x, V⟫_ℝ ≤ ρ * ⟪(Z - U) - x, U⟫_ℝ := by
    calc ρ * cc * ⟪(Z - U) - x, V⟫_ℝ ≤ ρ * cc * (cc⁻¹ * ⟪(Z - U) - x, U⟫_ℝ) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hρ0 hc.le)
      _ = ρ * ⟪(Z - U) - x, U⟫_ℝ := by field_simp
  have h3 : ⟪(Z - U) - x, U⟫_ℝ = ⟪Z - x, U⟫_ℝ - ‖U‖ ^ 2 := by
    rw [show (Z - U) - x = (Z - x) - U by abel, inner_sub_left, real_inner_self_eq_norm_sq]
  have h4 : ‖(Z - ρ • U + E) - x‖ ^ 2 = ‖Z - x‖ ^ 2 - 2 * ρ * ⟪Z - x, U⟫_ℝ + ρ ^ 2 * ‖U‖ ^ 2
      + 2 * ⟪(Z - x) - ρ • U, E⟫_ℝ + ‖E‖ ^ 2 := by
    rw [show (Z - ρ • U + E) - x = ((Z - x) - ρ • U) + E by abel, norm_add_sq_real,
      norm_sub_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ0, mul_pow]
    ring
  have h5 : ⟪(Z - x) - ρ • U, E⟫_ℝ ≤ (‖Z - x‖ + ‖ρ • U‖) * ‖E‖ :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _))
  have h6 : 0 ≤ ρ * (2 - ρ) * ‖U‖ ^ 2 :=
    mul_nonneg (mul_nonneg hρ0 (by linarith)) (sq_nonneg _)
  have h7 : 0 ≤ ‖E‖ ^ 2 := sq_nonneg _
  nlinarith

theorem pp_weak {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T)
    (c ρ ε : ℕ → ℝ) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z w : ℕ → H)
    (hz : ∀ k, z (k + 1) = (1 - ρ k) • z k + ρ k • w k)
    (hw : ∀ k, ‖w k - J k (z k)‖ ≤ ε k)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε_sum : Summable ε)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ₂ : ρ₂ < 2) (hρk : ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (hc : ∀ k, c₀ ≤ c k)
    (hfix : (zer T).Nonempty) : ∃ zs ∈ zer T, WeakTendsto z zs := by
  have hck : ∀ k, 0 < c k := fun k => hc₀.trans_le (hc k)
  obtain ⟨N, hNe⟩ : ∃ N : ℕ → H → H, ∀ k x, N k x = (2:ℝ) • J k x - x := ⟨_, fun _ _ => rfl⟩
  have hN : ∀ k x y, ‖N k x - N k y‖ ≤ ‖x - y‖ := fun k x y => by
    rw [hNe, hNe]; exact pp_refl_nonexp T hT.1 (c k) (hck k) (J k) (hJ k) x y
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ → ℝ, ∀ k, t k = ρ k / 2 := ⟨_, fun _ => rfl⟩
  have ha : 0 < ρ₁ / 2 := by linarith
  have hb : ρ₂ / 2 < 1 := by linarith
  have ht : ∀ k, ρ₁ / 2 ≤ t k ∧ t k ≤ ρ₂ / 2 := fun k =>
    ⟨by rw [ht_def]; linarith [(hρk k).1], by rw [ht_def]; linarith [(hρk k).2]⟩
  have ht0 : ∀ k, 0 ≤ t k := fun k => ha.le.trans (ht k).1
  have ht1 : ∀ k, t k ≤ 1 := fun k => (ht k).2.trans hb.le
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℕ → ℝ, ∀ k, ε' k = 2 * ε k := ⟨_, fun _ => rfl⟩
  have hε0 : ∀ k, 0 ≤ ε' k := fun k => by rw [hε']; linarith [hε_nonneg k]
  have hεs : Summable ε' := by
    have := hε_sum.mul_left 2
    exact this.congr fun k => (hε' k).symm
  obtain ⟨y, hy⟩ : ∃ y : ℕ → H, ∀ k, y k = (1 - t k) • z k + t k • N k (z k) := ⟨_, fun _ => rfl⟩
  have hzy : ∀ k, ‖z (k + 1) - y k‖ ≤ ε' k := by
    intro k
    have e : z (k + 1) - y k = ρ k • (w k - J k (z k)) := by
      rw [hz, hy, hNe, ht_def]; module
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ₁.le.trans (hρk k).1), hε']
    have := hw k
    have h2 : ρ k ≤ 2 := (hρk k).2.trans hρ₂.le
    nlinarith [norm_nonneg (w k - J k (z k)), hε_nonneg k]
  have hfixN : ∀ p, p ∈ zer T → ∀ k, N k p = p := by
    intro p hp k
    have hJp : J k p = p := by
      have := pp_res_eq T hT.1 (c k) (hck k) (J k) (hJ k) p 0 hp
      simpa using this
    rw [hNe, hJp]; module
  have hstep : ∀ p, ∀ k, ‖z (k + 1) - p‖ ≤ ‖y k - p‖ + ε' k := by
    intro p k
    have e : z (k + 1) - p = (z (k + 1) - y k) + (y k - p) := by abel
    rw [e]; refine (norm_add_le _ _).trans ?_; linarith [hzy k]
  have hyp : ∀ p, p ∈ zer T → ∀ k,
      ‖y k - p‖ ^ 2 ≤ ‖z k - p‖ ^ 2 - t k * (1 - t k) * ‖z k - N k (z k)‖ ^ 2 := by
    intro p hp k
    rw [hy]
    exact pp_y_fix (N k) (hN k) (z k) p (hfixN p hp k) (t k) (ht0 k) (ht1 k)
  have hyp' : ∀ p, p ∈ zer T → ∀ k, ‖y k - p‖ ≤ ‖z k - p‖ := by
    intro p hp k
    have h := hyp p hp k
    have : 0 ≤ t k * (1 - t k) * ‖z k - N k (z k)‖ ^ 2 :=
      mul_nonneg (mul_nonneg (ht0 k) (by linarith [ht1 k])) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)
  have hconv : ∀ p, p ∈ zer T → ∃ l, Tendsto (fun k => ‖z k - p‖) atTop (𝓝 l) := by
    intro p hp
    exact pp_conv_of_incr _ ε' (fun _ => norm_nonneg _) hε0 hεs
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
  have hres : Tendsto (fun k => ‖N k (z k) - z k‖) atTop (𝓝 0) := by
    obtain ⟨D, hD_def⟩ : ∃ D : ℕ → ℝ, ∀ k, D k = ‖z k - p0‖ := ⟨_, fun _ => rfl⟩
    have hl0' : Tendsto D atTop (𝓝 l0) := hl0.congr fun k => (hD_def k).symm
    have hε : Tendsto ε' atTop (𝓝 0) := hεs.tendsto_atTop_zero
    have hkey : ∀ k, (ρ₁ / 2) * (1 - ρ₂ / 2) * ‖N k (z k) - z k‖ ^ 2 ≤
        D k ^ 2 - D (k + 1) ^ 2 + ε' k * (2 * D k + ε' k) := by
      intro k
      have h1 := hstep p0 k
      have h2 := hyp p0 hp0 k
      have h3 := hyp' p0 hp0 k
      rw [← hD_def] at h1 h2 h3
      have hD : 0 ≤ D (k + 1) := by rw [hD_def]; exact norm_nonneg _
      have hsq : D (k + 1) ^ 2 ≤ (‖y k - p0‖ + ε' k) ^ 2 := pow_le_pow_left₀ hD h1 2
      have htt : (ρ₁ / 2) * (1 - ρ₂ / 2) ≤ t k * (1 - t k) := by
        have := ht k; nlinarith
      have hr : ‖N k (z k) - z k‖ = ‖z k - N k (z k)‖ := norm_sub_rev _ _
      rw [hr]
      have hyn := norm_nonneg (y k - p0)
      have := hε0 k
      have hrr := sq_nonneg ‖z k - N k (z k)‖
      nlinarith [mul_le_mul_of_nonneg_right htt hrr]
    have hlimR : Tendsto (fun k => (D k ^ 2 - D (k + 1) ^ 2 + ε' k * (2 * D k + ε' k)) /
        ((ρ₁ / 2) * (1 - ρ₂ / 2)))
        atTop (𝓝 ((l0 ^ 2 - l0 ^ 2 + 0 * (2 * l0 + 0)) / ((ρ₁ / 2) * (1 - ρ₂ / 2)))) := by
      refine Tendsto.div_const ?_ _
      exact ((hl0'.pow 2).sub ((hl0'.comp (tendsto_add_atTop_nat 1)).pow 2)).add
        (hε.mul ((hl0'.const_mul 2).add hε))
    simp only [sub_self, zero_mul, add_zero, zero_div] at hlimR
    have hab : 0 < (ρ₁ / 2) * (1 - ρ₂ / 2) := mul_pos ha (by linarith)
    have hsq : Tendsto (fun k => ‖N k (z k) - z k‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) hlimR
      rw [le_div_iff₀ hab, mul_comm]; exact hkey k
    have := hsq.sqrt
    simp only [Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] at this
    exact this
  have hresJ : Tendsto (fun k => ‖J k (z k) - z k‖) atTop (𝓝 0) := by
    have := hres.const_mul (1/2)
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [hNe, show (2:ℝ) • J k (z k) - z k - z k = (2:ℝ) • (J k (z k) - z k) by module,
      norm_smul, Real.norm_eq_abs]
    norm_num; ring
  obtain ⟨U0, hU0⟩ : ∃ U0 : Ultrafilter ℕ, (U0 : Filter ℕ) ≤ atTop :=
    ⟨Ultrafilter.of atTop, Ultrafilter.of_le _⟩
  obtain ⟨w0, hw0⟩ := pp_exists_ulim z _ hM U0
  have hw0fix : (0:H) ∈ T w0 :=
    pp_demiclosedT T hT c c₀ hc₀ hc J hJ z _ hM hresJ U0 hU0 w0 hw0
  refine ⟨w0, hw0fix, ?_⟩
  apply pp_weak_of_ulim z _ hM w0
  intro U hU w' hw'
  have hwfix : (0:H) ∈ T w' := pp_demiclosedT T hT c c₀ hc₀ hc J hJ z _ hM hresJ U hU w' hw'
  exact pp_opial_unique z w' w0 U U0 hU hU0 hw' hw0 (hconv w' hwfix) (hconv w0 hw0fix)

theorem pp_bdd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T)
    (c ρ ε : ℕ → ℝ) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z w : ℕ → H)
    (hz : ∀ k, z (k + 1) = (1 - ρ k) • z k + ρ k • w k)
    (hw : ∀ k, ‖w k - J k (z k)‖ ≤ ε k)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε_sum : Summable ε)
    (ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ₂ : ρ₂ < 2) (hρk : ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂)
    (c₀ : ℝ) (hc₀ : 0 < c₀) (hc : ∀ k, c₀ ≤ c k)
    (M : ℝ) (hM : ∀ k, ‖z k‖ ≤ M) : (zer T).Nonempty := by
  have hck : ∀ k, 0 < c k := fun k => hc₀.trans_le (hc k)
  have hρ0 : ∀ k, 0 ≤ ρ k := fun k => hρ₁.le.trans (hρk k).1
  have hρ2 : ∀ k, ρ k ≤ 2 := fun k => (hρk k).2.trans hρ₂.le
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑' k, ε k := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hS]; exact tsum_nonneg hε_nonneg
  have hεS : ∀ k, ε k ≤ S := fun k => by
    rw [hS]; exact hε_sum.le_tsum k (fun j _ => hε_nonneg j)
  have hsumS : ∀ K, ∑ k ∈ Finset.range K, ε k ≤ S := fun K => by
    rw [hS]; exact hε_sum.sum_le_tsum (Finset.range K) (fun i _ => hε_nonneg i)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨x, hx⟩ : ∃ x : ℕ → H, ∀ k, x k = J k (z k) := ⟨_, fun _ => rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℕ → H, ∀ k, u k = z k - x k := ⟨_, fun _ => rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℕ → H, ∀ k, e k = ρ k • (w k - x k) := ⟨_, fun _ => rfl⟩
  have hzk : ∀ k, z (k + 1) = z k - ρ k • u k + e k := by
    intro k; rw [hz, hu, he]; module
  have he_norm : ∀ k, ‖e k‖ ≤ 2 * ε k := by
    intro k; rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 k), hx]
    have := hw k; nlinarith [hρ2 k, norm_nonneg (w k - J k (z k)), hε_nonneg k]
  have hρu : ∀ k, ‖ρ k • u k‖ ≤ 2 * M + 2 * S := by
    intro k
    have e1 : ρ k • u k = (z k - z (k + 1)) + e k := by rw [hzk k]; abel
    rw [e1]
    calc ‖(z k - z (k+1)) + e k‖ ≤ ‖z k - z (k+1)‖ + ‖e k‖ := norm_add_le _ _
      _ ≤ (‖z k‖ + ‖z (k+1)‖) + 2 * ε k := add_le_add (norm_sub_le _ _) (he_norm k)
      _ ≤ 2 * M + 2 * S := by linarith [hM k, hM (k+1), hεS k]
  have hu_norm : ∀ k, ‖u k‖ ≤ (2 * M + 2 * S) / ρ₁ := by
    intro k
    have h := hρu k
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hρ0 k)] at h
    rw [le_div_iff₀ hρ₁]
    calc ‖u k‖ * ρ₁ ≤ ‖u k‖ * ρ k := mul_le_mul_of_nonneg_left (hρk k).1 (norm_nonneg _)
      _ = ρ k * ‖u k‖ := mul_comm _ _
      _ ≤ _ := h
  obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = M + (2 * M + 2 * S) / ρ₁ := ⟨_, rfl⟩
  have hx_norm : ∀ k, ‖x k‖ ≤ M' := by
    intro k
    have : x k = z k - u k := by rw [hu]; abel
    rw [this, hM']; exact (norm_sub_le _ _).trans (add_le_add (hM k) (hu_norm k))
  -- weights
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℝ, ∀ K, W K = ∑ k ∈ Finset.range K, ρ k * c k :=
    ⟨_, fun _ => rfl⟩
  have hw_nonneg : ∀ k, 0 ≤ ρ k * c k := fun k => mul_nonneg (hρ0 k) (hck k).le
  have hW_lower : ∀ K : ℕ, (K : ℝ) * (ρ₁ * c₀) ≤ W K := by
    intro K
    rw [hW]
    have h1 : ∀ k ∈ Finset.range K, ρ₁ * c₀ ≤ ρ k * c k := fun k _ =>
      mul_le_mul (hρk k).1 (hc k) hc₀.le (hρ0 k)
    have := Finset.sum_le_sum h1
    simpa using this
  have hW_pos : ∀ K, 0 < W (K + 1) := fun K => by
    have := hW_lower (K + 1)
    have h2 : (0:ℝ) < ((K + 1 : ℕ) : ℝ) * (ρ₁ * c₀) := by positivity
    linarith
  obtain ⟨xb, hxb⟩ : ∃ xb : ℕ → H, ∀ K, xb K =
      (W (K + 1))⁻¹ • ∑ k ∈ Finset.range (K + 1), (ρ k * c k) • x k := ⟨_, fun _ => rfl⟩
  have hxb_norm : ∀ K, ‖xb K‖ ≤ M' := by
    intro K
    rw [hxb, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hW_pos K))]
    have h1 : ‖∑ k ∈ Finset.range (K + 1), (ρ k * c k) • x k‖ ≤ W (K + 1) * M' := by
      refine (norm_sum_le _ _).trans ?_
      rw [hW, Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw_nonneg k)]
      exact mul_le_mul_of_nonneg_left (hx_norm k) (hw_nonneg k)
    calc (W (K+1))⁻¹ * ‖∑ k ∈ Finset.range (K + 1), (ρ k * c k) • x k‖
        ≤ (W (K+1))⁻¹ * (W (K+1) * M') :=
          mul_le_mul_of_nonneg_left h1 (inv_pos.2 (hW_pos K)).le
      _ = M' := by rw [← mul_assoc, inv_mul_cancel₀ (hW_pos K).ne', one_mul]
  -- key per-step inequality
  have hkey : ∀ (x0 v : H), v ∈ T x0 → ∀ k, ρ k * c k * inner ℝ (x k - x0) v ≤
      (1/2) * (‖z k - x0‖ ^ 2 - ‖z (k + 1) - x0‖ ^ 2)
        + ‖e k‖ * (‖z k - x0‖ + ‖ρ k • u k‖ + ‖e k‖) := by
    intro x0 v hv k
    have hJk : (c k)⁻¹ • u k ∈ T (x k) := by rw [hu, hx]; exact hJ k (z k)
    have hmono := hT.1 (x k) x0 _ v hJk hv
    have hxk : x k = z k - u k := by rw [hu]; abel
    rw [hxk] at hmono
    rw [hxk, hzk k]
    exact pp_key (z k) (u k) (e k) v x0 (ρ k) (c k) (hρ0 k) (hρ2 k) (hck k) hmono
  have hsum : ∀ (x0 v : H), v ∈ T x0 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ K, ∑ k ∈ Finset.range K, ρ k * c k * inner ℝ (x k - x0) v ≤ C := by
    intro x0 v hv
    obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 2 * (M + ‖x0‖ + (2 * M + 2 * S) + 2 * S) := ⟨_, rfl⟩
    have hL0 : 0 ≤ L := by rw [hL]; positivity
    refine ⟨(1/2) * ‖z 0 - x0‖ ^ 2 + L * S, by positivity, fun K => ?_⟩
    have hEk : ∀ k, ‖e k‖ * (‖z k - x0‖ + ‖ρ k • u k‖ + ‖e k‖) ≤ ε k * L := by
      intro k
      have h1 := he_norm k
      have h2 : ‖z k - x0‖ ≤ M + ‖x0‖ := (norm_sub_le _ _).trans (by linarith [hM k])
      have h3 := hρu k
      have h4 : ‖e k‖ ≤ 2 * S := by linarith [hεS k]
      have h5 : ‖z k - x0‖ + ‖ρ k • u k‖ + ‖e k‖ ≤ M + ‖x0‖ + (2 * M + 2 * S) + 2 * S := by
        linarith
      have h6 : 0 ≤ ‖z k - x0‖ + ‖ρ k • u k‖ + ‖e k‖ := by positivity
      calc ‖e k‖ * (‖z k - x0‖ + ‖ρ k • u k‖ + ‖e k‖)
          ≤ (2 * ε k) * (M + ‖x0‖ + (2 * M + 2 * S) + 2 * S) :=
            mul_le_mul h1 h5 h6 (by linarith [hε_nonneg k])
        _ = ε k * L := by rw [hL]; ring
    have htel := Finset.sum_range_sub' (fun k => ‖z k - x0‖ ^ 2) K
    calc ∑ k ∈ Finset.range K, ρ k * c k * inner ℝ (x k - x0) v
        ≤ ∑ k ∈ Finset.range K, ((1/2) * (‖z k - x0‖ ^ 2 - ‖z (k + 1) - x0‖ ^ 2) + ε k * L) :=
          Finset.sum_le_sum fun k _ => (hkey x0 v hv k).trans (by linarith [hEk k])
      _ = (1/2) * (‖z 0 - x0‖ ^ 2 - ‖z K - x0‖ ^ 2) + (∑ k ∈ Finset.range K, ε k) * L := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, htel, Finset.sum_mul]
      _ ≤ (1/2) * ‖z 0 - x0‖ ^ 2 + L * S := by
          have := hsumS K
          have h0 := sq_nonneg ‖z K - x0‖
          nlinarith
  obtain ⟨U, hU⟩ : ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop :=
    ⟨Ultrafilter.of atTop, Ultrafilter.of_le _⟩
  obtain ⟨w0, hw0⟩ := pp_exists_ulim xb M' hxb_norm U
  refine ⟨w0, pp_zero_of_closure T hT w0 ?_⟩
  intro x0 v hv
  obtain ⟨C, hC0, hC⟩ := hsum x0 v hv
  have hineq : ∀ K, inner ℝ (xb K) v - inner ℝ x0 v ≤ C / W (K + 1) := by
    intro K
    have hWp := hW_pos K
    have e1 : inner ℝ (xb K) v =
        (W (K + 1))⁻¹ * ∑ k ∈ Finset.range (K + 1), ρ k * c k * inner ℝ (x k) v := by
      rw [hxb, real_inner_smul_left, sum_inner]
      simp only [real_inner_smul_left]
    have e2 : ∑ k ∈ Finset.range (K + 1), ρ k * c k * inner ℝ (x k - x0) v
        = ∑ k ∈ Finset.range (K + 1), ρ k * c k * inner ℝ (x k) v
          - W (K + 1) * inner ℝ x0 v := by
      rw [hW, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [inner_sub_left]; ring
    have h := hC (K + 1)
    rw [e2] at h
    rw [e1, div_eq_inv_mul]
    have e3 : (W (K + 1))⁻¹ * ∑ k ∈ Finset.range (K + 1), ρ k * c k * inner ℝ (x k) v
        - inner ℝ x0 v
        = (W (K + 1))⁻¹ * (∑ k ∈ Finset.range (K + 1), ρ k * c k * inner ℝ (x k) v
          - W (K + 1) * inner ℝ x0 v) := by
      field_simp
    rw [e3]
    exact mul_le_mul_of_nonneg_left h (inv_pos.2 hWp).le
  have hlim : Tendsto (fun K : ℕ => C / W (K + 1)) atTop (𝓝 0) := by
    have hb : Tendsto (fun K : ℕ => C / (ρ₁ * c₀) * (1 / ((K : ℝ) + 1))) atTop
        (𝓝 (C / (ρ₁ * c₀) * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _
    rw [mul_zero] at hb
    refine squeeze_zero (fun K => div_nonneg hC0 (hW_pos K).le) (fun K => ?_) hb
    have h1 := hW_lower (K + 1)
    push_cast at h1
    rw [div_le_iff₀ (hW_pos K)]
    have hpos : 0 < ρ₁ * c₀ := by positivity
    calc C = C / (ρ₁ * c₀) * (1 / ((K:ℝ) + 1)) * (((K:ℝ) + 1) * (ρ₁ * c₀)) := by field_simp
      _ ≤ C / (ρ₁ * c₀) * (1 / ((K:ℝ) + 1)) * W (K + 1) := by
          apply mul_le_mul_of_nonneg_left h1; positivity
  have hl : Tendsto (fun K => inner ℝ (xb K) v - inner ℝ x0 v) U
      (𝓝 (inner ℝ w0 v - inner ℝ x0 v)) := (hw0 v).sub tendsto_const_nhds
  have := le_of_tendsto_of_tendsto' hl (hlim.mono_left hU) hineq
  rw [inner_sub_left]; linarith

theorem gpp_core
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T)
    (c ρ ε : ℕ → ℝ) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z w : ℕ → H)
    (hz : ∀ k, z (k + 1) = (1 - ρ k) • z k + ρ k • w k)
    (hw : ∀ k, ‖w k - J k (z k)‖ ≤ ε k)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε_sum : Summable ε)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂)
    (hc : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ ≤ c k) :
    ((zer T).Nonempty → ∃ zs ∈ zer T, WeakTendsto z zs) ∧
    (zer T = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by
  obtain ⟨ρ₁, ρ₂, hρ₁, hρ₂, hρk⟩ := hρ
  obtain ⟨c₀, hc₀, hc⟩ := hc
  constructor
  · intro hne
    exact pp_weak T hT c ρ ε J hJ z w hz hw hε_nonneg hε_sum ρ₁ ρ₂ hρ₁ hρ₂ hρk c₀ hc₀ hc hne
  · intro hzer hbdd
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hbdd
    have := pp_bdd T hT c ρ ε J hJ z w hz hw hε_nonneg hε_sum ρ₁ ρ₂ hρ₁ hρ₂ hρk c₀ hc₀ hc M
      (fun k => hM _ (Set.mem_range_self k))
    rw [hzer] at this; exact Set.not_nonempty_empty this

end DouglasRachfordPPA.GenDR

open DouglasRachfordPPA.GenDR


theorem solution
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T)
    (c ρ ε : ℕ → ℝ) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z w : ℕ → H)
    (hz : ∀ k, z (k + 1) = (1 - ρ k) • z k + ρ k • w k)
    (hw : ∀ k, ‖w k - J k (z k)‖ ≤ ε k)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε_sum : Summable ε)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂)
    (hc : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ ≤ c k) :
    ((zer T).Nonempty → ∃ zs ∈ zer T, WeakTendsto z zs) ∧
    (zer T = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by
  exact gpp_core T hT c ρ ε J hJ z w hz hw hε_nonneg hε_sum hρ hc
