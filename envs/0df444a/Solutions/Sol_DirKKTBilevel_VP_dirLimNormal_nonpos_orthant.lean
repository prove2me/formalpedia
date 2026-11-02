-- Prove2me | solution 1 for DirKKTBilevel.VP.dirLimNormal_nonpos_orthant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:56:24.903003+00:00
-- url     : https://prove2.me/submissions/b7070258-bb15-4440-ad95-37eaed68cb90

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open DirKKTBilevel.VP

lemma orth_inner_eq {q : ℕ} (x y : E q) : inner ℝ x y = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, mul_comm]

/-- A regular normal to the nonpositive orthant is nonnegative and complementary. -/
lemma orth_regNormal {q : ℕ} (b ξ : E q) (h : ξ ∈ regNormal {w : E q | ∀ j, w j ≤ 0} b) :
    (∀ j, 0 ≤ ξ j) ∧ (∀ j, b j < 0 → ξ j = 0) := by
  obtain ⟨hb, hreg⟩ := h
  -- moving along the j-th coordinate
  have key : ∀ (j : Fin q) (σ : ℝ), (∀ᶠ s in 𝓝[>] (0:ℝ), b + (s * σ) • EuclideanSpace.single j (1:ℝ)
      ∈ {w : E q | ∀ j, w j ≤ 0}) → σ * ξ j ≤ 0 := by
    intro j σ hev
    by_contra hpos
    push_neg at hpos
    set ε := σ * ξ j / (2 * (|σ| + 1)) with hε
    have hεpos : 0 < ε := by positivity
    have hT : Tendsto (fun s : ℝ => b + (s * σ) • EuclideanSpace.single j (1:ℝ)) (𝓝[>] 0)
        (𝓝[{w : E q | ∀ j, w j ≤ 0}] b) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, hev⟩
      have : Tendsto (fun s : ℝ => b + (s * σ) • EuclideanSpace.single j (1:ℝ)) (𝓝 0)
          (𝓝 (b + ((0:ℝ) * σ) • EuclideanSpace.single j (1:ℝ))) := by
        apply Continuous.tendsto; fun_prop
      simp only [zero_mul, zero_smul, add_zero] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    have h2 := (hT.eventually (hreg ε hεpos)).and self_mem_nhdsWithin
    obtain ⟨s, hs, hs0⟩ := h2.exists
    have hs0' : (0:ℝ) < s := hs0
    simp only [add_sub_cancel_left, inner_smul_right, norm_smul, Real.norm_eq_abs] at hs
    rw [EuclideanSpace.inner_single_right, EuclideanSpace.norm_single, norm_one] at hs
    simp only [map_one, one_mul, mul_one, abs_mul, abs_of_pos hs0', conj_trivial] at hs
    -- hs : s * σ * ξ j ≤ ε * (s * |σ|)
    have h3 : ε * (s * |σ|) < s * σ * ξ j := by
      rw [hε]
      have : σ * ξ j / (2 * (|σ| + 1)) * |σ| < σ * ξ j := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg σ]
      nlinarith
    linarith
  refine ⟨fun j => ?_, fun j hj => ?_⟩
  · have := key j (-1) (by
      filter_upwards [self_mem_nhdsWithin] with s hs i
      have hs' : (0:ℝ) < s := hs
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
      split_ifs <;> nlinarith [hb i])
    linarith
  · have h1 := key j (-1) (by
      filter_upwards [self_mem_nhdsWithin] with s hs i
      have hs' : (0:ℝ) < s := hs
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
      split_ifs <;> nlinarith [hb i])
    have h2 := key j 1 (by
      have hT : Tendsto (fun s : ℝ => b j + s) (𝓝[>] 0) (𝓝 (b j + 0)) :=
        tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.add tendsto_id)
      rw [add_zero] at hT
      filter_upwards [hT.eventually (gt_mem_nhds hj)] with s hs i
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, EuclideanSpace.single_apply]
      split_ifs with hij
      · subst hij; linarith
      · simpa using hb i)
    linarith

theorem solution {q : ℕ} (a d : E q) (ha : ∀ j, a j ≤ 0)
    (hd : ∀ j, a j = 0 → d j ≤ 0) :
    dirLimNormal {w : E q | ∀ j, w j ≤ 0} a d =
      {ξ | (∀ j, 0 ≤ ξ j) ∧ ∑ j, ξ j * a j = 0 ∧ ∑ j, ξ j * d j = 0} := by
  ext ξ
  constructor
  · rintro ⟨_, t, dk, vk, ht, ht0, hdk, hvk, hreg⟩
    have hcomp : ∀ j, Tendsto (fun k => vk k j) atTop (𝓝 (ξ j)) := fun j =>
      ((PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous.tendsto ξ).comp hvk
    have hdcomp : ∀ j, Tendsto (fun k => dk k j) atTop (𝓝 (d j)) := fun j =>
      ((PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous.tendsto d).comp hdk
    have hR := fun k => orth_regNormal _ _ (hreg k)
    -- if eventually the base point has a negative j-th coordinate, then ξ j = 0
    have hzero : ∀ j, (∀ᶠ k in atTop, (a + t k • dk k) j < 0) → ξ j = 0 := by
      intro j hev
      have : ∀ᶠ k in atTop, vk k j = 0 := by
        filter_upwards [hev] with k hk
        exact (hR k).2 j hk
      exact tendsto_nhds_unique (hcomp j) (tendsto_const_nhds.congr' (this.mono fun k hk => hk.symm))
    have hnn : ∀ j, 0 ≤ ξ j := fun j =>
      ge_of_tendsto (hcomp j) (Eventually.of_forall fun k => (hR k).1 j)
    have hterm : ∀ j, ξ j * a j = 0 ∧ ξ j * d j = 0 := by
      intro j
      rcases (ha j).lt_or_eq with hlt | heq
      · have : ξ j = 0 := by
          apply hzero j
          have hT : Tendsto (fun k => a j + t k * dk k j) atTop (𝓝 (a j + 0 * d j)) :=
            tendsto_const_nhds.add (ht0.mul (hdcomp j))
          rw [zero_mul, add_zero] at hT
          filter_upwards [hT.eventually (gt_mem_nhds hlt)] with k hk
          simpa using hk
        simp [this]
      · refine ⟨by rw [heq, mul_zero], ?_⟩
        rcases (hd j heq).lt_or_eq with hdl | hde
        · have : ξ j = 0 := by
            apply hzero j
            filter_upwards [(hdcomp j).eventually (gt_mem_nhds hdl)] with k hk
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, heq, zero_add]
            exact mul_neg_of_pos_of_neg (ht k) hk
          simp [this]
        · rw [hde, mul_zero]
    exact ⟨hnn, Finset.sum_eq_zero fun j _ => (hterm j).1,
      Finset.sum_eq_zero fun j _ => (hterm j).2⟩
  · rintro ⟨hnn, hsa, hsd⟩
    have hta : ∀ j, ξ j * a j = 0 := by
      have := (Finset.sum_eq_zero_iff_of_nonpos (fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (hnn j) (ha j))).mp hsa
      exact fun j => this j (Finset.mem_univ j)
    have htd : ∀ j, ξ j * d j = 0 := by
      have hnp : ∀ j ∈ Finset.univ, ξ j * d j ≤ 0 := by
        intro j _
        rcases (ha j).lt_or_eq with hlt | heq
        · have : ξ j = 0 := by
            have := hta j
            rcases mul_eq_zero.mp this with h | h
            · exact h
            · linarith
          simp [this]
        · exact mul_nonpos_of_nonneg_of_nonpos (hnn j) (hd j heq)
      have := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsd
      exact fun j => this j (Finset.mem_univ j)
    -- eventually `a + s d` is feasible
    have hev : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ j, (a + s • d) j ≤ 0 := by
      rw [eventually_all]
      intro j
      rcases (ha j).lt_or_eq with hlt | heq
      · have hT : Tendsto (fun s : ℝ => a j + s * d j) (𝓝[>] 0) (𝓝 (a j + 0 * d j)) :=
          tendsto_nhdsWithin_of_tendsto_nhds
            (tendsto_const_nhds.add (tendsto_id.mul tendsto_const_nhds))
        rw [zero_mul, add_zero] at hT
        filter_upwards [hT.eventually (gt_mem_nhds hlt)] with s hs
        simpa using hs.le
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : (0:ℝ) < s := hs
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, heq, zero_add]
        exact mul_nonpos_of_nonneg_of_nonpos hs'.le (hd j heq)
    have hseq : Tendsto (fun k : ℕ => 1 / ((k:ℝ) + 1)) atTop (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall fun k => ?_⟩
      show (0:ℝ) < 1 / ((k:ℝ) + 1)
      positivity
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hseq.eventually hev)
    refine ⟨fun j => ?_, fun k => 1 / (((k + N : ℕ) : ℝ) + 1), fun _ => d, fun _ => ξ,
      fun k => by positivity, ?_, tendsto_const_nhds, tendsto_const_nhds, fun k => ?_⟩
    · -- a is feasible
      exact ha j
    · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat N)
    · have hfe := hN (k + N) (Nat.le_add_left N k)
      refine ⟨hfe, fun ε hε => ?_⟩
      apply eventually_nhdsWithin_of_forall
      intro y hy
      have : inner ℝ ξ (y - (a + (1 / (((k + N : ℕ) : ℝ) + 1)) • d)) ≤ 0 := by
        rw [orth_inner_eq]
        apply Finset.sum_nonpos
        intro j _
        simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        have h1 := hta j
        have h2 := htd j
        have : ξ j * (y j - (a j + 1 / (((k + N : ℕ) : ℝ) + 1) * d j)) = ξ j * y j := by
          linear_combination (-1 : ℝ) * h1 - (1 / (((k + N : ℕ) : ℝ) + 1)) * h2
        rw [this]
        exact mul_nonpos_of_nonneg_of_nonpos (hnn j) (hy j)
      exact this.trans (by positivity)
