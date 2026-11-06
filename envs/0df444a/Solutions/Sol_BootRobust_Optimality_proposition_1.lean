-- Prove2me | solution 1 for BootRobust.Optimality.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:19:07.999206+00:00
-- url     : https://prove2.me/submissions/eb854478-00d9-4875-95aa-413b62d3c064

import Mathlib
import Definitions.Def_BootRobust_Optimality_Setting
import Theorems.Thm_BootRobust_Optimality_separation
import Theorems.Thm_BootRobust_Optimality_N_subset_disapp
import Theorems.Thm_BootRobust_Optimality_eq_31_sanov_lower
import Theorems.Thm_BootRobust_Optimality_bootDist_segment_le

open MeasureTheory

/-- Per-term Gibbs bound: `x - q ≤ x log (x / q)`, strictly unless `x = q`. -/
theorem br3_term_bound (x q : ℝ) (hx : 0 ≤ x) (hq : 0 < q) :
    x - q ≤ x * Real.log (x / q) ∧ (x ≠ q → x - q < x * Real.log (x / q)) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp; exact ⟨hq.le, fun _ => hq⟩
  · have hl : Real.log (x / q) = - Real.log (q / x) := by
      rw [← Real.log_inv, inv_div]
    have e : x * (q / x - 1) = q - x := by field_simp
    refine ⟨?_, fun hne => ?_⟩
    · have := Real.log_le_sub_one_of_pos (div_pos hq h)
      rw [hl]; nlinarith [mul_le_mul_of_nonneg_left this h.le]
    · have hne' : q / x ≠ 1 := by
        intro h1; rw [div_eq_one_iff_eq h.ne'] at h1; exact hne h1.symm
      have := Real.log_lt_sub_one_of_pos (div_pos hq h) hne'
      rw [hl]; nlinarith [mul_lt_mul_of_pos_left this h]

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (R : (ι → ℝ) → (ι → ℝ) → EReal) (hR : BootRobust.Optimality.IsDistributionDistance R)
    (D Dtr : ι → ℝ) (hD : D ∈ stdSimplex ℝ ι) (hDtr : Dtr ∈ stdSimplex ℝ ι)
    (hDtrpos : ∀ i, 0 < Dtr i) (r : ℝ) (hB : BootRobust.Perf.bootDist D Dtr = (r : EReal))
    (N : Set (ι → ℝ)) (hN : BootRobust.Optimality.relOpen N) (hDN : D ∈ N)
    (hRN : ∀ D' ∈ N, (r : EReal) < R D' Dtr) :
    ∃ G : ι → ℝ, (∀ i, 0 ≤ G i) ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (Real.exp (-((n : ℝ) * (r - ε)))) ≤
        BootRobust.Optimality.bootLaw Dtr n
          {ω | BootRobust.Optimality.empDist ω ∈ BootRobust.Optimality.linDisapp R Dtr r G} := by
  classical
  -- the bootstrap distance to `Dtr` is the finite sum
  have hBsum : ∀ E : ι → ℝ, BootRobust.Perf.bootDist E Dtr =
      ((∑ i, E i * Real.log (E i / Dtr i) : ℝ) : EReal) := by
    intro E
    unfold BootRobust.Perf.bootDist
    rw [if_pos]
    intro i hi; exact absurd hi (hDtrpos i).ne'
  -- Step 0: `r > 0` (Gibbs' inequality and discrimination of `R`)
  have hr : 0 < r := by
    have hrsum : ∑ i, D i * Real.log (D i / Dtr i) = r := by
      have := hB; rw [hBsum] at this; exact_mod_cast this
    by_cases hDeq : D = Dtr
    · exfalso
      have h1 := hRN D hDN
      rw [hDeq, (hR.eq_zero_iff Dtr hDtr Dtr hDtr).mpr rfl] at h1
      have h2 : r = 0 := by
        rw [← hrsum, hDeq]
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [div_self (hDtrpos i).ne', Real.log_one, mul_zero]
      rw [h2] at h1; exact lt_irrefl _ h1
    · obtain ⟨j, hj⟩ : ∃ j, D j ≠ Dtr j := by
        by_contra h; exact hDeq (funext fun i => by by_contra h'; exact h ⟨i, h'⟩)
      have hlt : ∑ i, (D i - Dtr i) < ∑ i, D i * Real.log (D i / Dtr i) :=
        Finset.sum_lt_sum (fun i _ => (br3_term_bound _ _ (hD.1 i) (hDtrpos i)).1)
          ⟨j, Finset.mem_univ _, (br3_term_bound _ _ (hD.1 j) (hDtrpos j)).2 hj⟩
      rw [Finset.sum_sub_distrib, hD.2, hDtr.2, sub_self, hrsum] at hlt
      exact hlt
  -- Step 1: a point `D1 = λ D + (1 - λ) Dtr ∈ N` with `λ ∈ (0,1)`
  obtain ⟨U, hU, rfl⟩ := hN
  have hseg : Filter.Tendsto (fun l : ℝ => l • D + (1 - l) • Dtr) (nhdsWithin 1 (Set.Iio 1))
      (nhds D) := by
    have hc : Continuous (fun l : ℝ => l • D + (1 - l) • Dtr) := by fun_prop
    have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio 1))
    simpa using this
  have hev : ∀ᶠ l in nhdsWithin (1 : ℝ) (Set.Iio 1),
      l • D + (1 - l) • Dtr ∈ U ∧ l ∈ Set.Ioo (0 : ℝ) 1 :=
    Filter.Eventually.and (hseg.eventually (hU.mem_nhds hDN.1)) (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1))
  obtain ⟨l, hlU, hl⟩ := hev.exists
  set D1 := l • D + (1 - l) • Dtr with hD1
  have hD1simp : D1 ∈ stdSimplex ℝ ι :=
    (convex_stdSimplex ℝ ι) hD hDtr hl.1.le (by linarith [hl.2]) (by ring)
  have hD1pos : ∀ i, 0 < D1 i := by
    intro i
    simp only [hD1, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := mul_pos (show 0 < 1 - l by linarith [hl.2]) (hDtrpos i)
    nlinarith [mul_nonneg hl.1.le (hD.1 i)]
  have hBD1 := (BootRobust.Optimality.bootDist_segment_le D Dtr hD hDtr hDtrpos l
    ⟨hl.1.le, hl.2.le⟩).2.2 r hB hr hl
  set b1 := ∑ i, D1 i * Real.log (D1 i / Dtr i) with hb1
  have hb1r : b1 < r := by
    rw [hBsum] at hBD1; exact_mod_cast hBD1
  -- Step 2: a convex, relatively open neighbourhood `N'` of `D1` inside `N`, of positive points
  let pos : Set (ι → ℝ) := ⋂ i, {y | 0 < y i}
  have hpos_open : IsOpen pos :=
    isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (continuous_apply i))
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hU.inter hpos_open) D1
    ⟨hlU, Set.mem_iInter.mpr hD1pos⟩
  let N' : Set (ι → ℝ) := Metric.ball D1 δ ∩ stdSimplex ℝ ι
  have hN'open : BootRobust.Optimality.relOpen N' := ⟨_, Metric.isOpen_ball, rfl⟩
  have hN'conv : Convex ℝ N' := (convex_ball D1 δ).inter (convex_stdSimplex ℝ ι)
  have hD1N' : D1 ∈ N' := ⟨Metric.mem_ball_self hδ, hD1simp⟩
  have hN'sub : N' ⊆ U ∩ stdSimplex ℝ ι := fun x hx => ⟨(hball hx.1).1, hx.2⟩
  have hN'pos : ∀ D' ∈ N', ∀ i, 0 < D' i := fun x hx i =>
    Set.mem_iInter.mp (hball hx.1).2 i
  have hRN' : ∀ D' ∈ N', (r : EReal) < R D' Dtr := fun x hx => hRN x (hN'sub hx)
  -- Step 3: Hahn–Banach separation, then shift `G` to be nonnegative
  obtain ⟨G0, a, hG0ball, hG0N⟩ := BootRobust.Optimality.separation R hR Dtr hDtr r N'
    hN'open hN'conv ⟨D1, hD1N'⟩ hN'pos hRN'
  set M := ∑ j, |G0 j| with hM
  let G : ι → ℝ := fun i => G0 i + M
  have hGnn : ∀ i, 0 ≤ G i := by
    intro i
    have : |G0 i| ≤ M := Finset.single_le_sum (f := fun j => |G0 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
    show 0 ≤ G0 i + M
    linarith [neg_abs_le (G0 i)]
  have hGsum : ∀ E ∈ stdSimplex ℝ ι, ∑ i, E i * G i = ∑ i, E i * G0 i + M := by
    intro E hE
    simp only [G, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hE.2, one_mul]
  have hball' : ∀ E ∈ stdSimplex ℝ ι, R E Dtr ≤ (r : EReal) → ∑ i, E i * G i ≤ a + M := by
    intro E hE hER; rw [hGsum E hE]; linarith [hG0ball E hE hER]
  have hsep' : ∀ D' ∈ N', a + M < ∑ i, D' i * G i := by
    intro E hE; rw [hGsum E hE.2]; linarith [hG0N E hE]
  -- Step 4: `N' = int N' ⊆ ℛ`
  obtain ⟨hint, hsub⟩ := BootRobust.Optimality.N_subset_disapp R Dtr r N' hN'open G (a + M)
    hball' hsep'
  have hD1int : D1 ∈ BootRobust.Optimality.relInt (BootRobust.Optimality.linDisapp R Dtr r G) := by
    have h := hD1N'
    rw [← hint] at h
    obtain ⟨hs, W, hW, hD1W, hWsub⟩ := h
    exact ⟨hs, W, hW, hD1W, hWsub.trans hsub⟩
  -- Step 5: Sanov's lower bound at `D1`
  have hS := BootRobust.Optimality.eq_31_sanov_lower Dtr hDtr hDtrpos
    (BootRobust.Optimality.linDisapp R Dtr r G) D1 hD1int ((r - b1) / 2) (by linarith)
  refine ⟨G, hGnn, (r - b1) / 2, by linarith, ?_⟩
  filter_upwards [hS] with n hn
  rw [hBsum, EReal.toReal_coe] at hn
  have e : r - (r - b1) / 2 = b1 + (r - b1) / 2 := by ring
  rw [e]
  exact hn
