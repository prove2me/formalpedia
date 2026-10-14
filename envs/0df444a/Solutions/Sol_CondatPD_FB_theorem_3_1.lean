-- Prove2me | solution 1 for CondatPD.FB.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:09:45.912982+00:00
-- url     : https://prove2.me/submissions/0303b366-dfd4-4320-811b-fa5dd48569dd

import Mathlib
import Definitions.Def_CondatPD_FB_Setting
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

set_option autoImplicit false

open Filter Topology

/-! ## Weak sequential compactness (copied from Sol_pv_84835cb2, accepted) -/

open InertialFB.IFB in
theorem cfb_weak_compact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (x : ℕ → H) (M : ℝ) (hM : ∀ n, ‖x n‖ ≤ M) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ p : H, WeakTendsto (x ∘ σ) p := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK : IsCompact (Set.univ.pi fun _ : ℕ => Set.Icc (-(M * M)) (M * M)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hF : ∀ n, (fun m => inner ℝ (x n) (x m)) ∈
      Set.univ.pi fun _ : ℕ => Set.Icc (-(M * M)) (M * M) := by
    intro n m _
    have h1 := abs_real_inner_le_norm (x n) (x m)
    have h2 : ‖x n‖ * ‖x m‖ ≤ M * M := mul_le_mul (hM n) (hM m) (norm_nonneg _) hM0
    exact abs_le.1 (h1.trans h2)
  obtain ⟨c, -, σ, hσ, hlim⟩ := hK.tendsto_subseq hF
  refine ⟨σ, hσ, ?_⟩
  have hcoord : ∀ m, Tendsto (fun j => inner ℝ (x (σ j)) (x m)) atTop (𝓝 (c m)) :=
    fun m => (continuous_apply m).continuousAt.tendsto.comp hlim
  have hspan : ∀ v ∈ Submodule.span ℝ (Set.range x),
      ∃ l, Tendsto (fun j => inner ℝ (x (σ j)) v) atTop (𝓝 l) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨m, rfl⟩ := hv
      exact ⟨c m, hcoord m⟩
    | zero => exact ⟨0, by simp⟩
    | add v w _ _ hv hw =>
      obtain ⟨l1, h1⟩ := hv
      obtain ⟨l2, h2⟩ := hw
      exact ⟨l1 + l2, by simpa only [inner_add_right] using h1.add h2⟩
    | smul r v _ hv =>
      obtain ⟨l, h⟩ := hv
      exact ⟨r * l, by simpa only [real_inner_smul_right] using h.const_mul r⟩
  have hcl : ∀ v ∈ closure ((Submodule.span ℝ (Set.range x) : Submodule ℝ H) : Set H),
      ∃ l, Tendsto (fun j => inner ℝ (x (σ j)) v) atTop (𝓝 l) := by
    intro v hv
    apply cauchySeq_tendsto_of_complete
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hδ : 0 < ε / (3 * (M + 1)) := by positivity
    obtain ⟨w, hwK, hvw⟩ := Metric.mem_closure_iff.1 hv _ hδ
    obtain ⟨l, hl⟩ := hspan w hwK
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 3) (by positivity)
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    have e1 : ∀ j, |inner ℝ (x (σ j)) v - inner ℝ (x (σ j)) w| ≤ M * (ε / (3 * (M + 1))) := by
      intro j
      rw [← inner_sub_right]
      refine (abs_real_inner_le_norm _ _).trans ?_
      refine mul_le_mul (hM _) ?_ (norm_nonneg _) hM0
      rw [← dist_eq_norm]
      exact hvw.le
    have e2 : M * (ε / (3 * (M + 1))) ≤ ε / 3 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [Real.dist_eq] at h1 ⊢
    have a1 := abs_le.1 ((e1 m).trans e2)
    have a2 := abs_le.1 ((e1 n).trans e2)
    have a3 := abs_lt.1 h1
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have hall : ∀ v : H, ∃ l, Tendsto (fun j => inner ℝ (x (σ j)) v) atTop (𝓝 l) := by
    intro v
    obtain ⟨y1, hy1, z1, hz1, rfl⟩ :=
      (Submodule.span ℝ (Set.range x)).topologicalClosure.exists_add_mem_mem_orthogonal v
    have hy1' : y1 ∈ closure ((Submodule.span ℝ (Set.range x) : Submodule ℝ H) : Set H) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hy1
    obtain ⟨l, hl⟩ := hcl y1 hy1'
    refine ⟨l, ?_⟩
    have hz : ∀ j, inner ℝ (x (σ j)) z1 = 0 := fun j =>
      Submodule.inner_right_of_mem_orthogonal
        ((Submodule.span ℝ (Set.range x)).le_topologicalClosure
          (Submodule.subset_span ⟨σ j, rfl⟩)) hz1
    simpa only [inner_add_right, hz, add_zero] using hl
  choose f hf using hall
  have hfadd : ∀ v w, f (v + w) = f v + f w := fun v w =>
    tendsto_nhds_unique (hf (v + w)) (by simpa only [inner_add_right] using (hf v).add (hf w))
  have hfsmul : ∀ (r : ℝ) v, f (r • v) = r * f v := fun r v =>
    tendsto_nhds_unique (hf (r • v))
      (by simpa only [real_inner_smul_right] using (hf v).const_mul r)
  have hfb : ∀ v, ‖f v‖ ≤ M * ‖v‖ := by
    intro v
    refine le_of_tendsto' (hf v).norm (fun j => ?_)
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
  let fl : H →ₗ[ℝ] ℝ :=
    { toFun := f
      map_add' := hfadd
      map_smul' := fun r v => by
        simp only [RingHom.id_apply, smul_eq_mul]
        exact hfsmul r v }
  let fc : StrongDual ℝ H := fl.mkContinuous M hfb
  refine ⟨(InnerProductSpace.toDual ℝ H).symm fc, fun v => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  have e : fc v = f v := rfl
  rw [e]
  exact hf v

theorem cfb_qfejer {V ε : ℕ → ℝ} {m B : ℝ} (hV : ∀ k, V (k + 1) ≤ V k + ε k)
    (hε : ∀ k, 0 ≤ ε k) (hεB : ∀ N, ∑ k ∈ Finset.range N, ε k ≤ B) (hm : ∀ k, m ≤ V k) :
    ∃ l, Tendsto V atTop (𝓝 l) := by
  have hs : Summable ε := summable_of_sum_range_le hε hεB
  have hAanti : Antitone (fun k => V k - ∑ j ∈ Finset.range k, ε j) := by
    apply antitone_nat_of_succ_le
    intro k
    simp only [Finset.sum_range_succ]
    linarith [hV k]
  have hAbdd : BddBelow (Set.range (fun k => V k - ∑ j ∈ Finset.range k, ε j)) := by
    refine ⟨m - B, ?_⟩
    rintro _ ⟨k, rfl⟩
    simp only
    linarith [hm k, hεB k]
  have h1 := tendsto_atTop_ciInf hAanti hAbdd
  have h2 := hs.hasSum.tendsto_sum_nat
  refine ⟨(⨅ i, (V i - ∑ j ∈ Finset.range i, ε j)) + ∑' k, ε k, ?_⟩
  refine (h1.add h2).congr (fun k => ?_)
  ring

/-! ## Generic Hilbert-space Krasnosel'skii–Mann machinery -/

section KM

open ThreeOpSplitting.Convergence

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem cfb_avg_id (a b : K) (t : ℝ) :
    ‖(1 - t) • a + t • b‖ ^ 2 = (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - t * (1 - t) * ‖b - a‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_comm b a]
  ring

/-- C2: demiclosedness of `I - T` at a bounded weakly convergent sequence. -/
theorem cfb_demiclosed (T : K → K) (hT : IsNonexpansive T)
    (s : ℕ → K) (p : K) (M : ℝ) (hM : ∀ n, ‖s n‖ ≤ M) (hs : WeakTendsto s p)
    (hr : Tendsto (fun n => ‖T (s n) - s n‖) atTop (𝓝 0)) : T p = p := by
  have key : ∀ n, ‖p - T p‖ ^ 2 ≤ 2 * ‖T (s n) - s n‖ * (M + ‖p‖) + ‖T (s n) - s n‖ ^ 2
      - 2 * (inner ℝ (s n) (p - T p) - inner ℝ p (p - T p)) := by
    intro n
    have h1 : ‖s n - T p‖ ^ 2 =
        ‖s n - p‖ ^ 2 + 2 * inner ℝ (s n - p) (p - T p) + ‖p - T p‖ ^ 2 := by
      have e1 : s n - T p = (s n - p) + (p - T p) := by abel
      rw [e1, norm_add_sq_real]
    have h2 : ‖s n - T p‖ ≤ ‖T (s n) - s n‖ + ‖s n - p‖ := by
      have e2 : s n - T p = -(T (s n) - s n) + (T (s n) - T p) := by abel
      rw [e2]
      refine (norm_add_le _ _).trans ?_
      rw [norm_neg]
      linarith [hT (s n) p]
    have h3 : ‖s n - p‖ ≤ M + ‖p‖ := (norm_sub_le _ _).trans (by linarith [hM n])
    have h4 : ‖s n - T p‖ ^ 2 ≤ (‖T (s n) - s n‖ + ‖s n - p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h5 : ‖T (s n) - s n‖ * ‖s n - p‖ ≤ ‖T (s n) - s n‖ * (M + ‖p‖) :=
      mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    have h6 : inner ℝ (s n - p) (p - T p) = inner ℝ (s n) (p - T p) - inner ℝ p (p - T p) :=
      inner_sub_left _ _ _
    nlinarith
  have hlim : Tendsto (fun n => 2 * ‖T (s n) - s n‖ * (M + ‖p‖) + ‖T (s n) - s n‖ ^ 2
      - 2 * (inner ℝ (s n) (p - T p) - inner ℝ p (p - T p))) atTop (𝓝 0) := by
    have hw : Tendsto (fun n => inner ℝ (s n) (p - T p) - inner ℝ p (p - T p)) atTop (𝓝 0) := by
      have := (hs (p - T p)).sub_const (inner ℝ p (p - T p))
      simpa using this
    have := (((hr.const_mul 2).mul_const (M + ‖p‖)).add (hr.pow 2)).sub (hw.const_mul 2)
    simpa using this
  have h0 : ‖p - T p‖ ^ 2 ≤ 0 := ge_of_tendsto' hlim key
  have : ‖p - T p‖ = 0 := by nlinarith [norm_nonneg (p - T p)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm

/-- Uniqueness of weak cluster points when all distances to `S` converge. -/
theorem cfb_uniq (s : ℕ → K) (S : Set K)
    (hd : ∀ z ∈ S, ∃ l, Tendsto (fun n => ‖s n - z‖) atTop (𝓝 l))
    {p q : K} (hp : p ∈ S) (hq : q ∈ S) {φ ψ : ℕ → ℕ} (hφ : StrictMono φ) (hψ : StrictMono ψ)
    (hwp : WeakTendsto (s ∘ φ) p) (hwq : WeakTendsto (s ∘ ψ) q) : p = q := by
  obtain ⟨lp, hlp⟩ := hd p hp
  obtain ⟨lq, hlq⟩ := hd q hq
  have hg : Tendsto (fun n => inner ℝ (s n) (q - p)) atTop
      (𝓝 ((lp ^ 2 - lq ^ 2 - ‖p‖ ^ 2 + ‖q‖ ^ 2) / 2)) := by
    have h := ((((hlp.pow 2).sub (hlq.pow 2)).sub_const (‖p‖ ^ 2)).add_const (‖q‖ ^ 2)).div_const 2
    refine h.congr (fun n => ?_)
    rw [norm_sub_sq_real, norm_sub_sq_real, inner_sub_right]
    ring
  have h1 := tendsto_nhds_unique (hg.comp hφ.tendsto_atTop) (hwp (q - p))
  have h2 := tendsto_nhds_unique (hg.comp hψ.tendsto_atTop) (hwq (q - p))
  have h3 : inner ℝ (q - p) (q - p) = (0:ℝ) := by
    rw [inner_sub_left]; linarith
  rw [real_inner_self_eq_norm_sq] at h3
  have : ‖q - p‖ = 0 := by nlinarith [norm_nonneg (q - p)]
  rw [norm_eq_zero, sub_eq_zero] at this
  exact this.symm

/-- C3: Opial-type lemma. -/
theorem cfb_opial [CompleteSpace K] (s : ℕ → K) (M : ℝ) (hM : ∀ n, ‖s n‖ ≤ M) (S : Set K)
    (hd : ∀ z ∈ S, ∃ l, Tendsto (fun n => ‖s n - z‖) atTop (𝓝 l))
    (hc : ∀ (φ : ℕ → ℕ) (p : K), StrictMono φ → WeakTendsto (s ∘ φ) p → p ∈ S) :
    ∃ p ∈ S, WeakTendsto s p := by
  obtain ⟨σ, hσ, p, hp⟩ := cfb_weak_compact s M hM
  have hpS := hc σ p hσ hp
  refine ⟨p, hpS, fun v => ?_⟩
  by_contra hcon
  obtain ⟨t, ht, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hcon
  obtain ⟨ψ, hψ, hψs⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨σ', hσ', p', hp'⟩ := cfb_weak_compact (s ∘ ψ) M (fun n => hM _)
  have hp'S := hc (ψ ∘ σ') p' (hψ.comp hσ') hp'
  have hpp : p = p' := cfb_uniq s S hd hpS hp'S hσ (hψ.comp hσ') hp hp'
  subst hpp
  obtain ⟨j, hj⟩ := ((hp' v).eventually_mem ht).exists
  exact hψs (σ' j) hj

/-- C4: inexact Krasnosel'skii–Mann iteration converges weakly to a fixed point. -/
theorem cfb_KM [CompleteSpace K] (R : K → K) (hR : IsNonexpansive R)
    (hfix : ∃ z, R z = z) (lam : ℕ → ℝ) (e s : ℕ → K)
    (hlam : ∀ n, 0 < lam n ∧ lam n < 1)
    (hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N, lam n * (1 - lam n)) atTop atTop)
    (he : Summable (fun n => lam n * ‖e n‖))
    (hs : ∀ n, s (n + 1) = s n + lam n • (R (s n) + e n - s n)) :
    ∃ z, R z = z ∧ WeakTendsto s z ∧ ∃ M, ∀ n, ‖s n‖ ≤ M := by
  set E := ∑' n, lam n * ‖e n‖ with hE
  have he0 : ∀ n, 0 ≤ lam n * ‖e n‖ := fun n => mul_nonneg (hlam n).1.le (norm_nonneg _)
  have hEb : ∀ N, ∑ n ∈ Finset.range N, lam n * ‖e n‖ ≤ E :=
    fun N => he.sum_le_tsum (Finset.range N) (fun i _ => he0 i)
  have hE0 : 0 ≤ E := by have := hEb 0; simpa using this
  have hEn : ∀ n, lam n * ‖e n‖ ≤ E := fun n => by
    have h1 := hEb (n + 1)
    rw [Finset.sum_range_succ] at h1
    have h2 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.range n) => he0 i)
    linarith
  have hstep : ∀ n z, R z = z → s (n + 1) - z =
      ((1 - lam n) • (s n - z) + lam n • (R (s n) - R z)) + lam n • e n := by
    intro n z hz; rw [hs n, hz]; module
  have hfe : ∀ z, R z = z → ∀ n, ‖s (n + 1) - z‖ ≤ ‖s n - z‖ + lam n * ‖e n‖ := by
    intro z hz n
    rw [hstep n z hz]
    have h1 := hR (s n) z
    have hl := hlam n
    calc _ ≤ ‖(1 - lam n) • (s n - z) + lam n • (R (s n) - R z)‖ + ‖lam n • e n‖ :=
          norm_add_le _ _
      _ ≤ (‖(1 - lam n) • (s n - z)‖ + ‖lam n • (R (s n) - R z)‖) + ‖lam n • e n‖ := by
          gcongr; exact norm_add_le _ _
      _ = (1 - lam n) * ‖s n - z‖ + lam n * ‖R (s n) - R z‖ + lam n * ‖e n‖ := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
            Real.norm_of_nonneg hl.1.le]
      _ ≤ ‖s n - z‖ + lam n * ‖e n‖ := by nlinarith
  have hbd : ∀ z, R z = z → ∀ n, ‖s n - z‖ ≤ ‖s 0 - z‖ + E := by
    intro z hz n
    have : ∀ n, ‖s n - z‖ ≤ ‖s 0 - z‖ + ∑ k ∈ Finset.range n, lam k * ‖e k‖ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ]; linarith [hfe z hz n]
    linarith [this n, hEb n]
  have hconv : ∀ z, R z = z → ∃ l, Tendsto (fun n => ‖s n - z‖) atTop (𝓝 l) := by
    intro z hz
    exact cfb_qfejer (hfe z hz) he0 hEb (fun k => norm_nonneg _)
  obtain ⟨z0, hz0⟩ := hfix
  set D := ‖s 0 - z0‖ + E with hD
  have hsq : ∀ n, ‖s (n + 1) - z0‖ ^ 2 ≤ ‖s n - z0‖ ^ 2
      - lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 + (2 * D + E) * (lam n * ‖e n‖) := by
    intro n
    have hl := hlam n
    set u := (1 - lam n) • (s n - z0) + lam n • (R (s n) - R z0) with hu
    have hid : ‖u‖ ^ 2 = (1 - lam n) * ‖s n - z0‖ ^ 2 + lam n * ‖R (s n) - R z0‖ ^ 2
        - lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 := by
      rw [hu, show R (s n) - s n = (R (s n) - R z0) - (s n - z0) by rw [hz0]; abel]
      exact cfb_avg_id _ _ _
    have hu1 : ‖u‖ ^ 2 ≤ ‖s n - z0‖ ^ 2 - lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 := by
      have h2 : ‖R (s n) - R z0‖ ^ 2 ≤ ‖s n - z0‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hR (s n) z0) 2
      rw [hid]; nlinarith
    have hu2 : ‖u‖ ≤ D := by
      have h7 : 0 ≤ lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 :=
        mul_nonneg (mul_nonneg hl.1.le (by linarith)) (sq_nonneg _)
      have h8 : ‖u‖ ≤ ‖s n - z0‖ := by nlinarith [norm_nonneg u, norm_nonneg (s n - z0)]
      linarith [hbd z0 hz0 n]
    have hsn : s (n + 1) - z0 = u + lam n • e n := by rw [hu]; exact hstep n z0 hz0
    have h3 : ‖s (n + 1) - z0‖ ≤ ‖u‖ + lam n * ‖e n‖ := by
      rw [hsn]; refine (norm_add_le _ _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hl.1.le]
    have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
    have h5 := hEn n
    have h6 := he0 n
    nlinarith [mul_le_mul_of_nonneg_right hu2 h6, mul_le_mul_of_nonneg_right h5 h6]
  have hw0 : ∀ n, 0 ≤ lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 := fun n => by
    have := hlam n
    exact mul_nonneg (mul_nonneg this.1.le (by linarith)) (sq_nonneg _)
  have hwsum : ∀ N, ∑ n ∈ Finset.range N, lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 ≤
      D ^ 2 + (2 * D + E) * E := by
    intro N
    have hT : ∀ N, ‖s N - z0‖ ^ 2 + ∑ n ∈ Finset.range N,
        lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2 ≤
        ‖s 0 - z0‖ ^ 2 + (2 * D + E) * ∑ n ∈ Finset.range N, lam n * ‖e n‖ := by
      intro N
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
        linarith [hsq N]
    have h1 := hT N
    have h2 : ‖s 0 - z0‖ ^ 2 ≤ D ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (by rw [hD]; linarith) 2
    have hD0 : 0 ≤ 2 * D + E := by rw [hD]; linarith [norm_nonneg (s 0 - z0)]
    have h3 := mul_le_mul_of_nonneg_left (hEb N) hD0
    nlinarith [sq_nonneg ‖s N - z0‖]
  have hwS := summable_of_sum_range_le hw0 hwsum
  have hres : ∀ n, ‖R (s (n + 1)) - s (n + 1)‖ ≤ ‖R (s n) - s n‖ + 2 * (lam n * ‖e n‖) := by
    intro n
    have hl := hlam n
    have hd1 : s (n + 1) - s n = lam n • (R (s n) - s n) + lam n • e n := by
      rw [hs n]; module
    have hd2 : R (s (n + 1)) - s (n + 1) = (R (s (n + 1)) - R (s n)) +
        ((1 - lam n) • (R (s n) - s n) - lam n • e n) := by
      generalize R (s (n + 1)) = a
      rw [hs n]; module
    have hn1 : ‖s (n + 1) - s n‖ ≤ lam n * ‖R (s n) - s n‖ + lam n * ‖e n‖ := by
      rw [hd1]; refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hl.1.le]
    have hn2 : ‖(1 - lam n) • (R (s n) - s n) - lam n • e n‖ ≤
        (1 - lam n) * ‖R (s n) - s n‖ + lam n * ‖e n‖ := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hl.1.le,
        Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ 1 - lam n)]
    rw [hd2]
    refine (norm_add_le _ _).trans ?_
    linarith [hR (s (n + 1)) (s n)]
  obtain ⟨l, hl⟩ := cfb_qfejer (V := fun n => ‖R (s n) - s n‖) (ε := fun n => 2 * (lam n * ‖e n‖)) (B := 2 * E) hres (fun n => by linarith [he0 n])
    (fun N => by rw [← Finset.mul_sum]; linarith [hEb N]) (fun _ => norm_nonneg _)
  have hl0 : 0 ≤ l := ge_of_tendsto' hl (fun n => norm_nonneg _)
  have hlz : l = 0 := by
    by_contra hne
    have hlpos : 0 < l := lt_of_le_of_ne hl0 (Ne.symm hne)
    have hev : ∀ᶠ n in atTop, l / 2 < ‖R (s n) - s n‖ :=
      hl.eventually (lt_mem_nhds (by linarith))
    have hsum2 : Summable (fun n => lam n * (1 - lam n)) := by
      refine Summable.of_norm_bounded_eventually_nat (hwS.mul_left (4 / l ^ 2)) ?_
      filter_upwards [hev] with n hn
      have h1 := hlam n
      have hp : 0 ≤ lam n * (1 - lam n) := mul_nonneg h1.1.le (by linarith)
      rw [Real.norm_of_nonneg hp]
      have h2 : l ^ 2 / 4 ≤ ‖R (s n) - s n‖ ^ 2 := by nlinarith
      have h3 : 1 ≤ 4 / l ^ 2 * ‖R (s n) - s n‖ ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]; linarith
      have h4 : 4 / l ^ 2 * (lam n * (1 - lam n) * ‖R (s n) - s n‖ ^ 2) =
          lam n * (1 - lam n) * (4 / l ^ 2 * ‖R (s n) - s n‖ ^ 2) := by ring
      rw [h4]
      nlinarith
    exact not_tendsto_atTop_of_tendsto_nhds hsum2.hasSum.tendsto_sum_nat hdiv
  rw [hlz] at hl
  have hMb : ∀ n, ‖s n‖ ≤ ‖z0‖ + D := fun n => by
    have h1 := hbd z0 hz0 n
    have h2 : ‖s n‖ ≤ ‖s n - z0‖ + ‖z0‖ := by
      calc ‖s n‖ = ‖(s n - z0) + z0‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith
  obtain ⟨p, hpS, hp⟩ := cfb_opial s (‖z0‖ + D) hMb {z | R z = z} (fun z hz => hconv z hz)
    (fun φ p hφ hwp => by
      show R p = p
      exact cfb_demiclosed R hR (s ∘ φ) p (‖z0‖ + D) (fun n => hMb _) hwp
        (hl.comp hφ.tendsto_atTop))
  exact ⟨p, hpS, hp, _, hMb⟩

end KM

/-! ## The P-metric Hilbert space on `X × Y` -/

section PSpace

open ThreeOpSplitting.Convergence

theorem cfb_le_of_sq {A B c C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hc : c ≤ C ^ 2)
    (h : A ^ 2 ≤ c * B ^ 2) : A ≤ C * B := by
  have h1 : A ^ 2 ≤ (C * B) ^ 2 := by nlinarith [sq_nonneg B]
  nlinarith [mul_nonneg hC hB]

/-- Elementary bounds for the quadratic form `(1/t) a² - 2 i + (1/s) b²`. -/
theorem cfb_q_bounds {a b i l t s : ℝ} (ht : 0 < t) (hs : 0 < s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hl : 0 ≤ l) (hi : |i| ≤ l * a * b) (hθ : 0 < 1 / t - s * l ^ 2) :
    (1 / t - s * l ^ 2) * a ^ 2 ≤ (1 / t) * a ^ 2 - 2 * i + (1 / s) * b ^ 2 ∧
    b ^ 2 ≤ 2 * s * (1 + s * l ^ 2 / (1 / t - s * l ^ 2)) *
      ((1 / t) * a ^ 2 - 2 * i + (1 / s) * b ^ 2) ∧
    (1 / t) * a ^ 2 - 2 * i + (1 / s) * b ^ 2 ≤ (1 / t + l) * a ^ 2 + (1 / s + l) * b ^ 2 := by
  have hi1 := (abs_le.1 hi).1
  have hi2 := (abs_le.1 hi).2
  set θ := 1 / t - s * l ^ 2 with hθdef
  set q := (1 / t) * a ^ 2 - 2 * i + (1 / s) * b ^ 2 with hq
  have k1 : (1 / s) * (s * l * a - b) ^ 2 = s * l ^ 2 * a ^ 2 - 2 * (l * a * b) + (1 / s) * b ^ 2 := by
    field_simp; ring
  have k2 : (1 / (2 * s)) * (2 * s * l * a - b) ^ 2 =
      2 * s * l ^ 2 * a ^ 2 - 2 * (l * a * b) + (1 / (2 * s)) * b ^ 2 := by
    field_simp; ring
  have p1 : 0 ≤ (1 / s) * (s * l * a - b) ^ 2 := by positivity
  have p2 : 0 ≤ (1 / (2 * s)) * (2 * s * l * a - b) ^ 2 := by positivity
  have c1 : θ * a ^ 2 ≤ q := by rw [hθdef, hq]; nlinarith
  refine ⟨c1, ?_, ?_⟩
  · -- b²/(2s) ≤ q + s l² a² ≤ q + s l² q / θ
    have c2 : (1 / (2 * s)) * b ^ 2 ≤ q + s * l ^ 2 * a ^ 2 := by
      have e : (1 / s) * b ^ 2 - (1 / (2 * s)) * b ^ 2 = (1 / (2 * s)) * b ^ 2 := by
        field_simp; ring
      rw [hq]; nlinarith
    have c3 : a ^ 2 ≤ q / θ := by rw [le_div_iff₀ hθ]; linarith
    have c4 : s * l ^ 2 * a ^ 2 ≤ s * l ^ 2 * (q / θ) :=
      mul_le_mul_of_nonneg_left c3 (by positivity)
    have e2 : 2 * s * (1 + s * l ^ 2 / θ) * q = 2 * s * (q + s * l ^ 2 * (q / θ)) := by ring
    rw [e2]
    have e3 : b ^ 2 = 2 * s * ((1 / (2 * s)) * b ^ 2) := by field_simp
    rw [e3]
    have : 0 < 2 * s := by positivity
    nlinarith
  · rw [hq]; nlinarith [sq_nonneg (a - b), mul_nonneg hl (sq_nonneg (a - b))]

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Parameters of the `P`-metric. -/
structure CFBParams (X Y : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] where
  τ : ℝ
  σ : ℝ
  L : X →L[ℝ] Y
  hτ : 0 < τ
  hσ : 0 < σ
  hθ : 0 < 1 / τ - σ * ‖L‖ ^ 2

/-- `X × Y` carrying the `P`-inner product. -/
def CFBProd (p : CFBParams X Y) : Type _ := X × Y

namespace CFBProd

variable (p : CFBParams X Y)

instance : AddCommGroup (CFBProd p) := inferInstanceAs (AddCommGroup (X × Y))
instance : Module ℝ (CFBProd p) := inferInstanceAs (Module ℝ (X × Y))

/-- The identification with `X × Y`. -/
def equiv : (X × Y) ≃ₗ[ℝ] CFBProd p := LinearEquiv.refl ℝ (X × Y)

def mk (x : X) (y : Y) : CFBProd p := equiv p (x, y)
def fst (z : CFBProd p) : X := ((equiv p).symm z).1
def snd (z : CFBProd p) : Y := ((equiv p).symm z).2

variable {p}

@[simp] theorem fst_mk (x : X) (y : Y) : fst p (mk p x y) = x := rfl
@[simp] theorem snd_mk (x : X) (y : Y) : snd p (mk p x y) = y := rfl
@[simp] theorem fst_add (z w : CFBProd p) : fst p (z + w) = fst p z + fst p w := rfl
@[simp] theorem snd_add (z w : CFBProd p) : snd p (z + w) = snd p z + snd p w := rfl
@[simp] theorem fst_smul (c : ℝ) (z : CFBProd p) : fst p (c • z) = c • fst p z := rfl
@[simp] theorem snd_smul (c : ℝ) (z : CFBProd p) : snd p (c • z) = c • snd p z := rfl
@[simp] theorem fst_sub (z w : CFBProd p) : fst p (z - w) = fst p z - fst p w := rfl
@[simp] theorem snd_sub (z w : CFBProd p) : snd p (z - w) = snd p z - snd p w := rfl
@[simp] theorem fst_zero : fst p (0 : CFBProd p) = 0 := rfl
@[simp] theorem snd_zero : snd p (0 : CFBProd p) = 0 := rfl
theorem mk_fst_snd (z : CFBProd p) : mk p (fst p z) (snd p z) = z := rfl
theorem ext' {z w : CFBProd p} (h1 : fst p z = fst p w) (h2 : snd p z = snd p w) : z = w := by
  rw [← mk_fst_snd z, ← mk_fst_snd w, h1, h2]
theorem mk_sub (x x' : X) (y y' : Y) : mk p x y - mk p x' y' = mk p (x - x') (y - y') := rfl
theorem mk_add (x x' : X) (y y' : Y) : mk p x y + mk p x' y' = mk p (x + x') (y + y') := rfl
theorem mk_smul (c : ℝ) (x : X) (y : Y) : c • mk p x y = mk p (c • x) (c • y) := rfl

variable (p)

/-- The `P`-bilinear form, symmetric normal form. -/
noncomputable def pin (z w : CFBProd p) : ℝ :=
  (1 / p.τ) * inner ℝ (fst p z) (fst p w) - inner ℝ (p.L (fst p z)) (snd p w)
    - inner ℝ (p.L (fst p w)) (snd p z) + (1 / p.σ) * inner ℝ (snd p z) (snd p w)

variable {p}

theorem pin_comm (z w : CFBProd p) : pin p z w = pin p w z := by
  unfold pin
  rw [real_inner_comm (fst p w) (fst p z), real_inner_comm (snd p w) (snd p z)]
  ring

theorem pin_add_left (z z' w : CFBProd p) : pin p (z + z') w = pin p z w + pin p z' w := by
  unfold pin
  simp only [fst_add, snd_add, map_add, inner_add_left, inner_add_right]
  ring

theorem pin_smul_left (c : ℝ) (z w : CFBProd p) : pin p (c • z) w = c * pin p z w := by
  unfold pin
  simp only [fst_smul, snd_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

theorem pin_self (z : CFBProd p) : pin p z z = (1 / p.τ) * ‖fst p z‖ ^ 2
    - 2 * inner ℝ (p.L (fst p z)) (snd p z) + (1 / p.σ) * ‖snd p z‖ ^ 2 := by
  unfold pin
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

theorem pin_bounds (z : CFBProd p) :
    (1 / p.τ - p.σ * ‖p.L‖ ^ 2) * ‖fst p z‖ ^ 2 ≤ pin p z z ∧
    ‖snd p z‖ ^ 2 ≤ 2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) * pin p z z ∧
    pin p z z ≤ (1 / p.τ + ‖p.L‖) * ‖fst p z‖ ^ 2 + (1 / p.σ + ‖p.L‖) * ‖snd p z‖ ^ 2 := by
  rw [pin_self]
  refine cfb_q_bounds p.hτ p.hσ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) ?_ p.hθ
  refine (abs_real_inner_le_norm _ _).trans ?_
  have := p.L.le_opNorm (fst p z)
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

theorem pin_nonneg (z : CFBProd p) : 0 ≤ pin p z z :=
  le_trans (mul_nonneg p.hθ.le (sq_nonneg _)) (pin_bounds z).1

theorem pin_definite (z : CFBProd p) (h : pin p z z = 0) : z = 0 := by
  obtain ⟨h1, h2, -⟩ := pin_bounds z
  have hx : ‖fst p z‖ ^ 2 ≤ 0 := by
    have := p.hθ
    nlinarith [sq_nonneg ‖fst p z‖]
  have hy : ‖snd p z‖ ^ 2 ≤ 0 := by rw [h, mul_zero] at h2; exact h2
  apply ext'
  · simpa using (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hx (sq_nonneg _))
  · simpa using (pow_eq_zero_iff two_ne_zero).1 (le_antisymm hy (sq_nonneg _))

variable (p)

noncomputable instance : Inner ℝ (CFBProd p) := ⟨pin p⟩

theorem inner_def (z w : CFBProd p) : inner ℝ z w = pin p z w := rfl

noncomputable instance : NormedAddCommGroup (CFBProd p) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (CFBProd p) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun z w => by
        simp only [inner_def, conj_trivial]; exact pin_comm w z
      re_inner_nonneg := fun z => by
        simp only [inner_def, RCLike.re_to_real]; exact pin_nonneg z
      definite := fun z hz => pin_definite z hz
      add_left := fun z z' w => pin_add_left z z' w
      smul_left := fun z w r => by
        simp only [inner_def, conj_trivial]; exact pin_smul_left r z w }

noncomputable instance : InnerProductSpace ℝ (CFBProd p) :=
  InnerProductSpace.ofCore _

variable {p}

theorem norm_sq (z : CFBProd p) : ‖z‖ ^ 2 = pin p z z := by
  rw [← real_inner_self_eq_norm_sq]; rfl

theorem norm_fst_le (z : CFBProd p) :
    ‖fst p z‖ ≤ ((1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ + 1) * ‖z‖ := by
  have hθ := p.hθ
  have h1 := (pin_bounds z).1
  rw [← norm_sq] at h1
  have hi : 0 < (1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ := inv_pos.2 hθ
  refine cfb_le_of_sq (norm_nonneg _) (norm_nonneg _) (by positivity)
    (c := (1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹) (by nlinarith) ?_
  rw [inv_mul_eq_div, le_div_iff₀ hθ]; linarith

theorem norm_snd_le (z : CFBProd p) :
    ‖snd p z‖ ≤ (2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) + 1) * ‖z‖ := by
  have hθ := p.hθ
  have hσ := p.hσ
  have h1 := (pin_bounds z).2.1
  rw [← norm_sq] at h1
  have hc : 0 ≤ 2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) := by positivity
  exact cfb_le_of_sq (norm_nonneg _) (norm_nonneg _) (by positivity) (by nlinarith) h1

theorem norm_equiv_le (w : X × Y) :
    ‖equiv p w‖ ≤ (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) * ‖w‖ := by
  have hτ := p.hτ
  have hσ := p.hσ
  have h1 := (pin_bounds (equiv p w)).2.2
  rw [← norm_sq] at h1
  have ha : ‖fst p (equiv p w)‖ ≤ ‖w‖ := _root_.norm_fst_le w
  have hb : ‖snd p (equiv p w)‖ ≤ ‖w‖ := _root_.norm_snd_le w
  have ha2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hl := norm_nonneg p.L
  have hc : 0 ≤ 1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ := by positivity
  refine cfb_le_of_sq (norm_nonneg _) (norm_nonneg _) (by positivity)
    (c := 1 / p.τ + 1 / p.σ + 2 * ‖p.L‖) (by nlinarith) ?_
  have e1 : 0 ≤ 1 / p.τ + ‖p.L‖ := by positivity
  have e2 : 0 ≤ 1 / p.σ + ‖p.L‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left ha2 e1, mul_le_mul_of_nonneg_left hb2 e2]

theorem norm_equiv_symm_le (z : CFBProd p) :
    ‖(equiv p).symm z‖ ≤ (((1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ + 1) +
      (2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) + 1)) * ‖z‖ := by
  rw [Prod.norm_def, add_mul]
  refine max_le ?_ ?_
  · have := norm_fst_le z
    have : 0 ≤ (2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) + 1) * ‖z‖ := by
      have := p.hθ; have := p.hσ; positivity
    unfold fst at *; linarith
  · have := norm_snd_le z
    have : 0 ≤ ((1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ + 1) * ‖z‖ := by
      have := p.hθ; positivity
    unfold snd at *; linarith

instance [CompleteSpace X] [CompleteSpace Y] : CompleteSpace (CFBProd p) := by
  have hu := (equiv p).isUniformEmbedding
    (AddMonoidHomClass.continuous_of_bound (equiv p) _ norm_equiv_le)
    (AddMonoidHomClass.continuous_of_bound (equiv p).symm _ norm_equiv_symm_le)
  exact (completeSpace_congr (e := (equiv p).toEquiv) hu).mp inferInstance

end CFBProd

end PSpace

/-! ## Proximal maps and subgradients -/

section Prox

open InertialFB.IFB

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Convexity along segments, for finite values. -/
def CfbSegConvex (f : H → EReal) : Prop :=
  ∀ (a b : H) (ra rb : ℝ), f a = ra → f b = rb → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (a + t • (b - a)) ≤ (((1 - t) * ra + t * rb : ℝ) : EReal)

theorem cfb_segConvex_of_ppc {f : H → EReal}
    (hf : ThreeOpSplitting.ConvexRates.IsProperClosedConvex f) : CfbSegConvex f := by
  intro a b ra rb ha hb t ht0 ht1
  have hA : (a, ra) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, ha, le_refl]
  have hB : (b, rb) ∈ {q : H × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    simp only [Set.mem_setOf_eq, hb, le_refl]
  have := hf.2.2.2 hA hB (by linarith : (0:ℝ) ≤ 1 - t) ht0 (by ring)
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at this
  have e : (1 - t) • a + t • b = a + t • (b - a) := by module
  rw [e] at this
  exact this

theorem cfb_conj_segConvex (h : H → EReal) : CfbSegConvex (CondatPD.FB.conj h) := by
  intro a b ra rb ha hb t ht0 ht1
  unfold CondatPD.FB.conj at ha hb ⊢
  refine iSup_le (fun s' => ?_)
  have h1 := (le_iSup (fun s'' => ((inner ℝ a s'' : ℝ) : EReal) - h s'') s').trans_eq ha
  have h2 := (le_iSup (fun s'' => ((inner ℝ b s'' : ℝ) : EReal) - h s'') s').trans_eq hb
  generalize h s' = c at h1 h2 ⊢
  induction c using EReal.rec with
  | bot => simp at h1
  | top => simp
  | coe c =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h1 h2 ⊢
    rw [inner_add_left, real_inner_smul_left, inner_sub_left]
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0:ℝ) ≤ 1 - t)
    have := mul_le_mul_of_nonneg_left h2 ht0
    nlinarith

theorem cfb_conj_ne_bot {h : H → EReal} (hb : ∀ x, h x ≠ ⊥) (hfin : ∃ x, h x ≠ ⊤) (s : H) :
    CondatPD.FB.conj h s ≠ ⊥ := by
  obtain ⟨x0, hx0⟩ := hfin
  have hle := le_iSup (fun s' => ((inner ℝ s s' : ℝ) : EReal) - h s') x0
  intro hbot
  unfold CondatPD.FB.conj at hbot
  rw [hbot] at hle
  have h2 : ((inner ℝ s x0 : ℝ) : EReal) - h x0 = ⊥ := le_bot_iff.1 hle
  rw [← EReal.coe_toReal hx0 (hb x0), ← EReal.coe_sub] at h2
  exact EReal.coe_ne_bot _ h2

theorem cfb_subgrad_real {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) {a b g : H}
    (ha : IsSubgradient f a g) (hb : f b ≠ ⊤) :
    (f a).toReal + inner ℝ g (b - a) ≤ (f b).toReal := by
  have h := ha.2 b
  rw [← EReal.coe_toReal ha.1 (hbot a), ← EReal.coe_toReal hb (hbot b), ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  exact h

theorem cfb_subgrad_mono {f : H → EReal} (hbot : ∀ x, f x ≠ ⊥) {a b g h : H}
    (ha : IsSubgradient f a g) (hb : IsSubgradient f b h) : 0 ≤ inner ℝ (g - h) (a - b) := by
  have h1 := cfb_subgrad_real hbot ha hb.1
  have h2 := cfb_subgrad_real hbot hb ha.1
  have e1 : inner ℝ g (b - a) = - inner ℝ g (a - b) := by rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]; linarith

theorem cfb_prox_subgrad {f : H → EReal} {γ : ℝ} {P : H → H} (hγ : 0 < γ)
    (hbot : ∀ x, f x ≠ ⊥) (hfin : ∃ x, f x ≠ ⊤) (hc : CfbSegConvex f)
    (hP : ThreeOpSplitting.ConvexRates.IsProx γ f P) (u : H) :
    IsSubgradient f (P u) ((1 / γ) • (u - P u)) := by
  obtain ⟨x0, hx0⟩ := hfin
  have hpt : f (P u) ≠ ⊤ := by
    intro htop
    have h1 := hP u x0
    rw [htop, EReal.top_add_coe, ← EReal.coe_toReal hx0 (hbot x0), ← EReal.coe_add] at h1
    exact EReal.coe_ne_top _ (top_le_iff.1 h1)
  set p := P u with hpdef
  set rp := (f p).toReal with hrp
  have hfp : f p = rp := (EReal.coe_toReal hpt (hbot p)).symm
  refine ⟨hpt, fun v => ?_⟩
  by_cases hv : f v = ⊤
  · rw [hv]; exact le_top
  set rv := (f v).toReal with hrv
  have hfv : f v = rv := (EReal.coe_toReal hv (hbot v)).symm
  rw [hfp, hfv, ← EReal.coe_add, EReal.coe_le_coe_iff]
  set I := inner ℝ (p - u) (v - p) with hI
  set K := ‖v - p‖ ^ 2 / (2 * γ) with hK
  have hK0 : 0 ≤ K := by positivity
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → rp - rv - I / γ ≤ t * K := by
    intro t ht0 ht1
    have h1 := hP u (p + t • (v - p))
    have h2 := hc p v rp rv hfp hfv t ht0.le ht1
    have h3 := add_le_add h2
      (le_refl (((‖p + t • (v - p) - u‖ ^ 2 / (2 * γ) : ℝ) : EReal)))
    have h4 := h1.trans h3
    rw [hfp, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h4
    have e : ‖p + t • (v - p) - u‖ ^ 2 =
        ‖p - u‖ ^ 2 + 2 * t * I + t ^ 2 * ‖v - p‖ ^ 2 := by
      have : p + t • (v - p) - u = (p - u) + t • (v - p) := by abel
      rw [this, norm_add_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
        sq_abs, hI]
      ring
    rw [e, show ‖P u - u‖ = ‖p - u‖ from rfl] at h4
    have e2 : (‖p - u‖ ^ 2 + 2 * t * I + t ^ 2 * ‖v - p‖ ^ 2) / (2 * γ) =
        ‖p - u‖ ^ 2 / (2 * γ) + t * (I / γ) + t * (t * K) := by
      rw [hK]; field_simp
    rw [e2] at h4
    have h5 : t * (rp - rv - I / γ) ≤ t * (t * K) := by nlinarith
    exact le_of_mul_le_mul_left h5 ht0
  have hD : rp - rv - I / γ ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    set D := rp - rv - I / γ
    set t := min 1 (D / (2 * (K + 1))) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ D / (2 * (K + 1)) := min_le_right _ _
    have h1 := key t ht0 ht1
    have h2 : t * K ≤ D / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right ht2 hK0
    have h3 : D / (2 * (K + 1)) * K < D := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have e3 : inner ℝ ((1 / γ) • (u - p)) (v - p) = - (I / γ) := by
    rw [real_inner_smul_left, hI, ← neg_sub p u, inner_neg_left]; ring
  rw [e3]; linarith

theorem cfb_prox_eq_of_subgrad {f : H → EReal} {γ : ℝ} {P : H → H} (hγ : 0 < γ)
    (hbot : ∀ x, f x ≠ ⊥) (hfin : ∃ x, f x ≠ ⊤) (hc : CfbSegConvex f)
    (hP : ThreeOpSplitting.ConvexRates.IsProx γ f P) {u x : H}
    (hx : IsSubgradient f x ((1 / γ) • (u - x))) : P u = x := by
  have hm := cfb_subgrad_mono hbot (cfb_prox_subgrad hγ hbot hfin hc hP u) hx
  have e : (1 / γ) • (u - P u) - (1 / γ) • (u - x) = (-(1 / γ)) • (P u - x) := by module
  rw [e, real_inner_smul_left, real_inner_self_eq_norm_sq] at hm
  have hg : 0 < 1 / γ := by positivity
  have h0 : ‖P u - x‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖P u - x‖ = 0 := by nlinarith [norm_nonneg (P u - x)]
  rwa [norm_eq_zero, sub_eq_zero] at this

theorem cfb_prox_firm {f : H → EReal} {γ : ℝ} {P : H → H} (hγ : 0 < γ)
    (hbot : ∀ x, f x ≠ ⊥) (hfin : ∃ x, f x ≠ ⊤) (hc : CfbSegConvex f)
    (hP : ThreeOpSplitting.ConvexRates.IsProx γ f P) (u v : H) :
    ‖P u - P v‖ ^ 2 ≤ inner ℝ (u - v) (P u - P v) := by
  have hm := cfb_subgrad_mono hbot (cfb_prox_subgrad hγ hbot hfin hc hP u)
    (cfb_prox_subgrad hγ hbot hfin hc hP v)
  have e : (1 / γ) • (u - P u) - (1 / γ) • (v - P v) = (1 / γ) • ((u - v) - (P u - P v)) := by
    module
  rw [e, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hg : 0 < 1 / γ := by positivity
  nlinarith

theorem cfb_prox_nonexp {f : H → EReal} {γ : ℝ} {P : H → H} (hγ : 0 < γ)
    (hbot : ∀ x, f x ≠ ⊥) (hfin : ∃ x, f x ≠ ⊤) (hc : CfbSegConvex f)
    (hP : ThreeOpSplitting.ConvexRates.IsProx γ f P) (u v : H) :
    ‖P u - P v‖ ≤ ‖u - v‖ := by
  have h := cfb_prox_firm hγ hbot hfin hc hP u v
  have h2 := real_inner_le_norm (u - v) (P u - P v)
  nlinarith [norm_nonneg (P u - P v), norm_nonneg (u - v)]

end Prox

section BH

open InnerProductSpace

/-! ## Baillon–Haddad (copied from Sol_pv_1b074b71, accepted) -/

open scoped RealInnerProductSpace in
theorem bh_inner_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (z w : E) : ⟪gradient f z, w⟫ = fderiv ℝ f z w := by
  simp [gradient, InnerProductSpace.toDual_symm_apply]

open scoped RealInnerProductSpace in
theorem bh_line_deriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hdiff : Differentiable ℝ f) (y w : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (y + s • w)) ⟪gradient f (y + t • w), w⟫ t := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w t := by
    simpa using ((hasDerivAt_id t).smul_const w).const_add y
  have := (hdiff (y + t • w)).hasFDerivAt.comp_hasDerivAt t hl
  rw [bh_inner_grad]
  exact this

open scoped RealInnerProductSpace in
theorem bh_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} {L : ℝ} (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : E) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x
  let g : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫ - L / 2 * t ^ 2 * ‖w‖ ^ 2
  have hg : ∀ t, HasDerivAt g (⟪gradient f (x + t • w), w⟫ - ⟪gradient f x, w⟫
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have h1 := bh_line_deriv hdiff x w t
    have h2 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, w⟫) ⟪gradient f x, w⟫ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g _ (zero_lt_one' ℝ)
    (fun t _ => (hg t).continuousAt.continuousWithinAt) (fun t _ => hg t)
  have hle : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ - L / 2 * (2 * c) * ‖w‖ ^ 2 ≤ 0 := by
    have e1 : ⟪gradient f (x + c • w), w⟫ - ⟪gradient f x, w⟫ =
        ⟪gradient f (x + c • w) - gradient f x, w⟫ := by rw [inner_sub_left]
    have e2 := real_inner_le_norm (gradient f (x + c • w) - gradient f x) w
    have e3 := hgrad (x + c • w) x
    have e4 : ‖x + c • w - x‖ = c * ‖w‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1]
    rw [e4] at e3
    have : ‖gradient f (x + c • w) - gradient f x‖ * ‖w‖ ≤ L * (c * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right e3 (norm_nonneg _)
    nlinarith
  rw [hcd] at hle
  have : g 1 ≤ g 0 := by
    have := hle; simp only [sub_zero, div_one] at this; linarith
  simp only [g, one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, sub_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at this
  have hw : x + w = y := by simp [w]
  rw [hw] at this
  linarith

open scoped RealInnerProductSpace in
theorem bh_convex_fo {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (x y : E) : f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set w := y - x
  have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • w)) := by
    have := hf.comp_affineMap (AffineMap.lineMap x y)
    simp only [Set.preimage_univ] at this
    have e : (fun t : ℝ => f (x + t • w)) = f ∘ AffineMap.lineMap x y := by
      funext t
      simp [AffineMap.lineMap_apply, w, add_comm]
    rw [e]; exact this
  have h := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
    (by simpa using bh_line_deriv hdiff x w 0)
  rw [slope_def_field] at h
  simp only [zero_smul, add_zero, one_smul, sub_zero, div_one] at h
  have hw : x + w = y := by simp [w]
  rw [hw] at h
  rw [bh_inner_grad]
  linarith


/-- Descent lemma: a convex function whose subgradient selection is nonexpansive
is majorized by its tangent plus `½‖w - z‖²`. -/
theorem bh_mdescent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) (z w : H) :
    φ w - φ z - ⟪w - z, p z⟫_ℝ ≤ ‖w - z‖ ^ 2 / 2 := by
  have step : ∀ n : ℕ, ∀ z w : H,
      φ w - φ z - ⟪w - z, p z⟫_ℝ ≤ (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * ‖w - z‖ ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro z w
      have h1 := hs w z
      have h2 : ⟪z - w, p w⟫_ℝ = -⟪w - z, p w⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      have h3 : ⟪w - z, p w - p z⟫_ℝ = ⟪w - z, p w⟫_ℝ - ⟪w - z, p z⟫_ℝ :=
        inner_sub_right _ _ _
      have h4 := real_inner_le_norm (w - z) (p w - p z)
      have h5 := hL w z
      have h6 := norm_nonneg (w - z)
      have h7 : ‖w - z‖ * ‖p w - p z‖ ≤ ‖w - z‖ * ‖w - z‖ := mul_le_mul_of_nonneg_left h5 h6
      have h8 : (1 / 2 + (1 / 2 : ℝ) ^ (0 + 1)) * ‖w - z‖ ^ 2 = ‖w - z‖ * ‖w - z‖ := by ring
      rw [h8]
      linarith
    | succ n ih =>
      intro z w
      have hmz : (z + (1 / 2 : ℝ) • (w - z)) - z = (1 / 2 : ℝ) • (w - z) := by abel
      have hwm : w - (z + (1 / 2 : ℝ) • (w - z)) = (1 / 2 : ℝ) • (w - z) := by
        have : w - (z + (1 / 2 : ℝ) • (w - z)) = (w - z) - (1 / 2 : ℝ) • (w - z) := by abel
        rw [this]
        nth_rewrite 1 [← one_smul ℝ (w - z)]
        rw [← sub_smul]
        norm_num
      have nhalf : ‖(1 / 2 : ℝ) • (w - z)‖ = ‖w - z‖ / 2 := by
        rw [norm_smul]; norm_num; ring
      have h1 := ih z (z + (1 / 2 : ℝ) • (w - z))
      have h2 := ih (z + (1 / 2 : ℝ) • (w - z)) w
      rw [hmz, nhalf] at h1
      rw [hwm, nhalf] at h2
      have hsplit : ⟪w - z, p z⟫_ℝ = ⟪(1 / 2 : ℝ) • (w - z), p z⟫_ℝ
          + ⟪(1 / 2 : ℝ) • (w - z), p z⟫_ℝ := by
        rw [← inner_add_left, ← add_smul]; norm_num
      have hcross : ⟪(1 / 2 : ℝ) • (w - z), p (z + (1 / 2 : ℝ) • (w - z)) - p z⟫_ℝ
          ≤ ‖w - z‖ ^ 2 / 4 := by
        have ha := real_inner_le_norm ((1 / 2 : ℝ) • (w - z))
          (p (z + (1 / 2 : ℝ) • (w - z)) - p z)
        have hb := hL (z + (1 / 2 : ℝ) • (w - z)) z
        rw [hmz, nhalf] at hb
        rw [nhalf] at ha
        have hc := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ ‖w - z‖ / 2)
        nlinarith
      rw [inner_sub_right] at hcross
      have hpow : (1 / 2 : ℝ) ^ (n + 1 + 1) = (1 / 2 : ℝ) ^ (n + 1) / 2 := by
        rw [pow_succ]; ring
      rw [hpow]
      have hid : (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * (‖w - z‖ / 2) ^ 2
          + (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * (‖w - z‖ / 2) ^ 2 + ‖w - z‖ ^ 2 / 4
          = (1 / 2 + (1 / 2 : ℝ) ^ (n + 1) / 2) * ‖w - z‖ ^ 2 := by ring
      rw [hsplit]
      linarith
  have ht : Filter.Tendsto (fun n : ℕ => (1 / 2 + (1 / 2 : ℝ) ^ (n + 1)) * ‖w - z‖ ^ 2)
      Filter.atTop (nhds ((1 / 2 + 0) * ‖w - z‖ ^ 2)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (Filter.tendsto_add_atTop_nat 1)
    exact (h0.const_add (1 / 2)).mul_const _
  have hlim := ge_of_tendsto' ht (fun n => step n z w)
  linarith

open scoped InnerProductSpace in
/-- Baillon–Haddad type co-coercivity inequality. -/
theorem bh_cocoercive {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : H → H) (φ : H → ℝ) (hL : ∀ z w, ‖p z - p w‖ ≤ ‖z - w‖)
    (hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u) (z w : H) :
    φ z + ⟪w - z, p z⟫_ℝ + ‖p w - p z‖ ^ 2 / 2 ≤ φ w := by
  have h1 := hs z (w - (p w - p z))
  have h2 := bh_mdescent p φ hL hs w (w - (p w - p z))
  have e1 : w - (p w - p z) - z = (w - z) - (p w - p z) := by abel
  have e2 : w - (p w - p z) - w = -(p w - p z) := by abel
  rw [e1, inner_sub_left] at h1
  rw [e2, inner_neg_left, norm_neg] at h2
  have e3 : ‖p w - p z‖ ^ 2 = ⟪p w - p z, p w⟫_ℝ - ⟪p w - p z, p z⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_right]
  linarith


open scoped RealInnerProductSpace in
theorem bh_main {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (J : K → ℝ) (κ : ℝ)
    (hconv : ConvexOn ℝ Set.univ J) (hdiff : Differentiable ℝ J) (hκ : 0 < κ)
    (hlip : ∀ x y : K, ‖κ • gradient J x - κ • gradient J y‖ ≤ ‖x - y‖) (x y : K) :
    κ * ‖gradient J x - gradient J y‖ ^ 2 ≤ ⟪gradient J x - gradient J y, x - y⟫_ℝ := by
  set p : K → K := fun z => κ • gradient J z with hp
  set φ : K → ℝ := fun z => κ * J z with hφ
  have hs : ∀ z u, φ z + ⟪u - z, p z⟫_ℝ ≤ φ u := by
    intro z u
    have h := bh_convex_fo hconv hdiff z u
    simp only [φ, p, real_inner_smul_right]
    rw [real_inner_comm]
    nlinarith
  have h1 := bh_cocoercive p φ hlip hs x y
  have h2 := bh_cocoercive p φ hlip hs y x
  have e : p x - p y = κ • (gradient J x - gradient J y) := by simp [p, smul_sub]
  have e' : p y - p x = -(p x - p y) := by abel
  rw [e', norm_neg] at h1
  have hsum : ‖p x - p y‖ ^ 2 ≤ ⟪x - y, p x - p y⟫_ℝ := by
    have : ⟪y - x, p x⟫_ℝ + ⟪x - y, p y⟫_ℝ = -⟪x - y, p x - p y⟫_ℝ := by
      have hn : ⟪y - x, p x⟫_ℝ = -⟪x - y, p x⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      rw [inner_sub_right, hn]; ring
    linarith
  rw [e, norm_smul, real_inner_smul_right, Real.norm_eq_abs, abs_of_pos hκ, mul_pow,
    real_inner_comm] at hsum
  have : κ * (κ * ‖gradient J x - gradient J y‖ ^ 2) ≤ κ * ⟪gradient J x - gradient J y, x - y⟫_ℝ := by
    nlinarith
  exact le_of_mul_le_mul_left this hκ

end BH

/-! ## The Algorithm 3.1 map in the P-metric -/

section Alg31

open InertialFB.IFB CFBProd

/-- Data making a proximal map well behaved. -/
def CfbProxOK {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (γ : ℝ)
    (f : H → EReal) (P : H → H) : Prop :=
  0 < γ ∧ (∀ x, f x ≠ ⊥) ∧ (∃ x, f x ≠ ⊤) ∧ CfbSegConvex f ∧
    ThreeOpSplitting.ConvexRates.IsProx γ f P

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

noncomputable def cfbTx (p : CFBParams X Y) (F : X → ℝ) (PG : X → X) (z : CFBProd p) : X :=
  PG (fst p z - p.τ • gradient F (fst p z) - p.τ • ContinuousLinearMap.adjoint p.L (snd p z))

noncomputable def cfbTy (p : CFBParams X Y) (F : X → ℝ) (PG : X → X) (PH : Y → Y)
    (z : CFBProd p) : Y :=
  PH (snd p z + p.σ • p.L ((2 : ℝ) • cfbTx p F PG z - fst p z))

noncomputable def cfbT1 (p : CFBParams X Y) (F : X → ℝ) (PG : X → X) (PH : Y → Y)
    (z : CFBProd p) : CFBProd p :=
  mk p (cfbTx p F PG z) (cfbTy p F PG PH z)

@[simp] theorem cfb_fst_T1 (p : CFBParams X Y) (F : X → ℝ) (PG : X → X) (PH : Y → Y)
    (z : CFBProd p) : fst p (cfbT1 p F PG PH z) = cfbTx p F PG z := rfl
@[simp] theorem cfb_snd_T1 (p : CFBParams X Y) (F : X → ℝ) (PG : X → X) (PH : Y → Y)
    (z : CFBProd p) : snd p (cfbT1 p F PG PH z) = cfbTy p F PG PH z := rfl

theorem cfb_T1_key (p : CFBParams X Y) (F : X → ℝ) (G : X → EReal) (H : Y → EReal)
    (PG : X → X) (PH : Y → Y)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH) (z z' : CFBProd p) :
    inner ℝ (gradient F (fst p z) - gradient F (fst p z')) (cfbTx p F PG z - cfbTx p F PG z') ≤
      inner ℝ ((z - cfbT1 p F PG PH z) - (z' - cfbT1 p F PG PH z'))
        (cfbT1 p F PG PH z - cfbT1 p F PG PH z') := by
  obtain ⟨hτ, hGb, hGf, hGc, hPG⟩ := hG
  obtain ⟨hσ, hHb, hHf, hHc, hPH⟩ := hH
  set L := p.L with hL
  set τ := p.τ with hτdef
  set σ := p.σ with hσdef
  set x := fst p z with hx
  set y := snd p z with hy
  set x' := fst p z' with hx'
  set y' := snd p z' with hy'
  set tx := cfbTx p F PG z with htx
  set tx' := cfbTx p F PG z' with htx'
  set ty := cfbTy p F PG PH z with hty
  set ty' := cfbTy p F PG PH z' with hty'
  set gx := gradient F x with hgx
  set gx' := gradient F x' with hgx'
  have m1 : 0 ≤ inner ℝ ((1 / τ) • ((x - τ • gx - τ • ContinuousLinearMap.adjoint L y) - tx) -
      (1 / τ) • ((x' - τ • gx' - τ • ContinuousLinearMap.adjoint L y') - tx')) (tx - tx') :=
    cfb_subgrad_mono hGb (cfb_prox_subgrad hτ hGb hGf hGc hPG _)
      (cfb_prox_subgrad hτ hGb hGf hGc hPG _)
  have m2 : 0 ≤ inner ℝ ((1 / σ) • ((y + σ • L ((2 : ℝ) • tx - x)) - ty) -
      (1 / σ) • ((y' + σ • L ((2 : ℝ) • tx' - x')) - ty')) (ty - ty') :=
    cfb_subgrad_mono hHb (cfb_prox_subgrad hσ hHb hHf hHc hPH _)
      (cfb_prox_subgrad hσ hHb hHf hHc hPH _)
  have e1 : (1 / τ) • ((x - τ • gx - τ • ContinuousLinearMap.adjoint L y) - tx) -
      (1 / τ) • ((x' - τ • gx' - τ • ContinuousLinearMap.adjoint L y') - tx') =
      (1 / τ) • ((x - x') - τ • (gx - gx') - τ • ContinuousLinearMap.adjoint L (y - y') -
        (tx - tx')) := by
    rw [← smul_sub]; congr 1; rw [map_sub]; simp only [smul_sub]; abel
  have e2 : (1 / σ) • ((y + σ • L ((2 : ℝ) • tx - x)) - ty) -
      (1 / σ) • ((y' + σ • L ((2 : ℝ) • tx' - x')) - ty') =
      (1 / σ) • ((y - y') + σ • ((2 : ℝ) • L (tx - tx') - L (x - x')) - (ty - ty')) := by
    rw [← smul_sub]; congr 1; simp only [map_sub, map_smul, smul_sub]; abel
  rw [e1, real_inner_smul_left] at m1
  rw [e2, real_inner_smul_left] at m2
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hτi : 0 < 1 / τ := by positivity
  have hσi : 0 < 1 / σ := by positivity
  have m1' := (mul_nonneg_iff_of_pos_left hτi).1 m1
  have m2' := (mul_nonneg_iff_of_pos_left hσi).1 m2
  rw [inner_sub_left, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm (L (tx - tx')) (y - y')] at m1'
  rw [inner_sub_left (y - y' + σ • ((2 : ℝ) • L (tx - tx') - L (x - x'))) (ty - ty') (ty - ty'),
    inner_add_left (y - y') (σ • ((2 : ℝ) • L (tx - tx') - L (x - x'))) (ty - ty'),
    real_inner_smul_left, inner_sub_left ((2 : ℝ) • L (tx - tx')) (L (x - x')) (ty - ty'),
    real_inner_smul_left] at m2'
  -- the P-inner product of the residual with the step
  have hp : inner ℝ ((z - cfbT1 p F PG PH z) - (z' - cfbT1 p F PG PH z'))
      (cfbT1 p F PG PH z - cfbT1 p F PG PH z') =
      (1 / τ) * (inner ℝ (x - x') (tx - tx') - inner ℝ (tx - tx') (tx - tx'))
      - (inner ℝ (L (x - x')) (ty - ty') - inner ℝ (L (tx - tx')) (ty - ty'))
      - (inner ℝ (L (tx - tx')) (y - y') - inner ℝ (L (tx - tx')) (ty - ty'))
      + (1 / σ) * (inner ℝ (y - y') (ty - ty') - inner ℝ (ty - ty') (ty - ty')) := by
    simp only [hx, hy, hx', hy', htx, htx', hty, hty', hL, hτdef, hσdef]
    rw [inner_def]
    unfold pin
    simp only [fst_sub, snd_sub, cfb_fst_T1, cfb_snd_T1, map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hp]
  have k1 : (1 / τ) * (inner ℝ (x - x') (tx - tx') - inner ℝ (tx - tx') (tx - tx')) =
      (1 / τ) * (inner ℝ (x - x') (tx - tx') - τ * inner ℝ (gx - gx') (tx - tx') -
        τ * inner ℝ (L (tx - tx')) (y - y') - inner ℝ (tx - tx') (tx - tx'))
      + inner ℝ (gx - gx') (tx - tx') + inner ℝ (L (tx - tx')) (y - y') := by
    field_simp; ring
  have k2 : (1 / σ) * (inner ℝ (y - y') (ty - ty') - inner ℝ (ty - ty') (ty - ty')) =
      (1 / σ) * (inner ℝ (y - y') (ty - ty') + σ * ((2 : ℝ) * inner ℝ (L (tx - tx')) (ty - ty') -
        inner ℝ (L (x - x')) (ty - ty')) - inner ℝ (ty - ty') (ty - ty'))
      - (2 * inner ℝ (L (tx - tx')) (ty - ty') - inner ℝ (L (x - x')) (ty - ty')) := by
    field_simp; ring
  rw [k1, k2]
  have := mul_nonneg hτi.le m1'
  have := mul_nonneg hσi.le m2'
  nlinarith

theorem cfb_T1_avg (p : CFBParams X Y) (F : X → ℝ) (G : X → EReal) (H : Y → EReal)
    (PG : X → X) (PH : Y → Y) (β : ℝ) (hF : CondatPD.FB.IsSmoothTerm β F) (hβ : 0 < β)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH) (z z' : CFBProd p) :
    ‖cfbT1 p F PG PH z - cfbT1 p F PG PH z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 -
      (1 - β / (2 * (1 / p.τ - p.σ * ‖p.L‖ ^ 2))) *
        ‖(z - cfbT1 p F PG PH z) - (z' - cfbT1 p F PG PH z')‖ ^ 2 := by
  set T := cfbT1 p F PG PH with hT
  set θ := 1 / p.τ - p.σ * ‖p.L‖ ^ 2 with hθ
  have hθ0 : 0 < θ := p.hθ
  set u := (z - T z) - (z' - T z') with hu
  have hkey := cfb_T1_key p F G H PG PH hG hH z z'
  rw [← hT, ← hu] at hkey
  set A := gradient F (fst p z) - gradient F (fst p z') with hA
  have hfu : fst p u = (fst p z - fst p z') - (cfbTx p F PG z - cfbTx p F PG z') := by
    rw [hu]; simp only [fst_sub, hT, cfb_fst_T1]; abel
  have hdtx : cfbTx p F PG z - cfbTx p F PG z' = (fst p z - fst p z') - fst p u := by
    rw [hfu]; abel
  rw [hdtx, inner_sub_right] at hkey
  -- Baillon–Haddad
  have hbh : (1 / β) * ‖A‖ ^ 2 ≤ inner ℝ A (fst p z - fst p z') := by
    have hlip : ∀ a b : X, ‖(1 / β) • gradient F a - (1 / β) • gradient F b‖ ≤ ‖a - b‖ := by
      intro a b
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
      have := hF.2.2.2 a b
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hβ]
      linarith
    exact bh_main F (1 / β) hF.1 hF.2.1 (by positivity) hlip (fst p z) (fst p z')
  have hcs : inner ℝ A (fst p u) ≤ ‖A‖ * ‖fst p u‖ := real_inner_le_norm _ _
  have hfu2 : θ * ‖fst p u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq]; exact (pin_bounds u).1
  have hsq : 0 ≤ (1 / β) * (‖A‖ - β / 2 * ‖fst p u‖) ^ 2 := by positivity
  have hsq' : (1 / β) * (‖A‖ - β / 2 * ‖fst p u‖) ^ 2 =
      (1 / β) * ‖A‖ ^ 2 - ‖A‖ * ‖fst p u‖ + β / 4 * ‖fst p u‖ ^ 2 := by
    field_simp; ring
  -- lower bound for ⟪u, Tz - Tz'⟫
  have hlow : -(β / (4 * θ)) * ‖u‖ ^ 2 ≤ inner ℝ u (T z - T z') := by
    have h1 : β / 4 * ‖fst p u‖ ^ 2 ≤ β / (4 * θ) * ‖u‖ ^ 2 := by
      have : β / (4 * θ) * ‖u‖ ^ 2 = β / 4 * (‖u‖ ^ 2 / θ) := by field_simp
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ hθ0]; linarith
    linarith
  have hTd : T z - T z' = (z - z') - u := by rw [hu]; abel
  have hn : ‖T z - T z'‖ ^ 2 = ‖z - z'‖ ^ 2 - 2 * inner ℝ (z - z') u + ‖u‖ ^ 2 := by
    rw [hTd, norm_sub_sq_real]
  have hi : inner ℝ u (T z - T z') = inner ℝ (z - z') u - ‖u‖ ^ 2 := by
    rw [hTd, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  have e3 : (1 - β / (2 * θ)) * ‖u‖ ^ 2 = ‖u‖ ^ 2 - 2 * (β / (4 * θ) * ‖u‖ ^ 2) := by
    field_simp; ring
  rw [hn, e3]
  nlinarith

end Alg31

/-! ## Fixed points, the relaxed map, weak transfer, and the Algorithm 3.1 half -/

section Glue

open CFBProd ThreeOpSplitting.Convergence

theorem cfb_smul_cancel {E : Type*} [AddCommGroup E] [Module ℝ E] {c : ℝ} (hc : c ≠ 0) (a : E) :
    (1 / c) • (c • a) = a := by rw [smul_smul, one_div, inv_mul_cancel₀ hc, one_smul]

noncomputable def cfbR {K : Type*} [AddCommGroup K] [Module ℝ K] (T : K → K) (δ : ℝ) (z : K) : K :=
  δ • T z - (δ - 1) • z

theorem cfb_R_nonexp {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] (T : K → K)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hT : ∀ z z', ‖T z - T z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 - (δ - 1) * ‖(z - T z) - (z' - T z')‖ ^ 2) :
    IsNonexpansive (cfbR T δ) := by
  intro z z'
  have hb : T z - T z' = (z - z') - ((z - T z) - (z' - T z')) := by abel
  have hR : cfbR T δ z - cfbR T δ z' = (z - z') - δ • ((z - T z) - (z' - T z')) := by
    unfold cfbR; module
  have h1 := hT z z'
  rw [hb, norm_sub_sq_real] at h1
  rw [hR]
  have h2 : ‖(z - z') - δ • ((z - T z) - (z' - T z'))‖ ^ 2 = ‖z - z'‖ ^ 2
      - 2 * δ * inner ℝ (z - z') ((z - T z) - (z' - T z'))
      + δ ^ 2 * ‖(z - T z) - (z' - T z')‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have h4 : δ * ‖(z - T z) - (z' - T z')‖ ^ 2 ≤
      2 * inner ℝ (z - z') ((z - T z) - (z' - T z')) := by linarith
  have h3 : ‖(z - z') - δ • ((z - T z) - (z' - T z'))‖ ^ 2 ≤ ‖z - z'‖ ^ 2 := by
    rw [h2]; nlinarith [mul_le_mul_of_nonneg_left h4 hδ]
  nlinarith [norm_nonneg ((z - z') - δ • ((z - T z) - (z' - T z'))), norm_nonneg (z - z')]

theorem cfb_R_fix {K : Type*} [AddCommGroup K] [Module ℝ K] (T : K → K) {δ : ℝ} (hδ : δ ≠ 0)
    (z : K) : cfbR T δ z = z ↔ T z = z := by
  have e : cfbR T δ z - z = δ • (T z - z) := by unfold cfbR; module
  rw [← sub_eq_zero, e, smul_eq_zero, sub_eq_zero]
  simp [hδ]

theorem cfb_weak_of_subseq {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] (s : ℕ → K) (M : ℝ) (hM : ∀ n, ‖s n‖ ≤ M) (q : K)
    (h : ∀ (φ : ℕ → ℕ) (p : K), StrictMono φ → WeakTendsto (s ∘ φ) p → p = q) :
    WeakTendsto s q := by
  intro v
  by_contra hcon
  obtain ⟨t, ht, hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.1 hcon
  obtain ⟨ψ, hψ, hψs⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨σ', hσ', p', hp'⟩ := cfb_weak_compact (s ∘ ψ) M (fun n => hM _)
  have hq := h (ψ ∘ σ') p' (hψ.comp hσ') hp'
  subst hq
  obtain ⟨j, hj⟩ := ((hp' v).eventually_mem ht).exists
  exact hψs (σ' j) hj

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem cfb_pin_eq_left {p : CFBParams X Y} (v w : CFBProd p) :
    inner ℝ v w = inner ℝ (fst p v) ((1 / p.τ) • fst p w - ContinuousLinearMap.adjoint p.L (snd p w))
      + inner ℝ (snd p v) (-(p.L (fst p w)) + (1 / p.σ) • snd p w) := by
  rw [inner_def]; unfold pin
  rw [inner_sub_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    inner_add_right, inner_neg_right, real_inner_smul_right,
    real_inner_comm (snd p v) (p.L (fst p w))]
  ring

theorem cfb_transfer {p : CFBParams X Y} (s : ℕ → CFBProd p) (M : ℝ) (hM : ∀ n, ‖s n‖ ≤ M)
    (zs : CFBProd p) (hw : WeakTendsto s zs) :
    WeakTendsto (fun n => fst p (s n)) (fst p zs) ∧
      WeakTendsto (fun n => snd p (s n)) (snd p zs) := by
  have hθ := p.hθ
  have hσ := p.hσ
  have hcx : 0 ≤ (1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ + 1 := by positivity
  have hcy : 0 ≤ 2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) + 1 := by
    positivity
  have hX : ∀ n, ‖fst p (s n)‖ ≤ ((1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ + 1) * M := fun n =>
    (CFBProd.norm_fst_le (s n)).trans (mul_le_mul_of_nonneg_left (hM n) hcx)
  have hY : ∀ n, ‖snd p (s n)‖ ≤
      (2 * p.σ * (1 + p.σ * ‖p.L‖ ^ 2 / (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) + 1) * M := fun n =>
    (CFBProd.norm_snd_le (s n)).trans (mul_le_mul_of_nonneg_left (hM n) hcy)
  have claim : ∀ (φ : ℕ → ℕ) (x' : X) (y' : Y), StrictMono φ →
      WeakTendsto (fun n => fst p (s (φ n))) x' → WeakTendsto (fun n => snd p (s (φ n))) y' →
      mk p x' y' = zs := by
    intro φ x' y' hφ hx hy
    have h3 : ∀ w, inner ℝ (mk p x' y' - zs) w = 0 := by
      intro w
      have h1 : Tendsto (fun n => inner ℝ (s (φ n)) w) atTop (𝓝 (inner ℝ (mk p x' y') w)) := by
        simp only [cfb_pin_eq_left, fst_mk, snd_mk]
        exact (hx _).add (hy _)
      have h2 : Tendsto (fun n => inner ℝ (s (φ n)) w) atTop (𝓝 (inner ℝ zs w)) :=
        (hw w).comp hφ.tendsto_atTop
      rw [inner_sub_left, tendsto_nhds_unique h1 h2, sub_self]
    have h4 := h3 (mk p x' y' - zs)
    rw [real_inner_self_eq_norm_sq] at h4
    have : ‖mk p x' y' - zs‖ = 0 := by nlinarith [norm_nonneg (mk p x' y' - zs)]
    rwa [norm_eq_zero, sub_eq_zero] at this
  constructor
  · refine cfb_weak_of_subseq _ _ hX _ (fun φ x' hφ hx' => ?_)
    obtain ⟨ψ, hψ, y', hy'⟩ := cfb_weak_compact (fun n => snd p (s (φ n))) _ (fun n => hY _)
    have hx'' : WeakTendsto (fun n => fst p (s (φ (ψ n)))) x' :=
      fun v => (hx' v).comp hψ.tendsto_atTop
    have := claim (φ ∘ ψ) x' y' (hφ.comp hψ) hx'' hy'
    rw [← this, fst_mk]
  · refine cfb_weak_of_subseq _ _ hY _ (fun φ y' hφ hy' => ?_)
    obtain ⟨ψ, hψ, x', hx'⟩ := cfb_weak_compact (fun n => fst p (s (φ n))) _ (fun n => hX _)
    have hy'' : WeakTendsto (fun n => snd p (s (φ (ψ n)))) y' :=
      fun v => (hy' v).comp hψ.tendsto_atTop
    have := claim (φ ∘ ψ) x' y' (hφ.comp hψ) hx' hy''
    rw [← this, snd_mk]

theorem cfb_T1_fix_iff (p : CFBParams X Y) (F : X → ℝ) (G : X → EReal) (H : Y → EReal)
    (PG : X → X) (PH : Y → Y)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH) (z : CFBProd p) :
    cfbT1 p F PG PH z = z ↔ CondatPD.FB.IsPDSolution F G H p.L (fst p z) (snd p z) := by
  obtain ⟨hτ, hGb, hGf, hGc, hPG⟩ := hG
  obtain ⟨hσ, hHb, hHf, hHc, hPH⟩ := hH
  have eG : (1 / p.τ) • ((fst p z - p.τ • gradient F (fst p z) -
      p.τ • ContinuousLinearMap.adjoint p.L (snd p z)) - fst p z)
      = -(ContinuousLinearMap.adjoint p.L (snd p z)) - gradient F (fst p z) := by
    have : (fst p z - p.τ • gradient F (fst p z) - p.τ • ContinuousLinearMap.adjoint p.L (snd p z))
        - fst p z = p.τ • (-(ContinuousLinearMap.adjoint p.L (snd p z)) - gradient F (fst p z)) := by
      module
    rw [this, cfb_smul_cancel hτ.ne']
  have eH : (1 / p.σ) • ((snd p z + p.σ • p.L (fst p z)) - snd p z) = p.L (fst p z) := by
    rw [add_sub_cancel_left, cfb_smul_cancel hσ.ne']
  have e2 : (2 : ℝ) • fst p z - fst p z = fst p z := by module
  have hTy : cfbTy p F PG PH z =
      PH (snd p z + p.σ • p.L ((2 : ℝ) • cfbTx p F PG z - fst p z)) := rfl
  have hTx : cfbTx p F PG z = PG (fst p z - p.τ • gradient F (fst p z) -
      p.τ • ContinuousLinearMap.adjoint p.L (snd p z)) := rfl
  constructor
  · intro hT
    have htx : cfbTx p F PG z = fst p z := by rw [← cfb_fst_T1 p F PG PH z, hT]
    have hty : cfbTy p F PG PH z = snd p z := by rw [← cfb_snd_T1 p F PG PH z, hT]
    refine ⟨?_, ?_⟩
    · have h := cfb_prox_subgrad hτ hGb hGf hGc hPG
        (fst p z - p.τ • gradient F (fst p z) - p.τ • ContinuousLinearMap.adjoint p.L (snd p z))
      rw [← hTx, htx, eG] at h
      exact h
    · have h := cfb_prox_subgrad hσ hHb hHf hHc hPH (snd p z + p.σ • p.L (fst p z))
      have h' : PH (snd p z + p.σ • p.L (fst p z)) = snd p z := by
        rw [hTy, htx, e2] at hty; exact hty
      rw [h', eH] at h
      exact h
  · rintro ⟨h1, h2⟩
    have htx : cfbTx p F PG z = fst p z := by
      rw [hTx]
      apply cfb_prox_eq_of_subgrad hτ hGb hGf hGc hPG
      rw [eG]; exact h1
    have hty : cfbTy p F PG PH z = snd p z := by
      rw [hTy, htx, e2]
      apply cfb_prox_eq_of_subgrad hσ hHb hHf hHc hPH
      rw [eH]; exact h2
    exact ext' (by rw [cfb_fst_T1, htx]) (by rw [cfb_snd_T1, hty])

end Glue

/-! ## Abstract glue and the Algorithm 3.1 half -/

section Glue2

open CFBProd ThreeOpSplitting.Convergence

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem cfb_glue {p : CFBParams X Y} (T : CFBProd p → CFBProd p) (δ : ℝ) (hδ1 : 1 ≤ δ)
    (hT : ∀ z z', ‖T z - T z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 - (δ - 1) * ‖(z - T z) - (z' - T z')‖ ^ 2)
    (hfix : ∃ z, T z = z) (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n ∧ ρ n < δ)
    (hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (δ - ρ n)) atTop atTop)
    (s Z : ℕ → CFBProd p) (hs : ∀ n, s (n + 1) = ρ n • Z n + (1 - ρ n) • s n)
    (hZ : Summable (fun n => ρ n * ‖Z n - T (s n)‖)) :
    ∃ zs, T zs = zs ∧ WeakTendsto (fun n => fst p (s n)) (fst p zs) ∧
      WeakTendsto (fun n => snd p (s n)) (snd p zs) := by
  have hδ0 : 0 < δ := by linarith
  have hδne : δ ≠ 0 := hδ0.ne'
  have hRne := cfb_R_nonexp T δ hδ0.le hT
  have hRfix : ∃ z, cfbR T δ z = z := by
    obtain ⟨z, hz⟩ := hfix; exact ⟨z, (cfb_R_fix T hδne z).2 hz⟩
  have hlam : ∀ n, 0 < ρ n / δ ∧ ρ n / δ < 1 := fun n =>
    ⟨div_pos (hρ n).1 hδ0, (div_lt_one hδ0).2 (hρ n).2⟩
  have hdiv' : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n / δ * (1 - ρ n / δ)) atTop atTop := by
    have e : (fun N => ∑ n ∈ Finset.range N, ρ n / δ * (1 - ρ n / δ)) =
        fun N => (1 / δ ^ 2) * ∑ n ∈ Finset.range N, ρ n * (δ - ρ n) := by
      funext N; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      field_simp
    rw [e]; exact Tendsto.const_mul_atTop (by positivity) hdiv
  have he : Summable (fun n => ρ n / δ * ‖δ • (Z n - T (s n))‖) := by
    refine hZ.congr (fun n => ?_)
    rw [norm_smul, Real.norm_of_nonneg hδ0.le, ← mul_assoc, div_mul_cancel₀ _ hδne]
  have hstep : ∀ n, s (n + 1) =
      s n + (ρ n / δ) • (cfbR T δ (s n) + δ • (Z n - T (s n)) - s n) := by
    intro n
    have e1 : cfbR T δ (s n) + δ • (Z n - T (s n)) - s n = δ • (Z n - s n) := by
      unfold cfbR; module
    rw [e1, smul_smul, div_mul_cancel₀ _ hδne, hs n]; module
  obtain ⟨zs, hRz, hw, M, hM⟩ := cfb_KM (cfbR T δ) hRne hRfix (fun n => ρ n / δ)
    (fun n => δ • (Z n - T (s n))) s hlam hdiv' he hstep
  exact ⟨zs, (cfb_R_fix T hδne zs).1 hRz, cfb_transfer s M hM zs hw⟩

theorem cfb_err31 (p : CFBParams X Y) (F : X → ℝ) (G : X → EReal) (H : Y → EReal)
    (PG : X → X) (PH : Y → Y)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH)
    (x : X) (y : Y) (eF eG : X) (eH : Y) (xt : X) (yt : Y)
    (hxt : xt = PG (x - p.τ • (gradient F x + eF) - p.τ • ContinuousLinearMap.adjoint p.L y) + eG)
    (hyt : yt = PH (y + p.σ • p.L ((2 : ℝ) • xt - x)) + eH) :
    ‖mk p xt yt - cfbT1 p F PG PH (mk p x y)‖ ≤
      (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) *
        ((1 + 2 * p.σ * ‖p.L‖) * (p.τ * ‖eF‖ + ‖eG‖) + ‖eH‖) := by
  obtain ⟨hτ, hGb, hGf, hGc, hPG⟩ := hG
  obtain ⟨hσ, hHb, hHf, hHc, hPH⟩ := hH
  have htx : cfbTx p F PG (mk p x y) =
      PG (x - p.τ • gradient F x - p.τ • ContinuousLinearMap.adjoint p.L y) := rfl
  have hty : cfbTy p F PG PH (mk p x y) =
      PH (y + p.σ • p.L ((2 : ℝ) • cfbTx p F PG (mk p x y) - x)) := rfl
  set tx := cfbTx p F PG (mk p x y) with htxdef
  have hdx : ‖xt - tx‖ ≤ p.τ * ‖eF‖ + ‖eG‖ := by
    have e : xt - tx = (PG (x - p.τ • (gradient F x + eF) - p.τ • ContinuousLinearMap.adjoint p.L y)
        - PG (x - p.τ • gradient F x - p.τ • ContinuousLinearMap.adjoint p.L y)) + eG := by
      rw [hxt, htx]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h := cfb_prox_nonexp hτ hGb hGf hGc hPG
      (x - p.τ • (gradient F x + eF) - p.τ • ContinuousLinearMap.adjoint p.L y)
      (x - p.τ • gradient F x - p.τ • ContinuousLinearMap.adjoint p.L y)
    have e2 : (x - p.τ • (gradient F x + eF) - p.τ • ContinuousLinearMap.adjoint p.L y) -
        (x - p.τ • gradient F x - p.τ • ContinuousLinearMap.adjoint p.L y) = -(p.τ • eF) := by
      module
    rw [e2, norm_neg, norm_smul, Real.norm_of_nonneg hτ.le] at h
    linarith
  have hdy : ‖yt - cfbTy p F PG PH (mk p x y)‖ ≤ 2 * p.σ * ‖p.L‖ * ‖xt - tx‖ + ‖eH‖ := by
    rw [hty, hyt]
    have e : (PH (y + p.σ • p.L ((2 : ℝ) • xt - x)) + eH) - PH (y + p.σ • p.L ((2 : ℝ) • tx - x)) =
        (PH (y + p.σ • p.L ((2 : ℝ) • xt - x)) - PH (y + p.σ • p.L ((2 : ℝ) • tx - x))) + eH := by
      abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h := cfb_prox_nonexp hσ hHb hHf hHc hPH (y + p.σ • p.L ((2 : ℝ) • xt - x))
      (y + p.σ • p.L ((2 : ℝ) • tx - x))
    have e2 : (y + p.σ • p.L ((2 : ℝ) • xt - x)) - (y + p.σ • p.L ((2 : ℝ) • tx - x)) =
        p.σ • p.L ((2 : ℝ) • (xt - tx)) := by
      simp only [map_sub, map_smul, smul_sub]; abel
    rw [e2, norm_smul, Real.norm_of_nonneg hσ.le] at h
    have h3 : ‖p.L ((2 : ℝ) • (xt - tx))‖ ≤ ‖p.L‖ * (2 * ‖xt - tx‖) := by
      refine (p.L.le_opNorm _).trans ?_
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have h4 := mul_le_mul_of_nonneg_left h3 hσ.le
    nlinarith
  have hm : mk p xt yt - cfbT1 p F PG PH (mk p x y) =
      equiv p (xt - tx, yt - cfbTy p F PG PH (mk p x y)) := rfl
  rw [hm]
  refine (norm_equiv_le _).trans ?_
  have hnorm : ‖((xt - tx, yt - cfbTy p F PG PH (mk p x y)) : X × Y)‖ ≤
      ‖xt - tx‖ + ‖yt - cfbTy p F PG PH (mk p x y)‖ := by
    rw [Prod.norm_def]; exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : 0 ≤ (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) := by positivity
  apply mul_le_mul_of_nonneg_left _ hc
  have hl : 0 ≤ 2 * p.σ * ‖p.L‖ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hdx hl]

open CondatPD.FB in
theorem cfb_alg31 (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (β τ σ : ℝ) (PG : X → X) (PH : Y → Y)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ xh yh, IsPDSolution F G H L xh yh)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (hi : β / 2 ≤ 1 / τ - σ * ‖L‖ ^ 2)
    (hii : ∀ n, 0 < ρ n ∧ ρ n < pdDelta β τ σ L)
    (hiii : Tendsto (fun N => ∑ n ∈ Finset.range N,
      ρ n * (pdDelta β τ σ L - ρ n)) atTop atTop)
    (hivF : Summable (fun n => ρ n * ‖eF n‖))
    (hivG : Summable (fun n => ρ n * ‖eG n‖))
    (hivH : Summable (fun n => ρ n * ‖eH n‖))
    (x : ℕ → X) (y : ℕ → Y) (hrun : IsAlg31Run F L PG PH τ σ ρ eF eG eH x y) :
    ∃ xh yh, IsPDSolution F G H L xh yh ∧ WeakTendsto x xh ∧ WeakTendsto y yh := by
  have hθ : 0 < 1 / τ - σ * ‖L‖ ^ 2 := by linarith
  obtain ⟨p, rfl, rfl, rfl⟩ : ∃ p : CFBParams X Y, p.τ = τ ∧ p.σ = σ ∧ p.L = L :=
    ⟨⟨τ, σ, L, hτ, hσ, hθ⟩, rfl, rfl, rfl⟩
  have hGok : CfbProxOK p.τ G PG := ⟨hτ, hG.1, hG.2.1, cfb_segConvex_of_ppc hG, hPG⟩
  have hHfin : ∃ s, conj H s ≠ ⊤ := by
    obtain ⟨xh, yh, _, h2⟩ := hsol; exact ⟨yh, h2.1⟩
  have hHok : CfbProxOK p.σ (conj H) PH :=
    ⟨hσ, cfb_conj_ne_bot hH.1 hH.2.1, hHfin, cfb_conj_segConvex H, hPH⟩
  have hδ1 : 1 ≤ pdDelta β p.τ p.σ p.L := by
    unfold pdDelta
    have : β / 2 * (1 / p.τ - p.σ * ‖p.L‖ ^ 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hθ]; exact hi
    linarith
  have hδm : 1 - β / (2 * (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) = pdDelta β p.τ p.σ p.L - 1 := by
    unfold pdDelta; field_simp; ring
  have hT : ∀ z z', ‖cfbT1 p F PG PH z - cfbT1 p F PG PH z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 -
      (pdDelta β p.τ p.σ p.L - 1) *
        ‖(z - cfbT1 p F PG PH z) - (z' - cfbT1 p F PG PH z')‖ ^ 2 := by
    intro z z'
    have := cfb_T1_avg p F G H PG PH β hF hβ hGok hHok z z'
    rwa [hδm] at this
  have hfix : ∃ z, cfbT1 p F PG PH z = z := by
    obtain ⟨xh, yh, hs⟩ := hsol
    exact ⟨mk p xh yh, (cfb_T1_fix_iff p F G H PG PH hGok hHok (mk p xh yh)).2 hs⟩
  set xt : ℕ → X := fun n => PG (x n - p.τ • (gradient F (x n) + eF n) -
      p.τ • ContinuousLinearMap.adjoint p.L (y n)) + eG n with hxt
  set yt : ℕ → Y := fun n => PH (y n + p.σ • p.L ((2 : ℝ) • xt n - x n)) + eH n with hyt
  have hs : ∀ n, mk p (x (n + 1)) (y (n + 1)) =
      ρ n • mk p (xt n) (yt n) + (1 - ρ n) • mk p (x n) (y n) := by
    intro n
    obtain ⟨h1, h2⟩ := hrun n
    rw [h1, h2]; rfl
  have hc0 : 0 ≤ (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) := by positivity
  have hc1 : 0 ≤ 1 + 2 * p.σ * ‖p.L‖ := by positivity
  have hZ : Summable (fun n => ρ n *
      ‖mk p (xt n) (yt n) - cfbT1 p F PG PH (mk p (x n) (y n))‖) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hii n).1.le (norm_nonneg _))
      (fun n => (mul_le_mul_of_nonneg_left (cfb_err31 p F G H PG PH hGok hHok (x n) (y n)
        (eF n) (eG n) (eH n) (xt n) (yt n) rfl rfl) (hii n).1.le).trans_eq ?_)
      (((hivF.mul_left ((1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) * (1 + 2 * p.σ * ‖p.L‖) * p.τ)).add
        (hivG.mul_left ((1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) * (1 + 2 * p.σ * ‖p.L‖)))).add
        (hivH.mul_left (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1)))
    ring
  obtain ⟨zs, hTz, hx, hy⟩ := cfb_glue (cfbT1 p F PG PH) (pdDelta β p.τ p.σ p.L) hδ1 hT hfix ρ
    hii hiii (fun n => mk p (x n) (y n)) (fun n => mk p (xt n) (yt n)) hs hZ
  exact ⟨fst p zs, snd p zs, (cfb_T1_fix_iff p F G H PG PH hGok hHok zs).1 hTz, hx, hy⟩

end Glue2

/-! ## The Algorithm 3.2 half (P'-metric = P-metric for `-L`) -/

section Alg32

open InertialFB.IFB CFBProd

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

noncomputable def cfbSy (p : CFBParams X Y) (L : X →L[ℝ] Y) (PH : Y → Y) (z : CFBProd p) : Y :=
  PH (snd p z + p.σ • L (fst p z))

noncomputable def cfbSx (p : CFBParams X Y) (L : X →L[ℝ] Y) (F : X → ℝ) (PG : X → X)
    (PH : Y → Y) (z : CFBProd p) : X :=
  PG (fst p z - p.τ • gradient F (fst p z) -
    p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • cfbSy p L PH z - snd p z))

noncomputable def cfbT2 (p : CFBParams X Y) (L : X →L[ℝ] Y) (F : X → ℝ) (PG : X → X)
    (PH : Y → Y) (z : CFBProd p) : CFBProd p :=
  mk p (cfbSx p L F PG PH z) (cfbSy p L PH z)

@[simp] theorem cfb_fst_T2 (p : CFBParams X Y) (L : X →L[ℝ] Y) (F : X → ℝ) (PG : X → X)
    (PH : Y → Y) (z : CFBProd p) : fst p (cfbT2 p L F PG PH z) = cfbSx p L F PG PH z := rfl
@[simp] theorem cfb_snd_T2 (p : CFBParams X Y) (L : X →L[ℝ] Y) (F : X → ℝ) (PG : X → X)
    (PH : Y → Y) (z : CFBProd p) : snd p (cfbT2 p L F PG PH z) = cfbSy p L PH z := rfl

theorem cfb_T2_key (p : CFBParams X Y) (L : X →L[ℝ] Y) (hpL : p.L = -L) (F : X → ℝ)
    (G : X → EReal) (H : Y → EReal) (PG : X → X) (PH : Y → Y)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH) (z z' : CFBProd p) :
    inner ℝ (gradient F (fst p z) - gradient F (fst p z'))
        (fst p (cfbT2 p L F PG PH z) - fst p (cfbT2 p L F PG PH z')) ≤
      inner ℝ ((z - cfbT2 p L F PG PH z) - (z' - cfbT2 p L F PG PH z'))
        (cfbT2 p L F PG PH z - cfbT2 p L F PG PH z') := by
  obtain ⟨hτ, hGb, hGf, hGc, hPG⟩ := hG
  obtain ⟨hσ, hHb, hHf, hHc, hPH⟩ := hH
  rw [cfb_fst_T2, cfb_fst_T2]
  set τ := p.τ with hτdef
  set σ := p.σ with hσdef
  set x := fst p z with hx
  set y := snd p z with hy
  set x' := fst p z' with hx'
  set y' := snd p z' with hy'
  set ty := cfbSy p L PH z with hty
  set ty' := cfbSy p L PH z' with hty'
  set tx := cfbSx p L F PG PH z with htx
  set tx' := cfbSx p L F PG PH z' with htx'
  set gx := gradient F x with hgx
  set gx' := gradient F x' with hgx'
  have m2 : 0 ≤ inner ℝ ((1 / σ) • ((y + σ • L x) - ty) -
      (1 / σ) • ((y' + σ • L x') - ty')) (ty - ty') :=
    cfb_subgrad_mono hHb (cfb_prox_subgrad hσ hHb hHf hHc hPH _)
      (cfb_prox_subgrad hσ hHb hHf hHc hPH _)
  have m1 : 0 ≤ inner ℝ ((1 / τ) • ((x - τ • gx - τ • ContinuousLinearMap.adjoint L
      ((2 : ℝ) • ty - y)) - tx) - (1 / τ) • ((x' - τ • gx' - τ • ContinuousLinearMap.adjoint L
      ((2 : ℝ) • ty' - y')) - tx')) (tx - tx') :=
    cfb_subgrad_mono hGb (cfb_prox_subgrad hτ hGb hGf hGc hPG _)
      (cfb_prox_subgrad hτ hGb hGf hGc hPG _)
  have e1 : (1 / τ) • ((x - τ • gx - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • ty - y)) - tx) -
      (1 / τ) • ((x' - τ • gx' - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • ty' - y')) - tx') =
      (1 / τ) • ((x - x') - τ • (gx - gx') -
        τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • (ty - ty') - (y - y')) - (tx - tx')) := by
    rw [← smul_sub]; congr 1; simp only [map_sub, map_smul, smul_sub]; abel
  have e2 : (1 / σ) • ((y + σ • L x) - ty) - (1 / σ) • ((y' + σ • L x') - ty') =
      (1 / σ) • ((y - y') + σ • L (x - x') - (ty - ty')) := by
    rw [← smul_sub]; congr 1; simp only [map_sub, smul_sub]; abel
  rw [e1, real_inner_smul_left] at m1
  rw [e2, real_inner_smul_left] at m2
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hτi : 0 < 1 / τ := by positivity
  have hσi : 0 < 1 / σ := by positivity
  have m1' := (mul_nonneg_iff_of_pos_left hτi).1 m1
  have m2' := (mul_nonneg_iff_of_pos_left hσi).1 m2
  rw [inner_sub_left, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left,
    real_inner_comm (L (tx - tx')) ((2 : ℝ) • (ty - ty') - (y - y')),
    inner_sub_right (L (tx - tx')) ((2 : ℝ) • (ty - ty')) (y - y'), real_inner_smul_right] at m1'
  rw [inner_sub_left (y - y' + σ • L (x - x')) (ty - ty') (ty - ty'),
    inner_add_left (y - y') (σ • L (x - x')) (ty - ty'), real_inner_smul_left] at m2'
  have hp : inner ℝ ((z - cfbT2 p L F PG PH z) - (z' - cfbT2 p L F PG PH z'))
      (cfbT2 p L F PG PH z - cfbT2 p L F PG PH z') =
      (1 / τ) * (inner ℝ (x - x') (tx - tx') - inner ℝ (tx - tx') (tx - tx'))
      + (inner ℝ (L (x - x')) (ty - ty') - inner ℝ (L (tx - tx')) (ty - ty'))
      + (inner ℝ (L (tx - tx')) (y - y') - inner ℝ (L (tx - tx')) (ty - ty'))
      + (1 / σ) * (inner ℝ (y - y') (ty - ty') - inner ℝ (ty - ty') (ty - ty')) := by
    simp only [hx, hy, hx', hy', htx, htx', hty, hty', hτdef, hσdef]
    rw [inner_def]
    unfold pin
    rw [hpL]
    simp only [fst_sub, snd_sub, cfb_fst_T2, cfb_snd_T2, ContinuousLinearMap.neg_apply,
      inner_neg_left, map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hp]
  have k1 : (1 / τ) * (inner ℝ (x - x') (tx - tx') - inner ℝ (tx - tx') (tx - tx')) =
      (1 / τ) * (inner ℝ (x - x') (tx - tx') - τ * inner ℝ (gx - gx') (tx - tx') -
        τ * (2 * inner ℝ (L (tx - tx')) (ty - ty') - inner ℝ (L (tx - tx')) (y - y')) -
        inner ℝ (tx - tx') (tx - tx'))
      + inner ℝ (gx - gx') (tx - tx')
      + (2 * inner ℝ (L (tx - tx')) (ty - ty') - inner ℝ (L (tx - tx')) (y - y')) := by
    field_simp; ring
  have k2 : (1 / σ) * (inner ℝ (y - y') (ty - ty') - inner ℝ (ty - ty') (ty - ty')) =
      (1 / σ) * (inner ℝ (y - y') (ty - ty') + σ * inner ℝ (L (x - x')) (ty - ty') -
        inner ℝ (ty - ty') (ty - ty')) - inner ℝ (L (x - x')) (ty - ty') := by
    field_simp; ring
  rw [k1, k2]
  have := mul_nonneg hτi.le m1'
  have := mul_nonneg hσi.le m2'
  nlinarith

/-- Averagedness from the key inequality (generic in the map). -/
theorem cfb_avg_of_key (p : CFBParams X Y) (T : CFBProd p → CFBProd p) (F : X → ℝ) (β : ℝ)
    (hF : CondatPD.FB.IsSmoothTerm β F) (hβ : 0 < β)
    (hkey : ∀ z z', inner ℝ (gradient F (fst p z) - gradient F (fst p z'))
        (fst p (T z) - fst p (T z')) ≤ inner ℝ ((z - T z) - (z' - T z')) (T z - T z'))
    (z z' : CFBProd p) :
    ‖T z - T z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 -
      (1 - β / (2 * (1 / p.τ - p.σ * ‖p.L‖ ^ 2))) * ‖(z - T z) - (z' - T z')‖ ^ 2 := by
  set θ := 1 / p.τ - p.σ * ‖p.L‖ ^ 2 with hθ
  have hθ0 : 0 < θ := p.hθ
  set u := (z - T z) - (z' - T z') with hu
  have hkey' := hkey z z'
  rw [← hu] at hkey'
  set A := gradient F (fst p z) - gradient F (fst p z') with hA
  have hfu : fst p u = (fst p z - fst p z') - (fst p (T z) - fst p (T z')) := by
    rw [hu]; simp only [fst_sub]; abel
  have hdtx : fst p (T z) - fst p (T z') = (fst p z - fst p z') - fst p u := by
    rw [hfu]; abel
  rw [hdtx, inner_sub_right] at hkey'
  have hbh : (1 / β) * ‖A‖ ^ 2 ≤ inner ℝ A (fst p z - fst p z') := by
    have hlip : ∀ a b : X, ‖(1 / β) • gradient F a - (1 / β) • gradient F b‖ ≤ ‖a - b‖ := by
      intro a b
      rw [← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
      have := hF.2.2.2 a b
      rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hβ]
      linarith
    exact bh_main F (1 / β) hF.1 hF.2.1 (by positivity) hlip (fst p z) (fst p z')
  have hcs : inner ℝ A (fst p u) ≤ ‖A‖ * ‖fst p u‖ := real_inner_le_norm _ _
  have hfu2 : θ * ‖fst p u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [norm_sq]; exact (pin_bounds u).1
  have hsq : 0 ≤ (1 / β) * (‖A‖ - β / 2 * ‖fst p u‖) ^ 2 := by positivity
  have hsq' : (1 / β) * (‖A‖ - β / 2 * ‖fst p u‖) ^ 2 =
      (1 / β) * ‖A‖ ^ 2 - ‖A‖ * ‖fst p u‖ + β / 4 * ‖fst p u‖ ^ 2 := by
    field_simp; ring
  have hlow : -(β / (4 * θ)) * ‖u‖ ^ 2 ≤ inner ℝ u (T z - T z') := by
    have h1 : β / 4 * ‖fst p u‖ ^ 2 ≤ β / (4 * θ) * ‖u‖ ^ 2 := by
      have : β / (4 * θ) * ‖u‖ ^ 2 = β / 4 * (‖u‖ ^ 2 / θ) := by field_simp
      rw [this]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [le_div_iff₀ hθ0]; linarith
    linarith
  have hTd : T z - T z' = (z - z') - u := by rw [hu]; abel
  have hn : ‖T z - T z'‖ ^ 2 = ‖z - z'‖ ^ 2 - 2 * inner ℝ (z - z') u + ‖u‖ ^ 2 := by
    rw [hTd, norm_sub_sq_real]
  have hi : inner ℝ u (T z - T z') = inner ℝ (z - z') u - ‖u‖ ^ 2 := by
    rw [hTd, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm]
  have e3 : (1 - β / (2 * θ)) * ‖u‖ ^ 2 = ‖u‖ ^ 2 - 2 * (β / (4 * θ) * ‖u‖ ^ 2) := by
    field_simp; ring
  rw [hn, e3]
  nlinarith

theorem cfb_T2_fix_iff (p : CFBParams X Y) (L : X →L[ℝ] Y) (F : X → ℝ) (G : X → EReal)
    (H : Y → EReal) (PG : X → X) (PH : Y → Y)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH) (z : CFBProd p) :
    cfbT2 p L F PG PH z = z ↔ CondatPD.FB.IsPDSolution F G H L (fst p z) (snd p z) := by
  obtain ⟨hτ, hGb, hGf, hGc, hPG⟩ := hG
  obtain ⟨hσ, hHb, hHf, hHc, hPH⟩ := hH
  have e2 : (2 : ℝ) • snd p z - snd p z = snd p z := by module
  have eG : (1 / p.τ) • ((fst p z - p.τ • gradient F (fst p z) -
      p.τ • ContinuousLinearMap.adjoint L (snd p z)) - fst p z)
      = -(ContinuousLinearMap.adjoint L (snd p z)) - gradient F (fst p z) := by
    have : (fst p z - p.τ • gradient F (fst p z) - p.τ • ContinuousLinearMap.adjoint L (snd p z))
        - fst p z = p.τ • (-(ContinuousLinearMap.adjoint L (snd p z)) - gradient F (fst p z)) := by
      module
    rw [this, cfb_smul_cancel hτ.ne']
  have eH : (1 / p.σ) • ((snd p z + p.σ • L (fst p z)) - snd p z) = L (fst p z) := by
    rw [add_sub_cancel_left, cfb_smul_cancel hσ.ne']
  have hSy : cfbSy p L PH z = PH (snd p z + p.σ • L (fst p z)) := rfl
  have hSx : cfbSx p L F PG PH z = PG (fst p z - p.τ • gradient F (fst p z) -
      p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • cfbSy p L PH z - snd p z)) := rfl
  constructor
  · intro hT
    have hsx : cfbSx p L F PG PH z = fst p z := by rw [← cfb_fst_T2 p L F PG PH z, hT]
    have hsy : cfbSy p L PH z = snd p z := by rw [← cfb_snd_T2 p L F PG PH z, hT]
    refine ⟨?_, ?_⟩
    · have h := cfb_prox_subgrad hτ hGb hGf hGc hPG
        (fst p z - p.τ • gradient F (fst p z) - p.τ • ContinuousLinearMap.adjoint L (snd p z))
      have h' : PG (fst p z - p.τ • gradient F (fst p z) -
          p.τ • ContinuousLinearMap.adjoint L (snd p z)) = fst p z := by
        rw [hSx, hsy, e2] at hsx; exact hsx
      rw [h', eG] at h
      exact h
    · have h := cfb_prox_subgrad hσ hHb hHf hHc hPH (snd p z + p.σ • L (fst p z))
      rw [← hSy, hsy, eH] at h
      exact h
  · rintro ⟨h1, h2⟩
    have hsy : cfbSy p L PH z = snd p z := by
      rw [hSy]
      apply cfb_prox_eq_of_subgrad hσ hHb hHf hHc hPH
      rw [eH]; exact h2
    have hsx : cfbSx p L F PG PH z = fst p z := by
      rw [hSx, hsy, e2]
      apply cfb_prox_eq_of_subgrad hτ hGb hGf hGc hPG
      rw [eG]; exact h1
    exact ext' (by rw [cfb_fst_T2, hsx]) (by rw [cfb_snd_T2, hsy])

theorem cfb_err32 (p : CFBParams X Y) (L : X →L[ℝ] Y) (F : X → ℝ) (G : X → EReal)
    (H : Y → EReal) (PG : X → X) (PH : Y → Y)
    (hG : CfbProxOK p.τ G PG) (hH : CfbProxOK p.σ (CondatPD.FB.conj H) PH)
    (x : X) (y : Y) (eF eG : X) (eH : Y) (xt : X) (yt : Y)
    (hyt : yt = PH (y + p.σ • L x) + eH)
    (hxt : xt = PG (x - p.τ • (gradient F x + eF) -
      p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - y)) + eG) :
    ‖mk p xt yt - cfbT2 p L F PG PH (mk p x y)‖ ≤
      (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) *
        (p.τ * ‖eF‖ + ‖eG‖ + (2 * p.τ * ‖ContinuousLinearMap.adjoint L‖ + 1) * ‖eH‖) := by
  obtain ⟨hτ, hGb, hGf, hGc, hPG⟩ := hG
  obtain ⟨hσ, hHb, hHf, hHc, hPH⟩ := hH
  have hSy : cfbSy p L PH (mk p x y) = PH (y + p.σ • L x) := rfl
  have hSx : cfbSx p L F PG PH (mk p x y) = PG (x - p.τ • gradient F x -
      p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • cfbSy p L PH (mk p x y) - y)) := rfl
  set sy := cfbSy p L PH (mk p x y) with hsydef
  have hdy : yt - sy = eH := by rw [hyt, hSy]; abel
  have hdx : ‖xt - cfbSx p L F PG PH (mk p x y)‖ ≤
      p.τ * ‖eF‖ + ‖eG‖ + 2 * p.τ * ‖ContinuousLinearMap.adjoint L‖ * ‖eH‖ := by
    rw [hSx, hxt]
    set a := x - p.τ • (gradient F x + eF) - p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt - y)
    set b := x - p.τ • gradient F x - p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • sy - y)
    have e : PG a + eG - PG b = (PG a - PG b) + eG := by abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h := cfb_prox_nonexp hτ hGb hGf hGc hPG a b
    have e2 : a - b = -(p.τ • eF) - p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • (yt - sy)) := by
      simp only [a, b, map_sub, map_smul, smul_sub]; module
    rw [e2, hdy] at h
    have h3 : ‖-(p.τ • eF) - p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • eH)‖ ≤
        p.τ * ‖eF‖ + p.τ * (‖ContinuousLinearMap.adjoint L‖ * (2 * ‖eH‖)) := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg, norm_smul, norm_smul, Real.norm_of_nonneg hτ.le]
      have h4 : ‖ContinuousLinearMap.adjoint L ((2 : ℝ) • eH)‖ ≤
          ‖ContinuousLinearMap.adjoint L‖ * (2 * ‖eH‖) := by
        refine ((ContinuousLinearMap.adjoint L).le_opNorm _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have := mul_le_mul_of_nonneg_left h4 hτ.le
      linarith
    nlinarith
  have hm : mk p xt yt - cfbT2 p L F PG PH (mk p x y) =
      equiv p (xt - cfbSx p L F PG PH (mk p x y), yt - sy) := rfl
  rw [hm]
  refine (norm_equiv_le _).trans ?_
  have hnorm : ‖((xt - cfbSx p L F PG PH (mk p x y), yt - sy) : X × Y)‖ ≤
      ‖xt - cfbSx p L F PG PH (mk p x y)‖ + ‖yt - sy‖ := by
    rw [Prod.norm_def]; exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)
  have hc : 0 ≤ (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) := by positivity
  apply mul_le_mul_of_nonneg_left _ hc
  rw [hdy] at hnorm ⊢
  nlinarith

end Alg32

/-! ## The Algorithm 3.2 half and the theorem -/

section Final

open CFBProd ThreeOpSplitting.Convergence

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

open CondatPD.FB in
theorem cfb_alg32 (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (β τ σ : ℝ) (PG : X → X) (PH : Y → Y)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ xh yh, IsPDSolution F G H L xh yh)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (hi : β / 2 ≤ 1 / τ - σ * ‖L‖ ^ 2)
    (hii : ∀ n, 0 < ρ n ∧ ρ n < pdDelta β τ σ L)
    (hiii : Tendsto (fun N => ∑ n ∈ Finset.range N,
      ρ n * (pdDelta β τ σ L - ρ n)) atTop atTop)
    (hivF : Summable (fun n => ρ n * ‖eF n‖))
    (hivG : Summable (fun n => ρ n * ‖eG n‖))
    (hivH : Summable (fun n => ρ n * ‖eH n‖))
    (x : ℕ → X) (y : ℕ → Y) (hrun : IsAlg32Run F L PG PH τ σ ρ eF eG eH x y) :
    ∃ xh yh, IsPDSolution F G H L xh yh ∧ WeakTendsto x xh ∧ WeakTendsto y yh := by
  have hθ : 0 < 1 / τ - σ * ‖L‖ ^ 2 := by linarith
  have hθ' : 0 < 1 / τ - σ * ‖-L‖ ^ 2 := by rwa [norm_neg]
  obtain ⟨p, rfl, rfl, hpL⟩ : ∃ p : CFBParams X Y, p.τ = τ ∧ p.σ = σ ∧ p.L = -L :=
    ⟨⟨τ, σ, -L, hτ, hσ, hθ'⟩, rfl, rfl, rfl⟩
  have hnL : ‖p.L‖ = ‖L‖ := by rw [hpL, norm_neg]
  have hGok : CfbProxOK p.τ G PG := ⟨hτ, hG.1, hG.2.1, cfb_segConvex_of_ppc hG, hPG⟩
  have hHfin : ∃ s, conj H s ≠ ⊤ := by
    obtain ⟨xh, yh, _, h2⟩ := hsol; exact ⟨yh, h2.1⟩
  have hHok : CfbProxOK p.σ (conj H) PH :=
    ⟨hσ, cfb_conj_ne_bot hH.1 hH.2.1, hHfin, cfb_conj_segConvex H, hPH⟩
  have hδ1 : 1 ≤ pdDelta β p.τ p.σ L := by
    unfold pdDelta
    have : β / 2 * (1 / p.τ - p.σ * ‖L‖ ^ 2)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hθ]; exact hi
    linarith
  have hδm : 1 - β / (2 * (1 / p.τ - p.σ * ‖p.L‖ ^ 2)) = pdDelta β p.τ p.σ L - 1 := by
    rw [hnL]; unfold pdDelta; field_simp; ring
  have hT : ∀ z z', ‖cfbT2 p L F PG PH z - cfbT2 p L F PG PH z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 -
      (pdDelta β p.τ p.σ L - 1) *
        ‖(z - cfbT2 p L F PG PH z) - (z' - cfbT2 p L F PG PH z')‖ ^ 2 := by
    intro z z'
    have := cfb_avg_of_key p (cfbT2 p L F PG PH) F β hF hβ
      (cfb_T2_key p L hpL F G H PG PH hGok hHok) z z'
    rwa [hδm] at this
  have hfix : ∃ z, cfbT2 p L F PG PH z = z := by
    obtain ⟨xh, yh, hs⟩ := hsol
    exact ⟨mk p xh yh, (cfb_T2_fix_iff p L F G H PG PH hGok hHok (mk p xh yh)).2 hs⟩
  set yt : ℕ → Y := fun n => PH (y n + p.σ • L (x n)) + eH n with hyt
  set xt : ℕ → X := fun n => PG (x n - p.τ • (gradient F (x n) + eF n) -
      p.τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • yt n - y n)) + eG n with hxt
  have hs : ∀ n, mk p (x (n + 1)) (y (n + 1)) =
      ρ n • mk p (xt n) (yt n) + (1 - ρ n) • mk p (x n) (y n) := by
    intro n
    obtain ⟨h1, h2⟩ := hrun n
    rw [h1, h2]; rfl
  have hZ : Summable (fun n => ρ n *
      ‖mk p (xt n) (yt n) - cfbT2 p L F PG PH (mk p (x n) (y n))‖) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hii n).1.le (norm_nonneg _))
      (fun n => (mul_le_mul_of_nonneg_left (cfb_err32 p L F G H PG PH hGok hHok (x n) (y n)
        (eF n) (eG n) (eH n) (xt n) (yt n) rfl rfl) (hii n).1.le).trans_eq ?_)
      (((hivF.mul_left ((1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) * p.τ)).add
        (hivG.mul_left (1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1))).add
        (hivH.mul_left ((1 / p.τ + 1 / p.σ + 2 * ‖p.L‖ + 1) *
          (2 * p.τ * ‖ContinuousLinearMap.adjoint L‖ + 1))))
    ring
  obtain ⟨zs, hTz, hx, hy⟩ := cfb_glue (cfbT2 p L F PG PH) (pdDelta β p.τ p.σ L) hδ1 hT hfix ρ
    hii hiii (fun n => mk p (x n) (y n)) (fun n => mk p (xt n) (yt n)) hs hZ
  exact ⟨fst p zs, snd p zs, (cfb_T2_fix_iff p L F G H PG PH hGok hHok zs).1 hTz, hx, hy⟩

end Final

open Filter Topology InnerProductSpace CondatPD.FB in
theorem solution {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (β τ σ : ℝ) (PG : X → X) (PH : Y → Y)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ xh yh, IsPDSolution F G H L xh yh)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (hi : β / 2 ≤ 1 / τ - σ * ‖L‖ ^ 2)
    (hii : ∀ n, 0 < ρ n ∧ ρ n < pdDelta β τ σ L)
    (hiii : Tendsto (fun N => ∑ n ∈ Finset.range N,
      ρ n * (pdDelta β τ σ L - ρ n)) atTop atTop)
    (hivF : Summable (fun n => ρ n * ‖eF n‖))
    (hivG : Summable (fun n => ρ n * ‖eG n‖))
    (hivH : Summable (fun n => ρ n * ‖eH n‖)) :
    (∀ (x : ℕ → X) (y : ℕ → Y),
      IsAlg31Run F L PG PH τ σ ρ eF eG eH x y →
        ∃ xh yh, IsPDSolution F G H L xh yh ∧
          ThreeOpSplitting.Convergence.WeakTendsto x xh ∧
          ThreeOpSplitting.Convergence.WeakTendsto y yh) ∧
    (∀ (x : ℕ → X) (y : ℕ → Y),
      IsAlg32Run F L PG PH τ σ ρ eF eG eH x y →
        ∃ xh yh, IsPDSolution F G H L xh yh ∧
          ThreeOpSplitting.Convergence.WeakTendsto x xh ∧
          ThreeOpSplitting.Convergence.WeakTendsto y yh) := by
  exact ⟨fun x y h => cfb_alg31 F G H L β τ σ PG PH ρ eF eG eH hF hG hH hsol hβ hτ hσ hPG hPH hi
      hii hiii hivF hivG hivH x y h,
    fun x y h => cfb_alg32 F G H L β τ σ PG PH ρ eF eG eH hF hG hH hsol hβ hτ hσ hPG hPH hi
      hii hiii hivF hivG hivH x y h⟩
