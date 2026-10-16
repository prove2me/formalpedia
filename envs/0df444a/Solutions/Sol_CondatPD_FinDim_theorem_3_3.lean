-- Prove2me | solution 1 for CondatPD.FinDim.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-15T13:12:11.309405+00:00
-- url     : https://prove2.me/submissions/ad77c24d-8727-467b-bcfb-069d8aa14f0c

import Mathlib
import Definitions.Def_CondatPD_FinDim_Setting

set_option autoImplicit false

open Filter Topology

/-- Nonexpansive maps. -/
def CfbNonexp {H : Type*} [NormedAddCommGroup H] (R : H → H) : Prop :=
  ∀ x y : H, ‖R x - R y‖ ≤ ‖x - y‖

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

open InertialFB.IFB

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

theorem cfb_avg_id (a b : K) (t : ℝ) :
    ‖(1 - t) • a + t • b‖ ^ 2 = (1 - t) * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 - t * (1 - t) * ‖b - a‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    real_inner_smul_right, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_comm b a]
  ring

/-- C2: demiclosedness of `I - T` at a bounded weakly convergent sequence. -/
theorem cfb_demiclosed (T : K → K) (hT : CfbNonexp T)
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
theorem cfb_KM [CompleteSpace K] (R : K → K) (hR : CfbNonexp R)
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

section Glue

open InertialFB.IFB

theorem cfb_smul_cancel {E : Type*} [AddCommGroup E] [Module ℝ E] {c : ℝ} (hc : c ≠ 0) (a : E) :
    (1 / c) • (c • a) = a := by rw [smul_smul, one_div, inv_mul_cancel₀ hc, one_smul]

noncomputable def cfbR {K : Type*} [AddCommGroup K] [Module ℝ K] (T : K → K) (δ : ℝ) (z : K) : K :=
  δ • T z - (δ - 1) • z

theorem cfb_R_nonexp {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] (T : K → K)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hT : ∀ z z', ‖T z - T z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 - (δ - 1) * ‖(z - T z) - (z' - T z')‖ ^ 2) :
    CfbNonexp (cfbR T δ) := by
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

end Glue


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

theorem cfb_conj_segConvex (h : H → EReal) : CfbSegConvex (CondatPD.FinDim.conj h) := by
  intro a b ra rb ha hb t ht0 ht1
  unfold CondatPD.FinDim.conj at ha hb ⊢
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
    CondatPD.FinDim.conj h s ≠ ⊥ := by
  obtain ⟨x0, hx0⟩ := hfin
  have hle := le_iSup (fun s' => ((inner ℝ s s' : ℝ) : EReal) - h s') x0
  intro hbot
  unfold CondatPD.FinDim.conj at hbot
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

/-! ## Generic: weak ⇒ strong in finite dimension, relaxed inexact KM for firm maps -/

section KMfin

open InertialFB.IFB

theorem fd_weak_strong {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [FiniteDimensional ℝ K] (s : ℕ → K) (z : K) (h : WeakTendsto s z) :
    Tendsto s atTop (𝓝 z) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let b := stdOrthonormalBasis ℝ K
  have h2 : Tendsto (fun n => ‖s n - z‖ ^ 2) atTop (𝓝 0) := by
    have e : ∀ n, ‖s n - z‖ ^ 2 = ∑ i, (inner ℝ (s n) (b i) - inner ℝ z (b i)) ^ 2 := by
      intro n
      rw [← b.sum_sq_norm_inner_left (s n - z)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Real.norm_eq_abs, sq_abs, inner_sub_left]
    simp_rw [e]
    have : Tendsto (fun n => ∑ i, (inner ℝ (s n) (b i) - inner ℝ z (b i)) ^ 2) atTop
        (𝓝 (∑ _i : Fin (Module.finrank ℝ K), (0:ℝ))) := by
      refine tendsto_finset_sum _ (fun i _ => ?_)
      have := ((h (b i)).sub_const (inner ℝ z (b i))).pow 2
      simpa using this
    simpa using this
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  exact h3.congr (fun n => by simp [Real.sqrt_sq (norm_nonneg _)])

theorem fd_km {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (R : K → K) (hR : ∀ u v, ‖R u - R v‖ ^ 2 ≤ inner ℝ (R u - R v) (u - v))
    (hfix : ∃ z, R z = z) (ρ : ℕ → ℝ) (hρ : ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ ρ n ∧ ρ n ≤ 2 - ε)
    (s Z : ℕ → K) (hs : ∀ n, s (n + 1) = ρ n • Z n + (1 - ρ n) • s n)
    (hZ : Summable (fun n => ‖Z n - R (s n)‖)) :
    ∃ zs, R zs = zs ∧ WeakTendsto s zs := by
  obtain ⟨ε, hε, hρε⟩ := hρ
  have hT : ∀ z z', ‖R z - R z'‖ ^ 2 ≤ ‖z - z'‖ ^ 2 - ((2:ℝ) - 1) * ‖(z - R z) - (z' - R z')‖ ^ 2 := by
    intro z z'
    have h1 := hR z z'
    have hb : (z - R z) - (z' - R z') = (z - z') - (R z - R z') := by abel
    have hc := real_inner_comm (z - z') (R z - R z')
    rw [hb, norm_sub_sq_real (z - z') (R z - R z')]
    linarith
  have hρ0 : ∀ n, 0 < ρ n ∧ ρ n < 2 := fun n => ⟨by linarith [(hρε n).1], by linarith [(hρε n).2]⟩
  have hdiv : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n * (2 - ρ n)) atTop atTop := by
    have hge : ∀ n, ε * ε ≤ ρ n * (2 - ρ n) := by
      intro n
      have h1 := (hρε n).1
      have h2 := (hρε n).2
      nlinarith
    refine tendsto_atTop_mono (fun N => ?_)
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (by positivity : 0 < ε * ε))
    calc (N : ℝ) * (ε * ε) = ∑ _n ∈ Finset.range N, ε * ε := by simp
      _ ≤ _ := Finset.sum_le_sum (fun n _ => hge n)
  have hZ' : Summable (fun n => ρ n * ‖Z n - R (s n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hρ0 n).1.le (norm_nonneg _))
      (fun n => ?_) (hZ.mul_left 2)
    exact mul_le_mul_of_nonneg_right (hρ0 n).2.le (norm_nonneg _)
  have hδ0 : (0:ℝ) < 2 := by norm_num
  have hδne : (2:ℝ) ≠ 0 := by norm_num
  have hRne := cfb_R_nonexp R 2 hδ0.le hT
  have hRfix : ∃ z, cfbR R 2 z = z := by
    obtain ⟨z, hz⟩ := hfix; exact ⟨z, (cfb_R_fix R hδne z).2 hz⟩
  have hlam : ∀ n, 0 < ρ n / 2 ∧ ρ n / 2 < 1 := fun n =>
    ⟨div_pos (hρ0 n).1 hδ0, (div_lt_one hδ0).2 (hρ0 n).2⟩
  have hdiv' : Tendsto (fun N => ∑ n ∈ Finset.range N, ρ n / 2 * (1 - ρ n / 2)) atTop atTop := by
    have e : (fun N => ∑ n ∈ Finset.range N, ρ n / 2 * (1 - ρ n / 2)) =
        fun N => (1 / 2 ^ 2 : ℝ) * ∑ n ∈ Finset.range N, ρ n * (2 - ρ n) := by
      funext N; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      field_simp
    rw [e]; exact Tendsto.const_mul_atTop (by positivity) hdiv
  have he : Summable (fun n => ρ n / 2 * ‖(2:ℝ) • (Z n - R (s n))‖) := by
    refine hZ'.congr (fun n => ?_)
    rw [norm_smul, Real.norm_of_nonneg hδ0.le, ← mul_assoc, div_mul_cancel₀ _ hδne]
  have hstep : ∀ n, s (n + 1) =
      s n + (ρ n / 2) • (cfbR R 2 (s n) + (2:ℝ) • (Z n - R (s n)) - s n) := by
    intro n
    have e1 : cfbR R 2 (s n) + (2:ℝ) • (Z n - R (s n)) - s n = (2:ℝ) • (Z n - s n) := by
      unfold cfbR; module
    rw [e1, smul_smul, div_mul_cancel₀ _ hδne, hs n]; module
  obtain ⟨zs, hRz, hw, M, hM⟩ := cfb_KM (cfbR R 2) hRne hRfix (fun n => ρ n / 2)
    (fun n => (2:ℝ) • (Z n - R (s n))) s hlam hdiv' he hstep
  exact ⟨zs, (cfb_R_fix R hδne zs).1 hRz, hw⟩

end KMfin

/-! ## The `P`-metric space on a finite-dimensional `E` -/

section QSpace

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fd_psd_zero {P : E →L[ℝ] E} (hsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v))
    (hpos : ∀ u, 0 ≤ inner ℝ (P u) u) (v : E) (h : inner ℝ (P v) v = 0) : P v = 0 := by
  by_contra hne
  set a := ‖P v‖ ^ 2 with ha
  have ha0 : 0 < a := by
    have := norm_pos_iff.2 hne
    positivity
  set w := -(P v) with hw
  set c := inner ℝ (P w) w with hc
  have hc0 : 0 ≤ c := hpos w
  have key : ∀ t : ℝ, 0 < t → 2 * a ≤ t * c := by
    intro t ht
    have h1 := hpos (v + t • w)
    have e1 : inner ℝ (P (v + t • w)) (v + t • w) =
        inner ℝ (P v) v + t * inner ℝ (P v) w + t * inner ℝ (P w) v + t * t * c := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right]
      rw [hc]; ring
    have e2 : inner ℝ (P w) v = inner ℝ (P v) w := by
      rw [hsym w v, real_inner_comm]
    have e3 : inner ℝ (P v) w = -a := by
      rw [hw, inner_neg_right, real_inner_self_eq_norm_sq]
    rw [e1, e2, e3, h] at h1
    nlinarith
  have := key (a / (c + 1)) (by positivity)
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at this
  nlinarith

/-- Data of the `P`-metric: `P` symmetric positive semidefinite and `N` the projection onto `ker P`. -/
structure QData (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  P : E →L[ℝ] E
  N : E →L[ℝ] E
  hsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v)
  hpos : ∀ u, 0 ≤ inner ℝ (P u) u
  hPN : ∀ v, P (N v) = 0
  hN : ∀ u, P u = 0 → N u = u

/-- `E` carrying the inner product `⟪P u, v⟫ + ⟪N u, N v⟫`. -/
def QSp (_d : QData E) : Type _ := E

namespace QSp

variable (d : QData E)

instance : AddCommGroup (QSp d) := inferInstanceAs (AddCommGroup E)
instance : Module ℝ (QSp d) := inferInstanceAs (Module ℝ E)

def ofE : E ≃ₗ[ℝ] QSp d := LinearEquiv.refl ℝ E

variable {d}

noncomputable def pin (u v : E) : ℝ := inner ℝ (d.P u) v + inner ℝ (d.N u) (d.N v)

theorem pin_comm (u v : E) : pin (d := d) u v = pin (d := d) v u := by
  unfold pin
  rw [d.hsym u v, real_inner_comm (d.N u) (d.N v), real_inner_comm]

theorem pin_add_left (u u' v : E) : pin (d := d) (u + u') v = pin (d := d) u v + pin (d := d) u' v := by
  unfold pin
  simp only [map_add, inner_add_left]
  ring

theorem pin_smul_left (c : ℝ) (u v : E) : pin (d := d) (c • u) v = c * pin (d := d) u v := by
  unfold pin
  simp only [map_smul, real_inner_smul_left]
  ring

theorem pin_nonneg (u : E) : 0 ≤ pin (d := d) u u := by
  unfold pin
  have := d.hpos u
  have : 0 ≤ inner ℝ (d.N u) (d.N u) := real_inner_self_nonneg
  linarith

theorem pin_definite (u : E) (h : pin (d := d) u u = 0) : u = 0 := by
  unfold pin at h
  have h1 := d.hpos u
  have h2 : 0 ≤ inner ℝ (d.N u) (d.N u) := real_inner_self_nonneg
  have h3 : inner ℝ (d.P u) u = 0 := by linarith
  have h4 : inner ℝ (d.N u) (d.N u) = 0 := by linarith
  have h5 := fd_psd_zero d.hsym d.hpos u h3
  have h6 := d.hN u h5
  rw [real_inner_self_eq_norm_sq] at h4
  have : ‖d.N u‖ = 0 := by nlinarith [norm_nonneg (d.N u)]
  rw [norm_eq_zero] at this
  rw [← h6, this]

variable (d)

noncomputable instance : Inner ℝ (QSp d) := ⟨fun u v => pin (d := d) (ofE d |>.symm u) (ofE d |>.symm v)⟩

theorem inner_def (u v : E) : inner ℝ (ofE d u) (ofE d v) = pin (d := d) u v := rfl

noncomputable instance : NormedAddCommGroup (QSp d) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ (QSp d) _ _ _
    { toInner := inferInstance
      conj_inner_symm := fun u v => by
        simp only [conj_trivial]; exact pin_comm (d := d) v u
      re_inner_nonneg := fun u => by
        simp only [RCLike.re_to_real]; exact pin_nonneg (d := d) u
      definite := fun u hu => pin_definite (d := d) u hu
      add_left := fun u u' v => pin_add_left (d := d) u u' v
      smul_left := fun u v r => by
        simp only [conj_trivial]; exact pin_smul_left (d := d) r u v }

noncomputable instance : InnerProductSpace ℝ (QSp d) :=
  InnerProductSpace.ofCore _

theorem norm_sq (u : E) : ‖ofE d u‖ ^ 2 = pin (d := d) u u := by
  rw [← real_inner_self_eq_norm_sq]; rfl

instance [FiniteDimensional ℝ E] : FiniteDimensional ℝ (QSp d) :=
  inferInstanceAs (FiniteDimensional ℝ E)

instance [FiniteDimensional ℝ E] : CompleteSpace (QSp d) :=
  FiniteDimensional.complete ℝ (QSp d)

end QSp

end QSpace

/-! ## The relaxed inexact KM core for a `P`-firm map -/

section KMP

open scoped RealInnerProductSpace

theorem fd_lemma46 (a b c : ℕ → ℝ)
    (h1 : ∀ n, 0 ≤ a n ∧ 0 ≤ c n ∧ c n < 1 ∧ 0 ≤ b n)
    (h2 : ∀ n, a (n + 1) ≤ c n * a n + b n)
    (h3 : Tendsto (fun N => ∑ n ∈ Finset.range N, (1 - c n)) atTop atTop)
    (h4 : Tendsto (fun n => b n / (1 - c n)) atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  have hεpos : 0 < δ / 3 := by positivity
  set ε := δ / 3 with hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 h4) ε hεpos
  have hb : ∀ n ≥ N, b n ≤ ε * (1 - c n) := by
    intro n hn
    have h := hN n hn
    rw [Real.dist_eq, sub_zero] at h
    have hc : 0 < 1 - c n := by linarith [(h1 n).2.2.1]
    have h' := (abs_lt.1 h).2
    rw [div_lt_iff₀ hc] at h'
    linarith
  set S : ℕ → ℝ := fun M => ∑ n ∈ Finset.range M, (1 - c n) with hS
  have key : ∀ m, N ≤ m →
      max (a m - ε) 0 ≤ max (a N - ε) 0 * Real.exp (-(S m - S N)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      have hc0 := (h1 m).2.1
      have hstep : max (a (m+1) - ε) 0 ≤ c m * max (a m - ε) 0 := by
        apply max_le
        · have e1 := h2 m
          have e2 := hb m hm
          have e3 := mul_le_mul_of_nonneg_left (le_max_left (a m - ε) 0) hc0
          nlinarith
        · exact mul_nonneg hc0 (le_max_right _ _)
      have hcexp : c m ≤ Real.exp (c m - 1) := by
        have := Real.add_one_le_exp (c m - 1); linarith
      have hSs : S (m+1) = S m + (1 - c m) := by
        simp only [hS]; rw [Finset.sum_range_succ]
      calc max (a (m+1) - ε) 0 ≤ c m * max (a m - ε) 0 := hstep
        _ ≤ Real.exp (c m - 1) * (max (a N - ε) 0 * Real.exp (-(S m - S N))) :=
            mul_le_mul hcexp ih (le_max_right _ _) (Real.exp_pos _).le
        _ = max (a N - ε) 0 * Real.exp (-(S (m+1) - S N)) := by
            rw [hSs, mul_left_comm, ← Real.exp_add]
            congr 2
            ring
  have hT1 : Tendsto (fun m => S m - S N) atTop atTop :=
    tendsto_atTop_add_const_right _ _ h3
  have hT : Tendsto (fun m => max (a N - ε) 0 * Real.exp (-(S m - S N))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hT1).const_mul (max (a N - ε) 0)
    simpa using this
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds hεpos))
  refine ⟨max N M, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnM : M ≤ n := le_trans (le_max_right _ _) hn
  have k1 := key n hnN
  have k2 := hM n hnM
  have k3 := le_max_left (a n - ε) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (h1 n).1]
  linarith


theorem fd_km_P {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : E →L[ℝ] E) (hPsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v))
    (hPpos : ∀ u, 0 ≤ inner ℝ (P u) u)
    (T : E → E) (hTc : Continuous T) (hfac : ∀ z z', P z = P z' → T z = T z')
    (hfirm : ∀ z z', inner ℝ (P (T z - T z')) (T z - T z') ≤ inner ℝ (P (T z - T z')) (z - z'))
    (hfix : ∃ z0, T z0 = z0)
    (ρ : ℕ → ℝ) (hρ : ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ ρ n ∧ ρ n ≤ 2 - ε)
    (e : ℕ → E) (he : Summable (fun n => ‖e n‖)) (z : ℕ → E)
    (hz : ∀ n, z (n + 1) = ρ n • (T (z n) + e n) + (1 - ρ n) • z n) :
    ∃ w, T w = w ∧ Tendsto z atTop (𝓝 w) := by
  classical
  set N : E →L[ℝ] E := (LinearMap.ker (P : E →ₗ[ℝ] E)).starProjection with hNdef
  have hPN : ∀ v, P (N v) = 0 := fun v => by
    have := Submodule.starProjection_apply_mem (LinearMap.ker (P : E →ₗ[ℝ] E)) v
    exact LinearMap.mem_ker.1 this
  have hN : ∀ u, P u = 0 → N u = u := fun u hu =>
    Submodule.starProjection_eq_self_iff.2 (LinearMap.mem_ker.2 hu)
  let d : QData E := ⟨P, N, hPsym, hPpos, hPN, hN⟩
  set S : E →L[ℝ] E := ContinuousLinearMap.id ℝ E - N with hSdef
  have hSv : ∀ v, S v = v - N v := fun v => rfl
  have hPS : ∀ v, P (S v) = P v := fun v => by rw [hSv, map_sub, hPN, sub_zero]
  have hNS : ∀ v, N (S v) = 0 := fun v => by
    rw [hSv, map_sub, hN (N v) (hPN v), sub_self]
  have hTS : ∀ v, T (S v) = T v := fun v => hfac _ _ (hPS v)
  let R : QSp d → QSp d := fun u => QSp.ofE d (S (T ((QSp.ofE d).symm u)))
  have hRe : ∀ a : E, R (QSp.ofE d a) = QSp.ofE d (S (T a)) := fun a => by
    simp only [R, LinearEquiv.symm_apply_apply]
  have hRfirm : ∀ u u' : QSp d, ‖R u - R u'‖ ^ 2 ≤ inner ℝ (R u - R u') (u - u') := by
    intro u u'
    obtain ⟨a, rfl⟩ := (QSp.ofE d).surjective u
    obtain ⟨a', rfl⟩ := (QSp.ofE d).surjective u'
    have hsub : ∀ p q : E, QSp.ofE d p - QSp.ofE d q = QSp.ofE d (p - q) :=
      fun p q => (map_sub _ p q).symm
    rw [hRe, hRe, hsub, hsub, QSp.norm_sq, QSp.inner_def]
    set dd := T a - T a' with hdd
    have e1 : S (T a) - S (T a') = S dd := by rw [hdd, map_sub]
    rw [e1]
    unfold QSp.pin
    have h1 : d.P (S dd) = P dd := hPS dd
    have h2 : d.N (S dd) = 0 := hNS dd
    have h3 : inner ℝ (P dd) (S dd) = inner ℝ (P dd) dd := by
      rw [hSv, inner_sub_right, hPsym dd (N dd), hPN, inner_zero_right, sub_zero]
    show inner ℝ (P (S dd)) (S dd) + inner ℝ (N (S dd)) (N (S dd)) ≤
      inner ℝ (P (S dd)) (a - a') + inner ℝ (N (S dd)) (N (a - a'))
    rw [hPS, hNS, h3]
    simp only [inner_zero_left, add_zero]
    exact hfirm a a'
  have hfixR : ∃ u, R u = u := by
    obtain ⟨z0, hz0⟩ := hfix
    refine ⟨QSp.ofE d (S z0), ?_⟩
    rw [hRe, hTS, hz0]
  let ofEL : E →L[ℝ] QSp d := LinearMap.toContinuousLinearMap (QSp.ofE d).toLinearMap
  let toEL : QSp d →L[ℝ] E := LinearMap.toContinuousLinearMap (QSp.ofE d).symm.toLinearMap
  let Mq : E →L[ℝ] QSp d := ofEL.comp S
  have hMq : ∀ v, Mq v = QSp.ofE d (S v) := fun v => rfl
  obtain ⟨ε, hε, hρε⟩ := hρ
  let s : ℕ → QSp d := fun n => QSp.ofE d (S (z n))
  let Z : ℕ → QSp d := fun n => QSp.ofE d (S (T (z n) + e n))
  have hs : ∀ n, s (n + 1) = ρ n • Z n + (1 - ρ n) • s n := by
    intro n
    simp only [s, Z, hz, map_add, map_smul]
  have hZdiff : ∀ n, Z n - R (s n) = Mq (e n) := by
    intro n
    simp only [s, Z]
    rw [hRe, hTS, hMq, ← map_sub, map_add]
    congr 1
    abel
  have hZsum : Summable (fun n => ‖Z n - R (s n)‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (he.mul_left ‖Mq‖)
    rw [hZdiff]
    exact Mq.le_opNorm (e n)
  obtain ⟨zs, hRz, hweak⟩ := fd_km R hRfirm hfixR ρ ⟨ε, hε, hρε⟩ s Z hs hZsum
  have hstrong : Tendsto s atTop (𝓝 zs) := fd_weak_strong s zs hweak
  set us : E := (QSp.ofE d).symm zs with hus
  have hsE : Tendsto (fun n => S (z n)) atTop (𝓝 us) := by
    have := (toEL.continuous.tendsto zs).comp hstrong
    refine this.congr (fun n => ?_)
    rfl
  have hfixE : S (T us) = us := by
    have := congrArg (QSp.ofE d).symm hRz
    simpa [R, hus] using this
  set w := T us with hw
  have hTc' : Tendsto (fun n => T (z n)) atTop (𝓝 w) := by
    have := (hTc.tendsto us).comp hsE
    refine this.congr (fun n => ?_)
    simp only [Function.comp, hTS]
  have hPw : P w = P us := by
    rw [← hPS w, hw, hfixE]
  refine ⟨w, ?_, ?_⟩
  · rw [hfac w us hPw]
  · -- convergence of z via lemma 4.6
    have he0 : Tendsto (fun n => ‖e n‖) atTop (𝓝 0) := he.tendsto_atTop_zero
    have hc1 : ∀ n, |1 - ρ n| ≤ 1 - ε := fun n => by
      rw [abs_le]; constructor <;> linarith [(hρε n).1, (hρε n).2]
    have hlem := fd_lemma46 (fun n => ‖z n - w‖) (fun n => ρ n * (‖T (z n) - w‖ + ‖e n‖))
      (fun n => |1 - ρ n|)
      (fun n => ⟨norm_nonneg _, abs_nonneg _, by linarith [hc1 n], by
        exact mul_nonneg (by linarith [(hρε n).1]) (by positivity)⟩) ?_ ?_ ?_
    · rw [tendsto_iff_norm_sub_tendsto_zero]; exact hlem
    · intro n
      have h1 : z (n + 1) - w = (1 - ρ n) • (z n - w) + ρ n • ((T (z n) - w) + e n) := by
        rw [hz n]; module
      show ‖z (n + 1) - w‖ ≤ |1 - ρ n| * ‖z n - w‖ + ρ n * (‖T (z n) - w‖ + ‖e n‖)
      rw [h1]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by linarith [(hρε n).1] : 0 < ρ n)]
      have := norm_add_le (T (z n) - w) (e n)
      have h2 := mul_le_mul_of_nonneg_left this (by linarith [(hρε n).1] : 0 ≤ ρ n)
      linarith
    · refine tendsto_atTop_mono (fun N => ?_)
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const hε)
      calc (N : ℝ) * ε = ∑ _n ∈ Finset.range N, ε := by simp
        _ ≤ _ := Finset.sum_le_sum (fun n _ => by linarith [hc1 n])
    · have hup : Tendsto (fun n => (2 / ε) * (‖T (z n) - w‖ + ‖e n‖)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n => ‖T (z n) - w‖) atTop (𝓝 0) := by
          rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hTc'
        simpa using (h1.add he0).const_mul (2 / ε)
      refine squeeze_zero (fun n => ?_) (fun n => ?_) hup
      · have hpos : 0 < 1 - |1 - ρ n| := by linarith [hc1 n]
        exact div_nonneg (mul_nonneg (by linarith [(hρε n).1]) (by positivity)) hpos.le
      · have hpos : 0 < 1 - |1 - ρ n| := by linarith [hc1 n]
        rw [div_le_iff₀ hpos]
        have hr := (hρε n).2
        have hsum : 0 ≤ ‖T (z n) - w‖ + ‖e n‖ := by positivity
        have h1 : ε ≤ 1 - |1 - ρ n| := by linarith [hc1 n]
        have h2 : ρ n * (‖T (z n) - w‖ + ‖e n‖) ≤ 2 * (‖T (z n) - w‖ + ‖e n‖) :=
          mul_le_mul_of_nonneg_right (by linarith) hsum
        calc ρ n * (‖T (z n) - w‖ + ‖e n‖) ≤ 2 * (‖T (z n) - w‖ + ‖e n‖) := h2
          _ = (2 / ε * (‖T (z n) - w‖ + ‖e n‖)) * ε := by field_simp
          _ ≤ (2 / ε * (‖T (z n) - w‖ + ‖e n‖)) * (1 - |1 - ρ n|) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)

end KMP

/-! ## Condat–Vũ step -/

section Condat

open InnerProductSpace
open CondatPD.FinDim


lemma fd_key (u v l τ σ c : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hl : 0 ≤ l)
    (hτ : 0 < τ) (hσ : 0 < σ) (hi : σ * τ * l ^ 2 ≤ 1) (hc : |c| ≤ l * u * v) :
    0 ≤ τ⁻¹ * u ^ 2 - 2 * c + σ⁻¹ * v ^ 2 ∧ 0 ≤ τ⁻¹ * u ^ 2 + 2 * c + σ⁻¹ * v ^ 2 := by
  have hst : 0 < σ * τ := mul_pos hσ hτ
  have key : 2 * (σ * τ) * (l * u * v) ≤ σ * u ^ 2 + τ * v ^ 2 := by
    have h1 : 0 ≤ (σ * u - σ * τ * l * v) ^ 2 := sq_nonneg _
    have h2 : 0 ≤ σ * τ * v ^ 2 * (1 - σ * τ * l ^ 2) :=
      mul_nonneg (by positivity) (by linarith)
    have : σ * (σ * u ^ 2 + τ * v ^ 2 - 2 * (σ * τ) * (l * u * v))
        = (σ * u - σ * τ * l * v) ^ 2 + σ * τ * v ^ 2 * (1 - σ * τ * l ^ 2) := by ring
    have h3 : 0 ≤ σ * (σ * u ^ 2 + τ * v ^ 2 - 2 * (σ * τ) * (l * u * v)) := by
      rw [this]; linarith
    have := nonneg_of_mul_nonneg_right (by linarith [h3] : 0 ≤ σ * (σ * u ^ 2 + τ * v ^ 2 - 2 * (σ * τ) * (l * u * v))) hσ
    linarith
  have e : τ⁻¹ * u ^ 2 + σ⁻¹ * v ^ 2 = (σ * u ^ 2 + τ * v ^ 2) / (σ * τ) := by
    field_simp
  have hb : 2 * (l * u * v) ≤ τ⁻¹ * u ^ 2 + σ⁻¹ * v ^ 2 := by
    rw [e, le_div_iff₀ hst]; linarith
  have := abs_le.mp hc
  constructor <;> linarith [this.1, this.2]


open CondatPD.FinDim in
theorem fd_P_positive {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (hi : σ * τ * ‖L‖ ^ 2 ≤ 1) :
    ∀ (x : X) (y : Y), 0 ≤ qP τ σ L x y ∧ 0 ≤ qP' τ σ L x y := by
  intro x y
  have hc : |⟪L x, y⟫_ℝ| ≤ ‖L‖ * ‖x‖ * ‖y‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (L.le_opNorm x) (norm_nonneg _))
  have hk := fd_key ‖x‖ ‖y‖ ‖L‖ τ σ ⟪L x, y⟫_ℝ (norm_nonneg _) (norm_nonneg _)
    (norm_nonneg _) hτ hσ hi hc
  have hadj : ⟪x, ContinuousLinearMap.adjoint L y⟫_ℝ = ⟪L x, y⟫_ℝ := by
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hsym : ⟪y, L x⟫_ℝ = ⟪L x, y⟫_ℝ := real_inner_comm _ _
  have hxx : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  have hyy : ⟪y, y⟫_ℝ = ‖y‖ ^ 2 := real_inner_self_eq_norm_sq y
  unfold qP qP'
  simp only [inner_sub_right, inner_add_right, inner_neg_right, real_inner_smul_right]
  rw [hadj, hsym, hxx, hyy]
  constructor <;> linarith [hk.1, hk.2]


open CondatPD.FinDim in
theorem fd_stepT_fac {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (PG : X → X) (PH : Y → Y) (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) :
    ∀ z z' : X × Y, opP τ σ L z = opP τ σ L z' →
      stepT PG PH τ σ L z = stepT PG PH τ σ L z' := by
  intro z z' h
  have h1 : τ⁻¹ • z.1 - ContinuousLinearMap.adjoint L z.2
      = τ⁻¹ • z'.1 - ContinuousLinearMap.adjoint L z'.2 := congrArg Prod.fst h
  have h2 : -(L z.1) + σ⁻¹ • z.2 = -(L z'.1) + σ⁻¹ • z'.2 := congrArg Prod.snd h
  have key1 : ∀ w : X × Y, w.1 - τ • ContinuousLinearMap.adjoint L w.2
      = τ • (τ⁻¹ • w.1 - ContinuousLinearMap.adjoint L w.2) := by
    intro w
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  have key2 : ∀ (w : X × Y) (a : X), w.2 + σ • L ((2 : ℝ) • a - w.1)
      = σ • (-(L w.1) + σ⁻¹ • w.2) + σ • L ((2 : ℝ) • a) := by
    intro w a
    rw [map_sub, smul_add, smul_sub, smul_neg, smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]
    abel
  have hx : PG (z.1 - τ • ContinuousLinearMap.adjoint L z.2)
      = PG (z'.1 - τ • ContinuousLinearMap.adjoint L z'.2) := by
    rw [key1 z, key1 z', h1]
  simp only [stepT]
  rw [key2 z, key2 z', h2, hx]


section
variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem fd_opP_add (τ σ : ℝ) (L : X →L[ℝ] Y) (a b : X × Y) :
    opP τ σ L (a + b) = opP τ σ L a + opP τ σ L b := by
  refine Prod.ext ?_ ?_
  · simp only [opP, Prod.fst_add, Prod.snd_add, map_add, smul_add]; abel
  · simp only [opP, Prod.fst_add, Prod.snd_add, map_add, smul_add]; abel

theorem fd_opP_smul (τ σ : ℝ) (L : X →L[ℝ] Y) (c : ℝ) (a : X × Y) :
    opP τ σ L (c • a) = c • opP τ σ L a := by
  refine Prod.ext ?_ ?_
  · simp only [opP, Prod.smul_fst, Prod.smul_snd, map_smul]; module
  · simp only [opP, Prod.smul_fst, Prod.smul_snd, map_smul]; module

theorem fd_opP_sub (τ σ : ℝ) (L : X →L[ℝ] Y) (a b : X × Y) :
    opP τ σ L (a - b) = opP τ σ L a - opP τ σ L b := by
  have := fd_opP_add τ σ L (a - b) b
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem fd_cont_of_firm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : H → H)
    (hP : ∀ a b, ‖P a - P b‖ ^ 2 ≤ inner ℝ (P a - P b) (a - b)) :
    (∀ a b, ‖P a - P b‖ ≤ ‖a - b‖) ∧ Continuous P := by
  have h1 : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖ := by
    intro a b
    have h := hP a b
    have h2 := real_inner_le_norm (P a - P b) (a - b)
    nlinarith [norm_nonneg (P a - P b), norm_nonneg (a - b)]
  refine ⟨h1, ?_⟩
  have : LipschitzWith 1 P := LipschitzWith.of_dist_le_mul (fun a b => by
    rw [dist_eq_norm, dist_eq_norm]; simpa using h1 a b)
  exact this.continuous

theorem fd_stepT_cont (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (L : X →L[ℝ] Y)
    (hPG : Continuous PG) (hPH : Continuous PH) : Continuous (stepT PG PH τ σ L) := by
  unfold stepT
  simp only []
  have h1 : Continuous fun z : X × Y => PG (z.1 - τ • ContinuousLinearMap.adjoint L z.2) := by
    fun_prop
  refine h1.prodMk ?_
  refine hPH.comp ?_
  fun_prop

theorem fd_firm_algebra (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (L : X →L[ℝ] Y)
    (d1 Δ1 : X) (d2 Δ2 : Y)
    (F1 : ‖d1‖ ^ 2 ≤ inner ℝ d1 (Δ1 - τ • ContinuousLinearMap.adjoint L Δ2))
    (F2 : ‖d2‖ ^ 2 ≤ inner ℝ d2 (Δ2 + σ • L ((2 : ℝ) • d1 - Δ1))) :
    inner ℝ (τ⁻¹ • d1 - ContinuousLinearMap.adjoint L d2) d1 +
        inner ℝ (-(L d1) + σ⁻¹ • d2) d2 ≤
      inner ℝ (τ⁻¹ • d1 - ContinuousLinearMap.adjoint L d2) Δ1 +
        inner ℝ (-(L d1) + σ⁻¹ • d2) Δ2 := by
  rw [inner_sub_right, real_inner_smul_right, ContinuousLinearMap.adjoint_inner_right] at F1
  rw [inner_add_right, real_inner_smul_right, map_sub, map_smul, inner_sub_right,
    real_inner_smul_right] at F2
  have c1 : inner ℝ d2 (L d1) = inner ℝ (L d1) d2 := real_inner_comm _ _
  have c2 : inner ℝ d2 (L Δ1) = inner ℝ (L Δ1) d2 := real_inner_comm _ _
  rw [c1, c2] at F2
  have G1 := mul_le_mul_of_nonneg_left F1 (inv_nonneg.2 hτ.le)
  have G2 := mul_le_mul_of_nonneg_left F2 (inv_nonneg.2 hσ.le)
  have i1 : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
  have i2 : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ.ne'
  have n1 : inner ℝ d1 d1 = ‖d1‖ ^ 2 := real_inner_self_eq_norm_sq d1
  have n2 : inner ℝ d2 d2 = ‖d2‖ ^ 2 := real_inner_self_eq_norm_sq d2
  simp only [inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left,
    ContinuousLinearMap.adjoint_inner_left, n1, n2]
  have c3 : inner ℝ d2 (L d1) = inner ℝ (L d1) d2 := real_inner_comm _ _
  have c4 : inner ℝ d2 (L Δ1) = inner ℝ (L Δ1) d2 := real_inner_comm _ _
  rw [c3, c4]
  rw [mul_sub, ← mul_assoc, i1, one_mul] at G1
  rw [mul_add, ← mul_assoc, i2, one_mul] at G2
  linarith

theorem fd_stepT_firm (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (L : X →L[ℝ] Y)
    (hPG : ∀ a b, ‖PG a - PG b‖ ^ 2 ≤ inner ℝ (PG a - PG b) (a - b))
    (hPH : ∀ a b, ‖PH a - PH b‖ ^ 2 ≤ inner ℝ (PH a - PH b) (a - b)) (z z' : X × Y) :
    inner ℝ (opP τ σ L (stepT PG PH τ σ L z - stepT PG PH τ σ L z')).1
        (stepT PG PH τ σ L z - stepT PG PH τ σ L z').1 +
      inner ℝ (opP τ σ L (stepT PG PH τ σ L z - stepT PG PH τ σ L z')).2
        (stepT PG PH τ σ L z - stepT PG PH τ σ L z').2 ≤
    inner ℝ (opP τ σ L (stepT PG PH τ σ L z - stepT PG PH τ σ L z')).1 (z - z').1 +
      inner ℝ (opP τ σ L (stepT PG PH τ σ L z - stepT PG PH τ σ L z')).2 (z - z').2 := by
  obtain ⟨x, y⟩ := z
  obtain ⟨x', y'⟩ := z'
  have F1 := hPG (x - τ • ContinuousLinearMap.adjoint L y) (x' - τ • ContinuousLinearMap.adjoint L y')
  set a := PG (x - τ • ContinuousLinearMap.adjoint L y) with ha
  set a' := PG (x' - τ • ContinuousLinearMap.adjoint L y') with ha'
  have F2 := hPH (y + σ • L ((2 : ℝ) • a - x)) (y' + σ • L ((2 : ℝ) • a' - x'))
  set b := PH (y + σ • L ((2 : ℝ) • a - x)) with hb
  set b' := PH (y' + σ • L ((2 : ℝ) • a' - x')) with hb'
  have hD : stepT PG PH τ σ L (x, y) - stepT PG PH τ σ L (x', y') = (a - a', b - b') := rfl
  have e1 : (x - τ • ContinuousLinearMap.adjoint L y) - (x' - τ • ContinuousLinearMap.adjoint L y')
      = (x - x') - τ • ContinuousLinearMap.adjoint L (y - y') := by
    simp only [map_sub]; module
  have e2 : (y + σ • L ((2 : ℝ) • a - x)) - (y' + σ • L ((2 : ℝ) • a' - x'))
      = (y - y') + σ • L ((2 : ℝ) • (a - a') - (x - x')) := by
    simp only [map_sub, map_smul]; module
  rw [e1] at F1
  rw [e2] at F2
  have key := fd_firm_algebra τ σ hτ hσ L (a - a') (x - x') (b - b') (y - y') F1 F2
  rw [hD]
  simpa only [opP, Prod.fst_sub, Prod.snd_sub] using key

end

end Condat

/-! ## Assembly -/

section Assembly

open InnerProductSpace
open CondatPD.FinDim
open InertialFB.IFB

variable {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem fd_pair_conv [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
    (PG : X → X) (PH : Y → Y) (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ) (L : X →L[ℝ] Y)
    (hi : σ * τ * ‖L‖ ^ 2 ≤ 1)
    (hPG : ∀ a b, ‖PG a - PG b‖ ^ 2 ≤ inner ℝ (PG a - PG b) (a - b))
    (hPH : ∀ a b, ‖PH a - PH b‖ ^ 2 ≤ inner ℝ (PH a - PH b) (a - b))
    (hfix : ∃ w : X × Y, stepT PG PH τ σ L w = w)
    (ρ : ℕ → ℝ) (hρ : ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ ρ n ∧ ρ n ≤ 2 - ε)
    (ex : ℕ → X) (ey : ℕ → Y) (hex : Summable fun n => ‖ex n‖) (hey : Summable fun n => ‖ey n‖)
    (x : ℕ → X) (y : ℕ → Y)
    (hrun : ∀ n, x (n + 1) = ρ n • ((stepT PG PH τ σ L (x n, y n)).1 + ex n) + (1 - ρ n) • x n ∧
        y (n + 1) = ρ n • ((stepT PG PH τ σ L (x n, y n)).2 + ey n) + (1 - ρ n) • y n) :
    ∃ w : X × Y, stepT PG PH τ σ L w = w ∧ Tendsto x atTop (𝓝 w.1) ∧ Tendsto y atTop (𝓝 w.2) := by
  classical
  let Pl : WithLp 2 (X × Y) →ₗ[ℝ] WithLp 2 (X × Y) :=
    { toFun := fun z => WithLp.toLp 2 (opP τ σ L (WithLp.ofLp z))
      map_add' := fun a b => by
        simp only [WithLp.ofLp_add]
        rw [fd_opP_add]; rfl
      map_smul' := fun c a => by
        simp only [WithLp.ofLp_smul, RingHom.id_apply]
        rw [fd_opP_smul]; rfl }
  let P : WithLp 2 (X × Y) →L[ℝ] WithLp 2 (X × Y) := LinearMap.toContinuousLinearMap Pl
  have hP : ∀ z, P z = WithLp.toLp 2 (opP τ σ L (WithLp.ofLp z)) := fun z => rfl
  let T : WithLp 2 (X × Y) → WithLp 2 (X × Y) :=
    fun z => WithLp.toLp 2 (stepT PG PH τ σ L (WithLp.ofLp z))
  have hPsym : ∀ u v, inner ℝ (P u) v = inner ℝ u (P v) := by
    intro u v
    simp only [hP, WithLp.prod_inner_apply, WithLp.ofLp_toLp, opP, inner_sub_left, inner_sub_right,
      inner_add_left, inner_add_right, inner_neg_left, inner_neg_right, real_inner_smul_left,
      real_inner_smul_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  have hPpos : ∀ u, 0 ≤ inner ℝ (P u) u := by
    intro u
    have h := (fd_P_positive L τ σ hτ hσ hi (WithLp.ofLp u).1 (WithLp.ofLp u).2).1
    unfold qP at h
    simp only [hP, WithLp.prod_inner_apply, WithLp.ofLp_toLp, opP]
    rw [real_inner_comm (WithLp.ofLp u).1, real_inner_comm (WithLp.ofLp u).2]
    exact h
  have hPGn := (fd_cont_of_firm PG hPG)
  have hPHn := (fd_cont_of_firm PH hPH)
  have hTc : Continuous T :=
    (WithLp.prod_continuous_toLp 2 X Y).comp
      ((fd_stepT_cont PG PH τ σ L hPGn.2 hPHn.2).comp (WithLp.prod_continuous_ofLp 2 X Y))
  have hfac : ∀ z z', P z = P z' → T z = T z' := by
    intro z z' h
    have h' : opP τ σ L (WithLp.ofLp z) = opP τ σ L (WithLp.ofLp z') := by
      have := congrArg WithLp.ofLp h
      simpa [hP] using this
    show WithLp.toLp 2 _ = WithLp.toLp 2 _
    rw [fd_stepT_fac PG PH L τ σ hτ hσ _ _ h']
  have hfirm : ∀ z z', inner ℝ (P (T z - T z')) (T z - T z') ≤ inner ℝ (P (T z - T z')) (z - z') := by
    intro z z'
    have h := fd_stepT_firm PG PH τ σ hτ hσ L hPG hPH (WithLp.ofLp z) (WithLp.ofLp z')
    simp only [hP, WithLp.prod_inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_sub, T]
    exact h
  have hfix' : ∃ z0, T z0 = z0 := by
    obtain ⟨w, hw⟩ := hfix
    exact ⟨WithLp.toLp 2 w, by simp only [T, WithLp.ofLp_toLp, hw]⟩
  let z : ℕ → WithLp 2 (X × Y) := fun n => WithLp.toLp 2 (x n, y n)
  let e : ℕ → WithLp 2 (X × Y) := fun n => WithLp.toLp 2 (ex n, ey n)
  have he : Summable (fun n => ‖e n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hex.add hey)
    have h : ‖e n‖ ^ 2 = ‖ex n‖ ^ 2 + ‖ey n‖ ^ 2 := WithLp.prod_norm_sq_eq_of_L2 (e n)
    by_contra hcon
    rw [not_le] at hcon
    have h1 := norm_nonneg (ex n)
    have h2 := norm_nonneg (ey n)
    have h3 : 0 ≤ ‖ex n‖ + ‖ey n‖ := add_nonneg h1 h2
    nlinarith [mul_pos (sub_pos.2 hcon) (add_pos_of_pos_of_nonneg (lt_of_le_of_lt h3 hcon) h3),
      mul_nonneg h1 h2]
  have hz : ∀ n, z (n + 1) = ρ n • (T (z n) + e n) + (1 - ρ n) • z n := by
    intro n
    obtain ⟨h1, h2⟩ := hrun n
    refine WithLp.ofLp_injective 2 ?_
    refine Prod.ext ?_ ?_
    · simp only [z, T, e, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.fst_add,
        Prod.smul_fst]
      exact h1
    · simp only [z, T, e, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_toLp, Prod.snd_add,
        Prod.smul_snd]
      exact h2
  obtain ⟨w, hw, hzw⟩ := fd_km_P P hPsym hPpos T hTc hfac hfirm hfix' ρ hρ e he z hz
  refine ⟨WithLp.ofLp w, ?_, ?_, ?_⟩
  · have := congrArg WithLp.ofLp hw
    simpa [T] using this
  · have h1 := ((continuous_fst.comp (WithLp.prod_continuous_ofLp 2 X Y)).tendsto w).comp hzw
    exact h1
  · have h1 := ((continuous_snd.comp (WithLp.prod_continuous_ofLp 2 X Y)).tendsto w).comp hzw
    exact h1

theorem fd_fix_iff (G : X → EReal) (Hs : Y → EReal) (L : X →L[ℝ] Y) (τ σ : ℝ) (hτ : 0 < τ)
    (hσ : 0 < σ) (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ Hs PH)
    (hGb : ∀ x, G x ≠ ⊥) (hGf : ∃ x, G x ≠ ⊤) (hGc : CfbSegConvex G)
    (hHb : ∀ y, Hs y ≠ ⊥) (hHf : ∃ y, Hs y ≠ ⊤) (hHc : CfbSegConvex Hs) (x : X) (y : Y) :
    stepT PG PH τ σ L (x, y) = (x, y) ↔
      IsSubgradient G x (-(ContinuousLinearMap.adjoint L y)) ∧ IsSubgradient Hs y (L x) := by
  have hu1 : (1 / τ) • ((x - τ • ContinuousLinearMap.adjoint L y) - x) =
      -(ContinuousLinearMap.adjoint L y) := by
    rw [sub_sub_cancel_left, smul_neg, one_div, smul_smul, inv_mul_cancel₀ hτ.ne', one_smul]
  have hu2 : (1 / σ) • ((y + σ • L x) - y) = L x := by
    rw [add_sub_cancel_left, one_div, smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]
  have e2 : (2 : ℝ) • x - x = x := by rw [two_smul]; abel
  constructor
  · intro h
    have h1 : PG (x - τ • ContinuousLinearMap.adjoint L y) = x := congrArg Prod.fst h
    have h2 : PH (y + σ • L ((2 : ℝ) • PG (x - τ • ContinuousLinearMap.adjoint L y) - x)) = y :=
      congrArg Prod.snd h
    rw [h1, e2] at h2
    constructor
    · have := cfb_prox_subgrad hτ hGb hGf hGc hPG (x - τ • ContinuousLinearMap.adjoint L y)
      rw [h1, hu1] at this; exact this
    · have := cfb_prox_subgrad hσ hHb hHf hHc hPH (y + σ • L x)
      rw [h2, hu2] at this; exact this
  · rintro ⟨h1, h2⟩
    have a1 : PG (x - τ • ContinuousLinearMap.adjoint L y) = x :=
      cfb_prox_eq_of_subgrad hτ hGb hGf hGc hPG (by rw [hu1]; exact h1)
    have a2 : PH (y + σ • L x) = y :=
      cfb_prox_eq_of_subgrad hσ hHb hHf hHc hPH (by rw [hu2]; exact h2)
    refine Prod.ext ?_ ?_
    · exact a1
    · show PH (y + σ • L ((2 : ℝ) • PG (x - τ • ContinuousLinearMap.adjoint L y) - x)) = y
      rw [a1, e2, a2]

theorem fd_pert {H : Type*} [NormedAddCommGroup H] (P : H → H) (hn : ∀ a b, ‖P a - P b‖ ≤ ‖a - b‖)
    (u1 u0 e : H) : ‖P u1 + e - P u0‖ ≤ ‖u1 - u0‖ + ‖e‖ := by
  have : P u1 + e - P u0 = (P u1 - P u0) + e := by abel
  rw [this]
  exact (norm_add_le _ _).trans (add_le_add (hn _ _) le_rfl)

end Assembly

open Filter Topology InnerProductSpace CondatPD.FinDim InertialFB.IFB in
theorem solution {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] [FiniteDimensional ℝ Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (hF0 : F = 0)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh)
    (τ σ : ℝ) (hτ : 0 < τ) (hσ : 0 < σ)
    (PG : X → X) (PH : Y → Y)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (heF : ∀ n, eF n = 0)
    (hi : σ * τ * ‖L‖ ^ 2 ≤ 1)
    (hii : ∃ ε : ℝ, 0 < ε ∧ ∀ n, ε ≤ ρ n ∧ ρ n ≤ 2 - ε)
    (hiii : Summable (fun n => ‖eG n‖) ∧ Summable (fun n => ‖eH n‖)) :
    (∀ (x : ℕ → X) (y : ℕ → Y), IsAlg31Run F PG PH τ σ L ρ eF eG eH x y →
      ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh ∧
        Tendsto x atTop (𝓝 xh) ∧ Tendsto y atTop (𝓝 yh)) ∧
    (∀ (x : ℕ → X) (y : ℕ → Y), IsAlg32Run F PG PH τ σ L ρ eF eG eH x y →
      ∃ (xh : X) (yh : Y), IsPDSolution F G H L xh yh ∧
        Tendsto x atTop (𝓝 xh) ∧ Tendsto y atTop (𝓝 yh)) := by
  subst hF0
  have hg0 : ∀ x : X, gradient (0 : X → ℝ) x = 0 := by
    intro x; simp [gradient]
  have hGb := hG.1
  have hGf := hG.2.1
  have hGc := cfb_segConvex_of_ppc hG
  obtain ⟨xh, yh, hsol1, hsol2⟩ := hsol
  have hHb : ∀ y, conj H y ≠ ⊥ := cfb_conj_ne_bot hH.1 hH.2.1
  have hHf : ∃ y, conj H y ≠ ⊤ := ⟨yh, hsol2.1⟩
  have hHc := cfb_conj_segConvex H
  have hPGf : ∀ a b, ‖PG a - PG b‖ ^ 2 ≤ inner ℝ (PG a - PG b) (a - b) := fun a b => by
    have := cfb_prox_firm hτ hGb hGf hGc hPG a b
    rwa [real_inner_comm] at this
  have hPHf : ∀ a b, ‖PH a - PH b‖ ^ 2 ≤ inner ℝ (PH a - PH b) (a - b) := fun a b => by
    have := cfb_prox_firm hσ hHb hHf hHc hPH a b
    rwa [real_inner_comm] at this
  have hPGn := (fd_cont_of_firm PG hPGf).1
  have hPHn := (fd_cont_of_firm PH hPHf).1
  obtain ⟨hex, hey⟩ := hiii
  have hsolOf : ∀ (xs : X) (ys : Y), IsSubgradient G xs (-(ContinuousLinearMap.adjoint L ys)) →
      IsSubgradient (conj H) ys (L xs) → IsPDSolution (0 : X → ℝ) G H L xs ys := by
    intro xs ys h1 h2
    refine ⟨?_, h2⟩
    rw [hg0, sub_zero]; exact h1
  have hsol1' : IsSubgradient G xh (-(ContinuousLinearMap.adjoint L yh)) := by
    have := hsol1; rw [hg0, sub_zero] at this; exact this
  refine ⟨fun x y hrun => ?_, fun x y hrun => ?_⟩
  · -- Algorithm 3.1
    have hfixpt : ∃ w : X × Y, stepT PG PH τ σ L w = w :=
      ⟨(xh, yh), (fd_fix_iff G (conj H) L τ σ hτ hσ PG PH hPG hPH hGb hGf hGc hHb hHf hHc
        xh yh).2 ⟨hsol1', hsol2⟩⟩
    have hpair : ∀ n, x (n + 1) = ρ n • ((stepT PG PH τ σ L (x n, y n)).1 + eG n) + (1 - ρ n) • x n ∧
        y (n + 1) = ρ n • ((stepT PG PH τ σ L (x n, y n)).2 +
          (PH (y n + σ • L ((2 : ℝ) • (PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) + eG n)
              - x n)) + eH n - (stepT PG PH τ σ L (x n, y n)).2)) + (1 - ρ n) • y n := by
      intro n
      obtain ⟨h1, h2⟩ := hrun n
      simp only [heF n, hg0, smul_zero, add_zero, sub_zero] at h1 h2
      refine ⟨h1, ?_⟩
      rw [add_sub_cancel]
      exact h2
    have hey' : Summable (fun n => ‖PH (y n + σ • L ((2 : ℝ) •
        (PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) + eG n) - x n)) + eH n -
        (stepT PG PH τ σ L (x n, y n)).2‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
        ((hex.mul_left (2 * σ * ‖L‖)).add hey)
      have hp := fd_pert PH hPHn (y n + σ • L ((2 : ℝ) •
        (PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) + eG n) - x n))
        (y n + σ • L ((2 : ℝ) • PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) - x n)) (eH n)
      have hd : (y n + σ • L ((2 : ℝ) •
        (PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) + eG n) - x n)) -
        (y n + σ • L ((2 : ℝ) • PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) - x n))
        = ((2 : ℝ) * σ) • L (eG n) := by
        simp only [map_sub, map_smul, map_add, smul_add, smul_sub]; module
      rw [hd, norm_smul, Real.norm_of_nonneg (by positivity)] at hp
      have hl := L.le_opNorm (eG n)
      have hp2 : (2 : ℝ) * σ * ‖L (eG n)‖ ≤ 2 * σ * ‖L‖ * ‖eG n‖ := by
        have := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ 2 * σ)
        linarith
      exact (show ‖_ + eH n - (stepT PG PH τ σ L (x n, y n)).2‖ ≤ _ from hp).trans
        (by linarith)
    obtain ⟨w, hw, hx, hy⟩ := fd_pair_conv PG PH τ σ hτ hσ L hi hPGf hPHf hfixpt ρ hii eG
      (fun n => PH (y n + σ • L ((2 : ℝ) •
        (PG (x n - τ • ContinuousLinearMap.adjoint L (y n)) + eG n) - x n)) + eH n -
        (stepT PG PH τ σ L (x n, y n)).2) hex hey' x y hpair
    have hw' : stepT PG PH τ σ L (w.1, w.2) = (w.1, w.2) := hw
    have := (fd_fix_iff G (conj H) L τ σ hτ hσ PG PH hPG hPH hGb hGf hGc hHb hHf hHc w.1 w.2).1 hw'
    exact ⟨w.1, w.2, hsolOf _ _ this.1 this.2, hx, hy⟩
  · -- Algorithm 3.2: Algorithm 3.1 for the swapped instance `(Y, X, PH, PG, σ, τ, -L†)`
    set L' : Y →L[ℝ] X := -(ContinuousLinearMap.adjoint L) with hL'
    have ha : ContinuousLinearMap.adjoint L' = -L := by
      rw [hL', map_neg, ContinuousLinearMap.adjoint_adjoint]
    have hL'v : ∀ v : Y, L' v = -(ContinuousLinearMap.adjoint L v) := fun v => rfl
    have hst : ∀ (y : Y) (x : X), stepT PH PG σ τ L' (y, x) =
        (PH (y + σ • L x),
          PG (x - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • PH (y + σ • L x) - y))) := by
      intro y x
      simp [stepT, ha, hL'v, sub_eq_add_neg]
    have hnL' : ‖L'‖ = ‖L‖ := by
      rw [hL', norm_neg]
      exact LinearIsometryEquiv.norm_map _ L
    have hi' : τ * σ * ‖L'‖ ^ 2 ≤ 1 := by
      have : τ * σ * ‖L‖ ^ 2 = σ * τ * ‖L‖ ^ 2 := by ring
      rw [hnL', this]; exact hi
    have hfixpt : ∃ w : Y × X, stepT PH PG σ τ L' w = w := by
      refine ⟨(yh, xh), (fd_fix_iff (conj H) G L' σ τ hσ hτ PH PG hPH hPG hHb hHf hHc hGb hGf hGc
        yh xh).2 ⟨?_, ?_⟩⟩
      · rw [ha]; simpa using hsol2
      · rw [hL']; simpa using hsol1'
    have hpair : ∀ n, y (n + 1) = ρ n • ((stepT PH PG σ τ L' (y n, x n)).1 + eH n) + (1 - ρ n) • y n ∧
        x (n + 1) = ρ n • ((stepT PH PG σ τ L' (y n, x n)).2 +
          (PG (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) •
              (PH (y n + σ • L (x n)) + eH n) - y n)) + eG n -
            (stepT PH PG σ τ L' (y n, x n)).2)) + (1 - ρ n) • x n := by
      intro n
      obtain ⟨h1, h2⟩ := hrun n
      simp only [heF n, hg0, smul_zero, add_zero, sub_zero] at h1 h2
      rw [hst, add_sub_cancel]
      exact ⟨h2, h1⟩
    have hey' : Summable (fun n => ‖PG (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) •
        (PH (y n + σ • L (x n)) + eH n) - y n)) + eG n -
        (stepT PH PG σ τ L' (y n, x n)).2‖) := by
      refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
        ((hey.mul_left (2 * τ * ‖L‖)).add hex)
      rw [hst]
      have hp := fd_pert PG hPGn (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) •
        (PH (y n + σ • L (x n)) + eH n) - y n))
        (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • PH (y n + σ • L (x n)) - y n)) (eG n)
      have hd : (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) •
        (PH (y n + σ • L (x n)) + eH n) - y n)) -
        (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) • PH (y n + σ • L (x n)) - y n))
        = (-((2 : ℝ) * τ)) • ContinuousLinearMap.adjoint L (eH n) := by
        simp only [map_sub, map_smul, map_add, smul_add, smul_sub]; module
      rw [hd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)] at hp
      have hl : ‖ContinuousLinearMap.adjoint L (eH n)‖ ≤ ‖L‖ * ‖eH n‖ := by
        have := (ContinuousLinearMap.adjoint L).le_opNorm (eH n)
        rwa [LinearIsometryEquiv.norm_map] at this
      have hp2 : (2 : ℝ) * τ * ‖ContinuousLinearMap.adjoint L (eH n)‖ ≤ 2 * τ * ‖L‖ * ‖eH n‖ := by
        have := mul_le_mul_of_nonneg_left hl (by positivity : (0:ℝ) ≤ 2 * τ)
        linarith
      exact (show ‖_ + eG n - _‖ ≤ _ from hp).trans (by linarith)
    obtain ⟨w, hw, hx, hy⟩ := fd_pair_conv PH PG σ τ hσ hτ L' hi' hPHf hPGf hfixpt ρ hii eH
      (fun n => PG (x n - τ • ContinuousLinearMap.adjoint L ((2 : ℝ) •
        (PH (y n + σ • L (x n)) + eH n) - y n)) + eG n -
        (stepT PH PG σ τ L' (y n, x n)).2) hey hey' y x hpair
    have hw' : stepT PH PG σ τ L' (w.1, w.2) = (w.1, w.2) := hw
    have := (fd_fix_iff (conj H) G L' σ τ hσ hτ PH PG hPH hPG hHb hHf hHc hGb hGf hGc
      w.1 w.2).1 hw'
    refine ⟨w.2, w.1, hsolOf _ _ ?_ ?_, hy, hx⟩
    · have h2 := this.2
      rw [hL'] at h2; simpa using h2
    · have h1 := this.1
      rw [ha] at h1; simpa using h1
