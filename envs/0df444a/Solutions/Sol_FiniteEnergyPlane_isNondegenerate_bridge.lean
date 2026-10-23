-- Prove2me | solution 1 for FiniteEnergyPlane.isNondegenerate_bridge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T16:59:09.532303+00:00
-- url     : https://prove2.me/submissions/3141dd1b-2527-406a-ae4c-473a4d990fc5

import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Definitions.Def_HryniewiczCriterion_ConleyZehnder
import Theorems.Thm_FiniteEnergyPlane_reeb_spec
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_spec

set_option linter.all false

open Set Metric Filter Topology

namespace NBCore

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gronwall with bootstrap: trajectories starting close stay close, as long as the
predicted bound stays below the radius of the Lipschitz tubes. -/
lemma traj_close {R : E → E} {x Q : ℝ → E} {K : NNReal} {δ : ℝ}
    (hL : ∀ t, LipschitzOnWith K R (ball (x t) δ))
    (hx : ∀ t, HasDerivAt x (R (x t)) t) (hQ : ∀ t, HasDerivAt Q (R (Q t)) t)
    {a b ε : ℝ} (h0 : dist (Q a) (x a) ≤ ε) (hε : ε * Real.exp (K * (b - a)) < δ) :
    ∀ t ∈ Icc a b, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
  have hxc : Continuous x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.2 fun t => (hQ t).continuousAt
  have gron : ∀ c ∈ Icc a b, (∀ t ∈ Ico a c, dist (Q t) (x t) < δ) →
      ∀ t ∈ Icc a c, dist (Q t) (x t) ≤ ε * Real.exp (K * (t - a)) := by
    intro c hc hin
    have hδ : 0 < δ := lt_of_le_of_lt (le_trans dist_nonneg h0 |> fun h =>
      mul_nonneg h (Real.exp_pos _).le) hε
    exact dist_le_of_trajectories_ODE_of_mem (v := fun _ => R) (s := fun t => ball (x t) δ)
      (fun t _ => hL t) hQc.continuousOn (fun t _ => (hQ t).hasDerivWithinAt)
      (fun t ht => mem_ball.2 (hin t ht)) hxc.continuousOn (fun t _ => (hx t).hasDerivWithinAt)
      (fun t _ => mem_ball_self hδ) h0
  have mono : ∀ t ∈ Icc a b, ε * Real.exp (K * (t - a)) < δ := by
    intro t ht
    refine lt_of_le_of_lt ?_ hε
    have hε0 : 0 ≤ ε := le_trans dist_nonneg h0
    gcongr
    exact ht.2
  -- the set of bad times
  by_cases hS : ∃ t ∈ Icc a b, δ ≤ dist (Q t) (x t)
  · exfalso
    set S := Icc a b ∩ {t | δ ≤ dist (Q t) (x t)} with hSdef
    have hSc : IsClosed S := isClosed_Icc.inter (isClosed_le continuous_const (hQc.dist hxc))
    have hSne : S.Nonempty := by obtain ⟨t, ht, h⟩ := hS; exact ⟨t, ht, h⟩
    have hSb : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set c := sInf S
    have hc : c ∈ Icc a b := hmem.1
    have hin : ∀ t ∈ Ico a c, dist (Q t) (x t) < δ := by
      intro t ht
      by_contra hcon
      push Not at hcon
      have : c ≤ t := csInf_le hSb ⟨⟨ht.1, ht.2.le.trans hc.2⟩, hcon⟩
      exact absurd ht.2 (not_lt.2 this)
    have := gron c hc hin c ⟨hc.1, le_rfl⟩
    have h2 := mono c hc
    exact absurd hmem.2 (not_le.2 (lt_of_le_of_lt this h2))
  · push Not at hS
    intro t ht
    exact gron b ⟨ht.1.trans ht.2, le_rfl⟩ (fun t ht => hS t ⟨ht.1, ht.2.le⟩) t ht


variable [FiniteDimensional ℝ E]

lemma range_compact {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hxc : Continuous x)
    (hper : ∀ t, x (t + T) = x t) : IsCompact (range x) := by
  have : range x = x '' Icc 0 T := by
    apply subset_antisymm
    · rintro _ ⟨t, rfl⟩
      obtain ⟨y, hy, hxy⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := x) hper hT t
      exact ⟨y, Ico_subset_Icc_self hy, hxy.symm⟩
    · exact image_subset_range _ _
  rw [this]; exact isCompact_Icc.image hxc

lemma setup {R : E → E} {U : Set E} (hU : IsOpen U) (hR : ContDiffOn ℝ 1 R U)
    {x : ℝ → E} {T : ℝ} (hT : 0 < T) (hxc : Continuous x) (hper : ∀ t, x (t + T) = x t)
    (hxU : ∀ t, x t ∈ U) :
    ∃ δ > 0, ∃ K : NNReal, 0 < (K : ℝ) ∧ (∀ t, LipschitzOnWith K R (ball (x t) δ)) ∧
      (∀ t, ‖fderiv ℝ R (x t)‖ ≤ K) ∧
      (∀ η > 0, ∃ r > 0, r ≤ δ ∧ ∀ τ y, dist y (x τ) < r →
        ‖R y - R (x τ) - fderiv ℝ R (x τ) (y - x τ)‖ ≤ η * ‖y - x τ‖) := by
  have hcpt := range_compact hT hxc hper
  obtain ⟨δ, hδ, hsub⟩ := hcpt.exists_cthickening_subset_open hU (by rintro _ ⟨t, rfl⟩; exact hxU t)
  have hK0 : IsCompact (cthickening δ (range x)) := hcpt.cthickening
  have hdiff : ∀ y ∈ U, DifferentiableAt ℝ R y := fun y hy =>
    (hR.differentiableOn one_ne_zero y hy).differentiableAt (hU.mem_nhds hy)
  have hcont : ContinuousOn (fderiv ℝ R) U := hR.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M, hM⟩ := hK0.exists_bound_of_continuousOn (hcont.mono hsub)
  have hball : ∀ t, ball (x t) δ ⊆ cthickening δ (range x) := fun t =>
    (ball_subset_thickening (mem_range_self t) δ).trans (thickening_subset_cthickening _ _)
  set K : NNReal := Real.toNNReal (M + 1) with hKdef
  have hKM : (M : ℝ) + 1 ≤ K := Real.le_coe_toNNReal _
  have hMK : ∀ y ∈ cthickening δ (range x), ‖fderiv ℝ R y‖ ≤ K := fun y hy =>
    (hM y hy).trans (by linarith)
  refine ⟨δ, hδ, K, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ M := (norm_nonneg _).trans (hM _ (self_subset_cthickening _ (mem_range_self 0)))
    linarith
  · intro t
    apply (convex_ball (x t) δ).lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
    · exact fun y hy => hdiff y (hsub (hball t hy))
    · intro y hy
      have := hMK y (hball t hy)
      exact_mod_cast this
  · exact fun t => hMK _ (self_subset_cthickening _ (mem_range_self t))
  · intro η hη
    have huc := hK0.uniformContinuousOn_of_continuous (hcont.mono hsub)
    rw [Metric.uniformContinuousOn_iff] at huc
    obtain ⟨ρ, hρ, hρ'⟩ := huc η hη
    refine ⟨min ρ δ, lt_min hρ hδ, min_le_right _ _, ?_⟩
    intro τ y hy
    have hyb : ∀ z ∈ ball (x τ) (min ρ δ), z ∈ cthickening δ (range x) := fun z hz =>
      hball τ (ball_subset_ball (min_le_right _ _) hz)
    have key := (convex_ball (x τ) (min ρ δ)).norm_image_sub_le_of_norm_fderiv_le
      (𝕜 := ℝ) (f := fun z => R z - fderiv ℝ R (x τ) z) (C := η) (x := x τ) (y := y)
      (fun z hz => ((hdiff z (hsub (hyb z hz))).sub (fderiv ℝ R (x τ)).differentiableAt))
      (fun z hz => by
        rw [fderiv_fun_sub (hdiff z (hsub (hyb z hz))) (fderiv ℝ R (x τ)).differentiableAt,
          ContinuousLinearMap.fderiv]
        have := hρ' z (hyb z hz) (x τ) (hyb _ (mem_ball_self (lt_min hρ hδ)))
          (lt_of_lt_of_le (mem_ball.1 hz) (min_le_left _ _))
        rw [dist_eq_norm] at this
        exact this.le)
      (mem_ball_self (lt_min hρ hδ)) (mem_ball.2 hy)
    simpa [map_sub, sub_sub, sub_add_eq_sub_sub, add_comm, add_left_comm, add_assoc,
      sub_eq_add_neg] using key


end NBCore

namespace NBCore
open FiniteEnergyPlane
open scoped ContDiff

variable {n : ℕ}

lemma contDiff_j0 : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 fun k => ?_
  unfold j0
  by_cases h : (k : ℕ) % 2 = 0
  · simp only [h, dite_true]
    exact (contDiff_apply ℝ ℝ _).neg
  · simp only [h, dite_false]
    exact contDiff_apply ℝ ℝ _

lemma contDiff_hamVF (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (hamVF H) := by
  have hg : ContDiff ℝ ∞ (grad H) := by
    refine contDiff_pi.2 fun k => ?_
    exact (hH.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact contDiff_j0.comp hg

lemma contDiff_liouville : ContDiff ℝ ∞ (fun p : V n × V n => liouville p.1 p.2) := by
  unfold liouville omega0 dot
  refine ContDiff.div_const (ContDiff.sum fun k _ => ?_) _
  exact ((contDiff_apply ℝ ℝ k).comp (contDiff_j0.comp contDiff_fst)).mul
    ((contDiff_apply ℝ ℝ k).comp contDiff_snd)

lemma liouvilleCLM_apply (x v : V n) : liouvilleCLM x v = liouville x v := by
  simp [liouvilleCLM, liouville, omega0, dot, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end NBCore

open FiniteEnergyPlane
open scoped ContDiff

namespace NBCore

section lode_sec
section lode
open Set Filter Topology
open scoped NNReal
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma uf_lode_local (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (h : ℝ) (hh : 0 < h) (hKh : 2 * (K:ℝ) * h ≤ 1) (s : ℝ) (x₀ : F) :
    ∃ y : ℝ → F, y s = x₀ ∧ ∀ t ∈ Icc (s - h) (s + h),
      HasDerivWithinAt y (B t (y t)) (Icc (s - h) (s + h)) t := by
  have hs : s ∈ Icc (s - h) (s + h) := ⟨by linarith, by linarith⟩
  have hP : IsPicardLindelof (fun t => (B t : F → F)) (⟨s, hs⟩ : Icc (s-h) (s+h)) x₀
      (‖x₀‖₊ + 1) 0 (K * (2 * ‖x₀‖₊ + 1)) K := by
    refine ⟨fun t _ => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith,
      fun x _ => (hB.clm_apply continuous_const).continuousOn, fun t _ x hx => ?_, ?_⟩
    · have hx' : ‖x‖ ≤ 2 * ‖x₀‖ + 1 := by
        have h1 := mem_closedBall_iff_norm.1 hx
        have h2 := norm_le_norm_add_norm_sub' x x₀
        push_cast at h1; linarith
      have hKt : ‖B t‖ ≤ K := by exact_mod_cast hK t
      calc ‖B t x‖ ≤ ‖B t‖ * ‖x‖ := (B t).le_opNorm x
        _ ≤ K * (2 * ‖x₀‖ + 1) := mul_le_mul hKt hx' (norm_nonneg _) K.2
        _ = ((K * (2 * ‖x₀‖₊ + 1) : ℝ≥0) : ℝ) := by push_cast; rfl
    · have e1 : (s + h) - s = h := by ring
      have e2 : s - (s - h) = h := by ring
      simp only [e1, e2, max_self, NNReal.coe_zero, sub_zero]
      push_cast
      have := norm_nonneg x₀
      have hK0 := K.2
      nlinarith
  obtain ⟨y, hy0, hy⟩ := hP.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨y, hy0, hy⟩

lemma uf_piece {y g : ℝ → F} {S : Set ℝ} (hS : IsClosed S) (B : ℝ → F →L[ℝ] F)
    (heq : EqOn y g S) (hg : ∀ t ∈ S, HasDerivWithinAt g (B t (g t)) S t) (t : ℝ) :
    HasDerivWithinAt y (B t (y t)) S t := by
  by_cases ht : t ∈ S
  · rw [heq ht]; exact (hg t ht).congr (fun x hx => heq hx) (heq ht)
  · exact hasDerivWithinAt_iff_hasFDerivWithinAt.2
      (HasFDerivWithinAt.of_notMem_closure (by rwa [hS.closure_eq]))

lemma uf_lode_steps (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (h : ℝ) (hh : 0 < h) (hKh : 2 * (K:ℝ) * h ≤ 1) (x₀ : F) (N : ℕ) :
    ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t ∈ Icc (-((N+1) * h)) ((N+1) * h),
      HasDerivWithinAt y (B t (y t)) (Icc (-((N+1) * h)) ((N+1) * h)) t := by
  induction N with
  | zero =>
    obtain ⟨y, hy0, hy⟩ := uf_lode_local B hB K hK h hh hKh 0 x₀
    refine ⟨y, hy0, ?_⟩
    simpa using hy
  | succ N ih =>
    obtain ⟨y, hy0, hy⟩ := ih
    set c : ℝ := (N + 1) * h with hc
    have hc0 : 0 < c := by positivity
    obtain ⟨u, hu0, hu⟩ := uf_lode_local B hB K hK h hh hKh c (y c)
    obtain ⟨w, hw0, hw⟩ := uf_lode_local B hB K hK h hh hKh (-c) (y (-c))
    let z : ℝ → F := fun t => if c < t then u t else if t < -c then w t else y t
    have hcc : ((N + 1 : ℕ) + 1 : ℝ) * h = c + h := by push_cast; rw [hc]; ring
    refine ⟨z, ?_, ?_⟩
    · simp only [z, if_neg (show ¬ c < 0 by linarith), if_neg (show ¬ (0:ℝ) < -c by linarith), hy0]
    rw [hcc]
    have hU : Icc (-(c + h)) (c + h) = (Icc (-(c+h)) (-c) ∪ Icc (-c) c) ∪ Icc c (c + h) := by
      rw [Icc_union_Icc_eq_Icc (by linarith) (by linarith),
        Icc_union_Icc_eq_Icc (by linarith) (by linarith)]
    intro t _
    rw [hU]
    refine HasDerivWithinAt.union (HasDerivWithinAt.union ?_ ?_) ?_
    · refine uf_piece isClosed_Icc B (g := w) ?_ ?_ t
      · intro s hs
        simp only [z]
        rcases eq_or_lt_of_le hs.2 with h1 | h1
        · rw [if_neg (by linarith), if_neg (by linarith), h1, hw0]
        · rw [if_neg (by linarith), if_pos h1]
      · intro s hs
        exact (hw s ⟨by linarith [hs.1], by linarith [hs.2]⟩).mono
          (Icc_subset_Icc (by linarith) (by linarith))
    · refine uf_piece isClosed_Icc B (g := y) ?_ ?_ t
      · intro s hs
        simp only [z]; rw [if_neg (by linarith [hs.2]), if_neg (by linarith [hs.1])]
      · intro s hs; exact hy s hs
    · refine uf_piece isClosed_Icc B (g := u) ?_ ?_ t
      · intro s hs
        simp only [z]
        rcases eq_or_lt_of_le hs.1 with h1 | h1
        · rw [if_neg (by linarith), if_neg (by linarith), ← h1, hu0]
        · rw [if_pos h1]
      · intro s hs
        exact (hu s ⟨by linarith [hs.1], by linarith [hs.2]⟩).mono
          (Icc_subset_Icc (by linarith) (by linarith))

lemma uf_lode_exists (B : ℝ → F →L[ℝ] F) (hB : Continuous B) (K : ℝ≥0)
    (hK : ∀ t, ‖B t‖₊ ≤ K) (x₀ : F) :
    ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t, HasDerivAt y (B t (y t)) t := by
  set h : ℝ := 1 / (2 * (K:ℝ) + 1) with hhdef
  have hh : 0 < h := by positivity
  have hKh : 2 * (K:ℝ) * h ≤ 1 := by
    rw [hhdef, mul_one_div, div_le_one (by positivity)]; linarith
  choose Ψ hΨ0 hΨ using uf_lode_steps B hB K hK h hh hKh x₀
  have hint : ∀ M : ℕ, ∀ t ∈ Ioo (-((M+1) * h)) ((M+1) * h), HasDerivAt (Ψ M) (B t (Ψ M t)) t := by
    intro M t ht
    exact (hΨ M t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hagree : ∀ M N : ℕ, ∀ s, |s| < (min M N + 1) * h → Ψ M s = Ψ N s := by
    intro M N s hs
    have hk : ((min M N : ℕ) : ℝ) = min (M:ℝ) (N:ℝ) := by push_cast; rfl
    have hsub : ∀ L : ℕ, min M N ≤ L → Ioo (-((min M N + 1) * h)) ((min M N + 1) * h) ⊆
        Ioo (-((L+1) * h)) ((L+1) * h) := by
      intro L hL
      have : ((min M N : ℕ) : ℝ) ≤ L := by exact_mod_cast hL
      apply Ioo_subset_Ioo <;> nlinarith
    have := ODE_solution_unique_of_mem_Ioo (K := K) (v := fun t => (B t : F → F))
      (s := fun _ => (univ : Set F)) (f := Ψ M) (g := Ψ N)
      (a := -((min M N + 1) * h)) (b := (min M N + 1) * h) (t₀ := 0)
      (fun t _ => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith)
      ⟨by have : (0:ℝ) ≤ min M N := by positivity
          nlinarith, by positivity⟩
      (fun t ht => ⟨hint M t (hsub M (min_le_left _ _) ht), trivial⟩)
      (fun t ht => ⟨hint N t (hsub N (min_le_right _ _) ht), trivial⟩)
      (by rw [hΨ0, hΨ0])
    exact this ⟨by rw [abs_lt] at hs; push_cast at hs ⊢; linarith, by rw [abs_lt] at hs; push_cast at hs ⊢; linarith⟩
  let Nf : ℝ → ℕ := fun t => ⌈|t| / h⌉₊
  have hNf : ∀ t, |t| ≤ Nf t * h := by
    intro t
    have := Nat.le_ceil (|t| / h)
    rwa [div_le_iff₀ hh] at this
  refine ⟨fun t => Ψ (Nf t) t, ?_, ?_⟩
  · exact hΨ0 _
  intro t
  set M := Nf t
  have hev : (fun s => Ψ (Nf s) s) =ᶠ[𝓝 t] Ψ M := by
    have hmem : Ioo (-((M+1) * h)) ((M+1) * h) ∈ 𝓝 t := by
      apply Ioo_mem_nhds
      · have := hNf t; have := neg_abs_le t; nlinarith
      · have := hNf t; have := le_abs_self t; nlinarith
    filter_upwards [hmem] with s hs
    apply hagree
    have h1 := hNf s
    have hs' : |s| < (M + 1) * h := abs_lt.2 ⟨by linarith [hs.1], hs.2⟩
    rcases le_total (Nf s) M with hle | hle
    · rw [min_eq_left hle]; nlinarith
    · rw [min_eq_right hle]; exact hs'
  have hd := hint M t ⟨by have := hNf t; have := neg_abs_le t; nlinarith,
    by have := hNf t; have := le_abs_self t; nlinarith⟩
  have := hd.congr_of_eventuallyEq hev
  exact this

lemma uf_lode_unique (B : ℝ → F →L[ℝ] F) (K : ℝ≥0) (hK : ∀ t, ‖B t‖₊ ≤ K)
    (y z : ℝ → F) (hy : ∀ t, HasDerivAt y (B t (y t)) t) (hz : ∀ t, HasDerivAt z (B t (z t)) t)
    (t₀ : ℝ) (h0 : y t₀ = z t₀) : y = z :=
  ODE_solution_unique_univ (K := K) (v := fun t => (B t : F → F)) (s := fun _ => (univ : Set F))
    (fun t => ((B t).lipschitz.weaken (hK t)).lipschitzOnWith)
    (fun t => ⟨hy t, trivial⟩) (fun t => ⟨hz t, trivial⟩) h0

end lode

end lode_sec
end NBCore


set_option linter.all false

open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff

namespace NB

abbrev R4 := HryniewiczCriterion.R4

variable (H : R4 → ℝ)

lemma vf (x : R4) :
    hamVF (n := 1) H x = HryniewiczCriterion.hamiltonianVectorField H x := by
  funext k
  fin_cases k <;> simp [hamVF, j0, grad, HryniewiczCriterion.hamiltonianVectorField,
    HryniewiczCriterion.partialDeriv]

lemma fd4 (x v : R4) :
    fderiv ℝ H x v = ∑ k, v k * fderiv ℝ H x (Pi.single k 1) := by
  have hx : v = ∑ k, v k • (Pi.single k (1:ℝ) : R4) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  calc fderiv ℝ H x v = fderiv ℝ H x (∑ k, v k • (Pi.single k (1:ℝ) : R4)) := by
        rw [← hx]
    _ = _ := by simp [map_sum, map_smul]

lemma j0e (x : V 1) : j0 x = ![-x 1, x 0, -x 3, x 2] := by
  funext k; fin_cases k <;> simp [j0]

@[simp] lemma c0 (a b c d : ℝ) : (![a, b, c, d] : R4) 0 = a := rfl
@[simp] lemma c1 (a b c d : ℝ) : (![a, b, c, d] : R4) 1 = b := rfl
@[simp] lemma c2 (a b c d : ℝ) : (![a, b, c, d] : R4) 2 = c := rfl
@[simp] lemma c3 (a b c d : ℝ) : (![a, b, c, d] : R4) 3 = d := rfl

lemma om_eq (u v : R4) : FiniteEnergyPlane.omega0 (n := 1) u v = HryniewiczCriterion.omega0 u v := by
  simp only [FiniteEnergyPlane.omega0, dot, j0e, HryniewiczCriterion.omega0]
  simp [Fin.sum_univ_succ]; ring

lemma liou_eq (x v : R4) : liouville (n := 1) x v = HryniewiczCriterion.liouvilleForm x v := by
  simp only [liouville, om_eq, HryniewiczCriterion.omega0, HryniewiczCriterion.liouvilleForm]

lemma hc_om (u v : R4) : HryniewiczCriterion.omega0 u v =
    u 0 * v 1 - u 1 * v 0 + u 2 * v 3 - u 3 * v 2 := rfl

lemma lam (x : R4) :
    liouville (n := 1) x (hamVF H x) = fderiv ℝ H x x / 2 := by
  rw [vf, fd4, liou_eq]
  simp only [HryniewiczCriterion.liouvilleForm, Fin.sum_univ_four,
    HryniewiczCriterion.hamiltonianVectorField, HryniewiczCriterion.partialDeriv]
  simp

lemma dHX (x : R4) : fderiv ℝ H x (hamVF (n := 1) H x) = 0 := by
  rw [fd4, vf]
  simp only [Fin.sum_univ_four, HryniewiczCriterion.hamiltonianVectorField,
    HryniewiczCriterion.partialDeriv]
  simp
  ring

/-! ### The frame -/

section frame
variable {H}
variable {p : R4} (hp : 0 < fderiv ℝ H p p)
include hp

lemma s_pos : 0 < HryniewiczCriterion.dot4 p p := by
  by_contra h
  have h0 : p = 0 := by
    have hs : HryniewiczCriterion.dot4 p p = 0 := by
      apply le_antisymm (not_lt.1 h)
      simp only [HryniewiczCriterion.dot4, Fin.sum_univ_four]; nlinarith [mul_self_nonneg (p 0), mul_self_nonneg (p 1), mul_self_nonneg (p 2), mul_self_nonneg (p 3)]
    simp only [HryniewiczCriterion.dot4, Fin.sum_univ_four] at hs
    funext k; fin_cases k <;> simp <;> nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  subst h0; simp at hp

lemma frame_xi1 : IsInXi (n := 1) H p (HryniewiczCriterion.xiFrame1 H p) := by
  have hne := hp.ne'
  constructor
  · rw [liou_eq]
    simp only [HryniewiczCriterion.liouvilleForm, HryniewiczCriterion.xiFrame1,
      HryniewiczCriterion.xiFrameRaw, HryniewiczCriterion.quatQ2, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, c0, c1, c2, c3]
    ring
  · simp only [HryniewiczCriterion.xiFrame1, HryniewiczCriterion.xiFrameRaw, map_smul, map_sub,
      smul_eq_mul]
    field_simp; ring

lemma frame_xi2 : IsInXi (n := 1) H p (HryniewiczCriterion.xiFrame2 H p) := by
  have hne := hp.ne'
  constructor
  · rw [liou_eq]
    simp only [HryniewiczCriterion.liouvilleForm, HryniewiczCriterion.xiFrame2,
      HryniewiczCriterion.xiFrameRaw, HryniewiczCriterion.quatQ1, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, c0, c1, c2, c3]
    ring
  · simp only [HryniewiczCriterion.xiFrame2, HryniewiczCriterion.xiFrameRaw, map_smul, map_sub,
      smul_eq_mul]
    field_simp; ring

lemma frame_om : HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H p)
    (HryniewiczCriterion.xiFrame2 H p) = 1 := by
  have hs := s_pos hp
  set r := HryniewiczCriterion.euclidNorm p with hr
  have hr2 : r ^ 2 = HryniewiczCriterion.dot4 p p := Real.sq_sqrt hs.le
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr2; linarith
  set a := fderiv ℝ H p (HryniewiczCriterion.quatQ2 p) / fderiv ℝ H p p
  set b := fderiv ℝ H p (HryniewiczCriterion.quatQ1 p) / fderiv ℝ H p p
  simp only [HryniewiczCriterion.dot4, Fin.sum_univ_four] at hr2
  simp only [hc_om, HryniewiczCriterion.xiFrame1, HryniewiczCriterion.xiFrame2,
    HryniewiczCriterion.xiFrameRaw, HryniewiczCriterion.quatQ1, HryniewiczCriterion.quatQ2, ← hr,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c0, c1, c2, c3]
  field_simp
  linear_combination (-((fderiv ℝ H p) p ^ 2)) * hr2

end frame

section lin
open HryniewiczCriterion in
lemma hom_lin (u v w : R4) (a b : ℝ) :
    HryniewiczCriterion.omega0 u (a • v + b • w) = a * HryniewiczCriterion.omega0 u v + b * HryniewiczCriterion.omega0 u w := by
  simp only [hc_om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma hom_lin_l (u v w : R4) (a b : ℝ) :
    HryniewiczCriterion.omega0 (a • v + b • w) u = a * HryniewiczCriterion.omega0 v u + b * HryniewiczCriterion.omega0 w u := by
  simp only [hc_om, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma hom_anti (u v : R4) : HryniewiczCriterion.omega0 u v = - HryniewiczCriterion.omega0 v u := by
  simp only [hc_om]; ring

lemma hom_self (u : R4) : HryniewiczCriterion.omega0 u u = 0 := by
  simp only [hc_om]; ring

lemma lf_eq (x v : R4) : HryniewiczCriterion.liouvilleForm x v = HryniewiczCriterion.omega0 x v / 2 := by
  simp only [HryniewiczCriterion.liouvilleForm, hc_om]
end lin

section frame2
variable {H}
variable {p : R4} (hp : 0 < fderiv ℝ H p p)
include hp

lemma nondeg {u : R4} (h1 : HryniewiczCriterion.liouvilleForm p u = 0) (h2 : fderiv ℝ H p u = 0)
    (h3 : HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H p) u = 0)
    (h4 : HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame2 H p) u = 0) : u = 0 := by
  have hs := s_pos hp
  set r := HryniewiczCriterion.euclidNorm p with hr
  have hr2 : r ^ 2 = HryniewiczCriterion.dot4 p p := Real.sq_sqrt hs.le
  have hr0 : r ≠ 0 := by intro h; rw [h] at hr2; linarith
  have hri : r⁻¹ ≠ 0 := inv_ne_zero hr0
  have eA : p 0 * u 1 - p 1 * u 0 + p 2 * u 3 - p 3 * u 2 = 0 := by
    simp only [HryniewiczCriterion.liouvilleForm] at h1; linarith
  have eC : p 3 * u 1 - p 2 * u 0 - p 1 * u 3 + p 0 * u 2 = 0 := by
    simp only [hc_om, HryniewiczCriterion.xiFrame1, HryniewiczCriterion.xiFrameRaw,
      HryniewiczCriterion.quatQ2, ← hr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c0, c1, c2, c3] at h4 h3
    have : r⁻¹ * ((p 3 * u 1 - p 2 * u 0 - p 1 * u 3 + p 0 * u 2) - (fderiv ℝ H p ![p 3, p 2, -p 1, -p 0] / fderiv ℝ H p p) * (p 0 * u 1 - p 1 * u 0 + p 2 * u 3 - p 3 * u 2)) = 0 := by
      linear_combination h3
    rw [eA, mul_zero, sub_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hri
  have eB : -p 2 * u 1 - p 3 * u 0 + p 0 * u 3 + p 1 * u 2 = 0 := by
    simp only [hc_om, HryniewiczCriterion.xiFrame2, HryniewiczCriterion.xiFrameRaw,
      HryniewiczCriterion.quatQ1, ← hr, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c0, c1, c2, c3] at h4
    have : r⁻¹ * ((-p 2 * u 1 - p 3 * u 0 + p 0 * u 3 + p 1 * u 2) - (fderiv ℝ H p ![-p 2, p 3, p 0, -p 1] / fderiv ℝ H p p) * (p 0 * u 1 - p 1 * u 0 + p 2 * u 3 - p 3 * u 2)) = 0 := by
      linear_combination h4
    rw [eA, mul_zero, sub_zero] at this
    exact (mul_eq_zero.1 this).resolve_left hri
  set S := HryniewiczCriterion.dot4 p p
  have hS : S = p 0 * p 0 + p 1 * p 1 + p 2 * p 2 + p 3 * p 3 := by
    simp only [S, HryniewiczCriterion.dot4, Fin.sum_univ_four]
  set m := p 0 * u 0 + p 1 * u 1 + p 2 * u 2 + p 3 * u 3
  have k0 : S * u 0 = m * p 0 := by rw [hS]; linear_combination (-p 1) * eA + (-p 3) * eB + (-p 2) * eC
  have k1 : S * u 1 = m * p 1 := by rw [hS]; linear_combination (p 0) * eA + (-p 2) * eB + (p 3) * eC
  have k2 : S * u 2 = m * p 2 := by rw [hS]; linear_combination (-p 3) * eA + (p 1) * eB + (p 0) * eC
  have k3 : S * u 3 = m * p 3 := by rw [hS]; linear_combination (p 2) * eA + (p 0) * eB + (-p 1) * eC
  have hdu := fd4 H p u
  have hdp := fd4 H p p
  simp only [Fin.sum_univ_four] at hdu hdp
  have hm : m = 0 := by
    have : S * fderiv ℝ H p u = m * fderiv ℝ H p p := by
      rw [hdu, hdp]; linear_combination (fderiv ℝ H p (Pi.single 0 1)) * k0 +
        (fderiv ℝ H p (Pi.single 1 1)) * k1 + (fderiv ℝ H p (Pi.single 2 1)) * k2 +
        (fderiv ℝ H p (Pi.single 3 1)) * k3
    rw [h2, mul_zero] at this
    exact (mul_eq_zero.1 this.symm).resolve_right hp.ne'
  have hS0 : S ≠ 0 := hs.ne'
  funext k
  fin_cases k
  · have := k0; rw [hm, zero_mul] at this; simpa using (mul_eq_zero.1 this).resolve_left hS0
  · have := k1; rw [hm, zero_mul] at this; simpa using (mul_eq_zero.1 this).resolve_left hS0
  · have := k2; rw [hm, zero_mul] at this; simpa using (mul_eq_zero.1 this).resolve_left hS0
  · have := k3; rw [hm, zero_mul] at this; simpa using (mul_eq_zero.1 this).resolve_left hS0

lemma span_xi {w : R4} (hw : IsInXi (n := 1) H p w) :
    w = HryniewiczCriterion.omega0 w (HryniewiczCriterion.xiFrame2 H p) • HryniewiczCriterion.xiFrame1 H p +
      HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H p) w • HryniewiczCriterion.xiFrame2 H p := by
  set Z1 := HryniewiczCriterion.xiFrame1 H p
  set Z2 := HryniewiczCriterion.xiFrame2 H p
  have h12 : HryniewiczCriterion.omega0 Z1 Z2 = 1 := frame_om hp
  have x1 := frame_xi1 hp
  have x2 := frame_xi2 hp
  set α := HryniewiczCriterion.omega0 w Z2
  set β := HryniewiczCriterion.omega0 Z1 w
  have key : w - (α • Z1 + β • Z2) = 0 := by
    apply nondeg hp
    · have := hw.1; have := x1.1; have := x2.1
      simp only [liou_eq, lf_eq] at *
      have e : HryniewiczCriterion.omega0 p (w - (α • Z1 + β • Z2)) =
        HryniewiczCriterion.omega0 p w - (α * HryniewiczCriterion.omega0 p Z1 + β * HryniewiczCriterion.omega0 p Z2) := by
        simp only [hc_om, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e]
      have : HryniewiczCriterion.omega0 p w = 0 := by linarith
      have : HryniewiczCriterion.omega0 p Z1 = 0 := by linarith
      have : HryniewiczCriterion.omega0 p Z2 = 0 := by linarith
      simp [*]
    · rw [map_sub, map_add, map_smul, map_smul, hw.2, x1.2, x2.2]; simp
    · have e : HryniewiczCriterion.omega0 Z1 (w - (α • Z1 + β • Z2)) =
        HryniewiczCriterion.omega0 Z1 w - (α * HryniewiczCriterion.omega0 Z1 Z1 + β * HryniewiczCriterion.omega0 Z1 Z2) := by
        simp only [hc_om, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e, hom_self, h12]; simp [β]
    · have e : HryniewiczCriterion.omega0 Z2 (w - (α • Z1 + β • Z2)) =
        HryniewiczCriterion.omega0 Z2 w - (α * HryniewiczCriterion.omega0 Z2 Z1 + β * HryniewiczCriterion.omega0 Z2 Z2) := by
        simp only [hc_om, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [e, hom_self, hom_anti Z2 Z1, h12, hom_anti Z2 w]; simp [α]
  exact sub_eq_zero.1 key

lemma coords_frame (c : Fin 2 → ℝ) :
    HryniewiczCriterion.xiCoords H p (c 0 • HryniewiczCriterion.xiFrame1 H p + c 1 • HryniewiczCriterion.xiFrame2 H p) = c := by
  have h12 := frame_om hp
  funext i
  fin_cases i
  · simp only [HryniewiczCriterion.xiCoords]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [hom_lin_l, hom_self, h12]; ring
  · simp only [HryniewiczCriterion.xiCoords]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [hom_lin, hom_self, h12]; ring

lemma xi_comb (c : Fin 2 → ℝ) :
    IsInXi (n := 1) H p (c 0 • HryniewiczCriterion.xiFrame1 H p + c 1 • HryniewiczCriterion.xiFrame2 H p) := by
  have x1 := frame_xi1 hp
  have x2 := frame_xi2 hp
  constructor
  · have a1 := x1.1; have a2 := x2.1
    simp only [liou_eq, lf_eq] at *
    rw [hom_lin]; rw [show HryniewiczCriterion.omega0 p (HryniewiczCriterion.xiFrame1 H p) = 0 by linarith,
      show HryniewiczCriterion.omega0 p (HryniewiczCriterion.xiFrame2 H p) = 0 by linarith]; simp
  · rw [map_add, map_smul, map_smul, x1.2, x2.2]; simp

/-! projection along `X_H` -/
lemma lX_pos : 0 < HryniewiczCriterion.liouvilleForm p (HryniewiczCriterion.hamiltonianVectorField H p) := by
  rw [← vf, ← liou_eq, lam]; linarith

lemma proj_xi {v : R4} (hv : fderiv ℝ H p v = 0) :
    IsInXi (n := 1) H p (HryniewiczCriterion.reebProjection H p v) := by
  have hl := lX_pos hp
  constructor
  · rw [liou_eq]
    simp only [HryniewiczCriterion.reebProjection]
    have e : ∀ (v w : R4) (c : ℝ), HryniewiczCriterion.liouvilleForm p (v - c • w) =
        HryniewiczCriterion.liouvilleForm p v - c * HryniewiczCriterion.liouvilleForm p w := by
      intro v w c
      simp only [HryniewiczCriterion.liouvilleForm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, div_mul_cancel₀ _ hl.ne', sub_self]
  · simp only [HryniewiczCriterion.reebProjection, map_sub, map_smul, hv, ← vf]; simp only [smul_eq_mul, sub_eq_self, mul_eq_zero]; exact Or.inr (dHX H p)

lemma proj_addX (v : R4) (c : ℝ) :
    HryniewiczCriterion.reebProjection H p (v + c • HryniewiczCriterion.hamiltonianVectorField H p) =
      HryniewiczCriterion.reebProjection H p v := by
  have hl := (lX_pos hp).ne'
  simp only [HryniewiczCriterion.reebProjection]
  have e : HryniewiczCriterion.liouvilleForm p (v + c • HryniewiczCriterion.hamiltonianVectorField H p) =
      HryniewiczCriterion.liouvilleForm p v + c * HryniewiczCriterion.liouvilleForm p (HryniewiczCriterion.hamiltonianVectorField H p) := by
    simp only [HryniewiczCriterion.liouvilleForm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [e, add_div, mul_div_assoc, div_self hl, mul_one, add_smul]
  abel

lemma proj_id {v : R4} (hv : HryniewiczCriterion.liouvilleForm p v = 0) :
    HryniewiczCriterion.reebProjection H p v = v := by
  simp [HryniewiczCriterion.reebProjection, hv]

end frame2

end NB


set_option linter.all false

open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff NNReal

namespace NB

lemma per_bdd {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} (hf : Continuous f) {T : ℝ}
    (hT : 0 < T) (hp : ∀ t, f (t + T) = f t) : ∃ K : ℝ≥0, ∀ t, ‖f t‖₊ ≤ K := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨C.toNNReal, fun t => ?_⟩
  obtain ⟨y, hy, hyt⟩ := Function.Periodic.exists_mem_Ico₀ (c := T) (f := f) hp hT t
  rw [hyt]
  have := hC y (Ico_subset_Icc_self hy)
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact this.trans (Real.le_coe_toNNReal C)

lemma lode_uniq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : ℝ → F →L[ℝ] F) (hB : Continuous B) {T : ℝ} (hT : 0 < T) (hp : ∀ t, B (t + T) = B t)
    (y z : ℝ → F) (hy : ∀ t, HasDerivAt y (B t (y t)) t) (hz : ∀ t, HasDerivAt z (B t (z t)) t)
    (t₀ : ℝ) (h0 : y t₀ = z t₀) : y = z := by
  obtain ⟨K, hK⟩ := per_bdd hB hT hp
  exact NBCore.uf_lode_unique B K hK y z hy hz t₀ h0

lemma lode_ex {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (B : ℝ → F →L[ℝ] F) (hB : Continuous B) {T : ℝ} (hT : 0 < T) (hp : ∀ t, B (t + T) = B t)
    (x₀ : F) : ∃ y : ℝ → F, y 0 = x₀ ∧ ∀ t, HasDerivAt y (B t (y t)) t := by
  obtain ⟨K, hK⟩ := per_bdd hB hT hp
  exact NBCore.uf_lode_exists B hB K hK x₀

variable {H : R4 → ℝ} (hH : HryniewiczCriterion.IsStrictlyStarShapedLevel H)
  (P : HryniewiczCriterion.PeriodicOrbit H)

lemma X_smooth (hH : HryniewiczCriterion.IsStrictlyStarShapedLevel H) :
    ContDiff ℝ ∞ (hamVF (n := 1) H) := NBCore.contDiff_hamVF (n := 1) H hH.1

lemma hx (t : ℝ) : HasDerivAt P.x (hamVF (n := 1) H (P.x t)) t := by
  have := P.trajectory.1 t; rwa [← vf] at this

lemma xc : Continuous P.x := continuous_iff_continuousAt.2 fun t => (hx P t).continuousAt

lemma hxs (a s : ℝ) : HasDerivAt (fun s => P.x (a + s)) (hamVF (n := 1) H (P.x (a + s))) s :=
  (hx P (a + s)).comp_const_add a s

/-- `D(t) = DX_H(x(t))` -/
noncomputable def DX (H : R4 → ℝ) (y : R4) : R4 →L[ℝ] R4 := fderiv ℝ (hamVF (n := 1) H) y

include hH in
lemma DX_cont : Continuous (DX H) := (X_smooth hH).continuous_fderiv (by simp)

include hH in
lemma X_hasFDeriv (y : R4) : HasFDerivAt (hamVF (n := 1) H) (DX H y) y :=
  ((X_smooth hH).differentiable (by simp) y).hasFDerivAt

/-- `Y` is the linearized flow along `t ↦ x(a + t)` starting at the identity. -/
def IsFl (P : HryniewiczCriterion.PeriodicOrbit H) (a : ℝ) (Y : ℝ → (R4 →L[ℝ] R4)) : Prop :=
  Y 0 = ContinuousLinearMap.id ℝ R4 ∧ ∀ t, HasDerivAt Y ((DX H (P.x (a + t))).comp (Y t)) t

lemma per_x (a t : ℝ) : P.x (a + (t + P.T)) = P.x (a + t) := by
  rw [← add_assoc, P.periodic]

include hH in
lemma exFl (a : ℝ) : ∃ Y, IsFl P a Y := by
  set B : ℝ → (R4 →L[ℝ] R4) →L[ℝ] (R4 →L[ℝ] R4) :=
    fun t => ContinuousLinearMap.compL ℝ R4 R4 R4 (DX H (P.x (a + t)))
  have hB : Continuous B := (ContinuousLinearMap.compL ℝ R4 R4 R4).continuous.comp
    ((DX_cont hH).comp ((xc P).comp (continuous_const.add continuous_id)))
  have hp : ∀ t, B (t + P.T) = B t := fun t => by simp only [B, per_x]
  obtain ⟨y, hy0, hy⟩ := lode_ex B hB P.T_pos hp (ContinuousLinearMap.id ℝ R4)
  exact ⟨y, hy0, fun t => hy t⟩

include hH in
lemma uniqFl {a : ℝ} {Y Z : ℝ → (R4 →L[ℝ] R4)}
    (hY : ∀ t, HasDerivAt Y ((DX H (P.x (a + t))).comp (Y t)) t)
    (hZ : ∀ t, HasDerivAt Z ((DX H (P.x (a + t))).comp (Z t)) t) (t₀ : ℝ) (h0 : Y t₀ = Z t₀) :
    Y = Z := by
  set B : ℝ → (R4 →L[ℝ] R4) →L[ℝ] (R4 →L[ℝ] R4) :=
    fun t => ContinuousLinearMap.compL ℝ R4 R4 R4 (DX H (P.x (a + t)))
  have hB : Continuous B := (ContinuousLinearMap.compL ℝ R4 R4 R4).continuous.comp
    ((DX_cont hH).comp ((xc P).comp (continuous_const.add continuous_id)))
  have hp : ∀ t, B (t + P.T) = B t := fun t => by simp only [B, per_x]
  exact lode_uniq B hB P.T_pos hp Y Z hY hZ t₀ h0

include hH in
lemma uniqV {a : ℝ} {y z : ℝ → R4}
    (hy : ∀ t, HasDerivAt y (DX H (P.x (a + t)) (y t)) t)
    (hz : ∀ t, HasDerivAt z (DX H (P.x (a + t)) (z t)) t) (t₀ : ℝ) (h0 : y t₀ = z t₀) :
    y = z := by
  set B : ℝ → R4 →L[ℝ] R4 := fun t => DX H (P.x (a + t))
  have hB : Continuous B := (DX_cont hH).comp ((xc P).comp (continuous_const.add continuous_id))
  have hp : ∀ t, B (t + P.T) = B t := fun t => by simp only [B, per_x]
  exact lode_uniq B hB P.T_pos hp y z hy hz t₀ h0

include hH in
lemma cocycle {a s : ℝ} {Ya Yb : ℝ → (R4 →L[ℝ] R4)} (ha : IsFl P a Ya) (hb : IsFl P (a + s) Yb)
    (t : ℝ) : (Yb t).comp (Ya s) = Ya (s + t) := by
  have h1 : ∀ t, HasDerivAt (fun t => (Yb t).comp (Ya s))
      ((DX H (P.x ((a + s) + t))).comp ((fun t => (Yb t).comp (Ya s)) t)) t := by
    intro t
    have := (hb.2 t).clm_comp (hasDerivAt_const t (Ya s))
    simpa [ContinuousLinearMap.comp_assoc] using this
  have h2 : ∀ t, HasDerivAt (fun t => Ya (s + t))
      ((DX H (P.x ((a + s) + t))).comp ((fun t => Ya (s + t)) t)) t := by
    intro t
    have := (ha.2 (s + t)).comp_const_add s t
    simpa [add_assoc] using this
  have := uniqFl hH P h1 h2 0 (by simp [hb.1])
  exact congrFun this t

lemma isFl_per {a : ℝ} {Y : ℝ → (R4 →L[ℝ] R4)} (h : IsFl P a Y) : IsFl P (a + P.T) Y := by
  refine ⟨h.1, fun t => ?_⟩
  have := h.2 t
  rwa [show a + P.T + t = a + t + P.T by ring, P.periodic]

include hH in
lemma fl_X {a : ℝ} {Y : ℝ → (R4 →L[ℝ] R4)} (h : IsFl P a Y) (s : ℝ) :
    Y s (hamVF (n := 1) H (P.x a)) = hamVF (n := 1) H (P.x (a + s)) := by
  have h1 : ∀ t, HasDerivAt (fun t => Y t (hamVF (n := 1) H (P.x a)))
      (DX H (P.x (a + t)) ((fun t => Y t (hamVF (n := 1) H (P.x a))) t)) t := by
    intro t
    have := (h.2 t).clm_apply (hasDerivAt_const t (hamVF (n := 1) H (P.x a)))
    simpa using this
  have h2 : ∀ t, HasDerivAt (fun t => hamVF (n := 1) H (P.x (a + t)))
      (DX H (P.x (a + t)) ((fun t => hamVF (n := 1) H (P.x (a + t))) t)) t := by
    intro t
    exact (X_hasFDeriv hH _).comp_hasDerivAt t (hxs P a t)
  have := uniqV hH P h1 h2 0 (by simp [h.1])
  exact congrFun this s

include hH in
/-- `dH(x) X_H(x) ≡ 0` differentiated, plus symmetry of `D²H`. -/
lemma d2H_X (y w : R4) :
    fderiv ℝ (fderiv ℝ H) y (hamVF (n := 1) H y) w + fderiv ℝ H y (DX H y w) = 0 := by
  have hH2 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.1.fderiv_right (m := ∞) (by simp)
  have hd2 : HasFDerivAt (fderiv ℝ H) (fderiv ℝ (fderiv ℝ H) y) y :=
    (hH2.differentiable (by simp) y).hasFDerivAt
  have hG : HasFDerivAt (fun y => fderiv ℝ H y (hamVF (n := 1) H y))
      ((fderiv ℝ H y).comp (DX H y) + (fderiv ℝ (fderiv ℝ H) y).flip (hamVF (n := 1) H y)) y :=
    hd2.clm_apply (X_hasFDeriv hH y)
  have h0 : (fun y => fderiv ℝ H y (hamVF (n := 1) H y)) = fun _ => (0:ℝ) := funext fun y => dHX H y
  rw [h0] at hG
  have := congrArg (fun L => L w) (hG.unique (hasFDerivAt_const 0 y))
  simp at this
  have hsym : fderiv ℝ (fderiv ℝ H) y (hamVF (n := 1) H y) w =
      fderiv ℝ (fderiv ℝ H) y w (hamVF (n := 1) H y) :=
    ((hH.1.contDiffAt (x := y)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)) _ _
  rw [hsym]; linarith

include hH in
lemma fl_dH {a : ℝ} {Y : ℝ → (R4 →L[ℝ] R4)} (h : IsFl P a Y) {v : R4}
    (hv : fderiv ℝ H (P.x a) v = 0) (s : ℝ) : fderiv ℝ H (P.x (a + s)) (Y s v) = 0 := by
  have hH2 : ContDiff ℝ ∞ (fderiv ℝ H) := hH.1.fderiv_right (m := ∞) (by simp)
  have hd : ∀ t, HasDerivAt (fun t => fderiv ℝ H (P.x (a + t)) (Y t v)) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t => fderiv ℝ H (P.x (a + t)))
        (fderiv ℝ (fderiv ℝ H) (P.x (a + t)) (hamVF (n := 1) H (P.x (a + t)))) t :=
      ((hH2.differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt t (hxs P a t)
    have h2 : HasDerivAt (fun t => Y t v) (DX H (P.x (a + t)) (Y t v)) t := by
      have := (h.2 t).clm_apply (hasDerivAt_const t v); simpa using this
    have h3 := d2H_X hH (P.x (a + t)) (Y t v)
    exact (h1.clm_apply h2).congr_deriv (by linarith)
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) s 0
  rw [hc]; simp [h.1, hv]

end NB


set_option linter.all false

open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff NNReal

namespace G70R
lemma sig_deriv {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (fun t => ∫ u in (0:ℝ)..t, g u) (g t) t :=
  (hg.integral_hasStrictDerivAt 0 t).hasDerivAt

lemma sig_per {g : ℝ → ℝ} (hg : Continuous g) {T : ℝ} (hp : ∀ t, g (t + T) = g t) (t : ℝ) :
    (∫ u in (0:ℝ)..(t + T), g u) = (∫ u in (0:ℝ)..t, g u) + ∫ u in (0:ℝ)..T, g u := by
  have hd : ∀ x, HasDerivAt (fun t => (∫ u in (0:ℝ)..(t + T), g u) - ∫ u in (0:ℝ)..t, g u) 0 x := by
    intro x
    have h1 := (sig_deriv hg (x + T)).comp x ((hasDerivAt_id x).add_const T)
    have h2 : HasDerivAt _ (0:ℝ) x := (h1.sub (sig_deriv hg x)).congr_deriv (by simp [hp])
    exact h2
  have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hc
  linarith

lemma sig_lb {g : ℝ → ℝ} (hg : Continuous g) {T : ℝ} (hT : 0 < T) (hp : ∀ t, g (t + T) = g t)
    (hpos : ∀ t, 0 < g t) : ∃ m > 0, ∀ t, m ≤ g t := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := T)).exists_isMinOn
    (Set.nonempty_Icc.2 hT.le) hg.continuousOn
  refine ⟨g x, hpos x, fun t => ?_⟩
  have hP : Function.Periodic g T := hp
  obtain ⟨y, hy, hyt⟩ := hP.exists_mem_Ico₀ hT t
  rw [hyt]; exact hmin ⟨hy.1, hy.2.le⟩

theorem reparam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {y : ℝ → E} {F : E → E} {c : E → ℝ} {T : ℝ} (hT : 0 < T)
    (hy : ∀ t, HasDerivAt y (F (y t)) t) (hper : ∀ t, y (t + T) = y t)
    (hc : Continuous (fun t => c (y t))) (hpos : ∀ t, 0 < c (y t)) :
    ∃ φ : ℝ → ℝ, (∀ s, HasDerivAt (fun s => y (φ s)) ((c (y (φ s)))⁻¹ • F (y (φ s))) s) ∧
      (∀ s, HasDerivAt φ (c (y (φ s)))⁻¹ s) ∧ φ 0 = 0 ∧ Function.Surjective φ ∧
      0 < (∫ u in (0:ℝ)..T, c (y u)) ∧
      ∀ s, φ (s + ∫ u in (0:ℝ)..T, c (y u)) = φ s + T := by
  set g := fun t => c (y t) with hgdef
  have hgp : ∀ t, g (t + T) = g t := fun t => by simp [hgdef, hper]
  set σ := fun t => ∫ u in (0:ℝ)..t, g u with hσ
  have hσd : ∀ t, HasDerivAt σ (g t) t := sig_deriv hc
  have hmono : StrictMono σ := strictMono_of_deriv_pos (fun x => by rw [(hσd x).deriv]; exact hpos x)
  have hcont : Continuous σ := continuous_iff_continuousAt.2 fun x => (hσd x).continuousAt
  obtain ⟨m, hm, hmg⟩ := sig_lb hc hT hgp hpos
  have hd2 : ∀ x, HasDerivAt (fun t => σ t - m * t) (g x - m) x := fun x => by
    convert (hσd x).sub ((hasDerivAt_id' x).const_mul m) using 1 <;> first | rfl | ring | (funext t; rfl)
  have hmon2 : Monotone (fun t => σ t - m * t) := by
    apply monotone_of_deriv_nonneg
    · exact fun x => (hd2 x).differentiableAt
    · intro x
      rw [(hd2 x).deriv]; linarith [hmg x]
  have h0 : σ 0 = 0 := by simp [hσ]
  have hup : ∀ t, 0 ≤ t → m * t ≤ σ t := fun t ht => by
    have := hmon2 ht; simp [h0] at this; linarith
  have hdn : ∀ t, t ≤ 0 → σ t ≤ m * t := fun t ht => by
    have := hmon2 ht; simp [h0] at this; linarith
  have hsurj : Function.Surjective σ := by
    apply hcont.surjective
    · refine tendsto_atTop_mono' atTop ?_ ((tendsto_id.const_mul_atTop hm))
      filter_upwards [eventually_ge_atTop 0] with t ht using hup t ht
    · refine tendsto_atBot_mono' atBot ?_ ((tendsto_id.const_mul_atBot hm))
      filter_upwards [eventually_le_atBot 0] with t ht using hdn t ht
  set e := StrictMono.orderIsoOfSurjective σ hmono hsurj
  have he : ∀ t, e t = σ t := fun t => rfl
  have hST : 0 < σ T := by rw [← h0]; exact hmono hT
  refine ⟨e.symm, ?_, ?_, ?_, e.symm.surjective, hST, ?_⟩
  · have hφd : ∀ s, HasDerivAt e.symm (g (e.symm s))⁻¹ s := by
      intro s
      apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
      · exact hσd _
      · exact (hpos _).ne'
      · exact Eventually.of_forall fun z => by rw [← he]; simp
    intro s
    have := (hy (e.symm s)).scomp s (hφd s)
    simpa [Function.comp_def, hgdef] using this
  · intro s
    apply HasDerivAt.of_local_left_inverse e.symm.continuous.continuousAt
    · exact hσd _
    · exact (hpos _).ne'
    · exact Eventually.of_forall fun z => by rw [← he]; simp
  · rw [OrderIso.symm_apply_eq, he, h0]
  · intro s
    rw [OrderIso.symm_apply_eq, he]
    show s + σ T = σ (e.symm s + T)
    rw [show σ (e.symm s + T) = σ (e.symm s) + σ T from sig_per hc hgp _, ← he]; simp
    exact (e.apply_symm_apply s).symm

end G70R

namespace G70R
end G70R

namespace NB

noncomputable def gL (H : R4 → ℝ) (y : R4) : ℝ := liouville (n := 1) y (hamVF (n := 1) H y)

variable {H : R4 → ℝ} (hH : HryniewiczCriterion.IsStrictlyStarShapedLevel H)

include hH in
lemma gL_smooth : ContDiff ℝ ∞ (gL H) :=
  (NBCore.contDiff_liouville (n := 1)).comp (contDiff_id.prodMk (X_smooth hH))

lemma reeb_eq : reeb (n := 1) H = fun y => (gL H y)⁻¹ • hamVF (n := 1) H y := rfl

include hH in
lemma reeb_cdo : ContDiffOn ℝ ∞ (reeb (n := 1) H) {y | 0 < gL H y} := by
  rw [reeb_eq]
  exact ((gL_smooth hH).contDiffOn.inv fun y hy => ne_of_gt hy).smul (X_smooth hH).contDiffOn

include hH in
lemma reeb_hasFDeriv (y : R4) (hy : 0 < gL H y) :
    HasFDerivAt (reeb (n := 1) H) ((gL H y)⁻¹ • DX H y +
      (fderiv ℝ (fun y => (gL H y)⁻¹) y).smulRight (hamVF (n := 1) H y)) y := by
  rw [reeb_eq]
  have hf : DifferentiableAt ℝ (fun y => (gL H y)⁻¹) y :=
    ((gL_smooth hH).differentiable (by simp) y).inv hy.ne'
  exact hf.hasFDerivAt.smul (X_hasFDeriv hH y)

include hH in
lemma gQ_pos (Q : ReebOrbit (n := 1) H) (τ : ℝ) : 0 < gL H (Q.x τ) :=
  (reeb_spec (n := 1) H hH (Q.x τ) (Q.mem τ)).1

include hH in
lemma gP_pos (P : HryniewiczCriterion.PeriodicOrbit H) (t : ℝ) : 0 < gL H (P.x t) :=
  (reeb_spec (n := 1) H hH (P.x t) (P.trajectory.2 t)).1

lemma Qc (Q : ReebOrbit (n := 1) H) : Continuous Q.x :=
  continuous_iff_continuousAt.2 fun t => (Q.hasDerivAt t).continuousAt

include hH in
lemma reparamQ (P : HryniewiczCriterion.PeriodicOrbit H) (Q : ReebOrbit (n := 1) H) (s0 : ℝ)
    (hs0 : P.x s0 = Q.x 0) (hT : Q.T = ∫ τ in (0:ℝ)..P.T, gL H (P.x τ)) :
    ∃ φ : ℝ → ℝ, (∀ τ, Q.x τ = P.x (s0 + φ τ)) ∧
      (∀ τ, HasDerivAt φ (gL H (P.x (s0 + φ τ)))⁻¹ τ) ∧ φ 0 = 0 ∧ φ Q.T = P.T := by
  have hgc : Continuous (gL H) := (gL_smooth hH).continuous
  obtain ⟨φ, hφ1, hφ2, hφ0, -, -, hper⟩ := G70R.reparam (y := fun s => P.x (s0 + s))
    (F := hamVF (n := 1) H) (c := gL H) P.T_pos (hxs P s0) (fun t => per_x P s0 t)
    (hgc.comp ((xc P).comp (continuous_const.add continuous_id))) (fun t => gP_pos hH P _)
  have hI : (∫ u in (0:ℝ)..P.T, gL H (P.x (s0 + u))) = Q.T := by
    rw [hT, intervalIntegral.integral_comp_add_left (fun x => gL H (P.x x)) s0, add_zero]
    have hpf : Function.Periodic (fun x => gL H (P.x x)) P.T := fun x => by
      simp only [P.periodic]
    have := hpf.intervalIntegral_add_eq s0 0
    rw [zero_add] at this
    exact this
  rw [hI] at hper
  set Q' : ℝ → R4 := fun τ => P.x (s0 + φ τ)
  have hQ' : ∀ τ, HasDerivAt Q' (reeb (n := 1) H (Q' τ)) τ := fun τ => hφ1 τ
  obtain ⟨δ, hδ, K, hK, hL, -, -⟩ := NBCore.setup (E := R4) (isOpen_lt continuous_const hgc)
    ((reeb_cdo hH).of_le (by simp)) Q.T_pos (Qc Q) Q.periodic (fun t => gQ_pos hH Q t)
  have hfwd : ∀ τ, 0 ≤ τ → Q' τ = Q.x τ := by
    intro τ hτ
    have := NBCore.traj_close (x := Q.x) (Q := Q') hL Q.hasDerivAt hQ' (a := 0) (b := τ) (ε := 0)
      (by simp [Q', hφ0, hs0]) (by simpa using hδ) τ ⟨hτ, le_rfl⟩
    simpa using this
  have hpQ : Function.Periodic Q.x Q.T := Q.periodic
  have hpQ' : Function.Periodic Q' Q.T := fun τ => by
    simp only [Q', hper]; exact per_x P s0 (φ τ)
  have hall : ∀ τ, Q.x τ = Q' τ := by
    intro τ
    obtain ⟨m, hm⟩ := exists_nat_gt (-τ / Q.T)
    have hm' : 0 ≤ τ + m * Q.T := by
      have := (div_lt_iff₀ Q.T_pos).1 hm; linarith
    rw [← hpQ.nat_mul m τ, ← hpQ'.nat_mul m τ, hfwd _ hm']
  refine ⟨φ, hall, fun τ => hφ2 τ, hφ0, ?_⟩
  have := hper 0
  rwa [zero_add, hφ0, zero_add] at this

include hH in
lemma phi_rel (P : HryniewiczCriterion.PeriodicOrbit H) (Q : ReebOrbit (n := 1) H) (s0 : ℝ)
    (φ : ℝ → ℝ) (hφQ : ∀ τ, Q.x τ = P.x (s0 + φ τ))
    (hφd : ∀ τ, HasDerivAt φ (gL H (P.x (s0 + φ τ)))⁻¹ τ) (hφ0 : φ 0 = 0)
    {Ys0 : ℝ → (R4 →L[ℝ] R4)} (hY : IsFl P s0 Ys0) {Φ : ℝ → (R4 →L[ℝ] R4)}
    (hΦ : IsLinReebFlow Q Φ) (v : R4) (τ : ℝ) :
    ∃ k : ℝ, Φ τ v = Ys0 (φ τ) v + k • hamVF (n := 1) H (Q.x τ) := by
  have hgc : Continuous (gL H) := (gL_smooth hH).continuous
  have hyU := gQ_pos hH Q
  have hUo : IsOpen {y : R4 | 0 < gL H y} := isOpen_lt continuous_const hgc
  set fD : R4 → R4 →L[ℝ] ℝ := fun y => fderiv ℝ (fun y => (gL H y)⁻¹) y with hfD
  have hfDc : ContinuousOn fD {y | 0 < gL H y} :=
    ((gL_smooth hH).contDiffOn.inv fun y hy => ne_of_gt hy).continuousOn_fderiv_of_isOpen hUo
      (by simp)
  have hW : ∀ τ, HasDerivAt (fun τ => Φ τ v) (fderiv ℝ (reeb (n := 1) H) (Q.x τ) (Φ τ v)) τ := by
    intro τ; have := (hΦ.2 τ).clm_apply (hasDerivAt_const τ v); simpa using this
  have hWc : Continuous (fun τ => Φ τ v) :=
    continuous_iff_continuousAt.2 fun t => (hW t).continuousAt
  have hcc : Continuous (fun τ => fD (Q.x τ) (Φ τ v)) :=
    (hfDc.comp_continuous (Qc Q) hyU).clm_apply hWc
  have hk : ∀ τ, HasDerivAt (fun τ => ∫ r in (0:ℝ)..τ, fD (Q.x r) (Φ r v)) (fD (Q.x τ) (Φ τ v)) τ :=
    fun τ => (hcc.integral_hasStrictDerivAt 0 τ).hasDerivAt
  have hw : ∀ τ, HasDerivAt (fun τ => Ys0 (φ τ) v)
      ((gL H (Q.x τ))⁻¹ • DX H (Q.x τ) (Ys0 (φ τ) v)) τ := by
    intro τ
    have h1 := (hY.2 (φ τ)).scomp τ (hφd τ)
    have h2 := h1.clm_apply (hasDerivAt_const τ v)
    simp only [Function.comp_def] at h2
    rw [hφQ τ]
    simpa using h2
  have hXy : ∀ τ, HasDerivAt (fun τ => hamVF (n := 1) H (Q.x τ))
      (DX H (Q.x τ) (reeb (n := 1) H (Q.x τ))) τ :=
    fun τ => (X_hasFDeriv hH _).comp_hasDerivAt τ (Q.hasDerivAt τ)
  set B : ℝ → R4 →L[ℝ] R4 := fun τ => (gL H (Q.x τ))⁻¹ • DX H (Q.x τ) with hB
  have hBc : Continuous B :=
    ((hgc.comp (Qc Q)).inv₀ fun t => (hyU t).ne').smul ((DX_cont hH).comp (Qc Q))
  have hBp : ∀ t, B (t + Q.T) = B t := fun t => by simp only [hB, Q.periodic]
  set u : ℝ → R4 := fun τ => Φ τ v - Ys0 (φ τ) v -
    (∫ r in (0:ℝ)..τ, fD (Q.x r) (Φ r v)) • hamVF (n := 1) H (Q.x τ) with hu
  have hud : ∀ τ, HasDerivAt u (B τ (u τ)) τ := by
    intro τ
    have := ((hW τ).sub (hw τ)).sub ((hk τ).smul (hXy τ))
    refine this.congr_deriv ?_
    rw [(reeb_hasFDeriv hH (Q.x τ) (hyU τ)).fderiv]
    simp only [hB, hu, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, reeb_eq]
    module
  have hz : ∀ τ, HasDerivAt (fun _ => (0 : R4)) (B τ ((fun _ => (0:R4)) τ)) τ := fun τ => by
    simpa using hasDerivAt_const τ (0 : R4)
  have hu0 : u 0 = 0 := by simp [hu, hΦ.1, hφ0, hY.1]
  have := congrFun (lode_uniq B hBc Q.T_pos hBp u (fun _ => 0) hud hz 0 hu0) τ
  refine ⟨∫ r in (0:ℝ)..τ, fD (Q.x r) (Φ r v), ?_⟩
  simp only [hu] at this
  rw [sub_sub, sub_eq_zero] at this
  exact this

end NB


set_option linter.all false

open Set Metric Filter Topology
open FiniteEnergyPlane
open scoped ContDiff NNReal

namespace NB

variable {H : R4 → ℝ}

lemma proj_lin (p u w : R4) (a b : ℝ) :
    HryniewiczCriterion.reebProjection H p (a • u + b • w) =
      a • HryniewiczCriterion.reebProjection H p u + b • HryniewiczCriterion.reebProjection H p w := by
  funext k
  simp only [HryniewiczCriterion.reebProjection, HryniewiczCriterion.liouvilleForm, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma proj_zero (p : R4) : HryniewiczCriterion.reebProjection H p 0 = 0 := by
  have := proj_lin (H := H) p 0 0 0 0
  simpa using this

lemma coords_lin (p u w : R4) (a b : ℝ) :
    HryniewiczCriterion.xiCoords H p (a • u + b • w) =
      a • HryniewiczCriterion.xiCoords H p u + b • HryniewiczCriterion.xiCoords H p w := by
  funext i
  fin_cases i
  · simp [HryniewiczCriterion.xiCoords, hom_lin_l]
  · simp [HryniewiczCriterion.xiCoords, hom_lin]

lemma coords0 (p v : R4) : HryniewiczCriterion.xiCoords H p v 0 =
    HryniewiczCriterion.omega0 v (HryniewiczCriterion.xiFrame2 H p) := by
  simp [HryniewiczCriterion.xiCoords]

lemma coords1 (p v : R4) : HryniewiczCriterion.xiCoords H p v 1 =
    HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H p) v := by
  simp [HryniewiczCriterion.xiCoords]

lemma isLin_iff (P : HryniewiczCriterion.PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4)) :
    HryniewiczCriterion.IsLinearizedFlow H P.x Y ↔ IsFl P 0 Y := by
  have e : HryniewiczCriterion.hamiltonianVectorField H = hamVF (n := 1) H :=
    funext fun x => (vf H x).symm
  simp only [HryniewiczCriterion.IsLinearizedFlow, IsFl, DX, e, zero_add]

lemma Px_T (P : HryniewiczCriterion.PeriodicOrbit H) : P.x P.T = P.x 0 := by
  have := P.periodic 0; rwa [zero_add] at this

lemma mulVec_eq (P : HryniewiczCriterion.PeriodicOrbit H) (Y : ℝ → (R4 →L[ℝ] R4))
    (c : Fin 2 → ℝ) :
    (HryniewiczCriterion.linearizedXiPath H P Y 1).mulVec c =
      HryniewiczCriterion.xiCoords H (P.x 0) (HryniewiczCriterion.reebProjection H (P.x 0)
        (Y P.T (c 0 • HryniewiczCriterion.xiFrame1 H (P.x 0) +
          c 1 • HryniewiczCriterion.xiFrame2 H (P.x 0)))) := by
  rw [map_add, map_smul, map_smul, proj_lin, coords_lin]
  funext i
  simp only [HryniewiczCriterion.linearizedXiPath, mul_one, Px_T, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

/-- fixed points of `DC` and `CD` -/
lemma fix_transfer {ξ1 ξ2 : R4 → Prop} (A B C D : R4 → R4)
    (hC : ∀ w, ξ1 w → ξ2 (C w)) (hD : ∀ v, ξ2 v → ξ1 (D v)) (hC0 : C 0 = 0)
    (hDC : ∀ w, ξ1 w → D (C w) = A w) (hCD : ∀ v, ξ2 v → C (D v) = B v)
    (hA : ∀ w, ξ1 w → A w = w → w = 0) : ∀ v, ξ2 v → B v = v → v = 0 := by
  intro v hv hBv
  have h1 : D v = 0 := by
    apply hA _ (hD v hv)
    rw [← hDC _ (hD v hv), hCD v hv, hBv]
  rw [← hBv, ← hCD v hv, h1, hC0]

theorem main (H : R4 → ℝ) (hH : HryniewiczCriterion.IsStrictlyStarShapedLevel H)
    (P : HryniewiczCriterion.PeriodicOrbit H) (Q : ReebOrbit (n := 1) H)
    (hr : Set.range Q.x = Set.range P.x) (hT : Q.T = ∫ τ in (0:ℝ)..P.T, gL H (P.x τ)) :
    Q.IsNondegenerate ↔ ∀ Y : ℝ → (R4 →L[ℝ] R4), HryniewiczCriterion.IsLinearizedFlow H P.x Y →
      ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H P Y 1).mulVec v = v → v = 0 := by
  have hq : Q.x 0 ∈ Set.range P.x := hr ▸ Set.mem_range_self 0
  obtain ⟨s0, hs0⟩ := hq
  obtain ⟨φ, hφQ, hφd, hφ0, hφT⟩ := reparamQ hH P Q s0 hs0 hT
  obtain ⟨Y0, hY0⟩ := exFl hH P 0
  obtain ⟨Ys0, hYs0⟩ := exFl hH P s0
  have hpP : ∀ t, 0 < fderiv ℝ H (P.x t) (P.x t) := fun t => hH.2.2 _ (P.trajectory.2 t)
  have hXe : ∀ y, hamVF (n := 1) H y = HryniewiczCriterion.hamiltonianVectorField H y := vf H
  have hQT : Q.x Q.T = (Q.x 0) := by have := Q.periodic 0; rwa [zero_add] at this
  have hpx0 : 0 < fderiv ℝ H (P.x 0) (P.x 0) := hpP 0
  have hpy0 : 0 < fderiv ℝ H (Q.x 0) (Q.x 0) := by rw [← hs0]; exact hpP s0
  -- Step 1: nondegeneracy of `Q` ↔ `B = HryniewiczCriterion.reebProjection H (Q.x 0) ∘ Ys0(T)` has no fixed vector on `ξ_{(Q.x 0)}`
  obtain ⟨Φ, hΦ⟩ := (linReebFlow_spec (n := 1) H hH Q).1.exists
  have hΦξ := ((linReebFlow_spec (n := 1) H hH Q).2 Φ hΦ).1
  have hrel : ∀ Φ, IsLinReebFlow Q Φ → ∀ v, ∃ k : ℝ,
      Φ Q.T v = Ys0 P.T v + k • HryniewiczCriterion.hamiltonianVectorField H (Q.x 0) := by
    intro Φ hΦ v
    obtain ⟨k, hk⟩ := phi_rel hH P Q s0 φ hφQ hφd hφ0 hYs0 hΦ v Q.T
    rw [hφT, hQT, hXe] at hk
    exact ⟨k, hk⟩
  have step1 : Q.IsNondegenerate ↔ ∀ v, IsInXi (n := 1) H (Q.x 0) v → HryniewiczCriterion.reebProjection H (Q.x 0) (Ys0 P.T v) = v → v = 0 := by
    constructor
    · intro hN v hv hBv
      obtain ⟨k, hk⟩ := hrel Φ hΦ v
      have hxi : IsInXi (n := 1) H (Q.x 0) (Φ Q.T v) := by
        have := (hΦξ Q.T v v hv hv).1; rwa [hQT] at this
      have : Φ Q.T v = v := by
        have e1 : HryniewiczCriterion.reebProjection H (Q.x 0) (Φ Q.T v) = Φ Q.T v := proj_id hpy0 (by rw [← liou_eq]; exact hxi.1)
        rw [← e1, hk, proj_addX hpy0, hBv]
      exact hN Φ hΦ v hv this
    · intro hB Φ' hΦ' v hv hfix
      obtain ⟨k, hk⟩ := hrel Φ' hΦ' v
      apply hB v hv
      have : Ys0 P.T v = v + (-k) • HryniewiczCriterion.hamiltonianVectorField H (Q.x 0) := by
        have h := hk.symm.trans hfix
        linear_combination (norm := module) h
      rw [this, proj_addX hpy0]
      exact proj_id hpy0 (by rw [← liou_eq]; exact hv.1)
  -- Step 2: transfer to `A = HryniewiczCriterion.reebProjection H (P.x 0) ∘ Y0(T)` on `ξ_{(P.x 0)}`
  have hY0s : IsFl P (0 + s0) Ys0 := by rwa [zero_add]
  have hY0T : IsFl P (s0 + (P.T - s0)) Y0 := by
    have := isFl_per P hY0; rwa [show s0 + (P.T - s0) = 0 + P.T by ring]
  have hpt : P.x (s0 + (P.T - s0)) = (P.x 0) := by rw [show s0 + (P.T - s0) = P.T by ring, Px_T]
  have hpt' : P.x (0 + s0) = (Q.x 0) := by rw [zero_add, hs0]
  set C : R4 → R4 := fun w => HryniewiczCriterion.reebProjection H (Q.x 0) (Y0 s0 w)
  set D : R4 → R4 := fun v => HryniewiczCriterion.reebProjection H (P.x 0) (Ys0 (P.T - s0) v)
  have hπ1 : ∀ u, HryniewiczCriterion.reebProjection H (Q.x 0) u = u - (HryniewiczCriterion.liouvilleForm (Q.x 0) u /
      HryniewiczCriterion.liouvilleForm (Q.x 0) (HryniewiczCriterion.hamiltonianVectorField H (Q.x 0))) •
      HryniewiczCriterion.hamiltonianVectorField H (Q.x 0) := fun u => rfl
  have hπ0 : ∀ u, HryniewiczCriterion.reebProjection H (P.x 0) u = u - (HryniewiczCriterion.liouvilleForm (P.x 0) u /
      HryniewiczCriterion.liouvilleForm (P.x 0) (HryniewiczCriterion.hamiltonianVectorField H (P.x 0))) •
      HryniewiczCriterion.hamiltonianVectorField H (P.x 0) := fun u => rfl
  have hXs : Ys0 (P.T - s0) (HryniewiczCriterion.hamiltonianVectorField H (Q.x 0)) =
      HryniewiczCriterion.hamiltonianVectorField H (P.x 0) := by
    rw [← hXe, ← hXe, ← hs0, fl_X hH P hYs0, hpt]
  have hX0 : Y0 s0 (HryniewiczCriterion.hamiltonianVectorField H (P.x 0)) =
      HryniewiczCriterion.hamiltonianVectorField H (Q.x 0) := by
    rw [← hXe, ← hXe, fl_X hH P hY0, hpt']
  have hDC : ∀ w, D (C w) = HryniewiczCriterion.reebProjection H (P.x 0) (Y0 P.T w) := by
    intro w
    simp only [C, D]
    rw [hπ1, map_sub, map_smul, hXs, sub_eq_add_neg, ← neg_smul, proj_addX hpx0]
    have := cocycle hH P hY0 hY0s (P.T - s0)
    rw [show s0 + (P.T - s0) = P.T by ring] at this
    rw [← this]; rfl
  have hCD : ∀ v, C (D v) = HryniewiczCriterion.reebProjection H (Q.x 0) (Ys0 P.T v) := by
    intro v
    simp only [C, D]
    rw [hπ0, map_sub, map_smul, hX0, sub_eq_add_neg, ← neg_smul, proj_addX hpy0]
    have := cocycle hH P hYs0 hY0T s0
    rw [show P.T - s0 + s0 = P.T by ring] at this
    rw [← this]; rfl
  have hCξ : ∀ w, IsInXi (n := 1) H (P.x 0) w → IsInXi (n := 1) H (Q.x 0) (C w) := by
    intro w hw
    apply proj_xi hpy0
    have := fl_dH hH P hY0 hw.2 s0
    rwa [hpt'] at this
  have hDξ : ∀ v, IsInXi (n := 1) H (Q.x 0) v → IsInXi (n := 1) H (P.x 0) (D v) := by
    intro v hv
    apply proj_xi hpx0
    have := fl_dH hH P hYs0 (v := v) (by rw [hs0]; exact hv.2) (P.T - s0)
    rwa [hpt] at this
  have step2 : (∀ v, IsInXi (n := 1) H (Q.x 0) v → HryniewiczCriterion.reebProjection H (Q.x 0) (Ys0 P.T v) = v → v = 0) ↔
      (∀ w, IsInXi (n := 1) H (P.x 0) w → HryniewiczCriterion.reebProjection H (P.x 0) (Y0 P.T w) = w → w = 0) := by
    constructor
    · exact fix_transfer (fun v => HryniewiczCriterion.reebProjection H (Q.x 0) (Ys0 P.T v)) (fun w => HryniewiczCriterion.reebProjection H (P.x 0) (Y0 P.T w)) D C hDξ hCξ
        (by simp [D, proj_zero]) (fun v _ => hCD v) (fun w _ => hDC w)
    · exact fix_transfer (fun w => HryniewiczCriterion.reebProjection H (P.x 0) (Y0 P.T w)) (fun v => HryniewiczCriterion.reebProjection H (Q.x 0) (Ys0 P.T v)) C D hCξ hDξ
        (by simp [C, proj_zero]) (fun w _ => hDC w) (fun v _ => hCD v)
  -- Step 3: frame coordinates
  have hAξ : ∀ w, IsInXi (n := 1) H (P.x 0) w → IsInXi (n := 1) H (P.x 0) (HryniewiczCriterion.reebProjection H (P.x 0) (Y0 P.T w)) := by
    intro w hw
    apply proj_xi hpx0
    have := fl_dH hH P hY0 hw.2 P.T
    rwa [zero_add, Px_T] at this
  have hspan : ∀ u, IsInXi (n := 1) H (P.x 0) u →
      u = HryniewiczCriterion.xiCoords H (P.x 0) u 0 • HryniewiczCriterion.xiFrame1 H (P.x 0) + HryniewiczCriterion.xiCoords H (P.x 0) u 1 • HryniewiczCriterion.xiFrame2 H (P.x 0) := by
    intro u hu
    rw [coords0, coords1]; exact span_xi hpx0 hu
  have step3 : (∀ w, IsInXi (n := 1) H (P.x 0) w → HryniewiczCriterion.reebProjection H (P.x 0) (Y0 P.T w) = w → w = 0) ↔
      ∀ Y : ℝ → (R4 →L[ℝ] R4), HryniewiczCriterion.IsLinearizedFlow H P.x Y →
        ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H P Y 1).mulVec v = v → v = 0 := by
    constructor
    · intro hA Y hY c hc
      have hYe : Y = Y0 := uniqFl hH P ((isLin_iff P Y).1 hY).2 hY0.2 0
        (by rw [((isLin_iff P Y).1 hY).1, hY0.1])
      subst hYe
      rw [mulVec_eq] at hc
      have hw : IsInXi (n := 1) H (P.x 0) (c 0 • HryniewiczCriterion.xiFrame1 H (P.x 0) + c 1 • HryniewiczCriterion.xiFrame2 H (P.x 0)) := xi_comb hpx0 c
      have hu := hAξ _ hw
      have hfix : HryniewiczCriterion.reebProjection H (P.x 0) (Y (P.T) (c 0 • HryniewiczCriterion.xiFrame1 H (P.x 0) + c 1 • HryniewiczCriterion.xiFrame2 H (P.x 0))) = c 0 • HryniewiczCriterion.xiFrame1 H (P.x 0) + c 1 • HryniewiczCriterion.xiFrame2 H (P.x 0) := by
        conv_lhs => rw [hspan _ hu]
        rw [hc]
      have := hA _ hw hfix
      rw [← coords_frame hpx0 c, this]
      funext i; fin_cases i <;> simp [HryniewiczCriterion.xiCoords, hc_om]
    · intro hR w hw hfix
      have hc := hR Y0 ((isLin_iff P Y0).2 hY0) (HryniewiczCriterion.xiCoords H (P.x 0) w) (by
        rw [mulVec_eq, ← hspan w hw, hfix])
      rw [hspan w hw, hc]; simp
  exact step1.trans (step2.trans step3)

end NB

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      (Q.IsNondegenerate ↔
        ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
          HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
          ∀ v : Fin 2 → ℝ, (HryniewiczCriterion.linearizedXiPath H₀ P Y 1).mulVec v = v →
            v = 0) := by
  intro toV H P Q hr hT
  refine NB.main H₀ hH₀ P Q hr ?_
  rw [hT]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  change liouville (n := 1) (P.x τ) (deriv P.x τ) = _
  rw [(NB.hx P τ).deriv]
  rfl
