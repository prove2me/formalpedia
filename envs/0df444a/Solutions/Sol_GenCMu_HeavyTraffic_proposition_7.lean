-- Prove2me | solution 1 for GenCMu.HeavyTraffic.proposition_7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T06:45:44.321484+00:00
-- url     : https://prove2.me/submissions/7bc2a3e8-782b-4f14-8fd2-732296058584
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits
import Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_T
import Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_W
import Theorems.Thm_GenCMu_HeavyTraffic_proposition_2_equiv
import Theorems.Thm_GenCMu_HeavyTraffic_proposition_5
import Theorems.Thm_GenCMu_HeavyTraffic_sec_4_1_unique_continuous
import Theorems.Thm_GenCMu_HeavyTraffic_eq_46_50_kuhn_tucker

namespace GenCMuP7Aux

open Filter Topology Finset GenCMu.HeavyTraffic

lemma genInv_mem (f : ℝ → ℝ) (a : ℝ) : genInv f a ∈ Set.Icc (0 : ℝ) 1 := by
  unfold genInv
  constructor
  · exact Real.sInf_nonneg (fun s hs => hs.1.1)
  · rcases Set.eq_empty_or_nonempty {s ∈ Set.Icc (0 : ℝ) 1 | a ≤ f s} with h | ⟨s, hs⟩
    · rw [h, Real.sInf_empty]; norm_num
    · exact le_trans (csInf_le ⟨0, fun r hr => hr.1.1⟩ hs) hs.1.2

/-- running supremum bounded -/
lemma bdd_run (x : ℝ → ℝ) (B : ℝ) (hB : ∀ s ∈ Set.Icc (0 : ℝ) 1, |x s| ≤ B) (t : ℝ)
    (ht : t ≤ 1) : BddAbove (Set.range fun s : Set.Icc (0 : ℝ) t => -x s) := by
  refine ⟨B, ?_⟩
  rintro _ ⟨s, rfl⟩
  have := hB s ⟨s.2.1, le_trans s.2.2 ht⟩
  have := neg_abs_le (x s)
  simp only
  linarith [abs_le.mp ‹|x s| ≤ B›]

lemma reflect_nonneg (x : ℝ → ℝ) (hx : ContinuousOn x (Set.Icc 0 1)) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ reflect x t := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  have hB' : ∀ s ∈ Set.Icc (0 : ℝ) 1, |x s| ≤ B := fun s hs => by
    simpa [Real.norm_eq_abs] using hB s hs
  unfold reflect
  have h1 : -x t ≤ ⨆ s : Set.Icc (0 : ℝ) t, -x s :=
    le_ciSup_of_le (bdd_run x B hB' t ht.2) ⟨t, ht.1, le_rfl⟩ le_rfl
  have h2 := le_max_right 0 (⨆ s : Set.Icc (0 : ℝ) t, -x s)
  linarith

lemma reflect_cont (x : ℝ → ℝ) (hx : ContinuousOn x (Set.Icc 0 1)) :
    ContinuousOn (reflect x) (Set.Icc 0 1) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hx
  have hB' : ∀ s ∈ Set.Icc (0 : ℝ) 1, |x s| ≤ B := fun s hs => by
    simpa [Real.norm_eq_abs] using hB s hs
  have hU : UniformContinuousOn x (Set.Icc 0 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hx
  set m : ℝ → ℝ := fun t => ⨆ s : Set.Icc (0 : ℝ) t, -x s with hm
  -- key estimate
  have key : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      t ≤ t' → t' - t < δ → m t ≤ m t' ∧ m t' ≤ m t + ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hU ε hε
    refine ⟨δ, hδ, fun t ht t' ht' htt' hd => ⟨?_, ?_⟩⟩
    · have : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht.1⟩⟩
      exact ciSup_le fun s => le_ciSup_of_le (bdd_run x B hB' t' ht'.2)
        ⟨s, s.2.1, le_trans s.2.2 htt'⟩ le_rfl
    · have : Nonempty (Set.Icc (0 : ℝ) t') := ⟨⟨0, le_rfl, ht'.1⟩⟩
      refine ciSup_le fun s => ?_
      by_cases hs : (s : ℝ) ≤ t
      · have : -x s ≤ m t := le_ciSup_of_le (bdd_run x B hB' t ht.2)
          ⟨s, s.2.1, hs⟩ le_rfl
        linarith
      · push Not at hs
        have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨s.2.1, le_trans s.2.2 ht'.2⟩
        have hd2 : dist (s : ℝ) t < δ := by
          rw [Real.dist_eq, abs_of_pos (by linarith)]
          linarith [s.2.2]
        have h3 := hδ' s hsI t ht hd2
        rw [Real.dist_eq] at h3
        have h4 : -x t ≤ m t := le_ciSup_of_le (bdd_run x B hB' t ht.2)
          ⟨t, ht.1, le_rfl⟩ le_rfl
        have := (abs_lt.mp h3).1
        linarith
  have hmc : ContinuousOn m (Set.Icc 0 1) := by
    rw [Metric.continuousOn_iff]
    intro b hb ε hε
    obtain ⟨δ, hδ, hk⟩ := key (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun a ha hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    rcases le_total a b with h | h
    · have := hk a ha b hb h (by rw [abs_lt] at hab; linarith)
      rw [abs_lt]; constructor <;> linarith [this.1, this.2]
    · have := hk b hb a ha h (by rw [abs_lt] at hab; linarith)
      rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have : reflect x = fun t => x t + max 0 (m t) := by
    funext t; rfl
  rw [this]
  exact hx.add (ContinuousOn.sup continuousOn_const hmc)

lemma key_unif {d : ℕ} (ι : Fin d → ℝ → (Fin d → ℝ) → ℝ) (y : ℝ → ℝ) (G : ℝ → Fin d → ℝ)
    (hι : ∀ k, ContinuousOn (fun p : ℝ × (Fin d → ℝ) => ι k p.1 p.2)
      (Set.Icc 0 1 ×ˢ {x | ∀ k, 0 ≤ x k}))
    (hy : ContinuousOn y (Set.Icc 0 1)) (hG : ContinuousOn G (Set.Icc 0 1))
    (huniq : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin d → ℝ, (∀ k, 0 ≤ x k) → ∑ k, x k = y t →
      (∀ k l, ι k t x = ι l t x) → x = G t) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin d → ℝ, (∀ k, 0 ≤ x k) →
      |∑ k, x k - y t| ≤ δ → (∀ k l, |ι k t x - ι l t x| ≤ δ) → dist x (G t) < ε := by
  intro ε hε
  obtain ⟨Y, hY⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hY' : ∀ t ∈ Set.Icc (0 : ℝ) 1, y t ≤ Y := fun t ht => by
    have := hY t ht; rw [Real.norm_eq_abs] at this; exact (abs_le.mp this).2
  set Bx : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 (Y + 1)) with hBx
  set S : Set (ℝ × (Fin d → ℝ)) := Set.Icc 0 1 ×ˢ Bx with hS
  have hSc : IsCompact S := isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hSsub : S ⊆ Set.Icc 0 1 ×ˢ {x | ∀ k, 0 ≤ x k} := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨ht, fun k => (hx k (Set.mem_univ k)).1⟩
  have hfst : Set.MapsTo Prod.fst S (Set.Icc 0 1) := fun p hp => hp.1
  have hΦ : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => dist p.2 (G p.1)) S :=
    continuous_dist.comp_continuousOn (continuous_snd.continuousOn.prodMk (hG.comp continuous_fst.continuousOn hfst))
  set Ψ : ℝ × (Fin d → ℝ) → ℝ := fun p => |∑ k, p.2 k - y p.1| +
      ∑ k, ∑ l, |ι k p.1 p.2 - ι l p.1 p.2| with hΨ
  have hΨc : ContinuousOn Ψ S := by
    refine ContinuousOn.add ?_ ?_
    · refine ContinuousOn.abs (ContinuousOn.sub ?_ (hy.comp continuous_fst.continuousOn hfst))
      exact continuous_finsetSum _ (fun k _ => (continuous_apply k).comp continuous_snd)
        |>.continuousOn
    · refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun l _ => ?_
      exact (((hι k).mono hSsub).sub ((hι l).mono hSsub)).abs
  have hΨnn : ∀ p, 0 ≤ Ψ p := fun p => add_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
  set C : Set (ℝ × (Fin d → ℝ)) := S ∩ (fun p : ℝ × (Fin d → ℝ) => dist p.2 (G p.1)) ⁻¹' Set.Ici ε
  have hCc : IsCompact C := by
    refine hSc.of_isClosed_subset ?_ Set.inter_subset_left
    exact hΦ.preimage_isClosed_of_isClosed hSc.isClosed isClosed_Ici
  -- membership in S
  have hmemS : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin d → ℝ, (∀ k, 0 ≤ x k) →
      |∑ k, x k - y t| ≤ 1 → (t, x) ∈ S := by
    intro t ht x hx h1
    refine ⟨ht, fun k _ => ⟨hx k, ?_⟩⟩
    have := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ k)
    have := (abs_le.mp h1).2
    linarith [hY' t ht]
  rcases Set.eq_empty_or_nonempty C with hC | hC
  · refine ⟨1, one_pos, fun t ht x hx h1 _ => ?_⟩
    have hm := hmemS t ht x hx h1
    by_contra hcon
    push Not at hcon
    have : (t, x) ∈ C := ⟨hm, hcon⟩
    rw [hC] at this; exact this
  · obtain ⟨p0, hp0, hmin⟩ := hCc.exists_isMinOn hC (hΨc.mono Set.inter_subset_left)
    have hpos : 0 < Ψ p0 := by
      rcases (hΨnn p0).lt_or_eq with h | h
      · exact h
      exfalso
      have h0 : Ψ p0 = 0 := h.symm
      have hA := hΨnn p0
      simp only [hΨ] at h0
      have hs1 : |∑ k, p0.2 k - y p0.1| = 0 := by
        have := Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) =>
          Finset.sum_nonneg (fun l (_ : l ∈ (Finset.univ : Finset (Fin d))) =>
            abs_nonneg (ι k p0.1 p0.2 - ι l p0.1 p0.2)))
        linarith [abs_nonneg (∑ k, p0.2 k - y p0.1)]
      have hs2 : ∑ k, ∑ l, |ι k p0.1 p0.2 - ι l p0.1 p0.2| = 0 := by
        rw [hs1] at h0; linarith
      have hsum : ∑ k, p0.2 k = y p0.1 := by
        have := abs_eq_zero.mp hs1; linarith
      have heq : ∀ k l, ι k p0.1 p0.2 = ι l p0.1 p0.2 := by
        intro k l
        have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Finset.sum_nonneg
          fun l _ => abs_nonneg (ι k p0.1 p0.2 - ι l p0.1 p0.2))).mp hs2 k (Finset.mem_univ k)
        have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ =>
          abs_nonneg (ι k p0.1 p0.2 - ι l p0.1 p0.2))).mp h3 l (Finset.mem_univ l)
        have := abs_eq_zero.mp h4; linarith
      have hnn : ∀ k, 0 ≤ p0.2 k := fun k => (hp0.1.2 k (Set.mem_univ k)).1
      have := huniq p0.1 hp0.1.1 p0.2 hnn hsum heq
      have h5 : ε ≤ dist p0.2 (G p0.1) := hp0.2
      rw [this, dist_self] at h5
      linarith
    set δ := min 1 (Ψ p0 / (2 * (1 + (d : ℝ) * d))) with hδ
    have hdd : (0 : ℝ) < 1 + (d : ℝ) * d := by positivity
    refine ⟨δ, lt_min one_pos (by positivity), fun t ht x hx h1 h2 => ?_⟩
    have hm := hmemS t ht x hx (le_trans h1 (min_le_left _ _))
    by_contra hcon
    push Not at hcon
    have hCm : (t, x) ∈ C := ⟨hm, hcon⟩
    have hle := hmin hCm
    simp only [Set.mem_ofPred_eq] at hle
    have hb : Ψ (t, x) ≤ (1 + (d : ℝ) * d) * δ := by
      simp only [hΨ]
      have : ∑ k, ∑ l, |ι k t x - ι l t x| ≤ ∑ _k : Fin d, ∑ _l : Fin d, δ :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => h2 k l
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      nlinarith
    have hδle : δ ≤ Ψ p0 / (2 * (1 + (d : ℝ) * d)) := min_le_right _ _
    have : (1 + (d : ℝ) * d) * δ ≤ Ψ p0 / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      have := mul_le_mul_of_nonneg_left hδle hdd.le
      rw [mul_div_assoc'] at this
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith
    linarith

end GenCMuP7Aux

open Filter Topology Finset GenCMu.HeavyTraffic GenCMuP7Aux

theorem solution {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (Cs : Fin d → ℝ → ℝ) (h2 : CostConvergence H Cs)
    (h3 : CostRegularity M Cs) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsFeasible (T n))
    (hpost : PostHorizonRegular H M T)
    (h51 : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ k l : Fin d,
      |M.muR k t * mc Cs k (H.Wt T n t k / M.rho k t)
        - M.muR l t * mc Cs l (H.Wt T n t l / M.rho l t)| ≤ ε) :
    TendstoUniformlyOn (H.Jt T) (Jstar M Cs) atTop (Set.Icc 0 1) ∧
    ∀ τs : ℝ → Fin d → ℝ,
      (∀ t ∈ Set.Icc (0 : ℝ) 1, IsMin43 (fun k => M.lam k t) (fun k => M.rho k t) Cs (Wstar M t)
        (fun k => M.rho k t * τs t k)) →
      TendstoUniformlyOn (H.taut T) τs atTop (Set.Icc 0 1) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hd
  · subst hd0
    constructor
    · rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards with n t ht
      have e1 : H.Jt T n t = 0 := by simp [HTSeq.Jt, System.cost]
      have e2 : Jstar M Cs t = 0 := by
        unfold Jstar
        have hv : ∀ s, val43 (fun k => M.lam k s) (fun k => M.rho k s) Cs (Wstar M s) = 0 := by
          intro s
          unfold val43
          set A := {z | ∃ x : Fin 0 → ℝ, (∀ k, 0 ≤ x k) ∧ ∑ k, x k = Wstar M s ∧
            z = obj43 (fun k => M.lam k s) (fun k => M.rho k s) Cs x}
          have hsub : A ⊆ {0} := by
            rintro z ⟨x, -, -, rfl⟩; simp [obj43]
          rcases Set.eq_empty_or_nonempty A with h | h
          · rw [h, Real.sInf_empty]
          · rw [h.subset_singleton_iff.mp hsub, csInf_singleton]
        simp [hv]
      rw [e1, e2, dist_self]; exact hε
    · intro τs _
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards with n t ht
      rw [dist_eq_zero.mpr (Subsingleton.elim _ _)]; exact hε
  set K := Set.Icc (0 : ℝ) 1 with hK
  have hlamc : ∀ k, ContinuousOn (fun t => M.lam k t) K := fun k =>
    (h1.Abs_C1 k).continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hmuc : ∀ k, ContinuousOn (fun s => M.mu k s) (Set.Icc 0 2) := fun k =>
    (h1.Sbs_C1 k).continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) le_rfl
  have hR := proposition_2_T H M h1 T hT
  have hRc : ContinuousOn (fun t k => M.Rstar k t) K := by
    refine hR.continuousOn (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => ?_))
    refine continuousOn_pi.mpr fun k => ?_
    refine ContinuousOn.div_const ?_ _
    refine ((hT n).cont k).comp (continuousOn_const.mul continuousOn_id) ?_
    intro t ht
    exact mul_nonneg (Nat.cast_nonneg n) ht.1
  have hRkc : ∀ k, ContinuousOn (fun t => M.Rstar k t) K := fun k =>
    (continuous_apply k).comp_continuousOn hRc
  have hRmem2 : ∀ k t, M.Rstar k t ∈ Set.Icc (0 : ℝ) 2 := fun k t => by
    have := genInv_mem (fun s => M.Sbs s k) (M.Abs t k)
    exact ⟨this.1, le_trans this.2 (by norm_num)⟩
  have hmuRc : ∀ k, ContinuousOn (fun t => M.muR k t) K := fun k =>
    (hmuc k).comp (hRkc k) (fun t _ => hRmem2 k t)
  have hmuRpos : ∀ k t, 0 < M.muR k t := fun k t => h1.mu_pos k _ (hRmem2 k t)
  have hlampos : ∀ k, ∀ t ∈ K, 0 < M.lam k t := h1.lam_pos
  have hrhoc : ∀ k, ContinuousOn (fun t => M.rho k t) K := fun k =>
    (hlamc k).div (hmuRc k) (fun t _ => ne_of_gt (hmuRpos k t))
  have hrhopos : ∀ k, ∀ t ∈ K, 0 < M.rho k t := fun k t ht =>
    div_pos (hlampos k t ht) (hmuRpos k t)
  have hLc : ContinuousOn (fun t => ∑ k, M.Lstar k t + M.cs t) K := by
    refine ContinuousOn.add ?_ h1.cs_cont
    refine continuousOn_finsetSum _ fun k _ => ?_
    unfold Limits.Lstar
    refine ContinuousOn.div (ContinuousOn.sub ?_ ?_) (hmuRc k) (fun t _ => ne_of_gt (hmuRpos k t))
    · exact (continuous_apply k).comp_continuousOn h1.Ats_cont
    · exact (continuous_apply k).comp_continuousOn
        (h1.Sts_cont.comp (hRkc k) (fun t _ => hRmem2 k t))
  have hWc : ContinuousOn (Wstar M) K := reflect_cont _ hLc
  have hWnn : ∀ t ∈ K, 0 ≤ Wstar M t := reflect_nonneg _ hLc
  have hCsc : ∀ k, ContinuousOn (Cs k) (Set.Ici 0) := fun k => (h3.smooth k).continuousOn
  have hmcc : ∀ k, ContinuousOn (mc Cs k) (Set.Ici 0) := fun k =>
    (h3.smooth k).continuousOn_derivWithin (uniqueDiffOn_Ici 0) le_rfl
  obtain ⟨G, hGc, hG⟩ := sec_4_1_unique_continuous hd (fun t k => M.lam k t)
    (fun t k => M.rho k t) Cs (continuousOn_pi.mpr hlamc) (continuousOn_pi.mpr hrhoc)
    (fun t ht k => hlampos k t ht) (fun t ht k => hrhopos k t ht) h3.strict hCsc h2.mono
    (Wstar M) hWc hWnn
  set ι : Fin d → ℝ → (Fin d → ℝ) → ℝ := fun k t x => M.muR k t * mc Cs k (x k / M.rho k t)
    with hι_def
  have hι : ∀ k, ContinuousOn (fun p : ℝ × (Fin d → ℝ) => ι k p.1 p.2)
      (K ×ˢ {x | ∀ k, 0 ≤ x k}) := by
    intro k
    have hfst : Set.MapsTo Prod.fst (K ×ˢ {x : Fin d → ℝ | ∀ k, 0 ≤ x k}) K :=
      fun p hp => hp.1
    have hin : ContinuousOn (fun p : ℝ × (Fin d → ℝ) => p.2 k / M.rho k p.1)
        (K ×ˢ {x | ∀ k, 0 ≤ x k}) :=
      ((continuous_apply k).comp continuous_snd).continuousOn.div
        ((hrhoc k).comp continuous_fst.continuousOn hfst)
        (fun p hp => ne_of_gt (hrhopos k p.1 hp.1))
    exact ((hmuRc k).comp continuous_fst.continuousOn hfst).mul
      ((hmcc k).comp hin (fun p hp => div_nonneg (hp.2 k) (hrhopos k p.1 hp.1).le))
  have huniq : ∀ t ∈ K, ∀ x : Fin d → ℝ, (∀ k, 0 ≤ x k) → ∑ k, x k = Wstar M t →
      (∀ k l, ι k t x = ι l t x) → x = G t := by
    intro t ht x hx hsum heq
    have hmin : IsMin43 (fun k => M.lam k t) (fun k => M.rho k t) Cs (Wstar M t) x := by
      refine ((eq_46_50_kuhn_tucker (fun k => M.lam k t) (fun k => M.rho k t) Cs
        (fun k => hlampos k t ht) (fun k => hrhopos k t ht) h2.convex h3.smooth (Wstar M t) x
        hx hsum).1).mpr ⟨ι ⟨0, hd⟩ t x, fun _ => 0, fun _ => le_rfl, fun k => ?_,
          fun k => by simp⟩
      have hl := hlampos k t ht
      have hm := hmuRpos k t
      have e : M.lam k t / M.rho k t = M.muR k t := by
        unfold Limits.rho; field_simp
      simp only
      rw [e, sub_zero]
      exact heq k ⟨0, hd⟩
    exact (hG t ht).2 x hmin
  have hWG : TendstoUniformlyOn (H.Wt T) G atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hkey⟩ := key_unif ι (Wstar M) G hι hWc hGc huniq ε hε
    have hW2 := proposition_2_W H M h1 T hT
    rw [Metric.tendstoUniformlyOn_iff] at hW2
    filter_upwards [hW2 δ hδ, h51 δ hδ] with n hn1 hn2
    intro t ht
    rw [dist_comm]
    refine hkey t ht _ (fun k => ?_) ?_ (hn2 t ht)
    · unfold HTSeq.Wt
      exact div_nonneg ((hT n).W_nonneg k _ (mul_nonneg (Nat.cast_nonneg n) ht.1))
        (Real.sqrt_nonneg _)
    · have := hn1 t ht
      rw [Real.dist_eq] at this
      unfold HTSeq.Wpt at this
      rw [abs_sub_comm]; exact this.le
  have hTs := (proposition_2_equiv H M h1 T hT hpost).1.mp ⟨G, hWG⟩
  obtain ⟨Ws, Ns, τs5, hWs, hNs, hτs, hlt, hmw, hJ⟩ :=
    proposition_5 H M h1 Cs h2 T hT hpost hTs
  have hWsG : ∀ t ∈ K, Ws t = G t := fun t ht =>
    tendsto_nhds_unique (hWs.tendsto_at ht) (hWG.tendsto_at ht)
  have hτG : ∀ t ∈ K, ∀ k, τs5 t k = G t k / M.rho k t := by
    intro t ht k
    have e1 := hlt t ht k
    have e2 := hmw t ht k
    rw [hWsG t ht] at e2
    have hl := hlampos k t ht
    have hm := hmuRpos k t
    unfold Limits.rho
    rw [eq_div_iff (by positivity)]
    field_simp
    linarith
  have hGnn : ∀ t ∈ K, ∀ k, 0 ≤ G t k := fun t ht k => (hG t ht).1.1 k
  have hcontint : ∀ k, ContinuousOn (fun s => M.lam k s * Cs k (G s k / M.rho k s)) K := by
    intro k
    refine (hlamc k).mul ((hCsc k).comp
      (((continuous_apply k).comp_continuousOn hGc).div (hrhoc k)
        (fun s hs => ne_of_gt (hrhopos k s hs))) ?_)
    intro s hs
    exact div_nonneg (hGnn s hs k) (hrhopos k s hs).le
  constructor
  · refine hJ.congr_right ?_
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ K := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    show ∑ k, ∫ s in (0 : ℝ)..t, M.lam k s * Cs k (τs5 s k) = Jstar M Cs t
    unfold Jstar
    calc ∑ k, ∫ s in (0 : ℝ)..t, M.lam k s * Cs k (τs5 s k)
        = ∑ k, ∫ s in (0 : ℝ)..t, M.lam k s * Cs k (G s k / M.rho k s) := by
          refine Finset.sum_congr rfl fun k _ => intervalIntegral.integral_congr ?_
          intro s hs
          simp only
          rw [hτG s (hsub hs) k]
      _ = ∫ s in (0 : ℝ)..t, ∑ k, M.lam k s * Cs k (G s k / M.rho k s) := by
          rw [intervalIntegral.integral_finsetSum]
          intro k _
          exact ((hcontint k).mono hsub).intervalIntegrable
      _ = ∫ s in (0 : ℝ)..t, val43 (fun k => M.lam k s) (fun k => M.rho k s) Cs (Wstar M s) := by
          refine intervalIntegral.integral_congr ?_
          intro s hs
          have hm := (hG s (hsub hs)).1
          simp only
          unfold val43
          symm
          apply IsLeast.csInf_eq
          constructor
          · exact ⟨G s, hm.1, hm.2.1, rfl⟩
          · rintro z ⟨x, hx, hxs, rfl⟩
            exact hm.2.2 x hx hxs
  · intro τs' hτs'
    refine hτs.congr_right ?_
    intro t ht
    funext k
    have h := (hG t ht).2 _ (hτs' t ht)
    have hk := congrFun h k
    rw [hτG t ht k, ← hk]
    have := hrhopos k t ht
    field_simp
