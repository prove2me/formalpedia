-- Prove2me | solution 1 for FiniteMemQL.Convergence.theorem_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:36:41.481925+00:00
-- url     : https://prove2.me/submissions/770ae66a-f00a-42cd-bfe4-17b026fea3ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_RiskSensMDP_AverageCost_HarrisRecurrence
import Definitions.Def_FiniteMemQL_Convergence_Model
import Definitions.Def_FiniteMemQL_Convergence_Setting
import Definitions.Def_FiniteMemQL_Convergence_Learning
import Theorems.Thm_FiniteMemQL_Convergence_appendixA_v_tendsto_zero
import Theorems.Thm_FiniteMemQL_Convergence_qStar_fixed_point
import Theorems.Thm_FiniteMemQL_Convergence_qStar_min_eq_JN
import Theorems.Thm_FiniteMemQL_Convergence_theorem_3_3

open MeasureTheory ProbabilityTheory Filter Finset Topology

namespace Aux_FMQ_41

lemma inf_diff {U : Type*} [Fintype U] [Nonempty U] (f g : U → ℝ) (d : ℝ)
    (h : ∀ v, |f v - g v| ≤ d) : |(⨅ v, f v) - ⨅ v, g v| ≤ d := by
  rw [abs_le]
  constructor
  · have : (⨅ v, g v) - d ≤ ⨅ v, f v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range g) v, (abs_le.mp (h v)).1]
    linarith
  · have : (⨅ v, f v) - d ≤ ⨅ v, g v := le_ciInf fun v => by
      linarith [ciInf_le (Finite.bddBelow_range f) v, (abs_le.mp (h v)).2]
    linarith

/-- A visit counter that increases at every visit tends to infinity when visits recur. -/
lemma cnt_unbounded (cnt : ℕ → ℕ) (vis : ℕ → Prop)
    (hcv : ∀ n, vis n → cnt (n + 1) = cnt n + 1) (hcn : ∀ n, ¬ vis n → cnt (n + 1) = cnt n)
    (hinf : ∀ m, ∃ n ≥ m, vis n) : ∀ m : ℕ, ∃ n0, ∀ n ≥ n0, m ≤ cnt n := by
  have hmono : Monotone cnt := by
    refine monotone_nat_of_le_succ fun n => ?_
    by_cases h : vis n
    · rw [hcv n h]; omega
    · rw [hcn n h]
  have key : ∀ m : ℕ, ∃ n, m ≤ cnt n := by
    intro m
    induction m with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ m ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n', hn', hv⟩ := hinf n
      refine ⟨n' + 1, ?_⟩
      rw [hcv n' hv]
      have := hmono hn'
      omega
  intro m
  obtain ⟨n, hn⟩ := key m
  exact ⟨n, fun k hk => hn.trans (hmono hk)⟩

/-- Excess decay along the averaging step sizes `1/(1+k)` at the `k`-th visit. -/
lemma excess_decay (x : ℕ → ℝ) (cnt : ℕ → ℕ) (vis : ℕ → Prop)
    (hcv : ∀ n, vis n → cnt (n + 1) = cnt n + 1) (hcn : ∀ n, ¬ vis n → cnt (n + 1) = cnt n)
    (hinf : ∀ m, ∃ n ≥ m, vis n) (G : ℝ) (n0 : ℕ)
    (hstep : ∀ n ≥ n0, vis n → |x (n + 1)| ≤
      (1 - 1 / (1 + (cnt (n + 1) : ℝ))) * |x n| + 1 / (1 + (cnt (n + 1) : ℝ)) * G)
    (hstay : ∀ n, ¬ vis n → x (n + 1) = x n) :
    ∀ δ > 0, ∃ n1, ∀ n ≥ n1, |x n| ≤ G + δ := by
  intro δ hδ
  set e : ℕ → ℝ := fun n => max (|x n| - G) 0 with he
  set P : ℕ → ℝ := fun n => (1 + (cnt n : ℝ)) * e n with hP
  have he0 : ∀ n, 0 ≤ e n := fun n => le_max_right _ _
  have hPstep : ∀ n ≥ n0, P (n + 1) ≤ P n := by
    intro n hn
    by_cases hv : vis n
    · have hc := hcv n hv
      have hs := hstep n hn hv
      rw [hc] at hs
      simp only [hP, hc]
      push_cast at hs ⊢
      set c : ℝ := (cnt n : ℝ) with hcdef
      have hc0 : 0 ≤ c := Nat.cast_nonneg _
      have h1 : (1 - 1 / (1 + (c + 1))) = (c + 1) / (c + 2) := by
        field_simp; ring
      rw [h1] at hs
      have h2 : 1 / (1 + (c + 1)) = 1 / (c + 2) := by ring_nf
      rw [h2] at hs
      -- e (n+1) ≤ (c+1)/(c+2) * e n
      have hen : e (n + 1) ≤ (c + 1) / (c + 2) * e n := by
        have hpos : 0 ≤ (c + 1) / (c + 2) := by positivity
        apply max_le
        · have : |x (n + 1)| - G ≤ (c + 1) / (c + 2) * (|x n| - G) := by
            have : (c + 1) / (c + 2) * |x n| + 1 / (c + 2) * G - G
                = (c + 1) / (c + 2) * (|x n| - G) := by field_simp; ring
            linarith
          exact this.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hpos)
        · exact mul_nonneg hpos (he0 n)
      have : (1 + (c + 1)) * e (n + 1) ≤ (1 + c) * e n := by
        have h3 : (1 + (c + 1)) * ((c + 1) / (c + 2) * e n) = (1 + c) * e n := by
          field_simp; ring
        calc (1 + (c + 1)) * e (n + 1) ≤ (1 + (c + 1)) * ((c + 1) / (c + 2) * e n) :=
              mul_le_mul_of_nonneg_left hen (by positivity)
          _ = (1 + c) * e n := h3
      exact this
    · simp only [hP, he, hcn n hv, hstay n hv]
      exact le_rfl
  have hPle : ∀ k, P (n0 + k) ≤ P n0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => exact (hPstep (n0 + k) (by omega)).trans ih
  obtain ⟨m, hm⟩ := exists_nat_ge (P n0 / δ)
  obtain ⟨n2, hn2⟩ := cnt_unbounded cnt vis hcv hcn hinf m
  refine ⟨max n0 n2, fun n hn => ?_⟩
  have hPn : P n ≤ P n0 := by
    have := hPle (n - n0)
    rwa [Nat.add_sub_cancel' (le_of_max_le_left hn)] at this
  have hcn2 : (m : ℝ) ≤ cnt n := by exact_mod_cast hn2 n (le_of_max_le_right hn)
  have hen : e n ≤ δ := by
    by_contra hcon
    push_neg at hcon
    have h1 : P n0 ≤ m * δ := by
      have := (div_le_iff₀ hδ).1 hm
      linarith
    have h2 : (1 + (m : ℝ)) * δ < (1 + (cnt n : ℝ)) * e n := by
      calc (1 + (m : ℝ)) * δ < (1 + (m : ℝ)) * e n :=
            mul_lt_mul_of_pos_left hcon (by positivity)
        _ ≤ (1 + (cnt n : ℝ)) * e n := mul_le_mul_of_nonneg_right (by linarith) (he0 n)
    have : P n = (1 + (cnt n : ℝ)) * e n := rfl
    nlinarith
  have : |x n| - G ≤ e n := le_max_left _ _
  linarith

/-- The deterministic part of the proof of Theorem 4.1(i): asynchronous averaging iterates driven
by a `β`-contraction plus a vanishing perturbation converge to `0`. -/
lemma det_conv {ι : Type*} [Fintype ι] (D v : ℕ → ι → ℝ) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (vis : ι → ℕ → Prop) (cnt : ι → ℕ → ℕ)
    (hcv : ∀ i n, vis i n → cnt i (n + 1) = cnt i n + 1)
    (hcn : ∀ i n, ¬ vis i n → cnt i (n + 1) = cnt i n)
    (hinf : ∀ i m, ∃ n ≥ m, vis i n)
    (hv : Tendsto v atTop (𝓝 0))
    (hrec : ∀ n i, vis i n → ∃ g : ℝ, |g| ≤ β * (‖D n‖ + ‖v n‖) ∧
      D (n + 1) i = (1 - 1 / (1 + (cnt i (n + 1) : ℝ))) * D n i
        + 1 / (1 + (cnt i (n + 1) : ℝ)) * g)
    (hstay : ∀ n i, ¬ vis i n → D (n + 1) i = D n i) :
    Tendsto D atTop (𝓝 0) := by
  have hvn : Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
    have := hv.norm; simpa using this
  obtain ⟨E, hE⟩ := hvn.bddAbove_range
  have hE' : ∀ n, ‖v n‖ ≤ E := fun n => hE ⟨n, rfl⟩
  have hE0 : 0 ≤ E := (norm_nonneg _).trans (hE' 0)
  -- coordinate bound at a visit
  have hcoord : ∀ n i, vis i n → |D (n + 1) i| ≤
      (1 - 1 / (1 + (cnt i (n + 1) : ℝ))) * |D n i|
        + 1 / (1 + (cnt i (n + 1) : ℝ)) * (β * (‖D n‖ + ‖v n‖)) := by
    intro n i hvi
    obtain ⟨g, hg, hD⟩ := hrec n i hvi
    rw [hD]
    set a : ℝ := 1 / (1 + (cnt i (n + 1) : ℝ))
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 := by
      apply div_le_one_of_le₀ _ (by positivity)
      have : (0 : ℝ) ≤ cnt i (n + 1) := Nat.cast_nonneg _
      linarith
    calc |(1 - a) * D n i + a * g| ≤ |(1 - a) * D n i| + |a * g| := abs_add_le _ _
      _ = (1 - a) * |D n i| + a * |g| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - a), abs_of_nonneg ha0]
      _ ≤ (1 - a) * |D n i| + a * (β * (‖D n‖ + ‖v n‖)) := by gcongr
  have hab : ∀ i n, (0 : ℝ) ≤ 1 / (1 + (cnt i (n + 1) : ℝ)) ∧
      1 / (1 + (cnt i (n + 1) : ℝ)) ≤ 1 := by
    intro i n
    refine ⟨by positivity, div_le_one_of_le₀ ?_ (by positivity)⟩
    have : (0 : ℝ) ≤ cnt i (n + 1) := Nat.cast_nonneg _
    linarith
  -- boundedness
  set K : ℝ := max ‖D 0‖ (β * E / (1 - β)) with hK
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (le_max_left _ _)
  have hKE : β * (K + E) ≤ K := by
    have : β * E / (1 - β) ≤ K := le_max_right _ _
    rw [div_le_iff₀ (by linarith)] at this
    nlinarith
  have hbdd : ∀ n, ‖D n‖ ≤ K := by
    intro n
    induction n with
    | zero => exact le_max_left _ _
    | succ n ih =>
      refine (pi_norm_le_iff_of_nonneg hK0).2 fun i => ?_
      rw [Real.norm_eq_abs]
      by_cases hvi : vis i n
      · have h1 := hcoord n i hvi
        obtain ⟨ha0, ha1⟩ := hab i n
        set a : ℝ := 1 / (1 + (cnt i (n + 1) : ℝ))
        have h2 : |D n i| ≤ K := by
          have := norm_le_pi_norm (D n) i; rw [Real.norm_eq_abs] at this; linarith
        have h3 : β * (‖D n‖ + ‖v n‖) ≤ K := by
          have := hE' n; nlinarith
        nlinarith
      · rw [hstay n i hvi]
        have := norm_le_pi_norm (D n) i; rw [Real.norm_eq_abs] at this; linarith
  -- one contraction round
  have hround : ∀ L : ℝ, 0 ≤ L → ∀ δ > 0, (∃ n0, ∀ n ≥ n0, ‖D n‖ ≤ L) →
      ∃ n1, ∀ n ≥ n1, ‖D n‖ ≤ β * L + 2 * δ := by
    intro L hL δ hδ ⟨n0, hn0⟩
    obtain ⟨n0', hn0'⟩ := (Metric.tendsto_atTop.1 hvn) δ hδ
    have hεv : ∀ n ≥ n0', ‖v n‖ ≤ δ := by
      intro n hn
      have := hn0' n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
      exact this.le
    have hi : ∀ i, ∃ n1, ∀ n ≥ n1, |D n i| ≤ β * (L + δ) + δ := by
      intro i
      refine excess_decay (fun n => D n i) (cnt i) (vis i) (hcv i) (hcn i) (hinf i)
        (β * (L + δ)) (max n0 n0') (fun n hn hvi => ?_) (fun n hvi => hstay n i hvi) δ hδ
      have h1 := hcoord n i hvi
      obtain ⟨ha0, ha1⟩ := hab i n
      have h3 : β * (‖D n‖ + ‖v n‖) ≤ β * (L + δ) := by
        have := hn0 n (le_of_max_le_left hn)
        have := hεv n (le_of_max_le_right hn)
        nlinarith
      calc |D (n + 1) i| ≤ _ := h1
        _ ≤ _ := by gcongr
    choose n1 hn1 using hi
    refine ⟨Finset.univ.sup n1, fun n hn => ?_⟩
    have hpos : 0 ≤ β * L + 2 * δ := by positivity
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun i => ?_
    rw [Real.norm_eq_abs]
    have := hn1 i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)
    nlinarith
  -- iterate
  have hiter : ∀ δ > 0, ∀ k : ℕ, ∃ n0, ∀ n ≥ n0, ‖D n‖ ≤ β ^ k * K + 2 * δ / (1 - β) := by
    intro δ hδ k
    have h1β : 0 < 1 - β := by linarith
    induction k with
    | zero =>
      refine ⟨0, fun n _ => ?_⟩
      have : 0 ≤ 2 * δ / (1 - β) := by positivity
      simp only [pow_zero, one_mul]
      linarith [hbdd n]
    | succ k ih =>
      have hL : 0 ≤ β ^ k * K + 2 * δ / (1 - β) := by positivity
      obtain ⟨n1, hn1⟩ := hround _ hL δ hδ ih
      refine ⟨n1, fun n hn => (hn1 n hn).trans (le_of_eq ?_)⟩
      field_simp
      ring
  rw [Metric.tendsto_atTop]
  intro η hη
  have h1β : 0 < 1 - β := by linarith
  set δ : ℝ := η * (1 - β) / 8 with hδ
  have hδ0 : 0 < δ := by positivity
  have hpow : Tendsto (fun k : ℕ => β ^ k * K) atTop (𝓝 (0 * K)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const K
  rw [zero_mul] at hpow
  obtain ⟨k, hk⟩ := (hpow.eventually (gt_mem_nhds (by linarith : (0:ℝ) < η / 2))).exists
  obtain ⟨n0, hn0⟩ := hiter δ hδ0 k
  refine ⟨n0, fun n hn => ?_⟩
  rw [dist_zero_right]
  have h2 : 2 * δ / (1 - β) = η / 4 := by
    rw [hδ]; field_simp; ring
  have := hn0 n hn
  linarith

end Aux_FMQ_41

open FiniteMemQL.Convergence Aux_FMQ_41 in
theorem solution {X Y U : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y] [MeasurableSpace Y] [DiscreteMeasurableSpace Y]
    [Fintype U] [DecidableEq U] [Nonempty U] [MeasurableSpace U] [DiscreteMeasurableSpace U]
    (M : POMDP X Y U)
    (N : ℕ) (σ : Measure U) [IsProbabilityMeasure σ] (hσ : ∀ u : U, 0 < σ {u})
    (hHarris : RiskSensMDP.AverageCost.IsPositiveHarrisRecurrent (explKernel M σ))
    (πs : Measure X) [IsProbabilityMeasure πs] (hπs : Kernel.Invariant (explKernel M σ) πs) :
    (∀ (μ : Measure X), IsProbabilityMeasure μ → ∀ Q₀ : Window Y U N → U → ℝ,
      (∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
        ∃ᶠ t in atTop, winAt (N := N) ω t = I ∧ (ω t).2.2 = u) →
      ∀ᵐ ω ∂pathMeasure M μ σ, ∀ (I : Window Y U N) (u : U),
        Tendsto (fun n : ℕ => qIter M Q₀ ω n I u) atTop (𝓝 (qStar M πs I u))) ∧
    (∀ (π₀ : Measure X), IsProbabilityMeasure π₀ → ∀ (γ₀ : HistPolicy Y U)
      (γN : Window Y U N → U), (∀ I : Window Y U N, qStar M πs I (γN I) = ⨅ u : U, qStar M πs I u) →
      ∑ ys : Fin (N + 1) → Y, histMass M π₀ γ₀ ys *
          (Jpol M γN (π₀, ((ys, histActs γ₀ ys) : Window Y U N)) -
            JstarW M π₀ ((ys, histActs γ₀ ys) : Window Y U N)) ≤
        2 * cNorm M / (1 - M.β) * ∑' t : ℕ, M.β ^ t * Lterm M πs π₀ N t) := by
  have hβ0 := M.β_pos
  have hβ1 := M.β_lt_one
  have hfp := qStar_fixed_point M (N := N) πs
  constructor
  · intro μ hμ Q₀ hvisit
    haveI := hμ
    have hv := appendixA_v_tendsto_zero M N σ hσ hHarris πs hπs μ hvisit
    filter_upwards [hv, hvisit] with ω h1 h2
    -- the deterministic argument along the path `ω`
    let D : ℕ → Window Y U N × U → ℝ := fun n p =>
      qIter M Q₀ ω n p.1 p.2 - qStar M πs p.1 p.2 - vIter M πs ω n p.1 p.2
    let v : ℕ → Window Y U N × U → ℝ := fun n p => vIter M πs ω n p.1 p.2
    let vis : Window Y U N × U → ℕ → Prop := fun p n =>
      winAt (N := N) ω (N + n) = p.1 ∧ (ω (N + n)).2.2 = p.2
    let cnt : Window Y U N × U → ℕ → ℕ := fun p n =>
      ((Finset.range n).filter (fun k => winAt (N := N) ω (N + k) = p.1 ∧
        (ω (N + k)).2.2 = p.2)).card
    have hcnt_succ : ∀ p n, cnt p (n + 1) = cnt p n + if vis p n then 1 else 0 := by
      intro p n
      simp only [cnt, vis, Finset.card_filter, Finset.sum_range_succ]
    have hcv : ∀ p n, vis p n → cnt p (n + 1) = cnt p n + 1 := by
      intro p n h; rw [hcnt_succ, if_pos h]
    have hcn : ∀ p n, ¬ vis p n → cnt p (n + 1) = cnt p n := by
      intro p n h; rw [hcnt_succ, if_neg h, add_zero]
    have hvisits : ∀ n I u, (visits (N := N) ω n I u : ℝ) = (cnt (I, u) (n + 1) : ℝ) := by
      intro n I u; rfl
    have hinf : ∀ p m, ∃ n ≥ m, vis p n := by
      intro p m
      obtain ⟨t, ht, hct⟩ := Filter.frequently_atTop.1 (h2 p.1 p.2) (N + m)
      refine ⟨t - N, by omega, ?_⟩
      show winAt (N := N) ω (N + (t - N)) = p.1 ∧ (ω (N + (t - N))).2.2 = p.2
      rw [Nat.add_sub_cancel' (by omega : N ≤ t)]
      exact hct
    have hvt : Tendsto v atTop (𝓝 0) := tendsto_pi_nhds.2 fun p => h1 p.1 p.2
    have hstay : ∀ n p, ¬ vis p n → D (n + 1) p = D n p := by
      intro n p h
      simp only [D, qIter, vIter]
      rw [if_neg h, if_neg h]
    have hrec : ∀ n p, vis p n → ∃ g : ℝ, |g| ≤ M.β * (‖D n‖ + ‖v n‖) ∧
        D (n + 1) p = (1 - 1 / (1 + (cnt p (n + 1) : ℝ))) * D n p
          + 1 / (1 + (cnt p (n + 1) : ℝ)) * g := by
      intro n p hp
      set J := winAt (N := N) ω (N + n + 1) with hJ
      refine ⟨M.β * ((⨅ w : U, qIter M Q₀ ω n J w) - ⨅ w : U, qStar M πs J w), ?_, ?_⟩
      · rw [abs_mul, abs_of_pos hβ0]
        apply mul_le_mul_of_nonneg_left _ hβ0.le
        apply inf_diff
        intro w
        have e : qIter M Q₀ ω n J w - qStar M πs J w = D n (J, w) + v n (J, w) := by
          simp only [D, v]; ring
        rw [e]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · have := norm_le_pi_norm (D n) (J, w); rwa [Real.norm_eq_abs] at this
        · have := norm_le_pi_norm (v n) (J, w); rwa [Real.norm_eq_abs] at this
      · obtain ⟨I, u⟩ := p
        have hp' : winAt (N := N) ω (N + n) = I ∧ (ω (N + n)).2.2 = u := hp
        simp only [D, qIter, vIter]
        rw [if_pos hp', if_pos hp', hvisits]
        have hf := hfp I u
        simp only [rStar]
        rw [← hJ]
        linear_combination (-(1 / (1 + (cnt (I, u) (n + 1) : ℝ)))) * hf
    have hD := det_conv D v M.β hβ0.le hβ1 vis cnt hcv hcn hinf hvt hrec hstay
    intro I u
    have hDI : Tendsto (fun n => D n (I, u)) atTop (𝓝 0) := tendsto_pi_nhds.1 hD (I, u)
    have hsum := (hDI.add (h1 I u)).add_const (qStar M πs I u)
    simp only [zero_add] at hsum
    refine hsum.congr fun n => ?_
    simp only [D]
    ring
  · intro π₀ hπ₀ γ₀ γN hγ
    haveI := hπ₀
    have hJN := qStar_min_eq_JN M (N := N) πs
    have hφ : ∀ I : Window Y U N, Cstar M πs I (γN I) +
        M.β * ∑ y : Y, Pstar M πs I (γN I) y * JN M πs (shift I (γN I) y) = JN M πs I := by
      intro I
      rw [← hJN I, ← hγ I, hfp I (γN I)]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hJN]
    have h33 := theorem_3_3 M N πs π₀ γ₀ γN hφ
    refine le_trans (Finset.sum_le_sum fun ys _ => ?_) h33
    exact mul_le_mul_of_nonneg_left (le_abs_self _) ENNReal.toReal_nonneg
