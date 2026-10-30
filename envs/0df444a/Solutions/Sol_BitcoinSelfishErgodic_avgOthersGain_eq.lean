-- Prove2me | solution 1 for BitcoinSelfishErgodic.avgOthersGain_eq
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-30T00:58:30.916473+00:00
-- url     : https://prove2.me/submissions/ed8a3b73-e882-454d-a4e9-91bbd5d2c12a

import Definitions.Def_BitcoinSelfishErgodic
import Theorems.Thm_BitcoinSelfishMining_stationary_balance
import Theorems.Thm_BitcoinSelfishMining_total_mass
import Theorems.Thm_BitcoinSelfishMining_stationary_nonneg
import Theorems.Thm_BitcoinSelfishMining_threshold
import Theorems.Thm_BitcoinSelfishUnique_stationary_unique
import Theorems.Thm_BitcoinSelfishErgodic_distN_mix
import Theorems.Thm_BitcoinSelfishErgodic_distN_zero_lead_le
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_one
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_succ
import Theorems.Thm_BitcoinSelfishErgodic_dist_lead_zero
import Theorems.Thm_BitcoinSelfishErgodic_dist_tie
import Theorems.Thm_BitcoinSelfishErgodic_dist_zero
import Theorems.Thm_BitcoinSelfishErgodic_isDist_delta
import Theorems.Thm_BitcoinSelfishErgodic_isDist_distN
import Theorems.Thm_BitcoinSelfishErgodic_le_one_of_isDist

open BitcoinSelfishErgodic BitcoinSelfishMining BitcoinSelfishUnique Filter Topology

private theorem one_sub_pos {α : ℝ} (h1 : α < 1 / 2) : 0 < 1 - α := by linarith

private theorem ratio_pos {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 < α / (1 - α) :=
  div_pos h0 (one_sub_pos h1)

private theorem ratio_nonneg {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) : 0 ≤ α / (1 - α) :=
  (ratio_pos h0 h1).le

private theorem ratio_lt_one {α : ℝ} (h1 : α < 1 / 2) : α / (1 - α) < 1 :=
  (div_lt_one (one_sub_pos h1)).mpr (by linarith)

/-- `α r^m + (1 - α) r^(m+2) = r^(m+1)` for `r = α / (1 - α)`. -/
private theorem ratio_step {α : ℝ} (h1 : α < 1 / 2) (m : ℕ) :
    α * (α / (1 - α)) ^ m + (1 - α) * (α / (1 - α)) ^ (m + 2) = (α / (1 - α)) ^ (m + 1) := by
  have h1' := (one_sub_pos h1).ne'
  have e : (1 - α) * (α / (1 - α)) = α := mul_div_cancel₀ _ h1'
  linear_combination ((α / (1 - α)) ^ (m + 1) - (α / (1 - α)) ^ m) * e

/-- Uniform form of the inflow at the leads `n + 1 ≥ 1`. -/
private theorem dist_lead_add_one (α γ : ℝ) (μ : State → ℝ) (n : ℕ) :
    dist α γ μ (.lead (n + 1)) = α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) := by
  rcases n with _ | n
  · exact dist_lead_one α γ μ
  · exact dist_lead_succ α γ μ n

private theorem dist_summable {α γ : ℝ} {μ : State → ℝ}
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    Summable (fun n : ℕ => dist α γ μ (.lead n)) := by
  rw [← summable_nat_add_iff 1]
  have : (fun n : ℕ => dist α γ μ (.lead (n + 1))) =
      fun n => α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) := by
    funext n; exact dist_lead_add_one α γ μ n
  rw [this]
  exact (hμ.mul_left α).add (((summable_nat_add_iff 2).2 hμ).mul_left (1 - α))

private theorem dist_lead_tsum {α γ : ℝ} {μ : State → ℝ}
    (hμ : Summable (fun n : ℕ => μ (.lead n))) :
    ∑' n : ℕ, dist α γ μ (.lead n) =
      α * μ .zero + α * ∑' n : ℕ, μ (.lead n)
        + (1 - α) * (∑' n : ℕ, μ (.lead n) - μ (.lead 0) - μ (.lead 1)) := by
  rw [(dist_summable (α := α) (γ := γ) hμ).tsum_eq_zero_add, dist_lead_zero]
  have e : ∀ n : ℕ, dist α γ μ (.lead (n + 1)) = α * μ (.lead n) + (1 - α) * μ (.lead (n + 2)) :=
    dist_lead_add_one α γ μ
  simp_rw [e]
  rw [(hμ.mul_left α).tsum_add (((summable_nat_add_iff 2).2 hμ).mul_left (1 - α)),
    tsum_mul_left, tsum_mul_left]
  have h2 := hμ.sum_add_tsum_nat_add 2
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h2
  rw [show ∑' n : ℕ, μ (.lead (n + 2)) = ∑' n : ℕ, μ (.lead n) - μ (.lead 0) - μ (.lead 1) by
    linarith]
  ring

private theorem delta_lead_summable (t : State) :
    Summable (fun n : ℕ => delta t (.lead n)) := by
  rcases t with _ | _ | j
  · simp [delta]
  · simp [delta]
  · have : (fun n : ℕ => delta (.lead j) (.lead n)) = fun n => if n = j then (1:ℝ) else 0 := by
      funext n; simp [delta]
    rw [this]
    exact (hasSum_ite_eq j (1:ℝ)).summable

private theorem dist_lead_le {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C) (hb : ∀ m, μ (.lead m) ≤ C * (α / (1 - α)) ^ m) (m : ℕ) :
    dist α γ μ (.lead m) ≤ C * (α / (1 - α)) ^ m := by
  rcases m with _ | m
  · rw [dist_lead_zero, pow_zero, mul_one]
    have := le_one_of_isDist μ hμ .zero
    have := hμ.nonneg .zero
    nlinarith
  · rw [dist_lead_add_one, ← ratio_step h1 m]
    have ha := hb m
    have hb2 := hb (m + 2)
    have h1' : 0 ≤ 1 - α := by linarith
    nlinarith [mul_le_mul_of_nonneg_left ha h0.le, mul_le_mul_of_nonneg_left hb2 h1']

private theorem distN_lead_le_aux {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C) (hb : ∀ m, μ (.lead m) ≤ C * (α / (1 - α)) ^ m)
    (n m : ℕ) : distN α γ μ n (.lead m) ≤ C * (α / (1 - α)) ^ m := by
  induction n generalizing m with
  | zero => exact hb m
  | succ n ih => exact dist_lead_le h0 h1 (isDist_distN α γ h0 h1 μ hμ n) hC ih m

private theorem dist_finsetSum (α γ : ℝ) (f : ℕ → State → ℝ) (F : Finset ℕ) (s : State) :
    dist α γ (fun t => ∑ k ∈ F, f k t) s = ∑ k ∈ F, dist α γ (f k) s := by
  rcases s with _ | _ | _ | _ | n <;>
    simp only [zero_add, BitcoinSelfishErgodic.dist_zero, dist_tie, dist_lead_zero, dist_lead_one,
      dist_lead_succ, Finset.mul_sum, Finset.sum_add_distrib]

private theorem dist_const_mul (α γ : ℝ) (c : ℝ) (μ : State → ℝ) (s : State) :
    dist α γ (fun t => c * μ t) s = c * dist α γ μ s := by
  rcases s with _ | _ | _ | _ | n <;>
    simp only [zero_add, BitcoinSelfishErgodic.dist_zero, dist_tie, dist_lead_zero, dist_lead_one,
      dist_lead_succ] <;> ring

/-- Continuity of one step of the chain in each coordinate (it is a finite linear combination of
at most three coordinates). -/
private theorem tendsto_dist {α γ : ℝ} {y : ℕ → State → ℝ} {ν : State → ℝ}
    (h : ∀ s, Tendsto (fun j => y j s) atTop (𝓝 (ν s))) (s : State) :
    Tendsto (fun j => dist α γ (y j) s) atTop (𝓝 (dist α γ ν s)) := by
  rcases s with _ | _ | _ | _ | n
  · simp only [BitcoinSelfishErgodic.dist_zero]
    exact (((h .zero).const_mul _).add (h .tie)).add ((h (.lead 1)).const_mul _)
  · simp only [dist_tie]; exact (h (.lead 0)).const_mul _
  · simp only [dist_lead_zero]; exact (h .zero).const_mul _
  · simp only [zero_add, dist_lead_one]
    exact ((h (.lead 0)).const_mul _).add ((h (.lead 2)).const_mul _)
  · simp only [dist_lead_succ]
    exact ((h (.lead (n + 1))).const_mul _).add ((h (.lead (n + 3))).const_mul _)

private theorem stateSum_add {f g : State → ℝ} (hf : Summable (fun n : ℕ => f (.lead n)))
    (hg : Summable (fun n : ℕ => g (.lead n))) :
    stateSum (fun s => f s + g s) = stateSum f + stateSum g := by
  unfold stateSum; rw [hf.tsum_add hg]; ring

private theorem stateSum_const_mul (c : ℝ) (f : State → ℝ) :
    stateSum (fun s => c * f s) = c * stateSum f := by
  unfold stateSum; rw [tsum_mul_left]; ring

private theorem stateSum_mul_const (c : ℝ) (f : State → ℝ) :
    stateSum (fun s => f s * c) = stateSum f * c := by
  unfold stateSum; rw [tsum_mul_right]; ring

private theorem stateSum_finsetSum {f : ℕ → State → ℝ} {F : Finset ℕ}
    (hf : ∀ k ∈ F, Summable (fun n : ℕ => f k (.lead n))) :
    stateSum (fun s => ∑ k ∈ F, f k s) = ∑ k ∈ F, stateSum (f k) := by
  unfold stateSum; rw [Summable.tsum_finsetSum hf, Finset.sum_add_distrib, Finset.sum_add_distrib]

private theorem cesaro_nonneg {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (n : ℕ) (s : State) : 0 ≤ cesaro α γ μ n s := by
  unfold cesaro
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).nonneg s))

private theorem cesaro_le {α γ : ℝ} {μ : State → ℝ} {s : State} {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k, distN α γ μ k s ≤ B) (n : ℕ) : cesaro α γ μ n s ≤ B := by
  unfold cesaro
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hB]
  · have hsum : ∑ k ∈ Finset.range n, distN α γ μ k s ≤ (n : ℝ) * B := by
      have := Finset.sum_le_card_nsmul (Finset.range n) (fun k => distN α γ μ k s) B
        (fun k _ => hb k)
      simpa [Finset.card_range, nsmul_eq_mul] using this
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s
        ≤ (1 / (n : ℝ)) * ((n : ℝ) * B) := by gcongr
      _ = B := by field_simp

private theorem cesaro_summable {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (n : ℕ) : Summable (fun m : ℕ => cesaro α γ μ n (.lead m)) := by
  unfold cesaro
  exact (summable_sum (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).summable)).mul_left _

private theorem cesaro_mass {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {n : ℕ} (hn : 1 ≤ n) : stateSum (cesaro α γ μ n) = 1 := by
  have e : cesaro α γ μ n = fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s := rfl
  rw [e, stateSum_const_mul,
    stateSum_finsetSum (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).summable)]
  rw [Finset.sum_congr rfl (fun k _ => (isDist_distN α γ h0 h1 μ hμ k).mass), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp

/-- Almost invariance: `dist (cesaro n) - cesaro n = (distN n - μ) / n`. -/
private theorem cesaro_dist_sub (α γ : ℝ) (μ : State → ℝ) (n : ℕ) (s : State) :
    dist α γ (cesaro α γ μ n) s - cesaro α γ μ n s =
      (1 / (n : ℝ)) * (distN α γ μ n s - μ s) := by
  have e : cesaro α γ μ n = fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ μ k s := rfl
  rw [e, dist_const_mul, dist_finsetSum]
  have e2 : ∀ k, dist α γ (distN α γ μ k) s = distN α γ μ (k + 1) s := fun k => rfl
  simp only [e2]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => distN α γ μ k s)]
  rfl

private theorem cesaro_dist_sub_tendsto {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (s : State) :
    Tendsto (fun n => dist α γ (cesaro α γ μ n) s - cesaro α γ μ n s) atTop (𝓝 0) := by
  simp only [cesaro_dist_sub]
  have h2 : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat 2
  refine squeeze_zero_norm (fun n => ?_) h2
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / n),
    div_eq_mul_one_div 2 (n : ℝ), mul_comm (2 : ℝ)]
  gcongr
  have := (isDist_distN α γ h0 h1 μ hμ n).nonneg s
  have := le_one_of_isDist _ (isDist_distN α γ h0 h1 μ hμ n) s
  have := hμ.nonneg s
  have := le_one_of_isDist μ hμ s
  rw [abs_le]; constructor <;> linarith

private theorem cesaro_subseq {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) {C : ℝ} (hC : 1 ≤ C)
    (hb : ∀ n m, distN α γ μ n (.lead m) ≤ C * (α / (1 - α)) ^ m)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop) :
    ∃ ms : ℕ → ℕ, Tendsto (fun j => cesaro α γ μ (ns (ms j))) atTop (𝓝 (stationary α)) := by
  have hr0 := ratio_nonneg h0 h1
  have hr1 := ratio_lt_one h1
  have hgeo : Summable (fun m : ℕ => C * (α / (1 - α)) ^ m) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left C
  set S : Set (State → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0:ℝ) 1) with hS
  have hSc : IsCompact S := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hmem : ∀ j, cesaro α γ μ (ns j) ∈ S := by
    intro j
    rw [hS, Set.mem_univ_pi]
    intro s
    exact ⟨cesaro_nonneg h0 h1 hμ _ s,
      cesaro_le zero_le_one (fun k => le_one_of_isDist _ (isDist_distN α γ h0 h1 μ hμ k) s) _⟩
  obtain ⟨ν, hνS, φ, hφ, hlim⟩ := hSc.tendsto_subseq hmem
  refine ⟨φ, ?_⟩
  have hpt : ∀ s, Tendsto (fun j => cesaro α γ μ (ns (φ j)) s) atTop (𝓝 (ν s)) :=
    fun s => tendsto_pi_nhds.1 hlim s
  have hnsφ : Tendsto (fun j => ns (φ j)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hν0 : ∀ s, 0 ≤ ν s := fun s => (Set.mem_univ_pi.1 hνS s).1
  have hνb : ∀ m, ν (.lead m) ≤ C * (α / (1 - α)) ^ m := fun m =>
    le_of_tendsto' (hpt (.lead m)) (fun j => cesaro_le (by positivity) (fun k => hb k m) _)
  have hνsum : Summable (fun m : ℕ => ν (.lead m)) :=
    Summable.of_nonneg_of_le (fun m => hν0 _) hνb hgeo
  have hstat : IsStationary α γ ν := by
    refine ⟨hν0, hνsum, ?_, ?_⟩
    · -- total mass one, by dominated convergence
      have hA : Tendsto (fun j => stateSum (cesaro α γ μ (ns (φ j)))) atTop (𝓝 (stateSum ν)) := by
        unfold stateSum
        refine ((hpt .zero).add (hpt .tie)).add ?_
        refine tendsto_tsum_of_dominated_convergence hgeo (fun m => hpt (.lead m))
          (Eventually.of_forall fun j m => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (cesaro_nonneg h0 h1 hμ _ _)]
        exact cesaro_le (by positivity) (fun k => hb k m) _
      have hB : Tendsto (fun j => stateSum (cesaro α γ μ (ns (φ j)))) atTop (𝓝 1) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hnsφ.eventually_ge_atTop 1] with j hj
        exact (cesaro_mass h0 h1 hμ hj).symm
      exact tendsto_nhds_unique hA hB
    · -- invariance
      intro s
      have hd : Tendsto (fun j => dist α γ (cesaro α γ μ (ns (φ j))) s) atTop (𝓝 (dist α γ ν s)) :=
        tendsto_dist hpt s
      have he : Tendsto (fun j => dist α γ (cesaro α γ μ (ns (φ j))) s - cesaro α γ μ (ns (φ j)) s)
          atTop (𝓝 0) :=
        (cesaro_dist_sub_tendsto h0 h1 hμ s).comp hnsφ
      have := tendsto_nhds_unique (hd.sub (hpt s)) he
      show ν s = dist α γ ν s
      linarith
  have hνeq : ν = stationary α := funext (stationary_unique α γ ν h0 h1 hstat)
  rw [← hνeq]
  exact hlim

private theorem mix_summable {μ : State → ℝ} (hμ : IsDist μ) {f : State → ℝ}
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    Summable (fun n : ℕ => μ (.lead n) * f (.lead n)) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (hμ.nonneg _) (hf0 _))
    (fun n => mul_le_of_le_one_right (hμ.nonneg _) (hf1 _)) hμ.summable

private theorem stateSum_delta (μ : State → ℝ) (s : State) :
    stateSum (fun t => μ t * delta t s) = μ s := by
  unfold stateSum delta
  rcases s with _ | _ | m
  · simp
  · simp
  · simp [eq_comm]

private theorem stateSum_mix3 {μ : State → ℝ} (hμ : IsDist μ) {f : State → State → ℝ}
    (hf0 : ∀ t s, 0 ≤ f t s) (hf1 : ∀ t s, f t s ≤ 1) (a b c : ℝ) (s1 s2 s3 : State) :
    stateSum (fun t => μ t * (a * f t s1 + b * f t s2 + c * f t s3)) =
      a * stateSum (fun t => μ t * f t s1) + b * stateSum (fun t => μ t * f t s2)
        + c * stateSum (fun t => μ t * f t s3) := by
  have hs : ∀ s', Summable (fun n : ℕ => μ (.lead n) * f (.lead n) s') :=
    fun s' => mix_summable hμ (fun t => hf0 t s') (fun t => hf1 t s')
  have e : ∀ t, μ t * (a * f t s1 + b * f t s2 + c * f t s3) =
      a * (μ t * f t s1) + b * (μ t * f t s2) + c * (μ t * f t s3) := fun t => by ring
  simp only [e]
  unfold stateSum
  rw [(((hs s1).mul_left a).add ((hs s2).mul_left b)).tsum_add ((hs s3).mul_left c),
    ((hs s1).mul_left a).tsum_add ((hs s2).mul_left b), tsum_mul_left, tsum_mul_left,
    tsum_mul_left]
  ring

private theorem stateSum_mix2 {μ : State → ℝ} (hμ : IsDist μ) {f : State → State → ℝ}
    (hf0 : ∀ t s, 0 ≤ f t s) (hf1 : ∀ t s, f t s ≤ 1) (a b : ℝ) (s1 s2 : State) :
    stateSum (fun t => μ t * (a * f t s1 + b * f t s2)) =
      a * stateSum (fun t => μ t * f t s1) + b * stateSum (fun t => μ t * f t s2) := by
  have hs : ∀ s', Summable (fun n : ℕ => μ (.lead n) * f (.lead n) s') :=
    fun s' => mix_summable hμ (fun t => hf0 t s') (fun t => hf1 t s')
  have e : ∀ t, μ t * (a * f t s1 + b * f t s2) =
      a * (μ t * f t s1) + b * (μ t * f t s2) := fun t => by ring
  simp only [e]
  unfold stateSum
  rw [((hs s1).mul_left a).tsum_add ((hs s2).mul_left b), tsum_mul_left, tsum_mul_left]
  ring

private theorem stateSum_mix1 {μ : State → ℝ} {f : State → State → ℝ} (a : ℝ) (s1 : State) :
    stateSum (fun t => μ t * (a * f t s1)) = a * stateSum (fun t => μ t * f t s1) := by
  have e : ∀ t, μ t * (a * f t s1) = a * (μ t * f t s1) := fun t => by ring
  simp only [e]
  exact stateSum_const_mul a _

/-- One step commutes with mixing. -/
private theorem dist_mix {α γ : ℝ} {μ : State → ℝ} (hμ : IsDist μ) {f : State → State → ℝ}
    (hf0 : ∀ t s, 0 ≤ f t s) (hf1 : ∀ t s, f t s ≤ 1) (s : State) :
    dist α γ (fun s' => stateSum (fun t => μ t * f t s')) s =
      stateSum (fun t => μ t * dist α γ (f t) s) := by
  rcases s with _ | _ | _ | _ | n
  · simp only [BitcoinSelfishErgodic.dist_zero]
    rw [show (fun t => μ t * ((1 - α) * f t .zero + f t .tie + (1 - α) * f t (.lead 1))) =
        fun t => μ t * ((1 - α) * f t .zero + 1 * f t .tie + (1 - α) * f t (.lead 1)) by
      funext t; ring, stateSum_mix3 hμ hf0 hf1]
    ring
  · simp only [dist_tie]
    exact (stateSum_mix1 _ _).symm
  · simp only [dist_lead_zero]
    exact (stateSum_mix1 _ _).symm
  · simp only [zero_add, dist_lead_one]
    exact (stateSum_mix2 hμ hf0 hf1 _ _ _ _).symm
  · simp only [dist_lead_succ]
    exact (stateSum_mix2 hμ hf0 hf1 _ _ _ _).symm

private theorem cesaro_mix {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {μ : State → ℝ}
    (hμ : IsDist μ) (n : ℕ) (s : State) :
    cesaro α γ μ n s = stateSum (fun t => μ t * cesaro α γ (delta t) n s) := by
  unfold cesaro
  simp only [distN_mix α γ h0 h1 μ hμ]
  have e : (fun t => μ t * ((1 / (n : ℝ)) * ∑ k ∈ Finset.range n, distN α γ (delta t) k s)) =
      fun t => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n, (μ t * distN α γ (delta t) k s) := by
    funext t; rw [← Finset.mul_sum]; ring
  rw [e, stateSum_const_mul, stateSum_finsetSum (fun k _ => mix_summable hμ
    (fun t => (isDist_distN α γ h0 h1 _ (isDist_delta t) k).nonneg s)
    (fun t => le_one_of_isDist _ (isDist_distN α γ h0 h1 _ (isDist_delta t) k) s))]

private theorem poolExpGain_zero (α γ : ℝ) : poolExpGain α γ .zero = 0 := by
  simp [poolExpGain, outcomeSum, poolGain]

private theorem poolExpGain_tie (α γ : ℝ) :
    poolExpGain α γ .tie = α * 2 + γ * (1 - α) * 1 := by
  simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring

private theorem poolExpGain_lead_bound {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (m : ℕ) :
    0 ≤ poolExpGain α γ (.lead m) ∧ poolExpGain α γ (.lead m) ≤ 2 := by
  rcases m with _ | _ | m
  · simp [poolExpGain, outcomeSum, poolGain]
  · have e : poolExpGain α γ (.lead 1) = (1 - α) * 2 := by
      simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring
    rw [e]; constructor <;> nlinarith
  · have e : poolExpGain α γ (.lead (m + 2)) = (1 - α) * 1 := by
      simp [poolExpGain, outcomeSum, outcomeProb, poolGain]; ring
    rw [e]; constructor <;> nlinarith

private theorem othersExpGain_zero (α γ : ℝ) : othersExpGain α γ .zero = (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_tie (α γ : ℝ) :
    othersExpGain α γ .tie = (1 - α) * (1 - γ) * 2 + γ * (1 - α) * 1 := by
  simp [othersExpGain, outcomeSum, outcomeProb, othersGain]; ring

private theorem othersExpGain_lead (α γ : ℝ) (n : ℕ) : othersExpGain α γ (.lead n) = 0 := by
  rcases n with _ | _ | n <;> simp [othersExpGain, outcomeSum, othersGain]

private theorem othersExpGain_lead_bound (α γ : ℝ) (m : ℕ) :
    0 ≤ othersExpGain α γ (.lead m) ∧ othersExpGain α γ (.lead m) ≤ 2 := by
  rw [othersExpGain_lead]; norm_num

/-- Dominated convergence for `Σ_s y n s · g s` when the `y n` are uniformly geometrically
dominated on the leads and `g` is bounded on the leads. -/
private theorem tendsto_stateSum_mul {α : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) {y : ℕ → State → ℝ}
    {ν : State → ℝ} (hy : ∀ s, Tendsto (fun n => y n s) atTop (𝓝 (ν s))) {C : ℝ}
    (hb : ∀ n m, |y n (.lead m)| ≤ C * (α / (1 - α)) ^ m) (g : State → ℝ) {G : ℝ}
    (hg : ∀ m, |g (.lead m)| ≤ G) :
    Tendsto (fun n => stateSum (fun s => y n s * g s)) atTop
      (𝓝 (stateSum (fun s => ν s * g s))) := by
  unfold stateSum
  refine (((hy .zero).mul_const _).add ((hy .tie).mul_const _)).add ?_
  refine tendsto_tsum_of_dominated_convergence (bound := fun m => C * (α / (1 - α)) ^ m * G)
    (((summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_left C).mul_right G)
    (fun m => (hy (.lead m)).mul_const _) (Eventually.of_forall fun n m => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hb n m) (hg m) (abs_nonneg _) ((abs_nonneg _).trans (hb n m))

private theorem cesaro_zero_abs_le {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (n m : ℕ) :
    |cesaro α γ (delta .zero) n (.lead m)| ≤ 1 * (α / (1 - α)) ^ m := by
  rw [abs_of_nonneg (cesaro_nonneg h0 h1 (isDist_delta _) n _), one_mul]
  exact cesaro_le (pow_nonneg (ratio_nonneg h0 h1) m) (fun k => distN_zero_lead_le α γ h0 h1 k m) n

private theorem distN_zero_mul_summable {α γ : ℝ} (h0 : 0 < α) (h1 : α < 1 / 2) (k : ℕ)
    {g : State → ℝ} (hg : ∀ m, 0 ≤ g (.lead m) ∧ g (.lead m) ≤ 2) :
    Summable (fun m : ℕ => distN α γ (delta .zero) k (.lead m) * g (.lead m)) := by
  refine Summable.of_nonneg_of_le (fun m => mul_nonneg
    ((isDist_distN α γ h0 h1 _ (isDist_delta _) k).nonneg _) (hg m).1) (fun m => ?_)
    ((summable_geometric_of_lt_one (ratio_nonneg h0 h1) (ratio_lt_one h1)).mul_right 2)
  exact mul_le_mul (distN_zero_lead_le α γ h0 h1 k m) (hg m).2 (hg m).1
    (pow_nonneg (ratio_nonneg h0 h1) m)

/-- The time-averaged honest gain is the expected honest gain under the Cesàro average. -/
theorem solution (α γ : ℝ) (h0 : 0 < α) (h1 : α < 1 / 2) (n : ℕ) :
    BitcoinSelfishErgodic.avgOthersGain α γ n =
      BitcoinSelfishErgodic.expOthersGain α γ
        (BitcoinSelfishErgodic.cesaro α γ (BitcoinSelfishErgodic.delta .zero) n) := by
  unfold avgOthersGain expOthersGain
  have e : (fun s => cesaro α γ (delta .zero) n s * othersExpGain α γ s) =
      fun s => (1 / (n : ℝ)) * ∑ k ∈ Finset.range n,
        (distN α γ (delta .zero) k s * othersExpGain α γ s) := by
    funext s; unfold cesaro; rw [mul_assoc, Finset.sum_mul]
  rw [e, stateSum_const_mul,
    stateSum_finsetSum (f := fun k s => distN α γ (delta .zero) k s * othersExpGain α γ s)
      (fun k _ => distN_zero_mul_summable h0 h1 k (othersExpGain_lead_bound α γ))]
