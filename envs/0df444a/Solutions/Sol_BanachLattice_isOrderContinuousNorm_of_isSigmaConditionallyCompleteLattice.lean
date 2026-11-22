-- Prove2me | solution 1 for BanachLattice.isOrderContinuousNorm_of_isSigmaConditionallyCompleteLattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:27.517527+00:00
-- url     : https://prove2.me/submissions/1f21185f-6433-4dbd-a074-f62f1f92ac69

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Basic
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Theorems.Thm_IsSigmaOrderContinuousNorm_tendsto_of_antitone_isGLB

section
@[expose] public section
namespace BanachLattice
section Forward
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
  [BanachLattice X]
end Forward
section Sigma
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable [BanachLattice X]
end Sigma
section Backward
variable {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X] [IsSigmaOrderContinuousNorm X]
private lemma tendsto_antitone_seq_of_bddBelow
    {z : ℕ → X} (hanti : Antitone z) (hbdd : BddBelow (Set.range z)) :
    ∃ v, IsGLB (Set.range z) v ∧ Filter.Tendsto z Filter.atTop (nhds v) := by
  have hcount : (Set.range z).Countable := Set.countable_range _
  have hne : (Set.range z).Nonempty := Set.range_nonempty _
  have hglb : IsGLB (Set.range z) (sInf (Set.range z)) :=
    ⟨fun _ hy => SigmaConditionallyCompleteLattice.csInf_le _ _ hcount hbdd hy,
     fun _ hy => SigmaConditionallyCompleteLattice.le_csInf _ _ hcount hne hy⟩
  exact ⟨_, hglb, IsSigmaOrderContinuousNorm.tendsto_of_antitone_isGLB hanti hglb⟩
private lemma cauchySeq_of_directed_dist {ι : Type*} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {Y : Type*} [PseudoMetricSpace Y]
    (y : ι → Y)
    (h : ∀ ε > 0, ∃ α₀, ∀ α ≥ α₀, ∀ β ≥ α₀, dist (y α) (y β) < ε) :
    CauchySeq y := by
  rw [CauchySeq, Metric.cauchy_iff]
  refine ⟨Filter.map_neBot, fun ε hε => ?_⟩
  obtain ⟨α₀, hα₀⟩ := h ε hε
  refine ⟨y '' {α | α₀ ≤ α}, ?_, ?_⟩
  · exact Filter.image_mem_map (Filter.mem_atTop α₀)
  · rintro _ ⟨α, hα, rfl⟩ _ ⟨β, hβ, rfl⟩
    exact hα₀ α hα β hβ
end Backward
end BanachLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
open BanachLattice
variable {X : Type*} [NormedAddCommGroup X] [SigmaConditionallyCompleteLattice X]
  [IsOrderedAddMonoid X] [BanachLattice X] [IsSigmaOrderContinuousNorm X]
namespace BanachLattice
theorem _root_.solution :
    IsOrderContinuousNorm X := by
  classical
  refine ⟨fun {ι} _ _ _ {y} hanti hnn hglb => ?_⟩
  -- Once `y` is Cauchy, completeness gives a limit, which is the order GLB.
  suffices hcauchy : CauchySeq y by
    obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hwglb : IsGLB (Set.range y) w := isGLB_of_tendsto_atTop hanti hw
    have hw_eq : w = 0 := hwglb.unique hglb
    rw [hw_eq] at hw
    exact hw
  -- For Cauchy: assume not, derive a "bad gap" for every starting point.
  refine cauchySeq_of_directed_dist y (fun ε hε => ?_)
  by_contra hcon
  push Not at hcon
  -- For every α₀, ∃ α₀ ≤ α ≤ γ with ‖y α - y γ‖ ≥ ε/2.
  have hbad : ∀ α₀ : ι, ∃ p : ι × ι, α₀ ≤ p.1 ∧ p.1 ≤ p.2 ∧ ε / 2 ≤ ‖y p.1 - y p.2‖ := by
    intro α₀
    obtain ⟨α, hα, β, hβ, hdist⟩ := hcon α₀
    obtain ⟨γ, hγα, hγβ⟩ := exists_ge_ge α β
    have h1 : ‖y α - y γ‖ + ‖y β - y γ‖ ≥ ε := by
      have htr := dist_triangle (y α) (y γ) (y β)
      rw [dist_comm (y γ) (y β)] at htr
      simp only [dist_eq_norm] at htr hdist
      linarith
    by_cases hαbad : ε / 2 ≤ ‖y α - y γ‖
    · exact ⟨(α, γ), hα, hγα, hαbad⟩
    · push Not at hαbad
      exact ⟨(β, γ), hβ, hγβ, by linarith⟩
  -- Define the recursive choice function and the resulting subsequence.
  let step : ι → ι × ι := fun α₀ => (hbad α₀).choose
  have hstep : ∀ α₀ : ι, α₀ ≤ (step α₀).1 ∧ (step α₀).1 ≤ (step α₀).2 ∧
      ε / 2 ≤ ‖y (step α₀).1 - y (step α₀).2‖ := fun α₀ => (hbad α₀).choose_spec
  -- Build the recursive pair-valued sequence g : ℕ → ι × ι.
  let g : ℕ → ι × ι := fun n => Nat.rec (step Classical.ofNonempty)
    (fun _ p => step p.2) n
  have hg_succ : ∀ n, g (n + 1) = step (g n).2 := fun _ => rfl
  have hg_le : ∀ n, (g n).1 ≤ (g n).2 := fun n => by
    induction n with
    | zero => exact (hstep _).2.1
    | succ k _ => rw [hg_succ]; exact (hstep _).2.1
  have hg_step : ∀ n, (g n).2 ≤ (g (n + 1)).1 := fun n => by
    rw [hg_succ]; exact (hstep _).1
  have hg_dist : ∀ n, ε / 2 ≤ ‖y (g n).1 - y (g n).2‖ := fun n => by
    induction n with
    | zero => exact (hstep _).2.2
    | succ k _ => rw [hg_succ]; exact (hstep _).2.2
  -- The interleaved sequence z : ℕ → X.
  let z : ℕ → X := fun k => if k % 2 = 0 then y (g (k / 2)).1 else y (g (k / 2)).2
  have hz_anti : Antitone z := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · subst hm
      have e1 : (m + m) % 2 = 0 := by omega
      have e2 : (m + m + 1) % 2 = 1 := by omega
      have e3 : (m + m) / 2 = m := by omega
      have e4 : (m + m + 1) / 2 = m := by omega
      simp only [z, e1, e2, e3, e4, ↓reduceIte]
      exact hanti (hg_le m)
    · subst hm
      have e1 : (2 * m + 1) % 2 = 1 := by omega
      have e2 : (2 * m + 1 + 1) % 2 = 0 := by omega
      have e3 : (2 * m + 1) / 2 = m := by omega
      have e4 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      simp only [z, e1, e2, e3, e4, ↓reduceIte]
      exact hanti (hg_step m)
  have hz_nn : ∀ k, 0 ≤ z k := by
    intro k; simp only [z]; split <;> exact hnn _
  have hz_bdd : BddBelow (Set.range z) := ⟨0, by rintro _ ⟨k, rfl⟩; exact hz_nn k⟩
  -- By σ-CCL + σ-OCN, z is Cauchy.
  obtain ⟨_, _, hzv⟩ := tendsto_antitone_seq_of_bddBelow hz_anti hz_bdd
  have hzcauchy : CauchySeq z := hzv.cauchySeq
  rw [Metric.cauchySeq_iff] at hzcauchy
  obtain ⟨N, hN⟩ := hzcauchy (ε / 2) (by linarith)
  -- The pair (2N, 2N+1) violates Cauchy by hg_dist.
  have hN1 : 2 * N ≥ N := by omega
  have hN2 : 2 * N + 1 ≥ N := by omega
  have hdN := hN (2 * N) hN1 (2 * N + 1) hN2
  have hh1 : (2 * N) % 2 = 0 := by omega
  have hh2 : (2 * N + 1) % 2 = 1 := by omega
  have hh3 : (2 * N) / 2 = N := by omega
  have hh4 : (2 * N + 1) / 2 = N := by omega
  simp only [z, hh1, hh2, hh3, hh4, ↓reduceIte, one_ne_zero] at hdN
  rw [dist_eq_norm] at hdN
  linarith [hg_dist N]
end BanachLattice
