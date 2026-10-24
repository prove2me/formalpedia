-- Prove2me | solution 1 for CommitteeVoting.ExpConv.eq_82
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:43:31.272291+00:00
-- url     : https://prove2.me/submissions/3595b353-2517-49a1-9509-e9a42564dfb7

import Mathlib
import Definitions.Def_CommitteeVoting_ExpConv_Committee
import Definitions.Def_CommitteeVoting_ExpConv_VoteProb

open MeasureTheory ProbabilityTheory

namespace CVEC82

/-- Hoeffding for independent `[0,1]`-valued variables, centered sum, non-strict upper tail. -/
lemma hoeff01 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (Z : Fin n → Ω → ℝ) (hZm : ∀ i, Measurable (Z i)) (hind : iIndepFun Z P)
    (h01 : ∀ i ω, Z i ω ∈ Set.Icc (0:ℝ) 1) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ ∑ i, (Z i ω - ∫ x, Z i x ∂P)} ≤ Real.exp (-(2 * ε ^ 2 / n)) := by
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasSubgaussianMGF (fun ω => Z i ω - ∫ x, Z i x ∂P) ((‖(1:ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro i _
    exact hasSubgaussianMGF_of_mem_Icc (hZm i).aemeasurable (ae_of_all _ (h01 i))
  have hind' : iIndepFun (fun i ω => Z i ω - ∫ x, Z i x ∂P) P :=
    hind.comp (fun i x => x - ∫ y, Z i y ∂P) (fun i => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind' hsub hε
  refine h.trans (le_of_eq ?_)
  congr 1
  have : ((∑ _i : Fin n, ((‖(1:ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : NNReal) : ℝ) = n / 4 := by
    push_cast
    simp [Finset.sum_const, Finset.card_univ]
    ring
  rw [this]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have : (n:ℝ) ≠ 0 := by positivity
    field_simp
    ring

end CVEC82

open CVEC82 CommitteeVoting.ExpConv
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n m : ℕ} (ballot : Fin n → Ω → Fin m → Bool) (hmeas : ∀ i, Measurable (ballot i))
    (hind : iIndepFun ballot P) (jh jm : Fin m) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i i' : Fin n, CommitteeVoting.ExpConv.voteProb P ballot i' jm + δ ≤
      CommitteeVoting.ExpConv.voteProb P ballot i jh) :
    P.real {ω | CommitteeVoting.ExpConv.score (fun i => ballot i ω) jh ≤
        CommitteeVoting.ExpConv.score (fun i => ballot i ω) jm}
      ≤ 2 * Real.exp (-(δ ^ 2 * n / 2)) := by
  -- indicator variables
  set Y : Fin m → Fin n → Ω → ℝ := fun j i ω => if ballot i ω j = true then 1 else 0 with hY
  have hYm : ∀ j i, Measurable (Y j i) := by
    intro j i
    have h1 : Measurable (fun ω => ballot i ω j) := (measurable_pi_apply j).comp (hmeas i)
    exact Measurable.ite (measurableSet_eq_fun h1 measurable_const) measurable_const
      measurable_const
  have hYind : ∀ j, iIndepFun (Y j) P := by
    intro j
    refine hind.comp (fun i (b : Fin m → Bool) => if b j = true then (1:ℝ) else 0) (fun i => ?_)
    exact Measurable.ite (measurableSet_eq_fun (measurable_pi_apply j) measurable_const)
      measurable_const measurable_const
  have hYint : ∀ j i, ∫ x, Y j i x ∂P = voteProb P ballot i j := by
    intro j i
    have hs : MeasurableSet {ω | ballot i ω j = true} :=
      measurableSet_eq_fun ((measurable_pi_apply j).comp (hmeas i)) measurable_const
    simp only [hY, voteProb]
    rw [show (fun x => if ballot i x j = true then (1:ℝ) else 0)
        = Set.indicator {ω | ballot i ω j = true} (fun _ => (1:ℝ)) by
          ext x; simp [Set.indicator]]
    rw [integral_indicator hs]
    simp
  have hscore : ∀ (ω : Ω) j, (score (fun i => ballot i ω) j : ℝ) = ∑ i, Y j i ω := by
    intro ω j
    simp only [score, hY]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  have hε : 0 ≤ (n:ℝ) * δ / 2 := by positivity
  -- upper tail of jm
  have hA := hoeff01 P (Y jm) (hYm jm) (hYind jm)
    (fun i ω => by simp only [hY]; split_ifs <;> simp) hε
  -- lower tail of jh via 1 - Y
  set W : Fin n → Ω → ℝ := fun i ω => 1 - Y jh i ω with hW
  have hWind : iIndepFun W P :=
    (hYind jh).comp (fun _ x => 1 - x) (fun _ => by fun_prop)
  have hB := hoeff01 P W (fun i => measurable_const.sub (hYm jh i)) hWind
    (fun i ω => by simp only [hW, hY]; split_ifs <;> simp) hε
  have hWint : ∀ i, ∫ x, W i x ∂P = 1 - voteProb P ballot i jh := by
    intro i
    simp only [hW]
    rw [integral_sub (integrable_const _), integral_const, hYint]
    · simp
    · exact Integrable.of_mem_Icc 0 1 (hYm jh i).aemeasurable
        (ae_of_all _ (fun ω => by simp only [hY]; split_ifs <;> simp))
  have hexp : Real.exp (-(2 * ((n:ℝ) * δ / 2) ^ 2 / n)) = Real.exp (-(δ ^ 2 * n / 2)) := by
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have : (n:ℝ) ≠ 0 := by positivity
      field_simp
  rw [hexp] at hA hB
  -- inclusion
  have hsumgap : ∑ i, voteProb P ballot i jm + n * δ ≤ ∑ i, voteProb P ballot i jh := by
    have : ∑ i : Fin n, (voteProb P ballot i jm + δ) ≤ ∑ i, voteProb P ballot i jh :=
      Finset.sum_le_sum (fun i _ => hgap i i)
    rw [Finset.sum_add_distrib] at this
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using this
  have hsub : {ω | score (fun i => ballot i ω) jh ≤ score (fun i => ballot i ω) jm} ⊆
      {ω | (n:ℝ) * δ / 2 ≤ ∑ i, (Y jm i ω - ∫ x, Y jm i x ∂P)} ∪
      {ω | (n:ℝ) * δ / 2 ≤ ∑ i, (W i ω - ∫ x, W i x ∂P)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    have hω' : (score (fun i => ballot i ω) jh : ℝ) ≤ score (fun i => ballot i ω) jm := by
      exact_mod_cast hω
    rw [hscore, hscore] at hω'
    simp only [Set.mem_union, Set.mem_setOf_eq, hYint, hWint, Finset.sum_sub_distrib]
    simp only [hW, Finset.sum_sub_distrib] at *
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    linarith
  calc P.real {ω | score (fun i => ballot i ω) jh ≤ score (fun i => ballot i ω) jm}
      ≤ P.real ({ω | (n:ℝ) * δ / 2 ≤ ∑ i, (Y jm i ω - ∫ x, Y jm i x ∂P)} ∪
      {ω | (n:ℝ) * δ / 2 ≤ ∑ i, (W i ω - ∫ x, W i x ∂P)}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ Real.exp (-(δ ^ 2 * n / 2)) + Real.exp (-(δ ^ 2 * n / 2)) := add_le_add hA hB
    _ = 2 * Real.exp (-(δ ^ 2 * n / 2)) := by ring
