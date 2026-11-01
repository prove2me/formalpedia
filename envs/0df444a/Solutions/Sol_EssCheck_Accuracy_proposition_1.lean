-- Prove2me | solution 1 for EssCheck.Accuracy.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:57:02.532606+00:00
-- url     : https://prove2.me/submissions/7cfd1851-6b7f-44c5-91bb-da2ef57efa73

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model
import Theorems.Thm_EssCheck_Accuracy_regime_condition
import Theorems.Thm_EssCheck_Accuracy_revenues_foc
import Theorems.Thm_EssCheck_Accuracy_welfare_formula
import Theorems.Thm_EssCheck_Accuracy_lemma_2
import Theorems.Thm_EssCheck_Accuracy_lemma_3

open EssCheck.Accuracy Filter Topology

namespace EssCheckP1Aux

theorem split_sum {n : ℕ} (S : Finset (Fin n)) (f g : Fin n → ℝ) :
    (∑ i ∈ S, f i) + (∑ i ∈ Finset.univ \ S, g i) =
      ∑ i, if i ∈ S then f i else g i := by
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i; simp

/-- Two index sets that agree on all states where `f` or `g` can be nonzero give the same
split sum. -/
theorem split_sum_congr {n : ℕ} (P : Fin n → Prop) (S T : Finset (Fin n))
    (hST : ∀ i, P i → (i ∈ S ↔ i ∈ T)) (f g : Fin n → ℝ)
    (hf : ∀ i, ¬ P i → f i = 0) (hg : ∀ i, ¬ P i → g i = 0) :
    (∑ i ∈ S, f i) + (∑ i ∈ Finset.univ \ S, g i) =
      (∑ i ∈ T, f i) + (∑ i ∈ Finset.univ \ T, g i) := by
  rw [split_sum, split_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hP : P i
  · have := hST i hP
    by_cases hS : i ∈ S
    · have hT : i ∈ T := this.1 hS
      simp [hS, hT]
    · have hT : i ∉ T := fun h => hS (this.2 h)
      simp [hS, hT]
  · rw [hf i hP, hg i hP]; simp

/-- Local constancy of the hybrid set on states of positive probability. -/
theorem hybrid_eventually {n : ℕ} (M : Model n) (hS : M.Standing)
    (β0 : ℝ) (hβ0 : 0 ≤ β0) (hβ1 : β0 < 1) (xs : ℝ → ℝ)
    (heq : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), IsEqEffort M β (xs β))
    (heq0 : IsEqEffort M β0 (xs β0))
    (hcont : ContinuousWithinAt xs (Set.Ici β0) β0)
    (hstrict : ∀ i, (0 < M.pH i ∨ 0 < M.p0 i) → ¬ Eq4 M β0 (xs β0) i) :
    ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), ∀ i, (0 < M.pH i ∨ 0 < M.p0 i) →
      (i ∈ hybridSet M β (xs β) ↔ i ∈ hybridSet M β0 (xs β0)) := by
  have hlt : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), β < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hβ1)
  have hge : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), β0 ≤ β := self_mem_nhdsWithin
  rw [Filter.eventually_all]
  intro i
  by_cases hP : 0 < M.pH i ∨ 0 < M.p0 i
  swap
  · exact Filter.Eventually.of_forall (fun β h => absurd h hP)
  let F : ℝ → ℝ := fun β => (1 - β) * (1 - xs β) * M.p0 i * (M.αbar * M.v i - M.l i) -
    xs β * M.pH i * M.l i
  have hFc : ContinuousWithinAt F (Set.Ici β0) β0 := by
    have h1 : ContinuousWithinAt (fun β : ℝ => β) (Set.Ici β0) β0 := continuousWithinAt_id
    exact ((((continuousWithinAt_const.sub h1).mul (continuousWithinAt_const.sub hcont)).mul
      continuousWithinAt_const).mul continuousWithinAt_const).sub
      ((hcont.mul continuousWithinAt_const).mul continuousWithinAt_const)
  have hF0 : F β0 ≠ 0 := by
    intro h; apply hstrict i hP; unfold Eq4; simp only [F] at h; linarith
  have key : ∀ β, 0 ≤ β → β ≤ 1 → IsEqEffort M β (xs β) →
      (i ∈ hybridSet M β (xs β) ↔ 0 ≤ F β) := by
    intro β h0 h1 he
    have := (regime_condition M hS β (xs β) h0 h1 he.1 he.2.1 i).1
    simp only [hybridSet, Finset.mem_filter, Finset.mem_univ, true_and, F]
    rw [this]; constructor <;> intro h <;> linarith
  have hb0 := key β0 hβ0 hβ1.le heq0
  rcases lt_or_gt_of_ne hF0 with hneg | hpos
  · have hev : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), F β < 0 :=
      hFc.eventually (gt_mem_nhds hneg)
    filter_upwards [hev, heq, hlt, hge] with β hF he hl hg _
    rw [key β (le_trans hβ0 hg) hl.le he, hb0]
    constructor <;> intro h <;> linarith
  · have hev : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), 0 < F β :=
      hFc.eventually (lt_mem_nhds hpos)
    filter_upwards [hev, heq, hlt, hge] with β hF he hl hg _
    rw [key β (le_trans hβ0 hg) hl.le he, hb0]
    constructor <;> intro h <;> linarith

end EssCheckP1Aux

open EssCheckP1Aux in
theorem solution {n : ℕ} (M : Model n) (hS : M.Standing)
    (hα : M.αbar = 1) (β0 : ℝ) (hβ0 : 0 ≤ β0) (hβ1 : β0 < 1)
    (xs : ℝ → ℝ)
    (heq : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), IsEqEffort M β (xs β))
    (heq0 : IsEqEffort M β0 (xs β0))
    (hcont : ContinuousWithinAt xs (Set.Ici β0) β0)
    (hstrict : ∀ i, (0 < M.pH i ∨ 0 < M.p0 i) → ¬ Eq4 M β0 (xs β0) i)
    (hc2 : 0 < iteratedDeriv 2 M.c (xs β0)) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun β => welfare M β (xs β)) d (Set.Ici β0) β0 ∧
      d ≤ 0 := by
  have hS' := hS
  obtain ⟨hpH, -, hp0, -, -, -, -, -, -, hcd, -⟩ := hS'
  set x0 := xs β0 with hx0
  set H := hybridSet M β0 x0 with hH
  -- Lemma 2: right derivative of the equilibrium path
  obtain ⟨hxs, hDpos⟩ := lemma_2 M hS β0 hβ0 hβ1 xs heq heq0 hcont hstrict hc2
  set D := ((∑ i ∈ H, M.p0 i * M.l i) +
      (∑ i ∈ Finset.univ \ H, M.p0 i * (M.αbar * M.v i))) /
        iteratedDeriv 2 M.c x0 with hD
  -- the reduced welfare function (6) with the regime sets frozen at β0
  set SA := (∑ i ∈ H, M.pH i * (M.v i - 2 * zt M i * M.l i *
          (M.αbar * M.v i / (M.αbar * M.v i - M.l i)))) +
        (∑ i ∈ Finset.univ \ H, M.pH i * M.v i) with hSA
  set SB := (∑ i ∈ H, M.p0 i * M.v i) + (∑ i ∈ Finset.univ \ H, M.p0 i * M.v i) with hSB
  let W : ℝ → ℝ := fun x => x * SA + (1 - x) * SB - M.c x
  have hnull : ∀ i, ¬ (0 < M.pH i ∨ 0 < M.p0 i) → M.pH i = 0 ∧ M.p0 i = 0 := by
    intro i h; push Not at h
    exact ⟨le_antisymm h.1 (hpH.1 i), le_antisymm h.2 (hp0.1 i)⟩
  have hloc := hybrid_eventually M hS β0 hβ0 hβ1 xs heq heq0 hcont hstrict
  have hlt : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), β < 1 :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hβ1)
  have hge : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), β0 ≤ β := self_mem_nhdsWithin
  have hW : ∀ᶠ β in nhdsWithin β0 (Set.Ici β0), welfare M β (xs β) = W (xs β) := by
    filter_upwards [hloc, heq, hlt, hge] with β hL he hb hg
    rw [(welfare_formula M hS β (xs β) (le_trans hβ0 hg) hb he.1 he.2.1).2]
    simp only [W]
    rw [split_sum_congr _ _ H hL
        (fun i => M.pH i * (M.v i - 2 * zt M i * M.l i *
          (M.αbar * M.v i / (M.αbar * M.v i - M.l i))))
        (fun i => M.pH i * M.v i) (fun i h => by simp [(hnull i h).1])
        (fun i h => by simp [(hnull i h).1]),
      split_sum_congr _ _ H hL (fun i => M.p0 i * M.v i)
        (fun i => M.p0 i * M.v i) (fun i h => by simp [(hnull i h).2])
        (fun i h => by simp [(hnull i h).2])]
  have hW0 : welfare M β0 (xs β0) = W (xs β0) := hW.self_of_nhdsWithin (Set.mem_Ici.2 le_rfl)
  -- derivative of W at x0
  have hx01 : x0 < 1 := heq0.2.1
  have hc : HasDerivAt M.c (deriv M.c x0) x0 :=
    ((hcd.contDiffAt (isOpen_Iio.mem_nhds hx01)).differentiableAt (by norm_num)).hasDerivAt
  have hWd : HasDerivAt W (SA - SB - deriv M.c x0) x0 := by
    have h1 : HasDerivAt (fun x : ℝ => x * SA + (1 - x) * SB - M.c x)
        (1 * SA + (0 - 1) * SB - deriv M.c x0) x0 :=
      (((hasDerivAt_id' x0).mul_const SA).add
        (((hasDerivAt_const x0 (1 : ℝ)).sub (hasDerivAt_id' x0)).mul_const SB)).sub hc
    have he : SA - SB - deriv M.c x0 = 1 * SA + (0 - 1) * SB - deriv M.c x0 := by ring
    rw [he]; exact h1
  have hcomp := (hWd.comp_hasDerivWithinAt β0 hxs).congr_of_eventuallyEq hW hW0
  refine ⟨_, hcomp, ?_⟩
  -- sign: Lemma 3 and the private first-order condition at β0
  have hfoc0 : deriv M.c x0 = privateWedge M H β0 := by
    rw [← heq0.2.2, (revenues_foc M hS β0 x0 hβ0 hβ1.le heq0.1 heq0.2.1).2.2]
  have h3 := lemma_3 M hS hα β0 hβ0 hβ1.le H
  have hsw : socialWedge M H = SA - SB := by
    simp only [socialWedge, hSA, hSB]
  have hneg : SA - SB - deriv M.c x0 ≤ 0 := by
    rw [hfoc0, ← hsw]; linarith
  exact mul_nonpos_of_nonpos_of_nonneg hneg hDpos.le
