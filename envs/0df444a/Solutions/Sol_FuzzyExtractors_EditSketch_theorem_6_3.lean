-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.theorem_6_3
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T15:24:21.547282+00:00
-- url     : https://prove2.me/submissions/9abdf53d-d9e0-44a0-a8c9-976cc96b51ae

import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace Recovery

open FuzzyExtractors.EditSketch

private theorem bch_injective {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (δ : ℕ) (M M' : Finset Kˣ) (hM : M.card ≤ (δ - 1) / 2) (hM' : M'.card ≤ (δ - 1) / 2)
    (hsyn : ∀ i : ℕ, 1 ≤ i → i ≤ δ - 1 → syn i M = syn i M') :
    M = M' := by
  classical
  let s := M ∪ M'
  let e : Fin s.card ≃ s := (Finset.equivFin s).symm
  let f : Fin s.card → K := fun j => (e j : Kˣ)
  let a : Kˣ → K := fun x => (if x ∈ M then 1 else 0) - (if x ∈ M' then 1 else 0)
  let b : Fin s.card → K := fun j => a (e j) * f j
  have hf : Function.Injective f := by
    intro j k h
    apply e.injective
    apply Subtype.ext
    exact Units.val_injective h
  have hs : s.card ≤ δ - 1 := by
    dsimp [s]
    have := Finset.card_union_le M M'
    omega
  have sum_a (k : ℕ) : (∑ x ∈ s, a x * (x : K) ^ k) = syn k M - syn k M' := by
    simp only [a, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    have h1 : s.filter (fun x => x ∈ M) = M := by ext x; simp [s]
    have h2 : s.filter (fun x => x ∈ M') = M' := by ext x; simp [s]
    rw [h1, h2]
    rfl
  have hb : b = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro k
    have hh := hsyn (k.val + 1) (by omega) (by omega)
    have hz := sum_a (k.val + 1)
    rw [hh, sub_self] at hz
    calc
      (∑ j : Fin s.card, b j * f j ^ k.val) =
          ∑ j : Fin s.card, a (e j) * (f j) ^ (k.val + 1) := by
        apply Finset.sum_congr rfl
        intro j _
        dsimp [b]
        rw [pow_succ]
        ring
      _ = ∑ x ∈ s, a x * (x : K) ^ (k.val + 1) := by
        rw [← Finset.sum_coe_sort s]
        exact e.sum_comp (fun x : s => a x * ((x : Kˣ) : K) ^ (k.val + 1))
      _ = 0 := hz
  apply Finset.ext
  intro x
  by_cases hx : x ∈ s
  · have hz := congrFun hb (e.symm ⟨x, hx⟩)
    have ha : a x = 0 := by
      have : a x * (x : K) = 0 := by simpa [b, f] using hz
      exact (mul_eq_zero.mp this).resolve_right x.ne_zero
    by_cases h1 : x ∈ M <;> by_cases h2 : x ∈ M' <;> simp_all [a]
  · have hxm : x ∉ M := fun h => hx (Finset.mem_union_left _ h)
    have hxm' : x ∉ M' := fun h => hx (Finset.mem_union_right _ h)
    simp [hxm, hxm']


private theorem syn_sq {K : Type} [Field K] [CharP K 2] (s : Finset Kˣ) (i : ℕ) :
    syn (2*i) s = syn i s ^ 2 := by
  classical
  unfold syn
  rw [sum_pow_char]
  apply Finset.sum_congr rfl
  intro x hx
  rw [← pow_mul, Nat.mul_comm]

private theorem syn_diff {K : Type} [Field K] [DecidableEq K] [CharP K 2]
    (w w' : Finset Kˣ) (k : ℕ) : syn k (symmDiff w w') = syn k w' - syn k w := by
  classical
  have hdis : Disjoint (w \ w') (w' \ w) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_sdiff.mp hx').1
  have hw := Finset.sum_sdiff (f := fun x : Kˣ => (x : K)^k) (Finset.inter_subset_left (s₁ := w) (s₂ := w'))
  have hw' := Finset.sum_sdiff (f := fun x : Kˣ => (x : K)^k) (Finset.inter_subset_right (s₁ := w) (s₂ := w'))
  simp only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] at hw hw'
  unfold syn
  rw [Finset.symmDiff_def, Finset.sum_union hdis, CharTwo.sub_eq_add]
  have hz := CharTwo.add_self_eq_zero (∑ x ∈ w ∩ w', (x : K)^k)
  linear_combination hw + hw' - hz

theorem solution {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2] (t : ℕ) (w w' v : Finset Kˣ) (hdis : symmDiffDis w w' ≤ t) (hv : v.card ≤ t)
    (hsyn : ∀ j : Fin t,
      syn (2 * (j : ℕ) + 1) v = syn (2 * (j : ℕ) + 1) w' - syn (2 * (j : ℕ) + 1) w) :
    v = symmDiff w w' := by
  have hodd : ∀ j : Fin t, syn (2 * (j : ℕ) + 1) v =
      syn (2 * (j : ℕ) + 1) (symmDiff w w') := by
    intro j
    rw [hsyn, syn_diff]
  apply bch_injective (2*t+1) v (symmDiff w w') (by simpa using hv)
    (by simpa [symmDiffDis] using hdis)
  intro k hk hkt
  have hall : ∀ k : ℕ, 1 ≤ k → k ≤ 2*t →
      syn k v = syn k (symmDiff w w') := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk hkt
      by_cases he : k % 2 = 0
      · have hhalf : 1 ≤ k/2 := by omega
        have hrec := ih (k/2) (by omega) hhalf (by omega)
        have heq : k = 2*(k/2) := by omega
        rw [heq, syn_sq, syn_sq, hrec]
      · have heq : k = 2*(k/2)+1 := by omega
        have hj : k/2 < t := by omega
        rw [heq]
        exact hodd ⟨k/2,hj⟩
  exact hall k hk (by omega)

#print axioms solution

theorem correct {K : Type} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]
    (t : ℕ) : FuzzyExtractors.Hamming.SketchCorrect (symmDiffDis (U := Kˣ)) t
      (pinSS (K := K) t) (pinRec t) := by
  classical
  intro w w' hdis s hs
  have hs' : s = (fun j : Fin t => syn (2 * (j : ℕ) + 1) w) := by
    simpa [pinSS] using hs
  subst s
  have he : ∃ v : Finset Kˣ, v.card ≤ t ∧ ∀ j : Fin t,
      syn (2 * (j : ℕ) + 1) v = syn (2 * (j : ℕ) + 1) w' -
        (fun j : Fin t => syn (2 * (j : ℕ) + 1) w) j :=
    ⟨symmDiff w w', hdis, fun j => syn_diff w w' _⟩
  unfold pinRec
  rw [dif_pos he]
  have hv := Classical.choose_spec he
  rw [solution t w w' (Classical.choose he) hdis hv.1 hv.2]
  congr 1
  simp [symmDiff_comm w w']
end Recovery

namespace Entropy
set_option autoImplicit false
open FuzzyExtractors.Hamming
open scoped ENNReal

lemma ss_withSketchAux_apply {M S ι : Type} (SS : M → PMF S) (WI : PMF (M × ι))
    (w : M) (s : S) (i : ι) :
    withSketchAux SS WI (w, (s, i)) = WI (w, i) * SS w s := by
  unfold withSketchAux
  rw [PMF.bind_apply, tsum_eq_single (w, i)]
  · rw [PMF.map_apply, tsum_eq_single s]
    · simp
    · intro s' hs'
      have : ¬ ((w, (s, i)) = (w, (s', i))) := by
        intro h
        have h' : s = s' := by simpa using h
        exact hs' h'.symm
      simp [this]
  · intro p hp
    rw [PMF.map_apply]
    have : ∀ s', ¬ ((w, (s, i)) = (p.1, (s', p.2))) := by
      intro s' h
      apply hp
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1.symm h.2.2.symm
    simp [this]

theorem solution {M S : Type} (dis : M → M → ℕ) (t : ℕ)
    (SS : M → PMF S) (Rec : M → S → PMF M) (hcorr : SketchCorrect dis t SS Rec) (lam : ℝ)
    (hrange : ∃ T : Finset S, (T.card : ℝ) ≤ (2 : ℝ) ^ lam ∧ ∀ w, (SS w).support ⊆ (T : Set S)) :
    ∀ m : ℝ, IsAvgSecureSketch dis m (m - lam) t SS Rec := by
  intro m
  refine ⟨hcorr, ?_⟩
  intro ι WI hm
  obtain ⟨T, hTcard, hT⟩ := hrange
  classical
  set A : ℝ≥0∞ := ∑' i : ι, ⨆ w : M, WI (w, i) with hA
  set A' : ℝ≥0∞ := ∑' x : S × ι, ⨆ w : M, withSketchAux SS WI (w, x) with hA'
  have hAeq : avgMinEntropy WI = -Real.logb 2 A.toReal := rfl
  have hA'eq : avgMinEntropy (withSketchAux SS WI) = -Real.logb 2 A'.toReal := rfl
  -- A ≤ 1
  have hA1 : A ≤ 1 := by
    calc A ≤ ∑' i : ι, ∑' w : M, WI (w, i) := by
          refine ENNReal.tsum_le_tsum fun i => iSup_le fun w => ?_
          exact ENNReal.le_tsum (f := fun w => WI (w, i)) w
      _ = ∑' p : M × ι, WI p := by
          rw [ENNReal.tsum_comm]
          exact (ENNReal.tsum_prod (f := fun w i => WI (w, i))).symm
      _ = 1 := WI.tsum_coe
  obtain ⟨⟨w0, i0⟩, hp0⟩ := WI.support_nonempty
  have hp0' : WI (w0, i0) ≠ 0 := hp0
  obtain ⟨s0, hs0⟩ := (SS w0).support_nonempty
  have hs0' : SS w0 s0 ≠ 0 := hs0
  have hApos : 0 < A := by
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hp0') ?_
    refine le_trans (le_iSup (fun w => WI (w, i0)) w0) ?_
    exact ENNReal.le_tsum i0
  have hA'pos : 0 < A' := by
    have : withSketchAux SS WI (w0, (s0, i0)) ≠ 0 := by
      rw [ss_withSketchAux_apply]; exact mul_ne_zero hp0' hs0'
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr this) ?_
    refine le_trans (le_iSup (fun w => withSketchAux SS WI (w, (s0, i0))) w0) ?_
    exact ENNReal.le_tsum (f := fun x : S × ι => ⨆ w : M, withSketchAux SS WI (w, x)) (s0, i0)
  -- main bound
  have hbound : A' ≤ (T.card : ℝ≥0∞) * A := by
    have h1 : A' = ∑' s : S, ∑' i : ι, ⨆ w : M, WI (w, i) * SS w s := by
      rw [hA']
      refine Eq.trans (ENNReal.tsum_prod (f := fun s i => ⨆ w : M, withSketchAux SS WI (w, (s, i)))) ?_
      refine tsum_congr fun s => tsum_congr fun i => ?_
      simp_rw [ss_withSketchAux_apply]
    rw [h1]
    have h2 : ∀ s i, (⨆ w : M, WI (w, i) * SS w s) ≤ (if s ∈ T then 1 else 0) * ⨆ w : M, WI (w, i) := by
      intro s i
      refine iSup_le fun w => ?_
      by_cases hs : s ∈ T
      · simp only [hs, if_true, one_mul]
        calc WI (w, i) * SS w s ≤ WI (w, i) * 1 :=
              mul_le_mul' le_rfl (PMF.coe_le_one _ _)
          _ ≤ _ := by rw [mul_one]; exact le_iSup (fun w => WI (w, i)) w
      · have : SS w s = 0 := by
          by_contra h
          exact hs (hT w ((PMF.mem_support_iff _ _).mpr h))
        simp [hs, this]
    calc ∑' s : S, ∑' i : ι, ⨆ w : M, WI (w, i) * SS w s
        ≤ ∑' s : S, ∑' i : ι, (if s ∈ T then 1 else 0) * ⨆ w : M, WI (w, i) :=
          ENNReal.tsum_le_tsum fun s => ENNReal.tsum_le_tsum fun i => h2 s i
      _ = ∑' s : S, (if s ∈ T then 1 else 0) * A := by
          refine tsum_congr fun s => ?_
          rw [ENNReal.tsum_mul_left]
      _ = (T.card : ℝ≥0∞) * A := by
          rw [ENNReal.tsum_mul_right]
          congr 1
          rw [tsum_eq_sum (s := T)]
          · simp
          · intro s hs; simp [hs]
  -- pass to reals
  have hAne : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hA1
  have hAreal_pos : 0 < A.toReal := ENNReal.toReal_pos hApos.ne' hAne
  have hA'ne : A' ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hbound
  have hA'real_pos : 0 < A'.toReal := ENNReal.toReal_pos hA'pos.ne' hA'ne
  have hreal : A'.toReal ≤ (T.card : ℝ) * A.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hAne) hbound
    simpa using this
  rw [hAeq] at hm
  have hAle : A.toReal ≤ (2:ℝ) ^ (-m) := by
    have : Real.logb 2 A.toReal ≤ -m := by linarith
    exact (Real.logb_le_iff_le_rpow (by norm_num) hAreal_pos).mp this
  have hfin : A'.toReal ≤ (2:ℝ) ^ (lam - m) := by
    calc A'.toReal ≤ (T.card : ℝ) * A.toReal := hreal
      _ ≤ (2:ℝ) ^ lam * (2:ℝ) ^ (-m) :=
          mul_le_mul hTcard hAle hAreal_pos.le (by positivity)
      _ = (2:ℝ) ^ (lam - m) := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf
  have : Real.logb 2 A'.toReal ≤ lam - m :=
    (Real.logb_le_iff_le_rpow (by norm_num) hA'real_pos).mpr hfin
  rw [hA'eq]
  linarith

end Entropy

open FuzzyExtractors.EditSketch
theorem solution {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2] (t : ℕ) (m : ℝ) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch (symmDiffDis (U := Kˣ)) m
      (m - (t : ℝ) * Real.logb 2 ((Fintype.card Kˣ : ℝ) + 1)) t
      (pinSS (K := K) t) (pinRec t) := by
  classical
  apply Entropy.solution _ _ _ _ (Recovery.correct t)
  refine ⟨Finset.univ, ?_, by intro w; simp⟩
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  have hc : (Fintype.card Kˣ : ℝ) + 1 = (Fintype.card K : ℝ) := by
    have h := Fintype.card_units (α := K)
    have hk : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast (show Fintype.card Kˣ + 1 = Fintype.card K by omega)
  rw [hc, mul_comm (t : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num) (by norm_num) (by positivity)]
  simp

#print axioms solution
