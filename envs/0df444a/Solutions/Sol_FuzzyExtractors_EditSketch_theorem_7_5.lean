-- Prove2me | solution 1 for FuzzyExtractors.EditSketch.theorem_7_5
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-23T17:37:12.619595+00:00
-- url     : https://prove2.me/submissions/f156f62b-147e-4479-a6e9-bf3e191238d2

import Init
import Mathlib
import Definitions.Def_FuzzyExtractors_EditSketch_Basic

namespace PinProof
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

end PinProof

namespace EmbedProof
open FuzzyExtractors.EditSketch
namespace ShingleSupport

theorem at_mem {𝓕 : Type} [Fintype 𝓕] [Inhabited 𝓕] (c : ℕ) (w : List 𝓕)
    (i : ℕ) (hi : i + c ≤ w.length) : shingleAt c w i ∈ shingles c w := by
  classical
  simp only [shingles, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨i, fun k => ?_⟩
  have hk : i + (k : ℕ) < w.length := by omega
  simp [shingleAt, List.getElem?_eq_getElem hk]

theorem card_le {𝓕 : Type} [Fintype 𝓕] [Inhabited 𝓕] (c : ℕ) (w : List 𝓕)
    (hc : 1 ≤ c) : (shingles c w).card ≤ w.length - c + 1 := by
  classical
  have hsub : shingles c w ⊆ (Finset.range (w.length - c + 1)).image (shingleAt c w) := by
    intro u hu
    simp only [shingles, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    obtain ⟨i, hi⟩ := hu
    have hlast := (List.getElem?_eq_some_iff.mp (hi ⟨c-1, by omega⟩)).1
    have hib : i < w.length - c + 1 := by dsimp only at hlast; omega
    refine Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hib, ?_⟩
    funext k
    obtain ⟨hk, heq⟩ := List.getElem?_eq_some_iff.mp (hi k)
    simpa [shingleAt, List.getElem?_eq_getElem hk] using heq
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))

theorem gc_lt {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (c n : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) (w : EditSpace 𝓕 n)
    (j : Fin ⌈(n : ℝ) / c⌉₊) : gc c w j < n - c + 1 := by
  classical
  have hi : min ((j : ℕ) * c) (n-c) + c ≤ w.1.length := by
    have h := min_le_right ((j : ℕ) * c) (n-c)
    rw [w.2]
    omega
  have hm := at_mem c w.1 (min ((j : ℕ) * c) (n-c)) hi
  have hlt : gc c w j < (shingles c w.1).card := by
    apply Finset.card_lt_card
    exact Finset.filter_ssubset.mpr ⟨_, hm, lt_irrefl _⟩
  exact hlt.trans_le (by simpa [w.2] using card_le c w.1 hc)

theorem recovery_range {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    ∃ T : Finset (Fin ⌈(n : ℝ) / c⌉₊ → ℕ),
      (T.card : ℝ) ≤ (2 : ℝ) ^ ((⌈(n : ℝ) / c⌉₊ : ℝ) *
        Real.logb 2 ((n : ℝ) - c + 1)) ∧ ∀ w : EditSpace 𝓕 n, gc c w ∈ T := by
  classical
  let f : (Fin ⌈(n : ℝ) / c⌉₊ → Fin (n-c+1)) → (Fin ⌈(n : ℝ) / c⌉₊ → ℕ) :=
    fun v j => (v j : ℕ)
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · have h := Finset.card_image_le (s := Finset.univ) (f := f)
    have hp : (n : ℝ) - c + 1 > 0 := by
      have h : (c : ℝ) ≤ n := by exact_mod_cast hcn
      linarith
    rw [mul_comm _ (Real.logb _ _), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hp]
    have hcast : ((n-c+1 : ℕ) : ℝ) = (n : ℝ) - c + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hcn, Nat.cast_one]
    calc
      ((Finset.univ.image f).card : ℝ) ≤ ((n-c+1)^⌈(n : ℝ) / c⌉₊ : ℕ) := by
        exact_mod_cast (by simpa using h)
      _ = ((n : ℝ) - c + 1) ^ (⌈(n : ℝ) / c⌉₊ : ℝ) := by simp [hcast]
  · intro w
    refine Finset.mem_image.mpr ⟨(fun j => ⟨gc c w j, gc_lt c n hc hcn w j⟩), by simp, rfl⟩

theorem rank_inj {α : Type*} [LinearOrder α] (s : Finset α) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s)
    (he : (s.filter (· < a)).card = (s.filter (· < b)).card) : a = b := by
  classical
  have hlt {x y : α} (hx : x ∈ s) (hxy : x < y) :
      (s.filter (· < x)).card < (s.filter (· < y)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro z hz
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
        ((Finset.mem_filter.mp hz).2).trans hxy⟩
    · intro heq
      have hmem : x ∈ s.filter (· < y) := Finset.mem_filter.mpr ⟨hx,hxy⟩
      rw [← heq] at hmem
      exact (lt_irrefl x) (Finset.mem_filter.mp hmem).2
  rcases lt_trichotomy a b with h | h | h
  · have := hlt ha h; omega
  · exact h
  · have := hlt hb h; omega

theorem recovery_injective {𝓕 : Type} [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    Function.Injective (fun w : EditSpace 𝓕 n => (shingles c w.1, gc c w)) := by
  classical
  intro w v h
  have hs := congrArg Prod.fst h
  change shingles c w.1 = shingles c v.1 at hs
  have hg := congrArg Prod.snd h
  change gc c w = gc c v at hg
  have hb (j : Fin ⌈(n : ℝ) / c⌉₊) :
      shingleAt c w.1 (min ((j : ℕ)*c) (n-c)) =
      shingleAt c v.1 (min ((j : ℕ)*c) (n-c)) := by
    have hi : min ((j : ℕ)*c) (n-c) + c ≤ n := by
      have := min_le_right ((j : ℕ)*c) (n-c); omega
    have hw := at_mem c w.1 _ (by simpa [w.2] using hi)
    have hv := at_mem c v.1 _ (by simpa [v.2] using hi)
    have he := congrFun hg j
    change ((shingles c w.1).filter _).card = ((shingles c v.1).filter _).card at he
    rw [← hs] at hv he
    have hlt (x y : Fin c → 𝓕) (hx : x ∈ shingles c w.1) (hxy : toLex x < toLex y) :
        ((shingles c w.1).filter (fun u => toLex u < toLex x)).card <
        ((shingles c w.1).filter (fun u => toLex u < toLex y)).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro z hz
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
          ((Finset.mem_filter.mp hz).2).trans hxy⟩
      · intro heq
        have hmem : x ∈ (shingles c w.1).filter (fun u => toLex u < toLex y) :=
          Finset.mem_filter.mpr ⟨hx,hxy⟩
        rw [← heq] at hmem
        exact (lt_irrefl _) (Finset.mem_filter.mp hmem).2
    rcases lt_trichotomy (toLex (shingleAt c w.1 (min ((j : ℕ)*c) (n-c))))
        (toLex (shingleAt c v.1 (min ((j : ℕ)*c) (n-c)))) with h | h | h
    · have := hlt _ _ hw h; omega
    · exact toLex.injective h
    · have := hlt _ _ hv h; omega
  apply Subtype.ext
  apply List.ext_getElem (by simp [w.2,v.2])
  intro k hkw hkv
  have hkn : k < n := by simpa [w.2] using hkw
  have hjc := Nat.div_mul_le_self k c
  have hj : k/c < ⌈(n : ℝ)/c⌉₊ := by
    apply Nat.lt_ceil.mpr
    apply (lt_div_iff₀ (by exact_mod_cast (show 0 < c by omega))).mpr
    exact_mod_cast (lt_of_le_of_lt hjc hkn)
  have hkc : k < (k/c)*c+c := by
    have hm := Nat.mod_lt k (show 0 < c by omega)
    have he := Nat.mod_add_div k c
    rw [Nat.mul_comm c (k/c)] at he
    omega
  let i := min ((k/c)*c) (n-c)
  have hik : i ≤ k := (min_le_left _ _).trans hjc
  have hki : k-i < c := by
    dsimp [i]
    rcases le_total ((k/c)*c) (n-c) with hi | hi
    · rw [min_eq_left hi]; omega
    · rw [min_eq_right hi]; omega
  have he := congrFun (hb ⟨k/c,hj⟩) ⟨k-i,hki⟩
  have hsum : i+(k-i)=k := Nat.add_sub_of_le hik
  simpa [shingleAt, show min ((k/c)*c) (n-c) = i from rfl, hsum,
    List.getElem?_eq_getElem hkw, List.getElem?_eq_getElem hkv] using he

theorem recovery_of_distortion (𝓕 : Type) [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c t₁ : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n)
    (hlip : ∀ w w' : EditSpace 𝓕 n, editDis w w' ≤ t₁ →
      symmDiffDis (shingles c w.1) (shingles c w'.1) ≤ (2*c-1)*t₁) :
    IsEmbeddingWithRecovery (editDis (𝓕 := 𝓕) (n := n)) symmDiffDis t₁ ((2*c-1)*t₁)
      ((⌈(n : ℝ)/c⌉₊ : ℝ)*Real.logb 2 ((n : ℝ)-c+1))
      (fun w => shingles c w.1) (gc c) :=
  ⟨hlip, recovery_range n c hc hcn, recovery_injective n c hc hcn⟩

#print axioms recovery_of_distortion
#print axioms recovery_range
#print axioms recovery_injective
end ShingleSupport

open MasekPaterson.Shared FuzzyExtractors.EditSketch
namespace EditCost
def cost {α : Type*} (S : List (EditOp α)) : ℕ :=
  (S.map fun o => if o.src.isSome ∧ o.tgt.isSome then 2 else 1).sum

lemma cast_cost {α : Type} (S : List (EditOp α)) : (cost S : ℝ) = seqCost gammaIndel S := by
  induction S with
  | nil => simp [cost,seqCost]
  | cons o S ih =>
    simp only [cost,List.map_cons,List.sum_cons,Nat.cast_add] at *
    rw [ih]
    simp [seqCost,gammaIndel]

lemma prepend {α : Type*} {S : List (EditOp α)} {A B : List α} (h : Takes S A B) (p : List α) :
    Takes S (p++A) (p++B) := by
  induction h with
  | nil A => exact Takes.nil _
  | @cons o S A C B hy ht ih =>
    apply Takes.cons (s:=o) _ ih
    obtain ⟨σ,τ,ha,hc⟩ := hy
    exact ⟨p++σ,τ,by simp [ha,List.append_assoc],by simp [hc,List.append_assoc]⟩

lemma reachable {α : Type*} (A B : List α) : ∃ S, Takes S A B := by
  induction A generalizing B with
  | nil =>
    induction B with
    | nil => exact ⟨[],Takes.nil []⟩
    | cons b B ih =>
      obtain ⟨S,hS⟩ := ih
      refine ⟨insOp b :: S, Takes.cons (C := [b]) ?_ ?_⟩
      · exact ⟨[],[],by simp [insOp],by simp [insOp]⟩
      · simpa using prepend hS [b]
  | cons a A ih =>
    obtain ⟨S,hS⟩ := ih B
    refine ⟨delOp a :: S, Takes.cons ?_ hS⟩
    exact ⟨[],A,by simp [delOp],by simp [delOp]⟩

theorem attained {α : Type} (A B : List α) :
    ∃ S, Takes S A B ∧ (cost S : ℝ) = editDist gammaIndel A B := by
  classical
  have hex : ∃ n : ℕ, ∃ S, Takes S A B ∧ cost S = n := by
    obtain ⟨S,hS⟩ := reachable A B
    exact ⟨cost S,S,hS,rfl⟩
  obtain ⟨S,hS,hc⟩ := Nat.find_spec hex
  refine ⟨S,hS,?_⟩
  have hset : BddBelow {x : ℝ | ∃ T : List (EditOp α), Takes T A B ∧ x=seqCost gammaIndel T} := by
    refine ⟨0,?_⟩
    rintro x ⟨T,hT,rfl⟩
    rw [← cast_cost]
    positivity
  unfold editDist
  apply le_antisymm
  · refine le_csInf (s := {x : ℝ | ∃ T : List (EditOp α), Takes T A B ∧ x=seqCost gammaIndel T}) ?_ ?_
    · exact ⟨seqCost gammaIndel S,S,hS,rfl⟩
    rintro x ⟨T,hT,rfl⟩
    rw [← cast_cost,hc]
    exact_mod_cast Nat.find_min' hex (show ∃ U, Takes U A B ∧ cost U=cost T from ⟨T,hT,rfl⟩)
  · exact csInf_le hset ⟨S,hS,cast_cost S⟩

theorem floor_witness {α : Type} (A B : List α) :
    ∃ S, Takes S A B ∧ cost S = ⌊editDist gammaIndel A B⌋₊ := by
  obtain ⟨S,hS,he⟩ := attained A B
  exact ⟨S,hS,by rw [← he,Nat.floor_natCast]⟩
end EditCost
#print axioms EditCost.floor_witness

open FuzzyExtractors.EditSketch
namespace ShingleWindows
variable {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]

lemma mem_iff {c : ℕ} {w : List α} {u : Fin c → α} :
    u ∈ shingles c w ↔ ∃ i : ℕ, ∀ k : Fin c, w[i+(k:ℕ)]?=some (u k) := by
  classical
  simp [shingles]

lemma at_eq {c : ℕ} {w : List α} {u : Fin c → α} {i : ℕ}
    (h : ∀ k : Fin c, w[i+(k:ℕ)]?=some (u k)) : shingleAt c w i = u := by
  funext k
  simp [shingleAt,List.getD_eq_getElem?_getD,h k]

lemma before {p s : List α} {a : α} {j : ℕ} (hj : j < p.length) :
    (p++a::s)[j]? = (p++s)[j]? := by
  rw [List.getElem?_append_left hj,List.getElem?_append_left hj]
lemma after {p s : List α} {a : α} {j : ℕ} (hj : p.length ≤ j) :
    (p++a::s)[j+1]? = (p++s)[j]? := by
  rw [List.getElem?_append_right (by omega),List.getElem?_append_right hj]
  rw [show j+1-p.length=(j-p.length)+1 by omega]
  simp

lemma old_lost {c : ℕ} (p s : List α) (a : α) :
    shingles c (p++s) \ shingles c (p++a::s) ⊆
      (Finset.Ico (p.length+1-c) p.length).image (shingleAt c (p++s)) := by
  classical
  intro u hu
  obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨i,hi⟩ := mem_iff.mp hu
  have hleft : ¬ i+c ≤ p.length := by
    intro h
    apply hn
    apply mem_iff.mpr
    refine ⟨i,fun k => ?_⟩
    rw [before (by have := k.isLt; omega)]
    exact hi k
  have hright : i < p.length := by
    by_contra h
    apply hn
    apply mem_iff.mpr
    refine ⟨i+1,fun k => ?_⟩
    rw [show i+1+(k:ℕ)=(i+(k:ℕ))+1 by omega, after (by omega)]
    exact hi k
  exact Finset.mem_image.mpr ⟨i,Finset.mem_Ico.mpr ⟨by omega,hright⟩,at_eq hi⟩

lemma new_gained {c : ℕ} (p s : List α) (a : α) :
    shingles c (p++a::s) \ shingles c (p++s) ⊆
      (Finset.Ico (p.length+1-c) (p.length+1)).image (shingleAt c (p++a::s)) := by
  classical
  intro u hu
  obtain ⟨hu,hn⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨i,hi⟩ := mem_iff.mp hu
  have hleft : ¬ i+c ≤ p.length := by
    intro h
    apply hn
    apply mem_iff.mpr
    refine ⟨i,fun k => ?_⟩
    rw [← before (a:=a) (by have := k.isLt; omega)]
    exact hi k
  have hright : i < p.length+1 := by
    by_contra h
    apply hn
    apply mem_iff.mpr
    refine ⟨i-1,fun k => ?_⟩
    have he := after (p:=p) (s:=s) (a:=a) (j:=i-1+(k:ℕ)) (by omega)
    rw [show i-1+(k:ℕ)+1=i+(k:ℕ) by omega] at he
    exact he.symm.trans (hi k)
  exact Finset.mem_image.mpr ⟨i,Finset.mem_Ico.mpr ⟨by omega,hright⟩,at_eq hi⟩

theorem insertion {c : ℕ} (hc : 1 ≤ c) (p s : List α) (a : α) :
    symmDiffDis (shingles c (p++s)) (shingles c (p++a::s)) ≤ 2*c-1 := by
  classical
  have ho := (Finset.card_le_card (old_lost (c:=c) p s a)).trans Finset.card_image_le
  have hn := (Finset.card_le_card (new_gained (c:=c) p s a)).trans Finset.card_image_le
  simp only [Nat.card_Ico] at ho hn
  unfold symmDiffDis
  rw [Finset.symmDiff_def]
  have h := Finset.card_union_le (shingles c (p++s) \ shingles c (p++a::s))
    (shingles c (p++a::s) \ shingles c (p++s))
  omega
end ShingleWindows
#print axioms ShingleWindows.insertion

open FuzzyExtractors.EditSketch MasekPaterson.Shared
open scoped symmDiff
namespace ShingleDistortion
lemma triangle {α : Type} [DecidableEq α] (A B C : Finset α) :
    symmDiffDis A C ≤ symmDiffDis A B + symmDiffDis B C := by
  have hs : A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
    intro x
    simp only [Finset.mem_symmDiff,Finset.mem_union]
    tauto
  exact (Finset.card_le_card hs).trans (Finset.card_union_le _ _)

lemma step {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]
    {c : ℕ} (hc : 1 ≤ c) {o : EditOp α} {A B : List α} (hy : Yields o A B) :
    symmDiffDis (shingles c A) (shingles c B) ≤ (2*c-1)*EditCost.cost [o] := by
  rcases o with ⟨src,tgt,hn⟩
  obtain ⟨p,s,rfl,rfl⟩ := hy
  cases src with
  | none =>
    cases tgt with
    | none => exact False.elim (hn ⟨rfl,rfl⟩)
    | some b => simpa [EditCost.cost,List.append_assoc] using ShingleWindows.insertion hc p s b
  | some a =>
    cases tgt with
    | none =>
      have hi := ShingleWindows.insertion hc p s a
      simpa [EditCost.cost,List.append_assoc,symmDiffDis,symmDiff_comm] using hi
    | some b =>
      have ha := ShingleWindows.insertion hc p s a
      have hb := ShingleWindows.insertion hc p s b
      have ht := triangle (shingles c (p++a::s)) (shingles c (p++s)) (shingles c (p++b::s))
      have he : symmDiffDis (shingles c (p++a::s)) (shingles c (p++s)) =
          symmDiffDis (shingles c (p++s)) (shingles c (p++a::s)) := by
        simp [symmDiffDis,symmDiff_comm]
      rw [he] at ht
      simp only [Option.toList_some,List.append_assoc,List.singleton_append]
      simp only [EditCost.cost,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
        Option.isSome_some,Bool.true_eq, and_self,if_true,add_zero]
      omega

theorem path {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]
    {c : ℕ} (hc : 1 ≤ c) {S : List (EditOp α)} {A B : List α} (h : Takes S A B) :
    symmDiffDis (shingles c A) (shingles c B) ≤ (2*c-1)*EditCost.cost S := by
  induction h with
  | nil A => simp [symmDiffDis,EditCost.cost]
  | @cons o S A C B hy ht ih =>
    have hs := step hc hy
    have htri := triangle (shingles c A) (shingles c C) (shingles c B)
    have he : EditCost.cost (o::S) = EditCost.cost [o] + EditCost.cost S := by simp [EditCost.cost]
    rw [he,mul_add]
    exact htri.trans (Nat.add_le_add hs ih)

theorem distance {α : Type} [Fintype α] [Inhabited α] [DecidableEq α]
    {c n : ℕ} (hc : 1 ≤ c) (w w' : EditSpace α n) :
    symmDiffDis (shingles c w.1) (shingles c w'.1) ≤ (2*c-1)*editDis w w' := by
  obtain ⟨S,hS,hcS⟩ := EditCost.floor_witness w.1 w'.1
  have hp := path hc hS
  simpa [editDis,hcS] using hp
end ShingleDistortion

theorem solution (𝓕 : Type) [Fintype 𝓕] [LinearOrder 𝓕] [Inhabited 𝓕]
    (n c t₁ : ℕ) (hc : 1 ≤ c) (hcn : c ≤ n) :
    IsEmbeddingWithRecovery (editDis (𝓕 := 𝓕) (n := n)) symmDiffDis t₁ ((2*c-1)*t₁)
      ((⌈(n : ℝ)/c⌉₊ : ℝ)*Real.logb 2 ((n : ℝ)-c+1))
      (fun w => shingles c w.1) (gc c) := by
  apply ShingleSupport.recovery_of_distortion 𝓕 n c t₁ hc hcn
  intro w w' h
  exact (ShingleDistortion.distance hc w w').trans (Nat.mul_le_mul_left _ h)
#print axioms solution

end EmbedProof

namespace PriorTransfer


open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming

theorem embedding_correct {M₁ M₂ G S : Type} (dis₁ : M₁ → M₁ → ℕ)
    (dis₂ : M₂ → M₂ → ℕ) (t₁ t₂ : ℕ) (lam : ℝ) (f : M₁ → M₂) (g : M₁ → G)
    (SS : M₂ → PMF S) (Rec : M₂ → S → PMF M₂)
    (hf : IsEmbeddingWithRecovery dis₁ dis₂ t₁ t₂ lam f g)
    (hc : SketchCorrect dis₂ t₂ SS Rec) :
    SketchCorrect dis₁ t₁ (embedSketch f g SS) (embedRec f g Rec) := by
  classical
  intro w w' hd sr hsr
  obtain ⟨s, hs, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hsr
  change (s, g w) = sr at he
  subst sr
  have hr := hc (f w) (f w') (hf.1 w w' hd) s hs
  unfold embedRec
  rw [hr, PMF.pure_map]
  have hex : ∃ a, f a = f w ∧ g a = g w := ⟨w,rfl,rfl⟩
  simp only [dif_pos hex]
  congr 1
  apply hf.2.2
  exact Prod.ext hex.choose_spec.1 hex.choose_spec.2



open scoped ENNReal
open Classical

namespace Paper40

noncomputable def guess {A I : Type} (P : PMF (A × I)) : ℝ≥0∞ :=
  ∑' i, ⨆ a, P (a,i)

noncomputable def reveal {A B G I : Type} (f : A → B) (g : A → G) (P : PMF (A × I)) :
    PMF (B × (G × I)) := P.map fun p => (f p.1,(g p.1,p.2))

theorem reveal_apply {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (P : PMF (A × I))
    (b : B) (r : G) (i : I) :
    reveal f g P (b,(r,i)) =
      if h : ∃ a, f a = b ∧ g a = r then P (h.choose,i) else 0 := by
  classical
  unfold reveal
  rw [PMF.map_apply]
  split
  next h =>
    rw [tsum_eq_single (h.choose,i)]
    · simp [h.choose_spec.1,h.choose_spec.2]
    · intro p hp
      split_ifs with he
      · have he' : f p.1 = b ∧ g p.1 = r ∧ p.2 = i := by
          simpa [Prod.mk.injEq, eq_comm, and_assoc] using he
        have ha : p.1 = h.choose := hinj (Prod.ext
          (he'.1.trans h.choose_spec.1.symm) (he'.2.1.trans h.choose_spec.2.symm))
        exact (hp (Prod.ext ha he'.2.2)).elim
      · rfl
  next h =>
    apply ENNReal.tsum_eq_zero.mpr
    intro p
    split_ifs with he
    · apply (h ?_).elim
      have he' : f p.1 = b ∧ g p.1 = r ∧ p.2 = i := by
        simpa [Prod.mk.injEq, eq_comm, and_assoc] using he
      exact ⟨p.1,he'.1,he'.2.1⟩
    · rfl

theorem reveal_guess_le {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (T : Finset G)
    (hT : ∀ a, g a ∈ T) (P : PMF (A × I)) :
    guess (reveal f g P) ≤ T.card * guess P := by
  classical
  have hbound (r : G) (i : I) :
      (⨆ b, reveal f g P (b,(r,i))) ≤
        if r ∈ T then ⨆ a, P (a,i) else 0 := by
    apply iSup_le
    intro b
    rw [reveal_apply f g hinj]
    split
    next h =>
      have hr : r ∈ T := h.choose_spec.2 ▸ hT h.choose
      simp only [hr,if_true]
      exact le_iSup (fun a => P (a,i)) h.choose
    next h => exact zero_le
  unfold guess
  change (∑' p : G × I, ⨆ b, reveal f g P (b,(p.1,p.2))) ≤ _
  rw [ENNReal.tsum_prod (f := fun r i => ⨆ b, reveal f g P (b,(r,i)))]
  calc
    (∑' r, ∑' i, ⨆ b, reveal f g P (b,(r,i))) ≤
        ∑' r, ∑' i, if r ∈ T then ⨆ a, P (a,i) else 0 :=
      ENNReal.tsum_le_tsum fun r => ENNReal.tsum_le_tsum (hbound r)
    _ = T.card * ∑' i, ⨆ a, P (a,i) := by
      have he (r : G) : (∑' i, if r ∈ T then ⨆ a, P (a,i) else 0) =
          if r ∈ T then ∑' i, ⨆ a, P (a,i) else 0 := by
        by_cases hr : r ∈ T <;> simp [hr]
      simp_rw [he]
      rw [tsum_eq_sum (s := T)]
      · simp
      · intro r hr; simp [hr]

end Paper40


open scoped ENNReal
open FuzzyExtractors.Hamming
namespace Paper40

theorem guess_le_one {A I : Type} (P : PMF (A × I)) : guess P ≤ 1 := by
  calc
    guess P ≤ ∑' i, ∑' a, P (a,i) := ENNReal.tsum_le_tsum fun i =>
      iSup_le fun a => ENNReal.le_tsum a
    _ = 1 := by rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod', P.tsum_coe]

theorem guess_pos {A I : Type} (P : PMF (A × I)) : 0 < guess P := by
  obtain ⟨⟨a,i⟩,h⟩ := P.support_nonempty
  exact (pos_iff_ne_zero.mpr h).trans_le
    ((le_iSup (fun a => P (a,i)) a).trans (ENNReal.le_tsum i))

theorem entropy_iff {A I : Type} (P : PMF (A × I)) (m : ℝ) :
    m ≤ avgMinEntropy P ↔ guess P ≤ ENNReal.ofReal ((2 : ℝ)^(-m)) := by
  have hf : guess P ≠ ∞ := ne_of_lt (lt_of_le_of_lt (guess_le_one P) ENNReal.one_lt_top)
  have hp : 0 < (guess P).toReal := ENNReal.toReal_pos (ne_of_gt (guess_pos P)) hf
  have he : m ≤ avgMinEntropy P ↔ Real.logb 2 (guess P).toReal ≤ -m := by
    unfold avgMinEntropy guess
    constructor <;> intro h <;> linarith
  rw [he, Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hp]
  constructor
  · intro h
    simpa [ENNReal.ofReal_toReal hf] using ENNReal.ofReal_le_ofReal h
  · intro h
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
      (ENNReal.toReal_ofReal (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)))

theorem entropy_reveal {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (T : Finset G)
    (hT : ∀ a, g a ∈ T) (lam m : ℝ) (hcard : (T.card : ℝ) ≤ (2 : ℝ)^lam)
    (P : PMF (A × I)) (hm : m ≤ avgMinEntropy P) :
    m-lam ≤ avgMinEntropy (reveal f g P) := by
  apply (entropy_iff _ _).mpr
  calc
    guess (reveal f g P) ≤ T.card * guess P := reveal_guess_le f g hinj T hT P
    _ ≤ ENNReal.ofReal ((2 : ℝ)^lam) * ENNReal.ofReal ((2 : ℝ)^(-m)) := by
      apply mul_le_mul'
      · simpa using ENNReal.ofReal_le_ofReal hcard
      · exact (entropy_iff P m).mp hm
    _ = ENNReal.ofReal ((2 : ℝ)^(-(m-lam))) := by
      rw [← ENNReal.ofReal_mul (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring

end Paper40


open scoped ENNReal
open Classical
open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming

namespace Paper40

theorem reveal_image {A B G I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (P : PMF (A × I))
    (a : A) (i : I) : reveal f g P (f a,(g a,i)) = P (a,i) := by
  rw [reveal_apply f g hinj]
  split
  next h =>
    congr 1
    congr 1
    exact hinj (Prod.ext h.choose_spec.1 h.choose_spec.2)
  next h => exact (h ⟨a,rfl,rfl⟩).elim

theorem sketchAux_apply {A S I : Type} (SS : A → PMF S) (P : PMF (A × I))
    (a : A) (s : S) (i : I) :
    withSketchAux SS P (a,(s,i)) = P (a,i) * SS a s := by
  unfold withSketchAux
  rw [PMF.bind_apply]
  have hm (p : A × I) : ((SS p.1).map fun s => (p.1,(s,p.2))) (a,(s,i)) =
      if p = (a,i) then SS a s else 0 := by
    by_cases hp : p = (a,i)
    · subst p; simp [PMF.map_apply]
    · have hp' : ¬ (a = p.1 ∧ i = p.2) := by
        intro h; apply hp; exact Prod.ext h.1.symm h.2.symm
      simp only [PMF.map_apply, Prod.mk.injEq]
      have hx : ∀ x, (if a = p.1 ∧ s = x ∧ i = p.2 then SS p.1 x else 0) = 0 := by
        intro x; split_ifs with h
        · exact (hp' ⟨h.1,h.2.2⟩).elim
        · rfl
      simp [hx,hp]
  simp_rw [hm]
  rw [tsum_eq_single (a,i)]
  · simp
  · intro p hp; simp [hp]

theorem embedSketch_apply {A B G S : Type} (f : A → B) (g : A → G)
    (SS : B → PMF S) (a : A) (s : S) (r : G) :
    embedSketch f g SS a (s,r) = if r = g a then SS (f a) s else 0 := by
  unfold embedSketch
  by_cases hr : r = g a
  · subst r; simp [PMF.map_apply]
  · simp [PMF.map_apply, Prod.mk.injEq, hr]

theorem embed_output_guess {A B G S I : Type} (f : A → B) (g : A → G)
    (hinj : Function.Injective fun a => (f a,g a)) (SS : B → PMF S) (P : PMF (A × I)) :
    guess (withSketchAux (embedSketch f g SS) P) ≤
      guess (withSketchAux SS (reveal f g P)) := by
  have hb (s : S) (r : G) (i : I) :
      (⨆ a, withSketchAux (embedSketch f g SS) P (a,((s,r),i))) ≤
        ⨆ b, withSketchAux SS (reveal f g P) (b,(s,(r,i))) := by
    apply iSup_le
    intro a
    rw [sketchAux_apply,embedSketch_apply]
    by_cases hr : r = g a
    · subst r
      simp only [if_true]
      have he : withSketchAux SS (reveal f g P) (f a,(s,(g a,i))) =
          P (a,i)*SS (f a) s := by rw [sketchAux_apply,reveal_image f g hinj]
      rw [← he]
      exact le_iSup (fun b : B => withSketchAux SS (reveal f g P) (b,(s,(g a,i)))) (f a)
    · simp [hr]
  unfold guess
  simp only [ENNReal.tsum_prod']
  apply ENNReal.tsum_le_tsum
  intro s
  apply ENNReal.tsum_le_tsum
  intro r
  exact ENNReal.tsum_le_tsum (hb s r)

end Paper40


open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming Paper40

theorem solution {M₁ M₂ G S : Type} (dis₁ : M₁ → M₁ → ℕ) (dis₂ : M₂ → M₂ → ℕ)
    (t₁ t₂ : ℕ) (lam m₁ m₂' : ℝ) (f : M₁ → M₂) (g : M₁ → G)
    (SS : M₂ → PMF S) (Rec : M₂ → S → PMF M₂)
    (hf : IsEmbeddingWithRecovery dis₁ dis₂ t₁ t₂ lam f g)
    (hSS : FuzzyExtractors.Hamming.IsAvgSecureSketch dis₂ (m₁ - lam) m₂' t₂ SS Rec) :
    FuzzyExtractors.Hamming.IsAvgSecureSketch dis₁ m₁ m₂' t₁ (embedSketch f g SS) (embedRec f g Rec) := by
  refine ⟨embedding_correct dis₁ dis₂ t₁ t₂ lam f g SS Rec hf hSS.1, ?_⟩
  intro I WI hm
  obtain ⟨T,hcard,hT⟩ := hf.2.1
  have hi := entropy_reveal f g hf.2.2 T hT lam m₁ hcard WI hm
  have ho := hSS.2 (G × I) (reveal f g WI) hi
  apply (entropy_iff _ _).mpr
  exact (embed_output_guess f g hf.2.2 SS WI).trans ((entropy_iff _ _).mp ho)


#print axioms solution

end PriorTransfer

#print axioms PinProof.solution
#print axioms EmbedProof.solution
#print axioms PriorTransfer.solution

open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming
namespace ShingleField
lemma field_size (F : Type) [Fintype F] [Nonempty F] (c : ℕ) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K) (_ : DecidableEq K) (_ : CharP K 2),
      Nonempty ((Fin c → F) ↪ Kˣ) ∧
      Real.logb 2 ((Fintype.card Kˣ : ℝ)+1) = (Nat.clog 2 (Fintype.card F ^ c+1) : ℝ) := by
  classical
  let l := Nat.clog 2 (Fintype.card F ^ c+1)
  have hl : 0 < l := Nat.clog_pos (by norm_num) (by
    have : 0 < Fintype.card F ^ c := pow_pos Fintype.card_pos c
    omega)
  let K := GaloisField 2 l
  letI : Fintype K := Fintype.ofFinite K
  have hk : Fintype.card K = 2^l := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 l (by omega)
  have hu : Fintype.card Kˣ = 2^l-1 := by rw [Fintype.card_units,hk]
  have he : Fintype.card (Fin c → F) ≤ Fintype.card Kˣ := by
    rw [Fintype.card_fun,Fintype.card_fin,hu]
    have h := Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card F^c+1)
    change Fintype.card F^c ≤ 2^l-1
    change Fintype.card F^c+1 ≤ 2^l at h
    omega
  refine ⟨K,inferInstance,inferInstance,inferInstance,inferInstance,
    (Function.Embedding.nonempty_iff_card_le).mpr he,?_⟩
  have hcard : (Fintype.card Kˣ : ℝ)+1 = (2:ℝ)^l := by
    have hp : 0 < 2^l := by positivity
    exact_mod_cast (show Fintype.card Kˣ+1=2^l by omega)
  rw [hcard,Real.logb_pow]
  norm_num
  rfl

lemma distance_map {U V : Type} [DecidableEq U] [DecidableEq V] (e : U ↪ V)
    (A B : Finset U) : symmDiffDis (A.map e) (B.map e) = symmDiffDis A B := by
  simp only [symmDiffDis,Finset.map_eq_image]
  rw [← Finset.image_symmDiff _ _ e.injective, Finset.card_image_of_injective _ e.injective]

lemma transport {M U V G : Type} [DecidableEq U] [DecidableEq V]
    (dis : M → M → ℕ) (t₁ t₂ : ℕ) (lam : ℝ)
    (f : M → Finset U) (g : M → G)
    (h : IsEmbeddingWithRecovery dis symmDiffDis t₁ t₂ lam f g) (e : U ↪ V) :
    IsEmbeddingWithRecovery dis symmDiffDis t₁ t₂ lam (fun w => (f w).map e) g := by
  refine ⟨?_,h.2.1,?_⟩
  · intro w w' hw
    rw [distance_map]
    exact h.1 w w' hw
  · intro a b hab
    apply h.2.2
    apply Prod.ext
    · exact Finset.map_injective e (congrArg Prod.fst hab)
    · exact congrArg (fun z : Finset V × G => z.2) hab
end ShingleField
#print axioms ShingleField.field_size
#print axioms ShingleField.transport

open FuzzyExtractors.EditSketch FuzzyExtractors.Hamming

theorem solution (𝓕 : Type) [Fintype 𝓕] [DecidableEq 𝓕] (n c t : ℕ) (m : ℝ)
    (hc : 1 ≤ c) (hcn : c ≤ n) :
    ∃ (S : Type) (SS : EditSpace 𝓕 n → PMF S) (Rec : EditSpace 𝓕 n → S → PMF (EditSpace 𝓕 n)),
      IsAvgSecureSketch editDis m
        (m - (⌈(n : ℝ) / c⌉₊ : ℝ) * Real.logb 2 ((n : ℝ) - c + 1)
          - (2 * (c : ℝ) - 1) * t * (Nat.clog 2 (Fintype.card 𝓕 ^ c + 1) : ℝ))
        t SS Rec := by
  rename_i instF decF
  clear decF
  classical
  cases isEmpty_or_nonempty 𝓕 with
  | inl h =>
    letI := h
    have noWord (w : EditSpace 𝓕 n) : False := by
      have hw : 0 < w.1.length := by rw [w.2]; omega
      exact isEmptyElim (w.1[0])
    refine ⟨Unit,(fun _ => PMF.pure ()),(fun w _ => PMF.pure w),?_,?_⟩
    · intro w
      exact (noWord w).elim
    · intro I WI
      obtain ⟨p,hp⟩ := WI.support_nonempty
      exact (noWord p.1).elim
  | inr h =>
    letI := h
    letI : Inhabited 𝓕 := Classical.inhabited_of_nonempty h
    letI : LinearOrder 𝓕 := LinearOrder.lift' (Fintype.equivFin 𝓕) (Fintype.equivFin 𝓕).injective
    obtain ⟨K,hfield,hfinite,hdec,hchar,⟨e⟩,hlog⟩ := ShingleField.field_size 𝓕 c
    letI := hfield
    letI := hfinite
    letI := hdec
    letI := hchar
    let lam : ℝ := (⌈(n:ℝ)/c⌉₊ : ℝ)*Real.logb 2 ((n:ℝ)-c+1)
    let t₂ := (2*c-1)*t
    let f : EditSpace 𝓕 n → Finset Kˣ := fun w => (shingles c w.1).map e
    have hb := EmbedProof.solution 𝓕 n c t hc hcn
    have ht := ShingleField.transport editDis t t₂ lam (fun w : EditSpace 𝓕 n => shingles c w.1) (gc c) hb e
    have hs := PinProof.solution (K:=K) t₂ (m-lam)
    have ho := PriorTransfer.solution editDis symmDiffDis t t₂ lam m _ f (gc c)
      (pinSS (K:=K) t₂) (pinRec t₂) ht hs
    have hcast : (t₂:ℝ) = (2*(c:ℝ)-1)*(t:ℝ) := by
      simp [t₂,Nat.cast_sub (by omega : 1 ≤ 2*c)]
    have hout : (m-lam)-(t₂:ℝ)*Real.logb 2 ((Fintype.card Kˣ:ℝ)+1) =
        m-lam-(2*(c:ℝ)-1)*(t:ℝ)*(Nat.clog 2 (Fintype.card 𝓕^c+1):ℝ) := by
      rw [hlog,hcast]
    rw [hout] at ho
    exact ⟨_,_,_,ho⟩
#print axioms solution
