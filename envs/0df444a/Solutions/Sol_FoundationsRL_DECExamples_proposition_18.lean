-- Prove2me | solution 1 for FoundationsRL.DECExamples.proposition_18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-12T08:18:36.418179+00:00
-- url     : https://prove2.me/submissions/5908365d-8e16-40af-aa24-c8d313b81a2a

import Mathlib
import Definitions.Def_FoundationsRL_DECExamples_decAt
import Definitions.Def_FoundationsRL_DECExamples_lipschitzClass
import Definitions.Def_FoundationsRL_DECExamples_HasCoveringGrowth
import Definitions.Def_FoundationsRL_DECExamples_IsCoverWitness
import Definitions.Def_FoundationsRL_DECExamples_IsIGWOn

set_option autoImplicit false

open scoped NNReal

namespace P18Aux

open FoundationsRL.DECExamples

lemma quad_le (a c : ℝ) (hc : 0 < c) : a - c * a ^ 2 ≤ 1 / (4 * c) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * c * a - 1)]

/-- Inverse gap weighting bound on a finite action set (factor `2γ` version). -/
lemma igw_bound (A : ℕ) (fh f : Fin A → ℝ) (γ : ℝ) (hγ : 0 < γ) (b : Fin A) (p : Fin A → ℝ)
    (h : FoundationsRL.Contextual.IsIGW A fh γ b p) (j : Fin A) :
    ∑ i, p i * (f j - f i - γ * (f i - fh i) ^ 2) ≤ 2 * A / γ := by
  obtain ⟨lam, ⟨hl1, hlA⟩, hp⟩ := h.lam_spec
  have hden : ∀ i, 0 < lam + 2 * γ * (fh b - fh i) := fun i => by
    have h0 : 0 ≤ 2 * γ * (fh b - fh i) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr (h.greedy i))
    linarith
  have hpi : ∀ i, p i * (f j - f i - γ * (f i - fh i) ^ 2) ≤
      p i * (1 / (2 * γ)) + 1 / (2 * γ) + p i * ((f j - fh j) - (fh b - fh j))
        - γ / 2 * (p i * (f i - fh i) ^ 2) := by
    intro i
    have h1 : -(f i - fh i) - γ / 2 * (f i - fh i) ^ 2 ≤ 1 / (2 * γ) := by
      have := quad_le (-(f i - fh i)) (γ / 2) (by positivity)
      have e : 4 * (γ / 2) = 2 * γ := by ring
      rw [e, neg_sq] at this
      exact this
    have h2 : p i * (fh b - fh i) ≤ 1 / (2 * γ) := by
      rw [hp i, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (hden i) (by positivity)]
      nlinarith [h.greedy i]
    have h3 := mul_le_mul_of_nonneg_left h1 (h.nonneg i)
    nlinarith [h3, h2]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpi i)
  have hS : ∑ i, (p i * (1 / (2 * γ)) + 1 / (2 * γ) + p i * ((f j - fh j) - (fh b - fh j))
        - γ / 2 * (p i * (f i - fh i) ^ 2)) =
      (∑ i, p i) * (1 / (2 * γ)) + A * (1 / (2 * γ)) + (∑ i, p i) * ((f j - fh j) - (fh b - fh j))
        - γ / 2 * ∑ i, p i * (f i - fh i) ^ 2 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    simp
  rw [hS, h.sum_one] at hsum
  have hsingle : p j * (f j - fh j) ^ 2 ≤ ∑ i, p i * (f i - fh i) ^ 2 :=
    Finset.single_le_sum (f := fun i => p i * (f i - fh i) ^ 2)
      (fun i _ => mul_nonneg (h.nonneg i) (sq_nonneg _)) (Finset.mem_univ j)
  have hT3 : (f j - fh j) - (fh b - fh j) - γ / 2 * (p j * (f j - fh j) ^ 2) ≤ lam / (2 * γ) := by
    have hD := hden j
    set Dj := lam + 2 * γ * (fh b - fh j) with hDj
    set x := f j - fh j
    have eq1 : Dj / (2 * γ) - (x - γ / 2 * (1 / Dj * x ^ 2)) = (Dj - γ * x) ^ 2 / (2 * γ * Dj) := by
      field_simp
      ring
    have eq2 : Dj / (2 * γ) = lam / (2 * γ) + (fh b - fh j) := by
      rw [hDj]
      field_simp
    have hnn : 0 ≤ (Dj - γ * x) ^ 2 / (2 * γ * Dj) := by positivity
    rw [hp j]
    linarith
  have hA : (1 : ℝ) ≤ A := by
    have : 0 < A := Fin.pos j
    exact_mod_cast this
  have hfin : 1 / (2 * γ) + A * (1 / (2 * γ)) + lam / (2 * γ) ≤ 2 * A / γ := by
    have e1 : 1 / (2 * γ) + A * (1 / (2 * γ)) + lam / (2 * γ) = (1 + A + lam) / (2 * γ) := by ring
    have e2 : 2 * (A : ℝ) / γ = (4 * A) / (2 * γ) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      ring
    rw [e1, e2]
    gcongr
    linarith
  have hγ2 : 0 ≤ γ / 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsingle hγ2]

/-- Core certificate for a fixed cover and IGW distribution. -/
lemma core {D : Type*} [MetricSpace D] [Nonempty D] (fhat : D → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (ε : ℝ≥0) (D' : Finset D) (p : PMF D) (hcov : Metric.IsCover ε Set.univ (D' : Set D))
    (hp : IsIGWOn D' fhat γ p) (f : D → ℝ) (hf : f ∈ lipschitzClass D) :
    offsetValue p f fhat γ ≤ (ε : ℝ) + 2 * (D'.card : ℝ) / γ := by
  obtain ⟨hsupp, e, b, higw⟩ := hp
  obtain ⟨hf01, hlip⟩ := hf
  rw [Metric.isCover_iff_subset_iUnion_closedBall] at hcov
  have hnear : ∀ π : D, ∃ y ∈ D', dist π y ≤ ε := by
    intro π
    have := hcov (Set.mem_univ π)
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Finset.mem_coe] at this
    obtain ⟨y, hy, hd⟩ := this
    exact ⟨y, hy, hd⟩
  have hsum_eq : offsetValue p f fhat γ = ∑ i : Fin D'.card, (p (e i)).toReal *
      ((⨆ π', f π') - f (e i) - γ * (f (e i) - fhat (e i)) ^ 2) := by
    unfold offsetValue expect
    rw [tsum_eq_sum (s := D') (fun π hπ => by simp [hsupp π hπ])]
    rw [← Finset.sum_coe_sort D']
    exact (Equiv.sum_comp e (fun x : D' =>
      (p x).toReal * ((⨆ π', f π') - f x - γ * (f x - fhat x) ^ 2))).symm
  obtain ⟨x0⟩ := ‹Nonempty D›
  obtain ⟨y0, hy0, -⟩ := hnear x0
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => f (e i))
    ⟨e.symm ⟨y0, hy0⟩, Finset.mem_univ _⟩
  have hS : (⨆ π', f π') ≤ f (e j) + ε := by
    apply ciSup_le
    intro π
    obtain ⟨y, hy, hd⟩ := hnear π
    have hl := hlip.dist_le_mul π y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hl
    have hl2 := (abs_sub_le_iff.mp hl).1
    have hy2 := hj (e.symm ⟨y, hy⟩) (Finset.mem_univ _)
    simp only [Equiv.apply_symm_apply] at hy2
    linarith
  rw [hsum_eq]
  have hb := igw_bound _ (fun i => fhat (e i)) (fun i => f (e i)) γ hγ b _ higw j
  have hs1 : ∑ i, (p (e i)).toReal = 1 := higw.sum_one
  have hle : ∀ i, (p (e i)).toReal * ((⨆ π', f π') - f (e i) - γ * (f (e i) - fhat (e i)) ^ 2) ≤
      (p (e i)).toReal * ε + (p (e i)).toReal *
        (f (e j) - f (e i) - γ * (f (e i) - fhat (e i)) ^ 2) := by
    intro i
    have h0 : 0 ≤ (p (e i)).toReal := ENNReal.toReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_left hS h0]
  calc _ ≤ ∑ i, ((p (e i)).toReal * ε + (p (e i)).toReal *
        (f (e j) - f (e i) - γ * (f (e i) - fhat (e i)) ^ 2)) :=
        Finset.sum_le_sum fun i _ => hle i
    _ = (∑ i, (p (e i)).toReal) * ε + ∑ i, (p (e i)).toReal *
        (f (e j) - f (e i) - γ * (f (e i) - fhat (e i)) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := by rw [hs1]; linarith

lemma cardbound {D : Type*} [MetricSpace D] (d : ℝ) (hcg : HasCoveringGrowth D d) (ε : ℝ≥0)
    (h0 : 0 < ε) (h1 : ε ≤ 1) (D' : Finset D) (hw : IsCoverWitness ε D') :
    (D'.card : ℝ) ≤ (ε : ℝ) ^ (-d) := by
  have h := hcg ε h0 h1
  rw [← hw.2, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h

lemma exists_cover {D : Type*} [MetricSpace D] (ε : ℝ≥0)
    (h : Metric.coveringNumber ε (Set.univ : Set D) ≠ ⊤) :
    ∃ D' : Finset D, IsCoverWitness ε D' := by
  obtain ⟨C, -, hfin, hcov, henc⟩ := Metric.exists_set_encard_eq_coveringNumber h
  refine ⟨hfin.toFinset, ?_, ?_⟩
  · simpa using hcov
  · rw [← henc, hfin.encard_eq_coe_toFinset_card]

lemma exists_igw {D : Type*} (D' : Finset D) (hne : D'.Nonempty) (fhat : D → ℝ) (γ : ℝ)
    (hγ : 0 < γ) : ∃ p : PMF D, IsIGWOn D' fhat γ p := by
  classical
  let e : Fin D'.card ≃ D' := D'.equivFin.symm
  have hpos : 0 < D'.card := Finset.card_pos.mpr hne
  obtain ⟨b, -, hb⟩ := Finset.exists_max_image Finset.univ (fun i => fhat (e i))
    ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  have hg0 : ∀ i, 0 ≤ 2 * γ * (fhat (e b) - fhat (e i)) := fun i =>
    mul_nonneg (by positivity) (sub_nonneg.mpr (hb i (Finset.mem_univ _)))
  let F : ℝ → ℝ := fun lam => ∑ i, 1 / (lam + 2 * γ * (fhat (e b) - fhat (e i)))
  have hN1 : (1 : ℝ) ≤ D'.card := by exact_mod_cast hpos
  have hcont : ContinuousOn F (Set.Icc 1 (D'.card : ℝ)) := by
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro x hx
    have := hx.1
    have := hg0 i
    exact ne_of_gt (by linarith)
  have hF1 : 1 ≤ F 1 := by
    have := Finset.single_le_sum (f := fun i => 1 / ((1 : ℝ) + 2 * γ * (fhat (e b) - fhat (e i))))
      (fun i _ => by have := hg0 i; positivity) (Finset.mem_univ b)
    refine le_trans (le_of_eq ?_) this
    simp
  have hFN : F D'.card ≤ 1 := by
    have : ∀ i ∈ Finset.univ, 1 / ((D'.card : ℝ) + 2 * γ * (fhat (e b) - fhat (e i)))
        ≤ 1 / (D'.card : ℝ) := fun i _ => by
      have := hg0 i
      exact one_div_le_one_div_of_le (by linarith) (by linarith)
    have hs := Finset.sum_le_sum this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have e3 : (D'.card : ℝ) * (1 / (D'.card : ℝ)) = 1 := by field_simp
    rw [e3] at hs
    exact hs
  obtain ⟨lam, hlam, hFlam⟩ := intermediate_value_Icc' hN1 hcont ⟨hFN, hF1⟩
  let q : Fin D'.card → ℝ := fun i => 1 / (lam + 2 * γ * (fhat (e b) - fhat (e i)))
  have hq0 : ∀ i, 0 ≤ q i := fun i => by
    have := hg0 i
    have := hlam.1
    show 0 ≤ 1 / (lam + 2 * γ * (fhat (e b) - fhat (e i)))
    apply div_nonneg zero_le_one
    linarith
  have hqs : ∑ i, q i = 1 := hFlam
  let w : D → ENNReal := fun π => if h : π ∈ D' then ENNReal.ofReal (q (e.symm ⟨π, h⟩)) else 0
  have hwe : ∀ i, w (e i) = ENNReal.ofReal (q i) := fun i => by
    simp [w]
  have hw : ∑ π ∈ D', w π = 1 := by
    rw [← Finset.sum_coe_sort D', ← Equiv.sum_comp e]
    simp only [hwe]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hq0 i), hqs, ENNReal.ofReal_one]
  have hw0 : ∀ π ∉ D', w π = 0 := fun π hπ => by simp [w, hπ]
  refine ⟨PMF.ofFinset w D' hw hw0, fun π hπ => hw0 π hπ, e, b, ?_⟩
  have hpe : ∀ i, (PMF.ofFinset w D' hw hw0 (e i)).toReal = q i := fun i => by
    rw [PMF.ofFinset_apply, hwe, ENNReal.toReal_ofReal (hq0 i)]
  refine ⟨fun i => hb i (Finset.mem_univ _), ⟨lam, hlam, fun i => hpe i⟩,
    fun i => ENNReal.toReal_nonneg, ?_⟩
  simp only [hpe]
  exact hqs

end P18Aux

open FoundationsRL.DECExamples NNReal in
theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : Type*) [MetricSpace D] [Nonempty D] (d : ℝ), 0 < d →
      HasCoveringGrowth D d →
      ∀ fhat : D → ℝ, (∀ π, fhat π ∈ Set.Icc (0 : ℝ) 1) →
      ∀ γ : ℝ, 1 ≤ γ →
        (∀ (ε : ℝ≥0) (D' : Finset D) (p : PMF D), (ε : ℝ) = γ ^ (-1 / (d + 1)) →
          IsCoverWitness ε D' → IsIGWOn D' fhat γ p →
          ∀ f ∈ lipschitzClass D, offsetValue p f fhat γ ≤ C * γ ^ (-1 / (d + 1))) ∧
        decAt (lipschitzClass D) fhat γ ≤ ((C * γ ^ (-1 / (d + 1)) : ℝ) : EReal) := by
  refine ⟨3, by norm_num, ?_⟩
  intro D _ _ d hd hcg fhat _ γ hγ
  have hγ0 : 0 < γ := by linarith
  have hd1 : d + 1 ≠ 0 := by linarith
  have hr0 : 0 < γ ^ (-1 / (d + 1)) := Real.rpow_pos_of_pos hγ0 _
  have hr1 : γ ^ (-1 / (d + 1)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hγ
    rw [neg_div]
    exact neg_nonpos.mpr (by positivity)
  have hkey : (γ ^ (-1 / (d + 1))) ^ (-d) / γ = γ ^ (-1 / (d + 1)) := by
    rw [← Real.rpow_mul hγ0.le, ← Real.rpow_sub_one hγ0.ne']
    congr 1
    field_simp
    ring
  have hεfacts : ∀ ε : ℝ≥0, (ε : ℝ) = γ ^ (-1 / (d + 1)) → 0 < ε ∧ ε ≤ 1 := by
    intro ε hε
    refine ⟨?_, ?_⟩
    · have : (0 : ℝ) < ε := hε ▸ hr0
      exact_mod_cast this
    · have : (ε : ℝ) ≤ 1 := hε ▸ hr1
      exact_mod_cast this
  have part1 : ∀ (ε : ℝ≥0) (D' : Finset D) (p : PMF D), (ε : ℝ) = γ ^ (-1 / (d + 1)) →
      IsCoverWitness ε D' → IsIGWOn D' fhat γ p →
      ∀ f ∈ lipschitzClass D, offsetValue p f fhat γ ≤ 3 * γ ^ (-1 / (d + 1)) := by
    intro ε D' p hε hw hp f hf
    have h1 := P18Aux.core fhat γ hγ0 ε D' p hw.1 hp f hf
    obtain ⟨he0, he1⟩ := hεfacts ε hε
    have hcard := P18Aux.cardbound d hcg ε he0 he1 D' hw
    rw [hε] at hcard h1
    have h2 : 2 * (D'.card : ℝ) / γ ≤ 2 * ((γ ^ (-1 / (d + 1))) ^ (-d)) / γ := by gcongr
    rw [mul_div_assoc, mul_div_assoc, hkey] at h2
    rw [mul_div_assoc] at h1
    linarith
  refine ⟨part1, ?_⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ≥0, (ε : ℝ) = γ ^ (-1 / (d + 1)) := ⟨⟨_, hr0.le⟩, rfl⟩
  obtain ⟨he0, he1⟩ := hεfacts ε hε
  have hne : Metric.coveringNumber ε (Set.univ : Set D) ≠ ⊤ := by
    intro htop
    have h := hcg ε he0 he1
    rw [htop, ENat.toENNReal_top, top_le_iff] at h
    exact ENNReal.ofReal_ne_top h
  obtain ⟨D', hw⟩ := P18Aux.exists_cover ε hne
  have hD'ne : D'.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty D›
    have hc := hw.1
    rw [Metric.isCover_iff_subset_iUnion_closedBall] at hc
    have := hc (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_closedBall, Finset.mem_coe] at this
    obtain ⟨y, hy, -⟩ := this
    exact ⟨y, hy⟩
  obtain ⟨p, hp⟩ := P18Aux.exists_igw D' hD'ne fhat γ hγ0
  unfold decAt
  refine le_trans (iInf_le _ p) ?_
  refine iSup₂_le fun f hf => ?_
  exact EReal.coe_le_coe_iff.mpr (part1 ε D' p hε hw hp f hf)
