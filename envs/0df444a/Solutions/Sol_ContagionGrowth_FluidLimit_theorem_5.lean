-- Prove2me | solution 1 for ContagionGrowth.FluidLimit.theorem_5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:48:42.117968+00:00
-- url     : https://prove2.me/submissions/1c1e0abb-9602-4546-9ea0-a9a84ee57218
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ContagionGrowth_FluidLimit_Limit
import Definitions.Def_ContagionGrowth_FluidLimit_Network
import Theorems.Thm_ContagionGrowth_FluidLimit_theorem_5_lower_bound
import Theorems.Thm_ContagionGrowth_FluidLimit_theorem_5_ii_survivors

open Filter Topology MeasureTheory
open ContagionGrowth.FluidLimit

namespace Sol5Aux

/-- The box `[0, π]^l` as an order interval of functions. -/
lemma box_eq (l : ℕ) (π : ℝ) :
    {x : Fin l → ℝ | ∀ i, x i ∈ Set.Icc 0 π} = Set.Icc (fun _ => (0 : ℝ)) (fun _ => π) := by
  ext x; simp [Set.mem_Icc, Pi.le_def, forall_and]

lemma mem_box (l : ℕ) (π : ℝ) (x : Fin l → ℝ) :
    x ∈ Set.Icc (fun _ => (0 : ℝ)) (fun _ => π) ↔ ∀ i, x i ∈ Set.Icc 0 π := by
  rw [← box_eq]; rfl

lemma vol_box (l : ℕ) (π : ℝ) :
    volume (Set.Icc (fun _ : Fin l => (0 : ℝ)) (fun _ => π)) = ENNReal.ofReal π ^ l := by
  rw [Real.volume_Icc_pi]; simp

lemma Pord_nonneg (c : ℝ) (θ l : ℕ) {π : ℝ} (hπ : 0 ≤ π) : 0 ≤ Pord c θ l π := by
  unfold Pord; split_ifs
  · exact zero_le_one
  · positivity

lemma Pord_le_one (c : ℝ) (θ l : ℕ) {π : ℝ} (hπ : 0 ≤ π) : Pord c θ l π ≤ 1 := by
  unfold Pord; split_ifs with h
  · exact le_rfl
  · rcases hπ.lt_or_eq with hπ | hπ
    · apply div_le_one_of_le₀ _ (by positivity)
      have hsub : {x : Fin l → ℝ | (∀ i, x i ∈ Set.Icc 0 π) ∧
          ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
            (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u} ⊆
          Set.Icc (fun _ => (0 : ℝ)) (fun _ => π) := by
        rw [← box_eq]; exact fun x hx => hx.1
      have h1 := measure_mono (μ := volume) hsub
      rw [vol_box] at h1
      have h2 : (ENNReal.ofReal π ^ l).toReal = π ^ l := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hπ.le]
      rw [← h2]
      exact ENNReal.toReal_mono (by simp) h1
    · subst hπ
      have : l ≠ 0 := by omega
      simp [zero_pow this]

/-- The subtracted sum in `B^α`. -/
noncomputable def Ssum (α : ℝ) (lam θ : ℕ) (π : ℝ) : ℝ :=
  ∑ l ∈ (Finset.range (lam + 1)).filter (fun l : ℕ => (l : ℤ) < ⌈(θ : ℝ) + α * lam * π⌉),
      (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) * Pord (1 / (α * lam)) θ l π

lemma Balpha_eq (α : ℝ) (lam θ : ℕ) (π : ℝ) (hθ : θ ≠ 0) :
    Balpha α lam θ π = 1 - Ssum α lam θ π := by
  simp [Balpha, Ssum, hθ]

lemma term_nonneg (α : ℝ) (lam θ l : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    0 ≤ (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) * Pord (1 / (α * lam)) θ l π := by
  have := Pord_nonneg (1 / (α * lam)) θ l h0
  have : 0 ≤ 1 - π := by linarith
  positivity

lemma Ssum_nonneg (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    0 ≤ Ssum α lam θ π :=
  Finset.sum_nonneg fun l _ => term_nonneg α lam θ l h0 h1

lemma Ssum_le_one (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    Ssum α lam θ π ≤ 1 := by
  unfold Ssum
  calc _ ≤ ∑ l ∈ Finset.range (lam + 1),
        (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) * Pord (1 / (α * lam)) θ l π :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun l _ _ => term_nonneg α lam θ l h0 h1)
    _ ≤ ∑ l ∈ Finset.range (lam + 1), π ^ l * (1 - π) ^ (lam - l) * (lam.choose l : ℝ) := by
        apply Finset.sum_le_sum; intro l _
        have := Pord_le_one (1 / (α * lam)) θ l h0
        have : 0 ≤ 1 - π := by linarith
        have : 0 ≤ (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) := by positivity
        nlinarith
    _ = 1 := by rw [← add_pow]; simp

lemma Balpha_le_one (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    Balpha α lam θ π ≤ 1 := by
  by_cases hθ : θ = 0
  · simp [Balpha, hθ]
  · rw [Balpha_eq _ _ _ _ hθ]; linarith [Ssum_nonneg α lam θ h0 h1]

lemma Balpha_nonneg (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 ≤ π) (h1 : π ≤ 1) :
    0 ≤ Balpha α lam θ π := by
  by_cases hθ : θ = 0
  · simp [Balpha, hθ]
  · rw [Balpha_eq _ _ _ _ hθ]; linarith [Ssum_le_one α lam θ h0 h1]

lemma piStar_nonneg (mu : ℕ × ℕ → ℝ) (α : ℝ) : 0 ≤ piStar mu α :=
  Real.sInf_nonneg fun _ hx => hx.1.1


/-- The count condition of `Pord` does not depend on `π`. -/
lemma vol_compare (c : ℝ) (θ l : ℕ) {π : ℝ} (h0 : 0 < π) (h1 : π ≤ 1) :
    (volume {x : Fin l → ℝ | (∀ i, x i ∈ Set.Icc 0 1) ∧
      ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
        (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}).toReal ≤
    (volume {x : Fin l → ℝ | (∀ i, x i ∈ Set.Icc 0 π) ∧
      ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
        (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}).toReal
      + (1 - π ^ l) := by
  set S1 := {x : Fin l → ℝ | (∀ i, x i ∈ Set.Icc 0 1) ∧
      ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
        (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}
  set Sπ := {x : Fin l → ℝ | (∀ i, x i ∈ Set.Icc 0 π) ∧
      ∀ u : ℕ, θ + 1 ≤ u → u ≤ l →
        (Finset.univ.filter (fun i => x i ≤ c * ((u : ℝ) - θ))).card < u}
  set B1 := Set.Icc (fun _ : Fin l => (0 : ℝ)) (fun _ => (1 : ℝ))
  set Bπ := Set.Icc (fun _ : Fin l => (0 : ℝ)) (fun _ => π)
  have hsub : S1 ⊆ Sπ ∪ (B1 \ Bπ) := by
    intro x hx
    by_cases hxπ : x ∈ Bπ
    · left
      exact ⟨(mem_box l π x).mp hxπ, hx.2⟩
    · right
      exact ⟨(mem_box l 1 x).mpr hx.1, hxπ⟩
  have hBB : Bπ ⊆ B1 := Set.Icc_subset_Icc le_rfl (fun _ => h1)
  have hdiff : volume (B1 \ Bπ) = ENNReal.ofReal (1 - π ^ l) := by
    rw [measure_sdiff hBB measurableSet_Icc.nullMeasurableSet (by rw [vol_box]; simp),
      vol_box, vol_box, ENNReal.ofReal_one, one_pow, ENNReal.ofReal_sub _ (by positivity),
      ENNReal.ofReal_one, ENNReal.ofReal_pow h0.le]
  have hSπ : volume Sπ ≠ ⊤ := by
    have : Sπ ⊆ Bπ := fun x hx => (mem_box l π x).mpr hx.1
    refine ne_top_of_le_ne_top ?_ (measure_mono this)
    rw [vol_box]; simp
  have h := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [hdiff] at h
  have hpl : π ^ l ≤ 1 := pow_le_one₀ h0.le h1
  calc (volume S1).toReal ≤ (volume Sπ + ENNReal.ofReal (1 - π ^ l)).toReal :=
        ENNReal.toReal_mono (by simp [hSπ]) h
    _ = _ := by rw [ENNReal.toReal_add hSπ (by simp), ENNReal.toReal_ofReal (by linarith)]

/-- Lower bound on the `l = λ` term of `S` near `π = 1`. -/
lemma Ssum_ge (α : ℝ) (lam θ : ℕ) {π : ℝ} (h0 : 0 < π) (h1 : π ≤ 1)
    (hmem : (lam : ℝ) < θ + α * lam * π) :
    Pord (1 / (α * lam)) θ lam 1 - (1 - π ^ lam) ≤ Ssum α lam θ π := by
  have hmemF : lam ∈ (Finset.range (lam + 1)).filter
      (fun l : ℕ => (l : ℤ) < ⌈(θ : ℝ) + α * lam * π⌉) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Int.lt_ceil.mpr (by exact_mod_cast hmem)⟩
  have hterm := Finset.single_le_sum (f := fun l =>
      (lam.choose l : ℝ) * π ^ l * (1 - π) ^ (lam - l) * Pord (1 / (α * lam)) θ l π)
    (fun l _ => term_nonneg α lam θ l h0.le h1) hmemF
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, pow_zero, mul_one] at hterm
  refine le_trans ?_ hterm
  unfold Pord
  split_ifs with h
  · simp
  · rw [one_pow, div_one, mul_div_cancel₀ _ (by positivity)]
    have := vol_compare (1 / (α * lam)) θ lam h0 h1
    linarith

lemma Ssum_at_one (α : ℝ) (lam θ : ℕ) :
    Ssum α lam θ 1 = if (lam : ℤ) < ⌈(θ : ℝ) + α * lam * 1⌉ then
      Pord (1 / (α * lam)) θ lam 1 else 0 := by
  unfold Ssum
  rw [Finset.sum_filter]
  rw [Finset.sum_eq_single lam]
  · simp
  · intro l hl hne
    have : l < lam := by simp at hl; omega
    have : lam - l ≠ 0 := by omega
    simp [zero_pow this]
  · intro h; simp at h

lemma J_gt (mu : ℕ × ℕ → ℝ) (α : ℝ) (hstar : piStar mu α = 1) {π : ℝ} (h0 : 0 ≤ π)
    (h1 : π < 1) : π < Jalpha mu α π := by
  by_contra h
  rw [not_lt] at h
  have : piStar mu α ≤ π := csInf_le ⟨0, fun x hx => hx.1.1⟩ ⟨⟨h0, h1.le⟩, h⟩
  linarith

lemma B_one (α : ℝ) (hα : 0 < α) (mu : ℕ × ℕ → ℝ) (hmu0 : ∀ p, 0 ≤ mu p)
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu)
    (hstar : piStar mu α = 1) (lam θ : ℕ) (hlam : 1 ≤ lam) (hθ : θ ≠ 0)
    (hm : 0 < mu (lam, θ)) : Balpha α lam θ 1 = 1 := by
  by_contra hne
  rw [Balpha_eq _ _ _ _ hθ] at hne
  have hS0 := Ssum_nonneg α lam θ (π := 1) zero_le_one le_rfl
  have hSpos : 0 < Ssum α lam θ 1 := lt_of_le_of_ne hS0 (fun h => hne (by rw [← h]; ring))
  rw [Ssum_at_one] at hSpos
  split_ifs at hSpos with hmem
  swap
  · exact (lt_irrefl _ hSpos).elim
  set d := Pord (1 / (α * lam)) θ lam 1 with hd
  have hmem' : (lam : ℝ) < θ + α * lam * 1 := by exact_mod_cast Int.lt_ceil.mp hmem
  set w0 := (lam : ℝ) * mu (lam, θ) / lbar mu with hw0
  have hw0pos : 0 < w0 := by
    have : (0 : ℝ) < lam := by exact_mod_cast hlam
    positivity
  -- choose π close to 1
  have e1 : ∀ᶠ π in 𝓝[<] (1 : ℝ), π < 1 := self_mem_nhdsWithin
  have e2 : ∀ᶠ π in 𝓝[<] (1 : ℝ), 0 < π :=
    nhdsWithin_le_nhds (lt_mem_nhds one_pos)
  have e3 : ∀ᶠ π in 𝓝[<] (1 : ℝ), (lam : ℝ) < θ + α * lam * π := by
    have ht : Tendsto (fun π : ℝ => (θ : ℝ) + α * lam * π) (𝓝[<] 1) (𝓝 (θ + α * lam * 1)) :=
      ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 1).mono_left
        nhdsWithin_le_nhds
    exact ht.eventually_const_lt hmem'
  have e4 : ∀ᶠ π in 𝓝[<] (1 : ℝ), 1 - d / 2 < π ^ lam := by
    have ht : Tendsto (fun π : ℝ => π ^ lam) (𝓝[<] 1) (𝓝 (1 ^ lam)) :=
      ((continuous_pow lam).tendsto 1).mono_left nhdsWithin_le_nhds
    rw [one_pow] at ht
    exact ht.eventually_const_lt (by linarith)
  have e5 : ∀ᶠ π in 𝓝[<] (1 : ℝ), 1 - w0 * (d / 2) < π :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_const_lt
      (by have : 0 < w0 * (d / 2) := by positivity
          linarith)
  obtain ⟨π, h1, h2, h3, h4, h5⟩ := (e1.and (e2.and (e3.and (e4.and e5)))).exists
  have hJ := J_gt mu α hstar h2.le h1
  -- summability
  have hsumm : Summable fun p : ℕ × ℕ =>
      (p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 π := by
    by_contra hns
    have : Jalpha mu α π = 0 := tsum_eq_zero_of_not_summable hns
    linarith
  have hw : HasSum (fun p : ℕ × ℕ => (p.1 : ℝ) * mu p / lbar mu) 1 := by
    have := hsum.hasSum.div_const (lbar mu)
    rwa [show (∑' p : ℕ × ℕ, (p.1 : ℝ) * mu p) = lbar mu from rfl, div_self hlb.ne'] at this
  have hg := hw.sub (hasSum_ite_eq (lam, θ) (w0 * (d / 2)))
  have hle := hasSum_le (f := fun p : ℕ × ℕ => (p.1 : ℝ) * mu p / lbar mu * Balpha α p.1 p.2 π)
    (g := fun p => (p.1 : ℝ) * mu p / lbar mu - if p = (lam, θ) then w0 * (d / 2) else 0)
    ?_ hsumm.hasSum hg
  · have : Jalpha mu α π ≤ 1 - w0 * (d / 2) := hle
    linarith
  · intro p
    have hwp : 0 ≤ (p.1 : ℝ) * mu p / lbar mu := by
      have := hmu0 p; positivity
    by_cases hp : p = (lam, θ)
    · subst hp
      simp only [if_true]
      rw [Balpha_eq _ _ _ _ hθ]
      have hS := Ssum_ge α lam θ h2 h1.le h3
      have : d / 2 ≤ Ssum α lam θ π := by rw [← hd] at hS; linarith
      rw [← hw0]
      nlinarith
    · simp only [hp, if_false, sub_zero]
      have := Balpha_le_one α p.1 p.2 h2.le h1.le
      nlinarith

/-- Part (i) analytic input: if `π* = 1` and no isolated node has a positive threshold, then
`L = Σ µ_{λ,θ} B^α_{λ,θ}(1) = 1`. -/
lemma L_eq_one (α : ℝ) (hα : 0 < α) (mu : ℕ × ℕ → ℝ) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1)
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu)
    (hstar : piStar mu α = 1) (hiso : ∀ θ : ℕ, 1 ≤ θ → mu (0, θ) = 0) :
    (∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α)) = 1 := by
  rw [hstar]
  conv_rhs => rw [← hmu1.tsum_eq]
  congr 1
  funext p
  obtain ⟨lam, θ⟩ := p
  rcases (hmu0 (lam, θ)).lt_or_eq with hm | hm
  · by_cases hθ : θ = 0
    · simp [Balpha, hθ]
    · have hlam : 1 ≤ lam := by
        by_contra h
        have : lam = 0 := by omega
        subst this
        have := hiso θ (by omega)
        linarith
      simp only
      rw [B_one α hα mu hmu0 hsum hlb hstar lam θ hlam hθ hm, mul_one]
  · simp [← hm]


section Prob

variable {n : ℕ} (deg : Fin n → ℕ)

lemma netProb_mono {E F : Set (Outcome deg)} (h : E ⊆ F) : netProb deg E ≤ netProb deg F := by
  unfold netProb
  apply Finset.sum_le_sum
  intro σ _
  gcongr

lemma netProb_union_le (E F : Set (Outcome deg)) :
    netProb deg (E ∪ F) ≤ netProb deg E + netProb deg F := by
  unfold netProb
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ _
  rw [← mul_add]
  gcongr
  exact measure_union_le (μ := (gapsLaw deg).prod (choiceLaw deg))
    {x | (σ, x) ∈ E} {x | (σ, x) ∈ F}

lemma netProb_biUnion_le {ι : Type*} [DecidableEq ι] (K : Finset ι)
    (E : ι → Set (Outcome deg)) :
    netProb deg (⋃ p ∈ K, E p) ≤ ∑ p ∈ K, netProb deg (E p) := by
  induction K using Finset.induction_on with
  | empty =>
    simp only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Finset.sum_empty]
    unfold netProb; simp
  | insert a K ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (netProb_union_le deg _ _).trans (add_le_add le_rfl ih)

lemma netProb_univ (hn : 1 ≤ n) : netProb deg Set.univ = 1 := by
  have : IsProbabilityMeasure (ProbabilityTheory.expMeasure (n : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by exact_mod_cast hn)
  have : IsProbabilityMeasure (volume.restrict (Set.Ico (0 : ℝ) 1)) := ⟨by simp⟩
  have : IsProbabilityMeasure (gapsLaw deg) := by unfold gapsLaw; infer_instance
  have : IsProbabilityMeasure (choiceLaw deg) := by unfold choiceLaw; infer_instance
  unfold netProb
  simp only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp)

lemma netProb_le_one (hn : 1 ≤ n) (E : Set (Outcome deg)) : netProb deg E ≤ 1 :=
  (netProb_mono deg (Set.subset_univ E)).trans (netProb_univ deg hn).le

lemma numFailed_le (θs : Fin n → ℕ) (α : ℝ) (ω : Outcome deg) : numFailed deg θs α ω ≤ n := by
  unfold numFailed
  simpa using Finset.card_le_univ (finalState deg θs α ω).failed

lemma survivors_sum_le (θs : Fin n → ℕ) (α : ℝ) (ω : Outcome deg) (K : Finset (ℕ × ℕ)) :
    ∑ p ∈ K, survivors deg θs α p.1 p.2 ω + numFailed deg θs α ω ≤ n := by
  classical
  set F := (finalState deg θs α ω).failed
  set G := Finset.univ.filter (fun i : Fin n => i ∉ F)
  have h1 : ∑ p ∈ K, survivors deg θs α p.1 p.2 ω =
      (G.filter (fun i => (deg i, θs i) ∈ K)).card := by
    have hf := Finset.card_eq_sum_card_fiberwise (f := fun i => (deg i, θs i)) (t := K)
      (s := G.filter (fun i => (deg i, θs i) ∈ K)) (fun i hi => (Finset.mem_filter.mp hi).2)
    rw [hf]
    apply Finset.sum_congr rfl
    intro p hp
    unfold survivors
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, G, F]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h3, ?_⟩, ?_⟩
      · rw [show (deg i, θs i) = p from Prod.ext h1 h2]; exact hp
      · exact Prod.ext h1 h2
    · rintro ⟨⟨h3, _⟩, h4⟩
      rw [← h4]; exact ⟨rfl, rfl, h3⟩
  have h2 : (G.filter (fun i => (deg i, θs i) ∈ K)).card ≤ G.card := Finset.card_filter_le _ _
  have h3 : G.card + F.card = n := by
    have hG : G = Fᶜ := by ext; simp [G]
    have hF : F.card ≤ n := by simpa using Finset.card_le_univ F
    rw [hG, Finset.card_compl, Fintype.card_fin]
    omega
  change _ + F.card ≤ n
  omega

end Prob

end Sol5Aux

open Sol5Aux in
theorem solution (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (mu : ℕ × ℕ → ℝ) (hmu0 : ∀ p, 0 ≤ mu p)
    (hmu1 : HasSum mu 1) (deg θs : (n : ℕ) → Fin n → ℕ)
    (hC1 : ∀ lam θ : ℕ, Tendsto (fun n => muN (deg n) (θs n) lam θ) atTop (𝓝 (mu (lam, θ))))
    (hsum : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * mu p) (hlb : 0 < lbar mu)
    (hC2 : Tendsto (fun n => lbarN (deg n)) atTop (𝓝 (lbar mu))) :
    (∀ ε > 0, Tendsto (fun n => netProb (deg n)
      {ω | (∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α)) - ε ≤
        (numFailed (deg n) (θs n) α ω : ℝ) / n}) atTop (𝓝 1)) ∧
    (piStar mu α = 1 → (∀ θ : ℕ, 1 ≤ θ → mu (0, θ) = 0) →
      ∀ ε > 0, Tendsto (fun n => netProb (deg n)
        {ω | ε < |(numFailed (deg n) (θs n) α ω : ℝ) / n - 1|}) atTop (𝓝 0)) ∧
    (piStar mu α < 1 → IsStableFixedPoint mu α →
      (∀ ε > 0, Tendsto (fun n => netProb (deg n)
        {ω | ε < |(numFailed (deg n) (θs n) α ω : ℝ) / n -
          ∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α)|}) atTop (𝓝 0)) ∧
      ∀ lam θ : ℕ, ∀ ε > 0, Tendsto (fun n => netProb (deg n)
        {ω | ε < |(survivors (deg n) (θs n) α lam θ ω : ℝ) / n -
          mu (lam, θ) * (1 - Balpha α lam θ (piStar mu α))|}) atTop (𝓝 0)) := by
  have hLB := ContagionGrowth.FluidLimit.theorem_5_lower_bound α hα hα1 mu hmu0 hmu1 deg θs hC1
    hsum hlb hC2
  set L := ∑' p : ℕ × ℕ, mu p * Balpha α p.1 p.2 (piStar mu α) with hL
  have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  refine ⟨?_, ?_, ?_⟩
  · -- the lower bound, in the form `P(A_n) → 1`
    intro ε hε
    have h0 := hLB ε hε
    have hlow : Tendsto (fun n => 1 - netProb (deg n)
        {ω | (numFailed (deg n) (θs n) α ω : ℝ) / n < L - ε}) atTop (𝓝 1) := by
      have := ENNReal.Tendsto.sub tendsto_const_nhds h0 (Or.inl ENNReal.one_ne_top)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [hev] with n hn
      rw [tsub_le_iff_right, ← netProb_univ (deg n) hn]
      refine le_trans (netProb_mono _ ?_) (netProb_union_le _ _ _)
      intro ω _
      by_cases h : L - ε ≤ (numFailed (deg n) (θs n) α ω : ℝ) / n
      · exact Or.inl h
      · exact Or.inr (not_le.mp h)
    · filter_upwards [hev] with n hn
      exact netProb_le_one _ hn _
  · -- part (i)
    intro hstar hiso ε hε
    have hL1 : L = 1 := L_eq_one α hα mu hmu0 hmu1 hsum hlb hstar hiso
    have h0 := hLB ε hε
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hev] with n hn
    apply netProb_mono
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hX : (numFailed (deg n) (θs n) α ω : ℝ) / n ≤ 1 := by
      rw [div_le_one hn']; exact_mod_cast numFailed_le _ _ _ _
    rw [hL1]
    rw [abs_sub_comm, abs_of_nonneg (by linarith)] at hω
    linarith
  · -- part (ii)
    intro hstar hstab
    have hS := ContagionGrowth.FluidLimit.theorem_5_ii_survivors α hα hα1 mu hmu0 hmu1 deg θs
      hC1 hsum hlb hC2 hstar hstab
    refine ⟨?_, hS⟩
    intro ε hε
    have hπ0 := piStar_nonneg mu α
    have hπ1 := hstar.le
    have hBsum : HasSum (fun p : ℕ × ℕ => mu p * Balpha α p.1 p.2 (piStar mu α)) L := by
      have : Summable (fun p : ℕ × ℕ => mu p * Balpha α p.1 p.2 (piStar mu α)) :=
        Summable.of_nonneg_of_le
          (fun p => mul_nonneg (hmu0 p) (Balpha_nonneg α p.1 p.2 hπ0 hπ1))
          (fun p => by
            have := Balpha_le_one α p.1 p.2 hπ0 hπ1
            have := hmu0 p
            nlinarith) hmu1.summable
      exact this.hasSum
    have hc : HasSum (fun p : ℕ × ℕ => mu (p.1, p.2) * (1 - Balpha α p.1 p.2 (piStar mu α)))
        (1 - L) := by
      have h2 : (fun p : ℕ × ℕ => mu (p.1, p.2) * (1 - Balpha α p.1 p.2 (piStar mu α))) =
          (fun p => mu p - mu p * Balpha α p.1 p.2 (piStar mu α)) := by
        funext p; simp only [Prod.mk.eta]; ring
      rw [h2]; exact hmu1.sub hBsum
    obtain ⟨K, hK⟩ := ((show Tendsto (fun s : Finset (ℕ × ℕ) =>
        ∑ p ∈ s, mu (p.1, p.2) * (1 - Balpha α p.1 p.2 (piStar mu α)))
        (SummationFilter.unconditional (ℕ × ℕ)).filter (𝓝 (1 - L)) from hc).eventually
      (Ioi_mem_nhds (show 1 - L - ε / 2 < 1 - L by linarith))).exists
    set δ : ℝ := ε / (2 * ((K.card : ℝ) + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    have hKδ : (K.card : ℝ) * δ ≤ ε / 2 := by
      rw [hδdef, show (K.card : ℝ) * (ε / (2 * ((K.card : ℝ) + 1))) =
        ε / 2 * ((K.card : ℝ) / ((K.card : ℝ) + 1)) by field_simp]
      exact mul_le_of_le_one_right (by positivity) (div_le_one_of_le₀ (by linarith) (by positivity))
    have hsumT : Tendsto (fun n => netProb (deg n)
        {ω | (numFailed (deg n) (θs n) α ω : ℝ) / n < L - ε} +
        ∑ p ∈ K, netProb (deg n) {ω | δ < |(survivors (deg n) (θs n) α p.1 p.2 ω : ℝ) / n -
          mu (p.1, p.2) * (1 - Balpha α p.1 p.2 (piStar mu α))|}) atTop (𝓝 0) := by
      have := (hLB ε hε).add (tendsto_finsetSum K (fun p _ => hS p.1 p.2 δ hδ))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsumT
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hev] with n hn
    refine le_trans (netProb_mono _ ?_) ((netProb_union_le _ _ _).trans
      (add_le_add le_rfl (netProb_biUnion_le _ K _)))
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion] at hω ⊢
    by_contra hcon
    simp only [not_or, not_lt, not_exists] at hcon
    obtain ⟨hA, hB⟩ := hcon
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set X : ℝ := (numFailed (deg n) (θs n) α ω : ℝ) / n with hXdef
    have hsurv := survivors_sum_le (deg n) (θs n) α ω K
    have hsurvR : (∑ p ∈ K, (survivors (deg n) (θs n) α p.1 p.2 ω : ℝ)) / n + X ≤ 1 := by
      rw [hXdef, ← add_div, div_le_one hn']
      exact_mod_cast hsurv
    have hlow : ∑ p ∈ K, (mu (p.1, p.2) * (1 - Balpha α p.1 p.2 (piStar mu α)) - δ) ≤
        (∑ p ∈ K, (survivors (deg n) (θs n) α p.1 p.2 ω : ℝ)) / n := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro p hp
      have := (abs_le.mp (hB p hp)).1
      linarith
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hlow
    have hXL : ε < X - L := by
      rcases lt_abs.mp hω with h | h
      · exact h
      · linarith
    linarith
