-- Prove2me | solution 1 for DefaultContagion.FinalSize.zHat_convergence
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:12:12.969015+00:00
-- url     : https://prove2.me/submissions/c571edc2-164a-4848-925c-38ef9a9266d0

import Mathlib
import Definitions.Def_DefaultContagion_FinalSize_Model
import Theorems.Thm_DefaultContagion_FinalSize_lemma_A_4

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DCFSzHat
open DefaultContagion.FinalSize

variable {X : Type*} [DecidableEq X]

lemma hasSum_muN (typ : (n : ℕ) → Fin n → X) (n : ℕ) (g : X → ℝ) :
    HasSum (fun x => muN typ n x * g x) ((∑ i : Fin n, g (typ n i)) / n) := by
  set s := Finset.univ.image (typ n)
  have h0 : ∀ x ∉ s, muN typ n x * g x = 0 := by
    intro x hx
    have : (Finset.univ.filter fun i : Fin n => typ n i = x) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro h; exact hx (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simp [muN, this]
  convert hasSum_sum_of_ne_finset_zero h0 using 1
  swap; · infer_instance
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s) (g := typ n)
    (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i)), Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const,
    nsmul_eq_mul, muN]
  ring

lemma binTail_one_le (d l : ℕ) : binTail d 1 l ≤ 1 := by
  have h : ∑ r ∈ Finset.range (d + 1), binPmf d 1 r = 1 := by
    calc ∑ r ∈ Finset.range (d + 1), binPmf d 1 r = ((1 : ℝ) + 0) ^ d := by
          rw [add_pow]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp [binPmf]; ring
      _ = 1 := by simp
  calc binTail d 1 l = ∑ r ∈ Finset.Icc l d, binPmf d 1 r := rfl
    _ ≤ ∑ r ∈ Finset.range (d + 1), binPmf d 1 r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr; simp [Finset.mem_Icc] at hr; simp; omega
      · intro r _ _; unfold binPmf; positivity
    _ = 1 := h

/-- The finite-economy `W` function is nonnegative at `z = 1`. -/
lemma fW_one_nonneg (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X) (qn : ℕ → X → ℕ → ℝ)
    (n : ℕ)
    (hqn : IsThresholdLaw dp (qn n)) (hdeg : ∑ i : Fin n, dp (typ n i) = ∑ i : Fin n, dm (typ n i)) :
    0 ≤ fW dp dm (lamN dp typ n) (muN typ n) (qn n) 1 := by
  unfold fW
  have hs := hasSum_muN typ n (fun x => (dm x : ℝ))
  have hlam : lamN dp typ n = ∑' x, muN typ n x * (dm x : ℝ) := by
    rw [hs.tsum_eq, lamN]
    congr 1
    exact_mod_cast hdeg
  have hle : ∀ x, muN typ n x * (dm x : ℝ) * ∑ θ ∈ Finset.Icc 1 (dp x),
      qn n x θ * binTail (dp x) 1 (dp x - θ + 1) ≤ muN typ n x * (dm x : ℝ) := by
    intro x
    have hmu : 0 ≤ muN typ n x * (dm x : ℝ) := by unfold muN; positivity
    have hsum : ∑ θ ∈ Finset.Icc 1 (dp x), qn n x θ * binTail (dp x) 1 (dp x - θ + 1) ≤ 1 := by
      obtain ⟨h0, -, h1⟩ := hqn x
      calc ∑ θ ∈ Finset.Icc 1 (dp x), qn n x θ * binTail (dp x) 1 (dp x - θ + 1)
          ≤ ∑ θ ∈ Finset.Icc 1 (dp x), qn n x θ :=
            Finset.sum_le_sum fun θ _ => by
              have := binTail_one_le (dp x) (dp x - θ + 1)
              nlinarith [h0 θ]
        _ ≤ ∑ θ ∈ Finset.range (dp x + 1), qn n x θ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro θ hθ; simp [Finset.mem_Icc] at hθ; simp; omega
            · intros; exact h0 _
        _ = 1 := h1
    nlinarith
  have hsum2 : Summable (fun x => muN typ n x * (dm x : ℝ) * ∑ θ ∈ Finset.Icc 1 (dp x),
      qn n x θ * binTail (dp x) 1 (dp x - θ + 1)) := by
    have := hasSum_muN typ n (fun x => (dm x : ℝ) * ∑ θ ∈ Finset.Icc 1 (dp x),
      qn n x θ * binTail (dp x) 1 (dp x - θ + 1))
    exact this.summable.congr fun x => by ring
  have := hsum2.tsum_le_tsum hle hs.summable
  rw [mul_one, hlam]
  linarith

lemma fW_muN_continuous (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X) (r : X → ℕ → ℝ) (n : ℕ) :
    Continuous (fun z => fW dp dm (lamN dp typ n) (muN typ n) r z) := by
  set s := Finset.univ.image (typ n)
  have h0 : ∀ z, ∀ x ∉ s, muN typ n x * (dm x : ℝ) *
      ∑ θ ∈ Finset.Icc 1 (dp x), r x θ * binTail (dp x) z (dp x - θ + 1) = 0 := by
    intro z x hx
    have : (Finset.univ.filter fun i : Fin n => typ n i = x) = ∅ := by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      intro h; exact hx (h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
    simp [muN, this]
  have e : (fun z => fW dp dm (lamN dp typ n) (muN typ n) r z) = fun z =>
      lamN dp typ n * z - ∑ x ∈ s, muN typ n x * (dm x : ℝ) *
        ∑ θ ∈ Finset.Icc 1 (dp x), r x θ * binTail (dp x) z (dp x - θ + 1) := by
    funext z; unfold fW; rw [tsum_eq_sum (h0 z)]
  rw [e]
  unfold binTail binPmf
  fun_prop

/-- Local sign change at a zero with positive derivative. -/
lemma local_sign {f : ℝ → ℝ} {a : ℝ} (hfa : f a = 0) (hd : 0 < deriv f a) :
    ∃ δ > 0, (∀ z, a < z → z < a + δ → 0 < f z) ∧ (∀ z, a - δ < z → z < a → f z < 0) := by
  have hdiff : DifferentiableAt ℝ f a := differentiableAt_of_deriv_ne_zero hd.ne'
  have ht := hdiff.hasDerivAt.tendsto_slope
  have hev : ∀ᶠ z in 𝓝[≠] a, 0 < slope f a z := ht.eventually (lt_mem_nhds hd)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨δ, hδ, fun z h1 h2 => ?_, fun z h1 h2 => ?_⟩
  · have hz : dist z a < δ := by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
    have := hball hz (Set.mem_compl_singleton_iff.2 (ne_of_gt h1))
    rw [slope_def_field, hfa, sub_zero] at this
    exact (div_pos_iff_of_pos_right (by linarith)).1 this
  · have hz : dist z a < δ := by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith
    have := hball hz (Set.mem_compl_singleton_iff.2 (ne_of_lt h2))
    rw [slope_def_field, hfa, sub_zero] at this
    by_contra hc
    push Not at hc
    have : f z / (z - a) ≤ 0 := div_nonpos_of_nonneg_of_nonpos hc (by linarith)
    linarith

end DCFSzHat

open DefaultContagion.FinalSize in
theorem solution {X : Type*} [Countable X] [DecidableEq X]
    (dp dm : X → ℕ) (typ : (n : ℕ) → Fin n → X)
    (qn : ℕ → X → ℕ → ℝ) (mu : X → ℝ) (q : X → ℕ → ℝ)
    (h2 : Assumption2 dp typ qn mu q)
    (h3a : Assumption3a dp dm typ mu)
    (h3b : Assumption3b dp dm typ) :
    let lam : ℝ := ∑' x, mu x * (dp x : ℝ)
    let zStar := lastZero (fW dp dm lam mu q)
    let zHat : ℕ → ℝ := fun n =>
      lastZero (fW dp dm (lamN dp typ n) (muN typ n) (qn n))
    0 < zStar → zStar ≤ 1 → 0 < deriv (fW dp dm lam mu q) zStar →
      Tendsto zHat atTop (𝓝 zStar) ∧
      ∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, ∀ z ∈ Set.Icc (zStar + ε) 1,
          0 < fW dp dm (lamN dp typ n) (muN typ n) (qn n) z := by
  intro lam zStar zHat hz0 hz1 hα
  set f := fW dp dm lam mu q with hf_def
  set fn : ℕ → ℝ → ℝ := fun n => fW dp dm (lamN dp typ n) (muN typ n) (qn n) with hfn_def
  have hU : TendstoUniformlyOn fn f atTop (Set.Icc (0 : ℝ) 1) := by
    have := lemma_A_4 dp dm typ qn mu q h2 h3a h3b 4 0
    simpa [fVec] using this
  have hfn_cont : ∀ n, Continuous (fn n) := fun n => DCFSzHat.fW_muN_continuous dp dm typ (qn n) n
  have hf_cont : ContinuousOn f (Set.Icc 0 1) :=
    hU.continuousOn (Eventually.of_forall (f := atTop) fun n => (hfn_cont n).continuousOn).frequently
  -- the zero set of `f`
  set Z := {z | z ∈ Set.Icc (0 : ℝ) 1 ∧ f z = 0} with hZ
  have hZbdd : BddAbove Z := ⟨1, fun z hz => hz.1.2⟩
  have hZne : Z.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : zStar = 0 := by
      show sSup Z = 0
      rw [h, Real.sSup_empty]
    linarith
  have hZclosed : IsClosed Z := by
    have := hf_cont.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := (0 : ℝ)))
    simpa [hZ, Set.preimage, Set.inter_def] using this
  have hzmem : zStar ∈ Z := hZclosed.csSup_mem hZne hZbdd
  have hfz : f zStar = 0 := hzmem.2
  obtain ⟨δ, hδ, hpos, hneg⟩ := DCFSzHat.local_sign hfz hα
  -- positivity of `f` to the right of `zStar`
  have hright : ∀ z, zStar < z → z ≤ 1 → 0 < f z := by
    intro z h1 h2
    have hne : f z ≠ 0 := by
      intro h
      have : z ≤ zStar := le_csSup hZbdd ⟨⟨by linarith, h2⟩, h⟩
      linarith
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exfalso
      set z1 := zStar + min (δ / 2) ((z - zStar) / 2)
      have hz1a : zStar < z1 := by simp only [z1]; have := lt_min (half_pos hδ) (half_pos (sub_pos.2 h1)); linarith
      have hz1b : z1 < zStar + δ := by simp only [z1]; have := min_le_left (δ / 2) ((z - zStar) / 2); linarith
      have hz1c : z1 < z := by simp only [z1]; have := min_le_right (δ / 2) ((z - zStar) / 2); linarith
      have hf1 := hpos z1 hz1a hz1b
      have hcont : ContinuousOn f (Set.Icc z1 z) :=
        hf_cont.mono (Set.Icc_subset_Icc (by linarith) h2)
      obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hz1c.le hcont ⟨hlt.le, hf1.le⟩
      have : y ≤ zStar := le_csSup hZbdd ⟨⟨by linarith [hy.1], by linarith [hy.2]⟩, hy0⟩
      linarith [hy.1]
    · exact hgt
  -- eventual positivity of `fn` on `[zStar + ε, 1]`
  have hpart2 : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ z ∈ Set.Icc (zStar + ε) 1, 0 < fn n z := by
    intro ε hε
    rcases (Set.Icc (zStar + ε) 1).eq_empty_or_nonempty with hE | hE
    · exact Eventually.of_forall fun n z hz => by simp [hE] at hz
    have hK : IsCompact (Set.Icc (zStar + ε) 1) := isCompact_Icc
    have hsub : Set.Icc (zStar + ε) 1 ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc (by linarith) le_rfl
    obtain ⟨m, hm, hmin⟩ := hK.exists_isMinOn hE (hf_cont.mono hsub)
    have hmpos : 0 < f m := hright m (by linarith [hm.1]) hm.2
    have hev := (Metric.tendstoUniformlyOn_iff.1 hU) (f m) hmpos
    filter_upwards [hev] with n hn z hz
    have h1 := hn z (hsub hz)
    rw [Real.dist_eq] at h1
    have h2 : f m ≤ f z := hmin hz
    have := (abs_lt.1 h1).2
    linarith
  refine ⟨?_, hpart2⟩
  -- convergence of the largest finite zeros
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := min (ε / 2) (min (zStar / 2) (δ / 2)) with he
  have he0 : 0 < e := by positivity
  have he1 : e ≤ ε / 2 := min_le_left _ _
  have he2 : e ≤ zStar / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : e ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hfl : f (zStar - e) < 0 := hneg _ (by linarith) (by linarith)
  have hmemL : zStar - e ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hevL : ∀ᶠ n in atTop, fn n (zStar - e) < 0 := by
    have := (hU.tendsto_at hmemL).eventually (gt_mem_nhds hfl)
    exact this
  obtain ⟨hdeg, -, -, -⟩ := h3a
  obtain ⟨-, -, -, hqn, -, -⟩ := h2
  have hev1 : ∀ᶠ n in atTop, 1 ≤ n := eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hevL.and ((hpart2 e he0).and hev1))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hL, hR, -⟩ := hN n hn
  set Zn := {z | z ∈ Set.Icc (0 : ℝ) 1 ∧ fn n z = 0} with hZn
  have hZnbdd : BddAbove Zn := ⟨1, fun z hz => hz.1.2⟩
  -- a zero in `[zStar - e, min (zStar + e) 1]`
  set b := min (zStar + e) 1 with hb
  have hb1 : b ≤ 1 := min_le_right _ _
  have hb2 : b ≤ zStar + e := min_le_left _ _
  have hfb : 0 ≤ fn n b := by
    rcases le_total (zStar + e) 1 with h | h
    · have : b = zStar + e := min_eq_left h
      rw [this]; exact (hR (zStar + e) ⟨le_rfl, h⟩).le
    · have : b = 1 := min_eq_right h
      rw [this]
      exact DCFSzHat.fW_one_nonneg dp dm typ qn n (hqn n) (hdeg n)
  have hab : zStar - e ≤ b := by
    rw [hb]; exact le_min (by linarith) (by linarith)
  obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hab (hfn_cont n).continuousOn ⟨hL.le, hfb⟩
  have hyZ : y ∈ Zn := ⟨⟨by linarith [hy.1], hy.2.trans hb1⟩, hy0⟩
  have hlow : y ≤ zHat n := le_csSup hZnbdd hyZ
  have hup : zHat n ≤ zStar + e := by
    apply csSup_le ⟨y, hyZ⟩
    intro w hw
    by_contra hc
    push Not at hc
    have := hR w ⟨hc.le, hw.1.2⟩
    rw [hw.2] at this
    exact lt_irrefl _ this
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1]
