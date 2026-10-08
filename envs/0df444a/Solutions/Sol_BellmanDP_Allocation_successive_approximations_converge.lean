-- Prove2me | solution 1 for BellmanDP.Allocation.successive_approximations_converge
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:07:40.607304+00:00
-- url     : https://prove2.me/submissions/2823eb60-b85b-4b9e-809c-4bdaa7a4a456

import Mathlib
import Definitions.Def_BellmanDP_Allocation_Model



namespace BellmanDP.Allocation

noncomputable def opT (g h : ℝ → ℝ) (a b : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  sSup ((fun y => allocT g h a b φ x y) '' Set.Icc 0 x)

lemma allocIter_succ_eq (g h : ℝ → ℝ) (a b : ℝ) (f₀ : ℝ → ℝ) (N : ℕ) :
    allocIter g h a b f₀ (N + 1) = opT g h a b (allocIter g h a b f₀ N) := rfl

lemma cont_ext {φ : ℝ → ℝ} (hφ : ContinuousOn φ (Set.Ici 0)) :
    Continuous (fun y => φ (max y 0)) :=
  hφ.comp_continuous (continuous_id.max continuous_const) (fun y => Set.mem_Ici.2 (le_max_right _ _))

lemma allocT_contOn {g h φ : ℝ → ℝ} {a b x : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) (hφ : ContinuousOn φ (Set.Ici 0)) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (fun y => allocT g h a b φ x y) (Set.Icc 0 x) := by
  unfold allocT
  have h1 : ContinuousOn g (Set.Icc 0 x) := hg.mono Set.Icc_subset_Ici_self
  have h2 : ContinuousOn (fun y => h (x - y)) (Set.Icc 0 x) :=
    hh.comp (by fun_prop) (fun y hy => by simp only [Set.mem_Ici]; linarith [hy.2])
  have h3 : ContinuousOn (fun y => φ (a * y + b * (x - y))) (Set.Icc 0 x) :=
    hφ.comp (by fun_prop) (fun y hy => by
      simp only [Set.mem_Ici]
      have := hy.1; have : 0 ≤ x - y := by linarith [hy.2]
      positivity)
  exact (h1.add h2).add h3

lemma opT_greatest {g h φ : ℝ → ℝ} {a b x : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) (hφ : ContinuousOn φ (Set.Ici 0)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 ≤ x) :
    IsGreatest ((fun y => allocT g h a b φ x y) '' Set.Icc 0 x) (opT g h a b φ x) := by
  have hK : IsCompact ((fun y => allocT g h a b φ x y) '' Set.Icc 0 x) :=
    isCompact_Icc.image_of_continuousOn (allocT_contOn hg hh hφ ha hb)
  have hne : ((fun y => allocT g h a b φ x y) '' Set.Icc 0 x).Nonempty :=
    (Set.nonempty_Icc.2 hx).image _
  exact ⟨hK.sSup_mem hne, fun z hz => le_csSup hK.bddAbove hz⟩

lemma opT_contOn {g h φ : ℝ → ℝ} {a b : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) (hφ : ContinuousOn φ (Set.Ici 0)) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ContinuousOn (opT g h a b φ) (Set.Ici 0) := by
  have cg := cont_ext hg
  have ch := cont_ext hh
  have cφ := cont_ext hφ
  set K : ℝ → ℝ → ℝ := fun x t =>
    g (max (t * max x 0) 0) + h (max (max x 0 - t * max x 0) 0) +
      φ (max (a * (t * max x 0) + b * (max x 0 - t * max x 0)) 0) with hKdef
  have hKc : Continuous (fun p : ℝ × ℝ => K p.1 p.2) := by
    simp only [hKdef]
    have e1 : Continuous (fun p : ℝ × ℝ => p.2 * max p.1 0) := by fun_prop
    have e2 : Continuous (fun p : ℝ × ℝ => max p.1 0 - p.2 * max p.1 0) := by fun_prop
    have e3 : Continuous (fun p : ℝ × ℝ => a * (p.2 * max p.1 0) + b * (max p.1 0 - p.2 * max p.1 0)) := by
      fun_prop
    exact ((cg.comp e1).add (ch.comp e2)).add (cφ.comp e3)
  have hc := IsCompact.continuous_sSup (f := K) (K := Set.Icc (0:ℝ) 1) isCompact_Icc hKc
  refine ContinuousOn.congr hc.continuousOn ?_
  intro x hx
  simp only [Set.mem_Ici] at hx
  have hmx : ∀ u : ℝ, 0 ≤ u → max u 0 = u := fun u hu => max_eq_left hu
  unfold opT
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨y, ⟨hy0, hyx⟩, rfl⟩
    rcases eq_or_lt_of_le hx with h0 | hpos
    · subst h0
      have : y = 0 := le_antisymm hyx hy0
      subst this
      refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      simp [hKdef, allocT]
    · refine ⟨y / x, ⟨div_nonneg hy0 hx, (div_le_one hpos).2 hyx⟩, ?_⟩
      have hyx' : y / x * x = y := div_mul_cancel₀ y hpos.ne'
      simp only [hKdef, allocT]
      rw [hmx x hx, hyx', hmx y hy0, hmx (x - y) (by linarith)]
      rw [hmx _ (by have : 0 ≤ x - y := by linarith
                    positivity)]
  · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
    refine ⟨t * x, ⟨by positivity, by nlinarith⟩, ?_⟩
    have h1 : 0 ≤ t * x := by positivity
    have h2 : 0 ≤ x - t * x := by nlinarith
    simp only [hKdef, allocT]
    rw [hmx x hx, hmx _ h1, hmx _ h2, hmx _ (by positivity)]

/-- key comparison -/
lemma greatest_diff {g h φ ψ : ℝ → ℝ} {a b x p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x)
    (hp : IsGreatest ((fun y => allocT g h a b φ x y) '' Set.Icc 0 x) p)
    (hq : IsGreatest ((fun y => allocT g h a b ψ x y) '' Set.Icc 0 x) q) :
    ∃ z ∈ Set.Icc 0 (max a b * x), |p - q| ≤ |φ z - ψ z| := by
  obtain ⟨y1, hy1, e1⟩ := hp.1
  obtain ⟨y2, hy2, e2⟩ := hq.1
  have q1 := hq.2 ⟨y1, hy1, rfl⟩
  have p2 := hp.2 ⟨y2, hy2, rfl⟩
  simp only at e1 e2 q1 p2
  have zmem : ∀ y ∈ Set.Icc 0 x, a * y + b * (x - y) ∈ Set.Icc 0 (max a b * x) := by
    intro y hy
    have h0 := hy.1; have h1 : 0 ≤ x - y := by linarith [hy.2]
    constructor
    · positivity
    · have := mul_le_mul_of_nonneg_right (le_max_left a b) h0
      have := mul_le_mul_of_nonneg_right (le_max_right a b) h1
      nlinarith
  unfold allocT at e1 e2 q1 p2
  rcases le_total q p with hpq | hpq
  · refine ⟨_, zmem y1 hy1, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    exact le_trans (by linarith) (le_abs_self _)
  · refine ⟨_, zmem y2 hy2, ?_⟩
    rw [abs_of_nonpos (by linarith)]
    have := neg_le_abs (φ (a * y2 + b * (x - y2)) - ψ (a * y2 + b * (x - y2)))
    linarith


lemma m_contOn {g h : ℝ → ℝ} {x : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) :
    ContinuousOn (fun y => max |g y| |h y|) (Set.Icc 0 x) :=
  continuous_max.comp_continuousOn (ContinuousOn.prodMk
    (ContinuousOn.abs (hg.mono Set.Icc_subset_Ici_self))
    (ContinuousOn.abs (hh.mono Set.Icc_subset_Ici_self)))

lemma m_bdd {g h : ℝ → ℝ} {x : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) :
    BddAbove ((fun y => max |g y| |h y|) '' Set.Icc 0 x) :=
  (isCompact_Icc.image_of_continuousOn (m_contOn hg hh)).bddAbove

lemma m_bound {g h : ℝ → ℝ} {x y : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) (hy : y ∈ Set.Icc 0 x) :
    |g y| ≤ allocM g h x ∧ |h y| ≤ allocM g h x := by
  have := le_csSup (m_bdd hg hh) ⟨y, hy, rfl⟩
  exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩

lemma m_mono {g h : ℝ → ℝ} {x x' : ℝ} (hg : ContinuousOn g (Set.Ici 0))
    (hh : ContinuousOn h (Set.Ici 0)) (hx : 0 ≤ x) (hxx : x ≤ x') :
    allocM g h x ≤ allocM g h x' :=
  csSup_le_csSup (m_bdd hg hh) ((Set.nonempty_Icc.2 hx).image _)
    (Set.image_mono (Set.Icc_subset_Icc le_rfl hxx))

lemma m_zero {g h : ℝ → ℝ} (hg0 : g 0 = 0) (hh0 : h 0 = 0) : allocM g h 0 = 0 := by
  unfold allocM
  rw [Set.Icc_self, Set.image_singleton, csSup_singleton]
  simp [hg0, hh0]

theorem uniq_core (g h : ℝ → ℝ) (a b : ℝ) (hyp : AllocationHyp g h a b)
    (F f : ℝ → ℝ) (hF : IsAllocationSolution g h a b F) (hf : IsAllocationSolution g h a b f)
    (hFc : ContinuousWithinAt F (Set.Ici 0) 0) (hF0 : F 0 = 0)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ∀ x : ℝ, 0 ≤ x → F x = f x := by
  intro x hx
  set c := max a b with hc
  have hc0 : 0 ≤ c := le_max_of_le_left hyp.a_nonneg
  have hc1 : c < 1 := max_lt hyp.a_lt_one hyp.b_lt_one
  have chain : ∀ n : ℕ, ∃ z ∈ Set.Icc 0 (c ^ n * x), |F x - f x| ≤ |F z - f z| := by
    intro n
    induction n with
    | zero => exact ⟨x, ⟨hx, by simp⟩, le_rfl⟩
    | succ n ih =>
      obtain ⟨z, hz, hle⟩ := ih
      obtain ⟨z', hz', hle'⟩ := greatest_diff hyp.a_nonneg hyp.b_nonneg hz.1 (hF z hz.1) (hf z hz.1)
      refine ⟨z', ⟨hz'.1, ?_⟩, hle.trans hle'⟩
      calc z' ≤ c * z := hz'.2
        _ ≤ c * (c ^ n * x) := mul_le_mul_of_nonneg_left hz.2 hc0
        _ = c ^ (n + 1) * x := by ring
  have hu : ContinuousWithinAt (fun z => |F z - f z|) (Set.Ici 0) 0 := (hFc.sub hfc).abs
  have key : ∀ ε > 0, |F x - f x| < ε := by
    intro ε hε
    rw [Metric.continuousWithinAt_iff] at hu
    obtain ⟨δ, hδ, hδ'⟩ := hu ε hε
    have ht : Filter.Tendsto (fun n : ℕ => c ^ n * x) Filter.atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const x
    obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
    obtain ⟨z, hz, hle⟩ := chain n
    have := hδ' (x := z) (Set.mem_Ici.2 hz.1) (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.1]; linarith [hz.2])
    simp only [hF0, hf0, sub_zero, Real.dist_eq, abs_abs, abs_zero] at this
    linarith
  have : |F x - f x| ≤ 0 := le_of_forall_pos_lt_add (fun ε hε => by simpa using key ε hε)
  have := abs_nonpos_iff.1 this
  linarith

theorem exist_core (g h : ℝ → ℝ) (a b : ℝ) (hyp : AllocationHyp g h a b) :
    ∃ f : ℝ → ℝ, IsAllocationSolution g h a b f ∧ f 0 = 0 ∧ ContinuousOn f (Set.Ici 0) := by
  set c := max a b with hc
  have hc0 : 0 ≤ c := le_max_of_le_left hyp.a_nonneg
  have hc1 : c < 1 := max_lt hyp.a_lt_one hyp.b_lt_one
  have hg := hyp.cont_g
  have hh := hyp.cont_h
  have ha := hyp.a_nonneg
  have hb := hyp.b_nonneg
  set fN : ℕ → ℝ → ℝ := allocIter g h a b (fun _ => 0) with hfN
  have fN0 : fN 0 = fun _ => 0 := rfl
  have fNs : ∀ N, fN (N + 1) = opT g h a b (fN N) := fun N => rfl
  have fNc : ∀ N, ContinuousOn (fN N) (Set.Ici 0) := by
    intro N
    induction N with
    | zero => rw [fN0]; exact continuousOn_const
    | succ N ih => rw [fNs]; exact opT_contOn hg hh ih ha hb
  have fNg : ∀ N x, 0 ≤ x →
      IsGreatest ((fun y => allocT g h a b (fN N) x y) '' Set.Icc 0 x) (fN (N + 1) x) := by
    intro N x hx; rw [fNs]; exact opT_greatest hg hh (fNc N) ha hb hx
  have bnd : ∀ N x, 0 ≤ x → |fN (N + 1) x - fN N x| ≤ 2 * allocM g h (c ^ N * x) := by
    intro N
    induction N with
    | zero =>
      intro x hx
      obtain ⟨y, hy, e⟩ := (fNg 0 x hx).1
      have hy' : x - y ∈ Set.Icc 0 x := ⟨by linarith [hy.2], by linarith [hy.1]⟩
      rw [← e]
      simp only [fN0, allocT, add_zero, sub_zero, pow_zero, one_mul]
      have := (m_bound hg hh hy).1
      have := (m_bound hg hh hy').2
      calc |g y + h (x - y)| ≤ |g y| + |h (x - y)| := abs_add_le _ _
        _ ≤ _ := by linarith
    | succ N ih =>
      intro x hx
      obtain ⟨z, hz, hle⟩ := greatest_diff ha hb hx (fNg (N + 1) x hx) (fNg N x hx)
      refine hle.trans ((ih z hz.1).trans ?_)
      have : allocM g h (c ^ N * z) ≤ allocM g h (c ^ (N + 1) * x) :=
        m_mono hg hh (by have := hz.1; positivity)
          (by rw [pow_succ, mul_assoc]; exact mul_le_mul_of_nonneg_left hz.2 (by positivity))
      linarith
  set d : ℕ → ℝ → ℝ := fun k x => fN (k + 1) x - fN k x with hd
  have tele : ∀ N x, (∑ k ∈ Finset.range N, d k x) = fN N x := by
    intro N x
    simp only [hd]
    rw [Finset.sum_range_sub (fun k => fN k x)]
    simp [fN0]
  set F : ℝ → ℝ := fun x => ∑' k, d k x with hF
  have unif : ∀ R, 0 ≤ R → TendstoUniformlyOn fN F Filter.atTop (Set.Icc 0 R) := by
    intro R hR
    have hs : Summable (fun k : ℕ => 2 * allocM g h (c ^ k * R)) :=
      (hyp.summable_m R hR).mul_left 2
    have := tendstoUniformlyOn_tsum_nat hs (f := d) (s := Set.Icc 0 R) (by
      intro k x hx
      rw [Real.norm_eq_abs]
      refine (bnd k x hx.1).trans ?_
      have := m_mono hg hh (x := c ^ k * x) (x' := c ^ k * R) (by have := hx.1; positivity)
        (mul_le_mul_of_nonneg_left hx.2 (by positivity))
      linarith)
    have e : (fun N x => ∑ n ∈ Finset.range N, d n x) = fN := by
      funext N x; exact tele N x
    rw [e] at this
    exact this
  have Fcont : ContinuousOn F (Set.Ici 0) := by
    intro x hx
    have hx' : 0 ≤ x := hx
    have hU := unif (x + 1) (by linarith)
    have hcO : ContinuousOn F (Set.Icc 0 (x + 1)) :=
      hU.continuousOn (Filter.Frequently.of_forall (fun N => (fNc N).mono Set.Icc_subset_Ici_self))
    refine (hcO x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin ?_
    exact Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Ici 0) (Iio_mem_nhds (by linarith : x < x + 1)))
      (fun y hy => ⟨hy.1, le_of_lt hy.2⟩)
  have F0 : F 0 = 0 := by
    have : ∀ k, d k 0 = 0 := by
      intro k
      have := bnd k 0 le_rfl
      rw [mul_zero, m_zero hyp.g_zero hyp.h_zero, mul_zero] at this
      exact abs_nonpos_iff.1 this
    simp [hF, this]
  refine ⟨F, ?_, F0, Fcont⟩
  intro x hx
  have hG := opT_greatest hg hh Fcont ha hb hx
  suffices hFx : F x = opT g h a b F x by rw [hFx]; exact hG
  have key : ∀ ε > 0, |F x - opT g h a b F x| < 2 * ε := by
    intro ε hε
    have hU := Metric.tendstoUniformlyOn_iff.1 (unif x hx) ε hε
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hU
    obtain ⟨z, hz, hle⟩ := greatest_diff ha hb hx (fNg N0 x hx) hG
    have hzx : z ∈ Set.Icc 0 x := ⟨hz.1, hz.2.trans (by nlinarith)⟩
    have h1 := hN0 N0 le_rfl z hzx
    have h2 := hN0 (N0 + 1) (Nat.le_succ _) x ⟨hx, le_rfl⟩
    rw [Real.dist_eq] at h1 h2
    have h1' : |fN N0 z - F z| < ε := by rw [abs_sub_comm]; exact h1
    calc |F x - opT g h a b F x|
        ≤ |F x - fN (N0 + 1) x| + |fN (N0 + 1) x - opT g h a b F x| := abs_sub_le _ _ _
      _ < ε + ε := add_lt_add_of_lt_of_le h2 (hle.trans h1'.le)
      _ = 2 * ε := by ring
  have : |F x - opT g h a b F x| ≤ 0 := by
    refine le_of_forall_pos_lt_add (fun ε hε => ?_)
    have := key (ε / 2) (by positivity)
    simp only [zero_add]; linarith
  have := abs_nonpos_iff.1 this
  linarith

theorem alloc_main (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b) :
    ∃ f : ℝ → ℝ, IsAllocationSolution g h a b f ∧
      ContinuousWithinAt f (Set.Ici 0) 0 ∧ f 0 = 0 ∧
      ContinuousOn f (Set.Ici 0) ∧
      ∀ F : ℝ → ℝ, IsAllocationSolution g h a b F →
        ContinuousWithinAt F (Set.Ici 0) 0 → F 0 = 0 →
        ∀ x : ℝ, 0 ≤ x → F x = f x := by
  obtain ⟨f, hf, hf0, hfc⟩ := exist_core g h a b hyp
  have hfc0 : ContinuousWithinAt f (Set.Ici 0) 0 := hfc 0 (Set.mem_Ici.2 le_rfl)
  exact ⟨f, hf, hfc0, hf0, hfc, fun F hF hFc hF0 => uniq_core g h a b hyp F f hF hf hFc hF0 hfc0 hf0⟩


lemma iter_contOn {g h : ℝ → ℝ} {a b : ℝ} (hyp : AllocationHyp g h a b) {φ0 : ℝ → ℝ}
    (hφ0 : ContinuousOn φ0 (Set.Ici 0)) : ∀ N, ContinuousOn (allocIter g h a b φ0 N) (Set.Ici 0) := by
  intro N
  induction N with
  | zero => exact hφ0
  | succ N ih => rw [allocIter_succ_eq]; exact opT_contOn hyp.cont_g hyp.cont_h ih hyp.a_nonneg hyp.b_nonneg

lemma iter_close {g h : ℝ → ℝ} {a b : ℝ} (hyp : AllocationHyp g h a b) {φ0 : ℝ → ℝ}
    (hφ0 : ContinuousOn φ0 (Set.Ici 0)) {f : ℝ → ℝ} (hf : IsAllocationSolution g h a b f) :
    ∀ N x, 0 ≤ x → ∃ z ∈ Set.Icc 0 (max a b ^ N * x),
      |allocIter g h a b φ0 N x - f x| ≤ |φ0 z - f z| := by
  have hc0 : 0 ≤ max a b := le_max_of_le_left hyp.a_nonneg
  intro N
  induction N with
  | zero => intro x hx; exact ⟨x, ⟨hx, by simp⟩, le_rfl⟩
  | succ N ih =>
    intro x hx
    have hG := opT_greatest hyp.cont_g hyp.cont_h (iter_contOn hyp hφ0 N) hyp.a_nonneg hyp.b_nonneg hx
    rw [← allocIter_succ_eq] at hG
    obtain ⟨z, hz, hle⟩ := greatest_diff hyp.a_nonneg hyp.b_nonneg hx hG (hf x hx)
    obtain ⟨z', hz', hle'⟩ := ih z hz.1
    refine ⟨z', ⟨hz'.1, hz'.2.trans ?_⟩, hle.trans hle'⟩
    calc max a b ^ N * z ≤ max a b ^ N * (max a b * x) :=
          mul_le_mul_of_nonneg_left hz.2 (by positivity)
      _ = max a b ^ (N + 1) * x := by ring

lemma sol_contOn {g h : ℝ → ℝ} {a b : ℝ} (hyp : AllocationHyp g h a b) {f : ℝ → ℝ}
    (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) : ContinuousOn f (Set.Ici 0) := by
  obtain ⟨f', hf', _, _, hc', hu⟩ := alloc_main g h a b hyp
  exact hc'.congr (fun x hx => hu f hf hfc hf0 x hx)

theorem succ_core (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (f₀ : ℝ → ℝ) (hf₀ : ContinuousOn f₀ (Set.Ici 0)) (hf₀0 : f₀ 0 = 0)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ∀ R : ℝ, 0 ≤ R →
      TendstoUniformlyOn (allocIter g h a b f₀) f Filter.atTop (Set.Icc 0 R) := by
  intro R hR
  have hc0 : 0 ≤ max a b := le_max_of_le_left hyp.a_nonneg
  have hc1 : max a b < 1 := max_lt hyp.a_lt_one hyp.b_lt_one
  have fcont := sol_contOn hyp hf hfc hf0
  have he : ContinuousWithinAt (fun z => |f₀ z - f z|) (Set.Ici 0) 0 :=
    ((hf₀ 0 (Set.mem_Ici.2 le_rfl)).sub (fcont 0 (Set.mem_Ici.2 le_rfl))).abs
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rw [Metric.continuousWithinAt_iff] at he
  obtain ⟨δ, hδ, hδ'⟩ := he ε hε
  have ht : Filter.Tendsto (fun n : ℕ => max a b ^ n * R) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const R
  filter_upwards [ht.eventually (gt_mem_nhds hδ)] with N hN x hx
  obtain ⟨z, hz, hle⟩ := iter_close hyp hf₀ hf N x hx.1
  have hzR : z ≤ max a b ^ N * R := hz.2.trans (mul_le_mul_of_nonneg_left hx.2 (by positivity))
  have := hδ' (x := z) (Set.mem_Ici.2 hz.1) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.1]; linarith)
  simp only [hf₀0, hf0, sub_zero, Real.dist_eq, abs_abs, abs_zero] at this
  rw [dist_comm, Real.dist_eq]
  linarith

end BellmanDP.Allocation

open BellmanDP.Allocation


theorem solution (g h : ℝ → ℝ) (a b : ℝ)
    (hyp : AllocationHyp g h a b)
    (f₀ : ℝ → ℝ) (hf₀ : ContinuousOn f₀ (Set.Ici 0)) (hf₀0 : f₀ 0 = 0)
    (f : ℝ → ℝ) (hf : IsAllocationSolution g h a b f)
    (hfc : ContinuousWithinAt f (Set.Ici 0) 0) (hf0 : f 0 = 0) :
    ∀ R : ℝ, 0 ≤ R →
      TendstoUniformlyOn (allocIter g h a b f₀) f Filter.atTop (Set.Icc 0 R) := by
  exact succ_core g h a b hyp f₀ hf₀ hf₀0 f hf hfc hf0
