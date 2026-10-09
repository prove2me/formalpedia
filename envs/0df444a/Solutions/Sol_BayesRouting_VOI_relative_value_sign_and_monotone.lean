-- Prove2me | solution 1 for BayesRouting.VOI.relative_value_sign_and_monotone
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T05:18:21.870726+00:00
-- url     : https://prove2.me/submissions/67c5e670-9d1f-4099-95d1-4cd4b8466d12
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential
import Definitions.Def_BayesRouting_VOI_Flows
import Definitions.Def_BayesRouting_VOI_Pairwise
import Theorems.Thm_BayesRouting_VOI_eqPotential_convex_dirDeriv
import Theorems.Thm_BayesRouting_VOI_eqPotential_regime_monotone

set_option autoImplicit false

open Finset Filter Topology

/-! ### The direction `z^{ij}` -/

open BayesRouting.VOI in
lemma brv_dir_swap {I : Type} [DecidableEq I] (i j : I) : dir j i = - dir i j := by
  simp only [dir, neg_sub]

open BayesRouting.VOI in
lemma brv_pt_i {I : Type} [DecidableEq I] {i j : I} (hij : i ≠ j) (lam : I → ℝ) (ε : ℝ) :
    (lam + ε • dir i j) i = lam i + ε := by
  simp [dir, Pi.single_apply, hij]

open BayesRouting.VOI in
lemma brv_pt_j {I : Type} [DecidableEq I] {i j : I} (hij : i ≠ j) (lam : I → ℝ) (ε : ℝ) :
    (lam + ε • dir i j) j = lam j - ε := by
  simp [dir, Pi.single_apply, hij.symm, sub_eq_add_neg]

open BayesRouting.VOI in
lemma brv_pt_other {I : Type} [DecidableEq I] {i j k : I} (hki : k ≠ i) (hkj : k ≠ j)
    (lam : I → ℝ) (ε : ℝ) : (lam + ε • dir i j) k = lam k := by
  simp [dir, Pi.single_apply, hki, hkj]

open BayesRouting.VOI in
lemma brv_sum_dir {I : Type} [Fintype I] [DecidableEq I] (i j : I) : ∑ k, dir i j k = 0 := by
  simp [dir, Finset.sum_sub_distrib]

open BayesRouting.VOI in
lemma brv_mem {I : Type} [Fintype I] [DecidableEq I] {i j : I} (hij : i ≠ j) {lam : I → ℝ}
    (hlam : lam ∈ stdSimplex ℝ I) {ε : ℝ} (h1 : -lam i ≤ ε) (h2 : ε ≤ lam j) :
    lam + ε • dir i j ∈ stdSimplex ℝ I := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases hki : k = i
    · subst hki; rw [brv_pt_i hij]; linarith
    · by_cases hkj : k = j
      · subst hkj; rw [brv_pt_j hij]; linarith
      · rw [brv_pt_other hki hkj]; exact hlam.1 k
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, brv_sum_dir, hlam.2]
    ring

lemma brv_add_add {I : Type} (lam z : I → ℝ) (a b : ℝ) :
    lam + a • z + b • z = lam + (a + b) • z := by
  rw [add_smul, add_assoc]

/-! ### The thresholds depend only on `λ^{-ij}` -/

open BayesRouting.VOI in
lemma brv_thr {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (lam lam' : I → ℝ)
    (h : ∀ k, k ≠ i → k ≠ j → lam' k = lam k) :
    lowThr G lam' i j = lowThr G lam i j ∧ highThr G lam' i j = highThr G lam i j := by
  have hr : restSize lam' i j = restSize lam i j := by
    unfold restSize
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_erase] at hk
    exact h k hk.2.1 hk.1
  have hp : pairFeasible G lam' i j = pairFeasible G lam i j := by
    ext f
    simp only [pairFeasible, Set.mem_inter_iff, Set.mem_setOf_eq, hr]
    constructor
    · rintro ⟨hb, h1, h2⟩
      refine ⟨hb, fun k hki hkj => ?_, h2⟩
      rw [← h k hki hkj]; exact h1 k hki hkj
    · rintro ⟨hb, h1, h2⟩
      refine ⟨hb, fun k hki hkj => ?_, h2⟩
      rw [h k hki hkj]; exact h1 k hki hkj
  constructor <;> simp only [lowThr, highThr, pairOptimal, hp, hr]

/-! ### One-variable convex analysis -/

lemma brv_line_convex {I : Type} {f : (I → ℝ) → ℝ} {C : Set (I → ℝ)} (hf : ConvexOn ℝ C f)
    (μ d : I → ℝ) : ConvexOn ℝ {ε : ℝ | μ + ε • d ∈ C} (fun ε => f (μ + ε • d)) := by
  have key : ∀ x y a b : ℝ, a + b = 1 →
      μ + (a • x + b • y) • d = a • (μ + x • d) + b • (μ + y • d) := by
    intro x y a b hab
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(μ k)) * hab
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    show μ + (a • x + b • y) • d ∈ C
    rw [key x y a b hab]
    exact hf.1 hx hy ha hb hab
  · intro x hx y hy a b ha hb hab
    show f (μ + (a • x + b • y) • d) ≤ a • f (μ + x • d) + b • f (μ + y • d)
    rw [key x y a b hab]
    exact hf.2 hx hy ha hb hab

lemma brv_slope {φ : ℝ → ℝ} {S : Set ℝ} {c L t : ℝ} (hconv : ConvexOn ℝ S φ)
    (hS : Set.Icc 0 t ⊆ S) (h0 : φ 0 = c)
    (hL : Tendsto (fun ε => (φ ε - c) / ε) (𝓝[>] 0) (𝓝 L)) (ht : 0 < t) :
    L ≤ (φ t - c) / t := by
  apply le_of_tendsto hL
  filter_upwards [Ioo_mem_nhdsGT ht] with ε hε
  have := hconv.secant_mono (a := 0) (x := ε) (y := t) (hS ⟨le_refl 0, ht.le⟩)
    (hS ⟨hε.1.le, hε.2.le⟩) (hS ⟨ht.le, le_refl t⟩) (ne_of_gt hε.1) (ne_of_gt ht) hε.2.le
  simpa [h0] using this

lemma brv_lim_nonneg {φ : ℝ → ℝ} {c L : ℝ}
    (hL : Tendsto (fun ε => (φ ε - c) / ε) (𝓝[>] 0) (𝓝 L))
    (hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c ≤ φ ε) : 0 ≤ L := by
  apply ge_of_tendsto hL
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos
  exact div_nonneg (by linarith) (le_of_lt hpos)

lemma brv_rcont {φ : ℝ → ℝ} {c L : ℝ}
    (hL : Tendsto (fun ε => (φ ε - c) / ε) (𝓝[>] 0) (𝓝 L)) :
    Tendsto φ (𝓝[>] 0) (𝓝 c) := by
  have h1 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h2 := (h1.mul hL).const_add c
  rw [zero_mul, add_zero] at h2
  apply h2.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hne : ε ≠ 0 := ne_of_gt hε
  field_simp
  ring

lemma brv_le_of_right {φ : ℝ → ℝ} {c b : ℝ} (hc : Tendsto φ (𝓝[>] 0) (𝓝 c)) (hb : 0 < b)
    (hlt : ∀ ε' ∈ Set.Ioo 0 b, φ ε' ≤ φ b) : c ≤ φ b := by
  apply le_of_tendsto hc
  filter_upwards [Ioo_mem_nhdsGT hb] with ε' h
  exact hlt ε' h

/-! ### Proposition 3 along the line `λ + s z^{ij}` -/

open BayesRouting.VOI in
lemma brv_V2pts {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I)
    (s t : ℝ) (hst : s < t) (hs : -lam i < s) (ht : t < lam j) :
    (lam i + t < lowThr G lam i j →
        eqPotential G (lam + t • dir i j) < eqPotential G (lam + s • dir i j)) ∧
    (lowThr G lam i j ≤ lam i + s → lam i + t ≤ highThr G lam i j →
        eqPotential G (lam + t • dir i j) = eqPotential G (lam + s • dir i j)) ∧
    (highThr G lam i j < lam i + s →
        eqPotential G (lam + s • dir i j) < eqPotential G (lam + t • dir i j)) := by
  set μ := lam + s • dir i j with hμ
  have hμmem : μ ∈ stdSimplex ℝ I := brv_mem hij hlam (by linarith) (by linarith)
  have hμi : μ i = lam i + s := brv_pt_i hij lam s
  have hμj : μ j = lam j - s := brv_pt_j hij lam s
  have hstep : μ + (t - s) • dir i j = lam + t • dir i j := by
    rw [hμ, brv_add_add]; congr 2; ring
  have hthr := brv_thr G i j lam μ (fun k hki hkj => brv_pt_other hki hkj lam s)
  have hV2 := (BayesRouting.VOI.eqPotential_regime_monotone G i j hij).1 μ hμmem
    (by rw [hμi]; linarith) (by rw [hμj]; linarith) (t - s) (by linarith)
    (by rw [hstep, brv_pt_j hij]; linarith)
  rw [hstep, hthr.1, hthr.2, hμi, brv_pt_i hij] at hV2
  obtain ⟨h1, h2, h3⟩ := hV2
  refine ⟨fun h => h1 ⟨by linarith, h⟩, fun ha hb => h2 ⟨ha, by linarith, by linarith, hb⟩,
    fun h => h3 ⟨h, by linarith⟩⟩

/-! ### The parent -/

open BayesRouting.VOI in
theorem solution {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (i j : I) (hij : i ≠ j) :
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ q : (k : I) → T k → R → ℝ, IsBWE G lam q →
        (lam i < lowThr G lam i j → 0 < relValue G q i j) ∧
        (lowThr G lam i j ≤ lam i → lam i ≤ highThr G lam i j → relValue G q i j = 0) ∧
        (highThr G lam i j < lam i → relValue G q i j < 0)) ∧
    (∀ lam ∈ stdSimplex ℝ I, 0 < lam i → 0 < lam j →
      ∀ ε : ℝ, 0 < ε → 0 < (lam + ε • dir i j) j →
        ∀ q q' : (k : I) → T k → R → ℝ, IsBWE G lam q → IsBWE G (lam + ε • dir i j) q' →
          relValue G q' i j ≤ relValue G q i j) := by
  obtain ⟨hconv, -, hder⟩ := BayesRouting.VOI.eqPotential_convex_dirDeriv G
  have hD := G.D_pos
  have hswap : ∀ (q : (k : I) → T k → R → ℝ), relValue G q j i = - relValue G q i j := by
    intro q; unfold relValue; ring
  have hsub : ∀ (lam : I → ℝ) (η : ℝ), lam + η • dir j i = lam + (-η) • dir i j := by
    intro lam η; rw [brv_dir_swap, smul_neg, neg_smul]
  refine ⟨?_, ?_⟩
  · intro lam hlam hi hj q hq
    set V := relValue G q i j with hV
    set g : ℝ → ℝ := fun s => eqPotential G (lam + s • dir i j) with hg
    set h : ℝ → ℝ := fun s => eqPotential G (lam + s • dir j i) with hh
    have hgh : ∀ s, h s = g (-s) := by intro s; simp only [hh, hg, hsub]
    have hg0 : g 0 = eqPotential G lam := by simp [hg]
    have hh0 : h 0 = eqPotential G lam := by simp [hh]
    have hR : Tendsto (fun s => (g s - eqPotential G lam) / s) (𝓝[>] 0) (𝓝 (-(G.D * V))) :=
      hder lam hlam i j hij hj q hq
    have hL : Tendsto (fun s => (h s - eqPotential G lam) / s) (𝓝[>] 0) (𝓝 (G.D * V)) := by
      have := hder lam hlam j i hij.symm hi q hq
      rw [hswap q, mul_neg, neg_neg] at this
      exact this
    have hgc : ConvexOn ℝ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} g :=
      brv_line_convex hconv lam (dir i j)
    have hhc : ConvexOn ℝ {s : ℝ | lam + s • dir j i ∈ stdSimplex ℝ I} h :=
      brv_line_convex hconv lam (dir j i)
    have hgS : Set.Icc 0 (lam j) ⊆ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} :=
      fun s hs => brv_mem hij hlam (by linarith [hs.1]) hs.2
    have hhS : Set.Icc 0 (lam i) ⊆ {s : ℝ | lam + s • dir j i ∈ stdSimplex ℝ I} :=
      fun s hs => brv_mem hij.symm hlam (by linarith [hs.1]) hs.2
    have P := brv_V2pts G i j hij lam hlam
    refine ⟨fun hl => ?_, fun hl hu => ?_, fun hu => ?_⟩
    · -- regime 1
      set t := min ((lowThr G lam i j - lam i) / 2) (lam j / 2) with ht
      have ht0 : 0 < t := lt_min (by linarith) (by linarith)
      have ht1 : t ≤ (lowThr G lam i j - lam i) / 2 := min_le_left _ _
      have ht2 : t ≤ lam j / 2 := min_le_right _ _
      have hdec : g t < g 0 := (P 0 t ht0 (by linarith) (by linarith)).1 (by linarith)
      have hsl := brv_slope hgc ((Set.Icc_subset_Icc_right (by linarith)).trans hgS) hg0 hR ht0
      have hneg : (g t - eqPotential G lam) / t < 0 :=
        div_neg_of_neg_of_pos (by linarith) ht0
      have : 0 < G.D * V := by linarith
      exact pos_of_mul_pos_right this hD.le
    · -- regime 2
      have hA : 0 ≤ -(G.D * V) := by
        apply brv_lim_nonneg hR
        rcases lt_or_eq_of_le hu with hu' | hu'
        · filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr hu') (half_pos hj))] with ε hε
          have h1 : ε < highThr G lam i j - lam i := lt_of_lt_of_le hε.2 (min_le_left _ _)
          have h2 : ε < lam j / 2 := lt_of_lt_of_le hε.2 (min_le_right _ _)
          have := (P 0 ε hε.1 (by linarith) (by linarith)).2.1 (by linarith) (by linarith)
          rw [← hg0]; exact this.symm.le
        · filter_upwards [Ioo_mem_nhdsGT (half_pos hj)] with ε hε
          rw [← hg0]
          refine brv_le_of_right (hg0 ▸ brv_rcont hR) hε.1 (fun ε' hε' => ?_)
          exact ((P ε' ε hε'.2 (by linarith [hε'.1]) (by linarith [hε.2])).2.2
            (by rw [hu']; linarith [hε'.1])).le
      have hB : 0 ≤ G.D * V := by
        apply brv_lim_nonneg hL
        rcases lt_or_eq_of_le hl with hl' | hl'
        · filter_upwards [Ioo_mem_nhdsGT (lt_min (sub_pos.mpr hl') (half_pos hi))] with η hη
          have h1 : η < lam i - lowThr G lam i j := lt_of_lt_of_le hη.2 (min_le_left _ _)
          have h2 : η < lam i / 2 := lt_of_lt_of_le hη.2 (min_le_right _ _)
          have := (P (-η) 0 (by linarith [hη.1]) (by linarith) (by linarith)).2.1
            (by linarith) (by linarith)
          rw [hgh, ← hg0]; exact this.le
        · filter_upwards [Ioo_mem_nhdsGT (half_pos hi)] with η hη
          rw [← hh0]
          refine brv_le_of_right (hh0 ▸ brv_rcont hL) hη.1 (fun η' hη' => ?_)
          rw [hgh, hgh]
          exact ((P (-η) (-η') (by linarith [hη'.2]) (by linarith [hη.2])
            (by linarith [hη'.1])).1 (by rw [← hl']; linarith [hη'.1])).le
      have hDV : G.D * V = 0 := le_antisymm (by linarith) hB
      rcases mul_eq_zero.mp hDV with h0 | h0
      · exact absurd h0 hD.ne'
      · exact h0
    · -- regime 3
      set t := min ((lam i - highThr G lam i j) / 2) (lam i / 2) with ht
      have ht0 : 0 < t := lt_min (by linarith) (by linarith)
      have ht1 : t ≤ (lam i - highThr G lam i j) / 2 := min_le_left _ _
      have ht2 : t ≤ lam i / 2 := min_le_right _ _
      have hinc : g (-t) < g 0 := (P (-t) 0 (by linarith) (by linarith) (by linarith)).2.2
        (by linarith)
      have hsl := brv_slope hhc ((Set.Icc_subset_Icc_right (by linarith)).trans hhS) hh0 hL ht0
      rw [hgh] at hsl
      have hneg : (g (-t) - eqPotential G lam) / t < 0 :=
        div_neg_of_neg_of_pos (by linarith) ht0
      have : G.D * V < 0 := by linarith
      by_contra hc
      push_neg at hc
      have := mul_nonneg hD.le hc
      linarith
  · intro lam hlam hi hj ε hε hεj q q' hq hq'
    have hεj' : ε < lam j := by rw [brv_pt_j hij] at hεj; linarith
    set lam' := lam + ε • dir i j with hlam'
    have hlam'mem : lam' ∈ stdSimplex ℝ I := brv_mem hij hlam (by linarith) hεj'.le
    have hi' : 0 < lam' i := by rw [hlam', brv_pt_i hij]; linarith
    set g : ℝ → ℝ := fun s => eqPotential G (lam + s • dir i j) with hg
    set h : ℝ → ℝ := fun s => eqPotential G (lam' + s • dir j i) with hh
    have hg0 : g 0 = eqPotential G lam := by simp [hg]
    have hh0 : h 0 = eqPotential G lam' := by simp [hh]
    have hR : Tendsto (fun s => (g s - eqPotential G lam) / s) (𝓝[>] 0)
        (𝓝 (-(G.D * relValue G q i j))) := hder lam hlam i j hij hj q hq
    have hL : Tendsto (fun s => (h s - eqPotential G lam') / s) (𝓝[>] 0)
        (𝓝 (G.D * relValue G q' i j)) := by
      have := hder lam' hlam'mem j i hij.symm hi' q' hq'
      rw [hswap q', mul_neg, neg_neg] at this
      exact this
    have hgc : ConvexOn ℝ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} g :=
      brv_line_convex hconv lam (dir i j)
    have hhc : ConvexOn ℝ {s : ℝ | lam' + s • dir j i ∈ stdSimplex ℝ I} h :=
      brv_line_convex hconv lam' (dir j i)
    have hgS : Set.Icc 0 ε ⊆ {s : ℝ | lam + s • dir i j ∈ stdSimplex ℝ I} :=
      fun s hs => brv_mem hij hlam (by linarith [hs.1]) (by linarith [hs.2])
    have hhS : Set.Icc 0 ε ⊆ {s : ℝ | lam' + s • dir j i ∈ stdSimplex ℝ I} := by
      intro s hs
      apply brv_mem hij.symm hlam'mem
      · rw [hlam', brv_pt_j hij]; linarith [hs.1]
      · rw [hlam', brv_pt_i hij]; linarith [hs.2]
    have s1 := brv_slope hgc hgS hg0 hR hε
    have s2 := brv_slope hhc hhS hh0 hL hε
    have hback : h ε = eqPotential G lam := by
      simp only [hh, hlam', hsub, brv_add_add, add_neg_cancel, zero_smul, add_zero]
    have hfwd : g ε = eqPotential G lam' := by simp only [hg, hlam']
    rw [hback] at s2
    rw [hfwd] at s1
    have e : (eqPotential G lam - eqPotential G lam') / ε =
        -((eqPotential G lam' - eqPotential G lam) / ε) := by ring
    have : G.D * relValue G q' i j ≤ G.D * relValue G q i j := by linarith
    exact le_of_mul_le_mul_left this hD
