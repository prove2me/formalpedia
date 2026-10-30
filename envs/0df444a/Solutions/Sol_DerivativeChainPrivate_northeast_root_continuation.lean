-- Prove2me | solution 1 for DerivativeChainPrivate.northeast_root_continuation
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:16:36.919306+00:00
-- url     : https://prove2.me/submissions/02d34ab5-6126-40d7-a477-82b4a39d9500

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
open Filter Topology Set
namespace DerivativeChainPrivate

theorem monic_small_eval_near_root (p : Polynomial ℂ) (hp : p.Monic)
    (a : ℂ) (ε : ℝ) (hε : 0 < ε) (hsmall : ‖p.eval a‖ < ε ^ p.natDegree) :
    ∃ b : ℂ, p.eval b = 0 ∧ ‖a - b‖ < ε := by
  have hsplit := IsAlgClosed.splits p
  have heval : (p.roots.map (fun b => ‖a - b‖)).prod = ‖p.eval a‖ := by
    calc
      _ = ‖(p.roots.map (fun b => a - b)).prod‖ := by
        change (p.roots.map (fun b => NormedField.toMulRingNorm ℂ (a - b))).prod = _
        rw [p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun b => a - b)]
        rfl
      _ = _ := by rw [hsplit.eval_eq_prod_roots_of_monic hp]
  by_contra! h
  have hlower : ∀ b ∈ p.roots, ε ≤ ‖a - b‖ := by
    intro b hb
    exact h b ((Polynomial.mem_roots hp.ne_zero).mp hb)
  have hprod := Multiset.prod_map_le_prod_map₀ (fun _ : ℂ => ε)
    (fun b => ‖a - b‖) (fun _ _ => hε.le) hlower
  simp only [Multiset.map_const', Multiset.prod_replicate,
    ← hsplit.natDegree_eq_card_roots, heval] at hprod
  exact (not_le_of_gt hsmall) hprod

theorem northeast_root_existence_isOpen {T : Type*} [TopologicalSpace T]
    (p : T → Polynomial ℂ) (n : ℕ) (hp : ∀ t, (p t).Monic)
    (hdeg : ∀ t, (p t).natDegree = n)
    (heval : Continuous (fun x : T × ℂ => (p x.1).eval x.2))
    (w : T → ℂ) (hw : Continuous w) :
    IsOpen {t | ∃ z : ℂ, (p t).eval z = 0 ∧ (w t).re < z.re ∧ (w t).im < z.im} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro t ⟨z, hz, hre, him⟩
  let ε := min (z.re - (w t).re) (z.im - (w t).im) / 4
  have hε : 0 < ε := div_pos (lt_min (sub_pos.mpr hre) (sub_pos.mpr him)) (by norm_num)
  have hεre : 2 * ε < z.re - (w t).re := by
    dsimp only [ε]; linarith [min_le_left (z.re - (w t).re) (z.im - (w t).im)]
  have hεim : 2 * ε < z.im - (w t).im := by
    dsimp only [ε]; linarith [min_le_right (z.re - (w t).re) (z.im - (w t).im)]
  have hE : Tendsto (fun s => ‖(p s).eval z‖) (𝓝 t) (𝓝 0) := by
    have hc : Continuous (fun s : T => (p s).eval z) :=
      heval.comp (continuous_id.prodMk (continuous_const (y := z)))
    simpa only [hz, norm_zero] using hc.norm.continuousAt.tendsto (x := t)
  have hsmall : ∀ᶠ s in 𝓝 t, ‖(p s).eval z‖ < ε ^ n :=
    hE.eventually (Iio_mem_nhds (pow_pos hε n))
  have hwr : ∀ᶠ s in 𝓝 t, (w s).re < (w t).re + ε :=
    (Complex.continuous_re.comp hw).continuousAt.tendsto.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  have hwi : ∀ᶠ s in 𝓝 t, (w s).im < (w t).im + ε :=
    (Complex.continuous_im.comp hw).continuousAt.tendsto.eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hsmall, hwr, hwi] with s hs hsr hsi
  obtain ⟨b, hb, hnear⟩ := monic_small_eval_near_root (p s) (hp s) z ε hε
    (by simpa only [hdeg] using hs)
  have hbr := lt_of_le_of_lt (Complex.re_le_norm (z - b)) hnear
  have hbi := lt_of_le_of_lt (Complex.im_le_norm (z - b)) hnear
  simp only [Complex.sub_re, Complex.sub_im] at hbr hbi
  exact ⟨b, hb, by linarith, by linarith⟩

theorem northeast_root_existence_isClosed {T : Type*} [MetricSpace T]
    (p : T → Polynomial ℂ)
    (heval : Continuous (fun x : T × ℂ => (p x.1).eval x.2))
    (w : T → ℂ) (hw : Continuous w) (R : ℝ) (_hR : 0 ≤ R)
    (hbound : ∀ t z, (p t).eval z = 0 → ‖z‖ ≤ R)
    (hboundary : ∀ t z, (p t).eval z = 0 →
      ((z.re = (w t).re ∧ (w t).im ≤ z.im) ∨
        ((w t).re ≤ z.re ∧ z.im = (w t).im)) → False) :
    IsClosed {t | ∃ z : ℂ, (p t).eval z = 0 ∧ (w t).re < z.re ∧ (w t).im < z.im} := by
  apply IsSeqClosed.isClosed
  intro ts t hs ht
  choose z hz hre him using hs
  have hmem (j : ℕ) : z j ∈ Metric.closedBall (0 : ℂ) R := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hbound (ts j) (z j) (hz j)
  obtain ⟨b, _, φ, hφ, hb⟩ := (isCompact_closedBall (0 : ℂ) R).isSeqCompact hmem
  have htφ := ht.comp hφ.tendsto_atTop
  have hlimit := heval.continuousAt.tendsto.comp (htφ.prodMk_nhds hb)
  have hzero : (p t).eval b = 0 := tendsto_nhds_unique hlimit (by
    simpa only [Function.comp_def, hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  have hrle : (w t).re ≤ b.re := le_of_tendsto_of_tendsto
    ((Complex.continuous_re.comp hw).continuousAt.tendsto.comp htφ)
    (Complex.continuous_re.continuousAt.tendsto.comp hb)
    (Eventually.of_forall (fun j => (hre (φ j)).le))
  have hile : (w t).im ≤ b.im := le_of_tendsto_of_tendsto
    ((Complex.continuous_im.comp hw).continuousAt.tendsto.comp htφ)
    (Complex.continuous_im.continuousAt.tendsto.comp hb)
    (Eventually.of_forall (fun j => (him (φ j)).le))
  refine ⟨b, hzero, ?_, ?_⟩
  · by_contra h
    exact hboundary t b hzero (Or.inl ⟨le_antisymm (le_of_not_gt h) hrle, hile⟩)
  · by_contra h
    exact hboundary t b hzero (Or.inr ⟨hrle, le_antisymm (le_of_not_gt h) hile⟩)



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution {T : Type*} [MetricSpace T] [PreconnectedSpace T]
    (p : T → Polynomial ℂ) (n : ℕ) (hp : ∀ t, (p t).Monic)
    (hdeg : ∀ t, (p t).natDegree = n)
    (heval : Continuous (fun x : T × ℂ => (p x.1).eval x.2))
    (w : T → ℂ) (hw : Continuous w) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ t z, (p t).eval z = 0 → ‖z‖ ≤ R)
    (hboundary : ∀ t z, (p t).eval z = 0 →
      ((z.re = (w t).re ∧ (w t).im ≤ z.im) ∨
        ((w t).re ≤ z.re ∧ z.im = (w t).im)) → False)
    (t₀ : T) (z₀ : ℂ) (hz₀ : (p t₀).eval z₀ = 0)
    (hr₀ : (w t₀).re < z₀.re) (hi₀ : (w t₀).im < z₀.im) :
    ∀ t, ∃ z : ℂ, (p t).eval z = 0 ∧ (w t).re < z.re ∧ (w t).im < z.im := by
  have hclopen : IsClopen {t | ∃ z : ℂ,
      (p t).eval z = 0 ∧ (w t).re < z.re ∧ (w t).im < z.im} :=
    ⟨northeast_root_existence_isClosed p heval w hw R hR hbound hboundary,
      northeast_root_existence_isOpen p n hp hdeg heval w hw⟩
  have hall := hclopen.eq_univ ⟨t₀, z₀, hz₀, hr₀, hi₀⟩
  intro t
  have hm : t ∈ ({t | ∃ z : ℂ, (p t).eval z = 0 ∧ (w t).re < z.re ∧ (w t).im < z.im} : Set T) := by
    rw [hall]; exact mem_univ t
  exact hm
