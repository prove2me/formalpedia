-- Prove2me | solution 1 for ChanceStateCtrl.General.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T01:00:55.205877+00:00
-- url     : https://prove2.me/submissions/21db74aa-4499-456d-85cf-957795ac0425

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
import Theorems.Thm_ChanceStateCtrl_General_prekopa_logconcave
import Theorems.Thm_ChanceStateCtrl_General_gaussian_density_logconcave
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

open ChanceStateCtrl.General

theorem solution {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_qc : QuasiconvexOn ℝ Set.univ (Function.uncurry g)) (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) :
    (∀ u : U, p ≤ probFn P ξ g u ↔ phiTilde P ξ g p u ≤ 0) ∧
      (∀ u : U, phiTilde P ξ g p u ≠ ⊥) ∧
      ConvexEpi (phiTilde P ξ g p) ∧
      LowerSemicontinuous (phiTilde P ξ g p) := by
  classical
  haveI := hA.isProb
  set φ := probFn P ξ g with hφdef
  have hpos : 0 < p := hp.1
  set A : U → Set Ω := fun u => {ω | g u (ξ ω) ≤ 0} with hAdef
  have hgc : Continuous (Function.uncurry g) := hA.locLip.continuous
  have hgcu : ∀ u, Continuous (g u) := fun u =>
    hgc.comp (Continuous.prodMk continuous_const continuous_id)
  have hAmeas : ∀ u, MeasurableSet (A u) := fun u =>
    hA.measurable_xi (isClosed_le (hgcu u) continuous_const).measurableSet
  have hPA : ∀ u, P (A u) = ENNReal.ofReal (φ u) := fun u => by
    simp only [hφdef, probFn, hAdef]; rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hφnn : ∀ u, 0 ≤ φ u := fun u => ENNReal.toReal_nonneg
  have hPT : ∀ u, 0 < φ u →
      phiTilde P ξ g p u = ((-Real.log (φ u) + Real.log p : ℝ) : EReal) := by
    intro u hu
    unfold phiTilde
    rw [show {ω | g u (ξ ω) ≤ 0} = A u from rfl, hPA u, ENNReal.log_ofReal_of_pos hu,
      EReal.coe_add, EReal.coe_neg]
  have hPT0 : ∀ u, φ u = 0 → phiTilde P ξ g p u = ⊤ := by
    intro u hu
    unfold phiTilde
    rw [show {ω | g u (ξ ω) ≤ 0} = A u from rfl, hPA u, hu, ENNReal.ofReal_zero,
      ENNReal.log_zero, EReal.neg_bot, EReal.top_add_coe]
  have hcases : ∀ u, 0 < φ u ∨ φ u = 0 := fun u => (hφnn u).lt_or_eq.imp id Eq.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (9) ⟺ (20)
    intro u
    rcases hcases u with h | h
    · rw [hPT u h]
      constructor
      · intro hle
        have := Real.log_le_log hpos hle
        exact_mod_cast (by linarith : -Real.log (φ u) + Real.log p ≤ 0)
      · intro hle
        have h' : -Real.log (φ u) + Real.log p ≤ 0 := by exact_mod_cast hle
        exact (Real.log_le_log_iff hpos h).1 (by linarith)
    · rw [hPT0 u h, h]
      constructor
      · intro hle; linarith
      · intro hle; exact absurd hle (by simp)
  · -- `φ̃ > -∞`
    intro u
    rcases hcases u with h | h
    · rw [hPT u h]; exact EReal.coe_ne_bot _
    · rw [hPT0 u h]; exact bot_lt_top.ne'
  · -- convexity, from Prékopa's log-concavity
    obtain ⟨dens, hd0, hdm, hlaw, hlc⟩ := gaussian_density_logconcave Sigma hA.posDef
    have hpk := prekopa_logconcave P ξ hA.measurable_xi dens hd0 hdm (hA.law.trans hlaw) hlc
      g hA.locLip hg_qc
    rintro ⟨u, a⟩ hu ⟨w, b⟩ hw s t hs ht hst
    simp only [Set.mem_setOf_eq] at hu hw ⊢
    have hpu : 0 < φ u := by
      rcases hcases u with h | h
      · exact h
      · rw [hPT0 u h] at hu; exact absurd hu (by simp)
    have hpw : 0 < φ w := by
      rcases hcases w with h | h
      · exact h
      · rw [hPT0 w h] at hw; exact absurd hw (by simp)
    rw [hPT u hpu] at hu
    rw [hPT w hpw] at hw
    have hu' : -Real.log (φ u) + Real.log p ≤ a := by exact_mod_cast hu
    have hw' : -Real.log (φ w) + Real.log p ≤ b := by exact_mod_cast hw
    have ht' : t = 1 - s := by linarith
    have hk := hpk u w s ⟨hs, by linarith⟩
    rw [← ht'] at hk
    have hprod : 0 < φ u ^ s * φ w ^ t :=
      mul_pos (Real.rpow_pos_of_pos hpu s) (Real.rpow_pos_of_pos hpw t)
    have hz : 0 < φ (s • u + t • w) := lt_of_lt_of_le hprod hk
    have hlog : s * Real.log (φ u) + t * Real.log (φ w) ≤ Real.log (φ (s • u + t • w)) := by
      have := Real.log_le_log hprod hk
      rwa [Real.log_mul (Real.rpow_pos_of_pos hpu s).ne' (Real.rpow_pos_of_pos hpw t).ne',
        Real.log_rpow hpu, Real.log_rpow hpw] at this
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    rw [hPT _ hz]
    apply EReal.coe_le_coe_iff.2
    have e : Real.log p = s * Real.log p + t * Real.log p := by rw [← add_mul, hst, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hu' hs, mul_le_mul_of_nonneg_left hw' ht]
  · -- lower semicontinuity
    -- `u ↦ P (A u)` is upper semicontinuous
    have husc : UpperSemicontinuous (fun u => P (A u)) := by
      intro u y hy
      by_contra hne
      rw [Filter.not_eventually] at hne
      obtain ⟨us, hus, hyus⟩ := exists_seq_forall_of_frequently hne
      push_neg at hyus
      set S : ℕ → Set Ω := fun N => ⋃ n, A (us (n + N)) with hS
      have hSanti : Antitone S := by
        intro N M hNM ω hω
        simp only [hS, Set.mem_iUnion] at hω ⊢
        obtain ⟨n, hn⟩ := hω
        exact ⟨n + (M - N), by rwa [show n + (M - N) + N = n + M by omega]⟩
      have hSmeas : ∀ N, NullMeasurableSet (S N) P := fun N =>
        (MeasurableSet.iUnion fun n => hAmeas _).nullMeasurableSet
      have hT := tendsto_measure_iInter_atTop hSmeas hSanti ⟨0, measure_ne_top _ _⟩
      have hge : y ≤ P (⋂ N, S N) := by
        refine ge_of_tendsto hT (Eventually.of_forall fun N => ?_)
        calc y ≤ P (A (us (0 + N))) := hyus _
          _ ≤ P (S N) := measure_mono (Set.subset_iUnion (fun n => A (us (n + N))) 0)
      have hsub : (⋂ N, S N) ⊆ A u := by
        intro ω hω
        by_contra hωA
        simp only [hAdef, Set.mem_setOf_eq, not_le] at hωA
        have hcont : Tendsto (fun n => g (us n) (ξ ω)) atTop (𝓝 (g u (ξ ω))) :=
          (hgc.comp (Continuous.prodMk continuous_id continuous_const)).continuousAt.tendsto.comp
            hus
        obtain ⟨N, hN⟩ := eventually_atTop.1 (hcont.eventually (lt_mem_nhds hωA))
        have := Set.mem_iInter.1 hω N
        simp only [hS, Set.mem_iUnion, hAdef, Set.mem_setOf_eq] at this
        obtain ⟨n, hn⟩ := this
        have := hN (n + N) (by omega)
        linarith
      exact absurd (lt_of_le_of_lt (hge.trans (measure_mono hsub)) hy) (lt_irrefl _)
    set Φ : ENNReal → EReal := fun x => -(ENNReal.log x) + (Real.log p : EReal) with hΦ
    have hΦc : Continuous Φ := by
      have h1 : Continuous fun x : ENNReal => -(ENNReal.log x) :=
        continuous_neg.comp ENNReal.continuous_log
      rw [continuous_iff_continuousAt]
      intro x
      have h2 : ContinuousAt (fun q : EReal × EReal => q.1 + q.2)
          (-(ENNReal.log x), (Real.log p : EReal)) :=
        EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
      exact ContinuousAt.comp (f := fun x : ENNReal => (-(ENNReal.log x), (Real.log p : EReal)))
        (x := x) h2 (h1.continuousAt.prodMk continuousAt_const)
    have hΦa : Antitone Φ := by
      intro x y hxy
      simp only [hΦ]
      gcongr
      exact EReal.neg_le_neg_iff.2 (ENNReal.log_monotone hxy)
    have := hΦc.comp_upperSemicontinuous_antitone husc hΦa
    exact (show phiTilde P ξ g p = Φ ∘ (fun u => P (A u)) from rfl) ▸ this
