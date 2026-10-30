-- Prove2me | solution 1 for DerivativeChainPrivate.bounded_holomorphic_contraction
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:43:11.546653+00:00
-- url     : https://prove2.me/submissions/832510da-e4be-440d-bf2e-cc3e91bc61d7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped NNReal


theorem solution (F : ℂ → ℂ → ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M)
    (hhol : Differentiable ℂ (fun p : ℂ × ℂ => F p.1 p.2))
    (hmap : ∀ t : ℂ, ‖t‖ ≤ R → ∀ v : ℂ, ‖v‖ ≤ M → ‖F t v‖ ≤ M)
    (hcontract : ∀ t : ℂ, ‖t‖ ≤ R → ∀ v w : ℂ, ‖v‖ ≤ M → ‖w‖ ≤ M →
      ‖F t v-F t w‖ ≤ (1/2)*‖v-w‖)
    (hreal : ∀ x y : ℝ, (F (x:ℂ) (y:ℂ)).im=0) :
    ∃ Y : ℂ → ℂ,
      (∀ t : ℂ, ‖t‖ ≤ R → ‖Y t‖ ≤ M ∧ F t (Y t)=Y t) ∧
      DifferentiableOn ℂ Y (Metric.ball 0 R) ∧
      ∀ x : ℝ, |x| ≤ R → (Y (x:ℂ)).im=0 := by
  classical
  have hex (t : ℂ) (ht : ‖t‖ ≤ R) : ∃ y : ℂ, ‖y‖ ≤ M ∧ F t y=y := by
    let S := Metric.closedBall (0:ℂ) M
    have hm : MapsTo (F t) S S := by
      intro v hv
      have hv' : ‖v‖ ≤ M := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv
      simpa only [S,Metric.mem_closedBall,dist_zero_right] using hmap t ht v hv'
    have hc : ContractingWith (1/2:ℝ≥0) (hm.restrict (F t) S S) := by
      constructor
      · norm_num
      · apply LipschitzWith.of_dist_le_mul
        intro v w
        have hv : ‖(v:ℂ)‖ ≤ M := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using v.property
        have hw : ‖(w:ℂ)‖ ≤ M := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using w.property
        change dist (F t v) (F t w) ≤ ((1/2:ℝ≥0):ℝ)*dist (v:ℂ) (w:ℂ)
        simpa only [dist_eq_norm,NNReal.coe_div,NNReal.coe_ofNat,NNReal.coe_one] using hcontract t ht v w hv hw
    have hs : IsComplete S := Metric.isClosed_closedBall.isComplete
    have hz : (0:ℂ) ∈ S := by simpa only [S,Metric.mem_closedBall,dist_self] using hM
    obtain ⟨y,hy,hfy,_,_⟩ := ContractingWith.exists_fixedPoint' hs hm hc hz (edist_ne_top _ _)
    exact ⟨y,by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hy,hfy⟩
  let Y : ℂ → ℂ := fun t => if ht : ‖t‖ ≤ R then Classical.choose (hex t ht) else 0
  have hspec (t : ℂ) (ht : ‖t‖ ≤ R) : ‖Y t‖ ≤ M ∧ F t (Y t)=Y t := by
    dsimp only [Y]
    rw [dif_pos ht]
    exact Classical.choose_spec (hex t ht)
  have hiter_norm (t : ℂ) (ht : ‖t‖ ≤ R) (n : ℕ) : ‖((F t)^[n]) 0‖ ≤ M := by
    induction n with
    | zero => simpa using hM
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmap t ht _ ih
  have hiter_dist (t : ℂ) (ht : ‖t‖ ≤ R) (n : ℕ) :
      dist (((F t)^[n]) 0) (Y t) ≤ (1/2:ℝ)^n*M := by
    induction n with
    | zero => simpa only [Function.iterate_zero_apply,dist_zero_left,pow_zero,one_mul] using (hspec t ht).1
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        _ = dist (F t (((F t)^[n]) 0)) (F t (Y t)) := by rw [(hspec t ht).2]
        _ ≤ (1/2)*dist (((F t)^[n]) 0) (Y t) := by
          simpa only [dist_eq_norm] using hcontract t ht _ _ (hiter_norm t ht n) (hspec t ht).1
        _ ≤ (1/2)*((1/2:ℝ)^n*M) := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1/2:ℝ)^(n+1)*M := by rw [pow_succ]; ring
  have hiter_hol (n : ℕ) : Differentiable ℂ (fun t : ℂ => ((F t)^[n]) 0) := by
    induction n with
    | zero => simpa only [Function.iterate_zero_apply] using (differentiable_const (0:ℂ))
    | succ n ih =>
      have hh := hhol.comp (differentiable_id.prodMk ih)
      convert hh using 1 <;> first | rfl | simp only [Function.comp_def, Function.iterate_succ_apply', id_eq]
  have huniform : TendstoUniformlyOn (fun n : ℕ => fun t : ℂ => ((F t)^[n]) 0) Y atTop (Metric.closedBall 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hl : Tendsto (fun n : ℕ => (1/2:ℝ)^n*M) atTop (𝓝 0) := by
      simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_const M
    filter_upwards [hl.eventually (Iio_mem_nhds hε)] with n hn
    intro t ht
    have ht' : ‖t‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using ht
    simpa only [dist_comm] using lt_of_le_of_lt (hiter_dist t ht' n) hn
  refine ⟨Y,hspec,?_,?_⟩
  · exact (huniform.mono Metric.ball_subset_closedBall).tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall (fun n => (hiter_hol n).differentiableOn)) Metric.isOpen_ball
  · intro x hx
    have ht : (x:ℂ) ∈ Metric.closedBall (0:ℂ) R := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Complex.norm_real,Real.norm_eq_abs] using hx
    have hr (n : ℕ) : (((F (x:ℂ))^[n]) 0).im=0 := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        have he : ((F (x:ℂ))^[n]) 0 = (((((F (x:ℂ))^[n]) 0).re:ℝ):ℂ) := by
          apply Complex.ext <;> simp [ih]
        rw [he]
        exact hreal x _
    have hlim := Complex.continuous_im.continuousAt.tendsto.comp (huniform.tendsto_at ht)
    exact tendsto_nhds_unique hlim (by simpa only [Function.comp_def,hr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0)))
