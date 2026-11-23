-- Prove2me | solution 1 for FlowSparsSchur.Main.lemma_9_44
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:53:15.762716+00:00
-- url     : https://prove2.me/submissions/1d00da50-84ce-4234-b6c6-a78caf8ef843

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph
import Definitions.Def_FlowSparsSchur_Main_Embedding
import Definitions.Def_FlowSparsSchur_Main_Heat

namespace Aux944

open FlowSparsSchur.Main
open Matrix

section ScalarIneq

lemma log_mean_le_half_add_ordered {a b : ℝ} (hb : 0 < b) (hba : b ≤ a) :
    2 * (a - b) ≤ (a + b) * (Real.log a - Real.log b) := by
  rcases eq_or_lt_of_le hba with rfl | hlt
  · ring_nf; rfl
  · let φ : ℝ → ℝ := fun x => (x + b) * (Real.log x - Real.log b) - 2 * (x - b)
    have hderiv : ∀ x ∈ Set.Icc b a,
        HasDerivAt φ ((1 * (Real.log x - Real.log b) + (x + b) * x⁻¹) - 2 * 1) x := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hb hx.1
      have h1 : HasDerivAt (fun t => t + b) 1 x := (hasDerivAt_id x).add_const b
      have h2 : HasDerivAt (fun t => Real.log t - Real.log b) x⁻¹ x :=
        (Real.hasDerivAt_log (ne_of_gt hx_pos)).sub_const (Real.log b)
      have h3 : HasDerivAt (fun t => 2 * (t - b)) (2 * 1) x :=
        ((hasDerivAt_id x).sub_const b).const_mul 2
      exact (h1.mul h2).sub h3
    have hcont : ContinuousOn φ (Set.Icc b a) :=
      fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
    rcases exists_hasDerivAt_eq_slope φ _ hlt hcont
      (fun x hx => hderiv x (Set.Ioo_subset_Icc_self hx)) with ⟨c, hc, hslope⟩
    have hc_pos : 0 < c := lt_trans hb hc.1
    have hlog : Real.log (b / c) ≤ b / c - 1 :=
      Real.log_le_sub_one_of_pos (div_pos hb hc_pos)
    have hlog_div : Real.log (b / c) = Real.log b - Real.log c :=
      Real.log_div (ne_of_gt hb) (ne_of_gt hc_pos)
    have hfrac : (c + b) * c⁻¹ = 1 + b / c := by
      field_simp [ne_of_gt hc_pos]
    have hderiv_nn : 0 ≤ (1 * (Real.log c - Real.log b) + (c + b) * c⁻¹) - 2 * 1 := by
      linarith
    rw [hslope] at hderiv_nn
    have hφb : φ b = 0 := by simp [φ]
    have hpos_ab : 0 < a - b := sub_pos.mpr hlt
    have hφa_nn : 0 ≤ φ a - φ b := (div_nonneg_iff.mp hderiv_nn).resolve_right
      (fun h => absurd hpos_ab (not_lt_of_ge h.2)) |>.1
    dsimp only [φ] at hφa_nn hφb
    linarith

lemma log_mean_sq_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2 * (a - b) ^ 2 ≤ (a + b) * ((a - b) * (Real.log a - Real.log b)) := by
  rcases le_total b a with hba | hab
  · have h := log_mean_le_half_add_ordered hb hba
    have hsub : 0 ≤ a - b := sub_nonneg.mpr hba
    have hm := mul_le_mul_of_nonneg_left h hsub
    linarith
  · have h := log_mean_le_half_add_ordered ha hab
    have hsub : 0 ≤ b - a := sub_nonneg.mpr hab
    have hm := mul_le_mul_of_nonneg_left h hsub
    nlinarith

lemma mul_log_diff_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (a - b) * (Real.log a - Real.log b) := by
  have h := log_mean_sq_le ha hb
  have hpos : 0 < a + b := add_pos ha hb
  have hsq : 0 ≤ 2 * (a - b) ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith

lemma sqrt_diff_sq_le_mul_log_diff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ (a - b) * (Real.log a - Real.log b) := by
  have h := log_mean_sq_le (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)
  have hprod : (Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b) = a - b := by
    calc
      (Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b)
          = (Real.sqrt a) ^ 2 - (Real.sqrt b) ^ 2 := by ring
      _ = a - b := by rw [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
  have hlog : Real.log (Real.sqrt a) - Real.log (Real.sqrt b) =
      (Real.log a - Real.log b) / 2 := by
    rw [Real.log_sqrt (le_of_lt ha), Real.log_sqrt (le_of_lt hb)]
    ring
  have hrew : (Real.sqrt a + Real.sqrt b) *
      ((Real.sqrt a - Real.sqrt b) * (Real.log (Real.sqrt a) - Real.log (Real.sqrt b))) =
      ((a - b) * (Real.log a - Real.log b)) / 2 := by
    calc
      (Real.sqrt a + Real.sqrt b) *
          ((Real.sqrt a - Real.sqrt b) * (Real.log (Real.sqrt a) - Real.log (Real.sqrt b)))
          = ((Real.sqrt a + Real.sqrt b) * (Real.sqrt a - Real.sqrt b)) *
              (Real.log (Real.sqrt a) - Real.log (Real.sqrt b)) := by ring
      _ = ((a - b) * (Real.log a - Real.log b)) / 2 := by rw [hprod, hlog]; ring
  rw [hrew] at h
  have hsq_nn : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  linarith

lemma min_zero_diff_sq_le (a b : ℝ) :
    (min a 0 - min b 0) ^ 2 ≤ (min a 0 - min b 0) * (a - b) := by
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb
  · rw [min_eq_left ha, min_eq_left hb]; ring_nf; rfl
  · rw [min_eq_left ha, min_eq_right hb]; nlinarith
  · rw [min_eq_right ha, min_eq_left hb]; nlinarith
  · rw [min_eq_right ha, min_eq_right hb]; simp

end ScalarIneq

section GraphAndSchur

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma sum_split_finset (S : Finset V) (f : V → ℝ) :
    ∑ w : V, f w = (∑ s : S, f s.val) + ∑ u : {w : V // w ∉ S}, f u.val := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  have h1 : Finset.univ.filter (· ∈ S) = S := by ext; simp
  rw [h1, ← Finset.sum_coe_sort S f]
  congr 1
  exact (Finset.sum_subtype (Finset.univ.filter (· ∉ S)) (fun _ => by simp) f)

lemma lap_transpose (G : CGraph V E) : (G.lap)ᵀ = G.lap := by
  simp [CGraph.lap, CGraph.condMat, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma incidence_mulVec (G : CGraph V E) (x : V → ℝ) (e : E) :
    (G.incidence *ᵥ x) e = x (G.src e) - x (G.dst e) := by
  simp [CGraph.incidence, Matrix.mulVec, dotProduct, sub_mul]

lemma wInc_mulVec (G : CGraph V E) (x : V → ℝ) (e : E) :
    (G.wInc *ᵥ x) e = Real.sqrt (G.cond e) * (x (G.src e) - x (G.dst e)) := by
  rw [CGraph.wInc, ← Matrix.mulVec_mulVec, CGraph.sqrtCondMat, mulVec_diagonal, incidence_mulVec]

lemma dotProduct_lap_mulVec (G : CGraph V E) (x y : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ y) =
      ∑ e : E, G.cond e * (x (G.src e) - x (G.dst e)) * (y (G.src e) - y (G.dst e)) := by
  have h1 : x ⬝ᵥ (G.lap *ᵥ y) = (G.incidence *ᵥ x) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) := by
    calc
      x ⬝ᵥ (G.lap *ᵥ y)
          = x ⬝ᵥ (G.incidenceᵀ *ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y))) := by
              simp only [CGraph.lap, Matrix.mul_assoc, Matrix.mulVec_mulVec]
      _ = (x ᵥ* G.incidenceᵀ) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) :=
            Matrix.dotProduct_mulVec x G.incidenceᵀ _
      _ = (G.incidence *ᵥ x) ⬝ᵥ (G.condMat *ᵥ (G.incidence *ᵥ y)) := by
            rw [Matrix.vecMul_transpose]
  rw [h1]
  simp only [dotProduct, CGraph.condMat, mulVec_diagonal, incidence_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma quad_lap_eq (G : CGraph V E) (x : V → ℝ) :
    x ⬝ᵥ (G.lap *ᵥ x) = ∑ e : E, G.cond e * (x (G.src e) - x (G.dst e)) ^ 2 := by
  rw [dotProduct_lap_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma dissipation_lap_eq (G : CGraph V E) (f : V → ℝ) :
    dissipation G.lap f =
      ∑ e : E, G.cond e * ((f (G.src e) - f (G.dst e)) *
        (Real.log (f (G.src e)) - Real.log (f (G.dst e)))) := by
  have hsym : (G.lap *ᵥ f) ⬝ᵥ (fun v => Real.log (f v)) =
      f ⬝ᵥ (G.lap *ᵥ (fun v => Real.log (f v))) := by
    calc
      (G.lap *ᵥ f) ⬝ᵥ (fun v => Real.log (f v))
          = (f ᵥ* (G.lap)ᵀ) ⬝ᵥ (fun v => Real.log (f v)) := by rw [Matrix.vecMul_transpose]
      _ = f ⬝ᵥ (G.lap *ᵥ (fun v => Real.log (f v))) := by
            rw [lap_transpose G, ← Matrix.dotProduct_mulVec]
  unfold dissipation
  rw [hsym, dotProduct_lap_mulVec]
  refine Finset.sum_congr rfl fun e _ => by ring

lemma const_of_quad_lap_zero (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    {z : V → ℝ} (hz : z ⬝ᵥ (G.lap *ᵥ z) = 0) (u v : V) : z u = z v := by
  rw [quad_lap_eq] at hz
  have hedge_zero : ∀ e : E, z (G.src e) = z (G.dst e) := by
    intro e
    have hnn : ∀ e' ∈ (Finset.univ : Finset E),
        0 ≤ G.cond e' * (z (G.src e') - z (G.dst e')) ^ 2 :=
      fun e' _ => mul_nonneg (le_of_lt (hpos e')) (sq_nonneg _)
    have he0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz e (Finset.mem_univ e)
    have hsq : (z (G.src e) - z (G.dst e)) ^ 2 = 0 :=
      (mul_eq_zero.mp he0).resolve_left (ne_of_gt (hpos e))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hadj : ∀ a b : V, G.Adj a b → z a = z b := by
    intro a b hab
    rcases hab with ⟨e, ⟨ rfl, rfl ⟩ | ⟨ rfl, rfl ⟩⟩
    · exact hedge_zero e
    · exact (hedge_zero e).symm
  exact Relation.ReflTransGen.head_induction_on (hconn u v) rfl
    (fun {a b} hab _ ih => (hadj a b hab).trans ih)

lemma halfEndpointMass_dot (G : CGraph V E) (hloop : G.NoLoops) (w : E → ℝ) (f : V → ℝ) :
    halfEndpointMass G w ⬝ᵥ f =
      (1 / 2) * ∑ e : E, w e ^ 2 * (f (G.src e) + f (G.dst e)) := by
  calc
    halfEndpointMass G w ⬝ᵥ f
        = ∑ v : V, ((1 / 2 : ℝ) * ∑ e : E,
            if G.src e = v ∨ G.dst e = v then w e ^ 2 else (0 : ℝ)) * f v := rfl
    _ = (1 / 2 : ℝ) * ∑ v : V, ∑ e : E,
          (if G.src e = v ∨ G.dst e = v then w e ^ 2 * f v else (0 : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [mul_assoc, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          split_ifs <;> ring
    _ = (1 / 2) * ∑ e : E, ∑ v : V,
          (if G.src e = v ∨ G.dst e = v then w e ^ 2 * f v else (0 : ℝ)) := by
          rw [Finset.sum_comm]
    _ = (1 / 2) * ∑ e : E, w e ^ 2 * (f (G.src e) + f (G.dst e)) := by
          congr 1
          refine Finset.sum_congr rfl fun e _ => ?_
          have hne : G.src e ≠ G.dst e := hloop e
          have hsplit : ∀ v : V,
              (if G.src e = v ∨ G.dst e = v then w e ^ 2 * f v else (0 : ℝ)) =
                (if v = G.src e then w e ^ 2 * f v else (0 : ℝ)) +
                  (if v = G.dst e then w e ^ 2 * f v else (0 : ℝ)) := by
            intro v
            by_cases h1 : v = G.src e
            · rw [h1]
              simp [hne]
            · by_cases h2 : v = G.dst e
              · rw [h2]
                simp [hne.symm]
              · have h1' : G.src e ≠ v := Ne.symm h1
                have h2' : G.dst e ≠ v := Ne.symm h2
                simp [h1, h2, h1', h2']
          simp_rw [hsplit, Finset.sum_add_distrib]
          simp [mul_add]

lemma halfEndpointMass_sum_eq_one (G : CGraph V E) (hloop : G.NoLoops) {w : E → ℝ}
    (hw : norm2 w = 1) : ∑ v : V, halfEndpointMass G w v = 1 := by
  have h1 : ∑ v : V, halfEndpointMass G w v = halfEndpointMass G w ⬝ᵥ (fun _ => 1) := by
    simp [dotProduct]
  have hsq : ∑ e : E, w e ^ 2 = 1 := by
    have := congr_arg (· ^ 2) hw
    rwa [norm2, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), one_pow] at this
  rw [h1, halfEndpointMass_dot G hloop w (fun _ => 1)]
  calc
    (1 / 2 : ℝ) * ∑ e : E, w e ^ 2 * (1 + 1)
        = ∑ e : E, w e ^ 2 := by
            rw [← Finset.sum_mul]
            ring
    _ = 1 := hsq

lemma flow_sq_le_endpoint_dissip (G : CGraph V E) (hloop : G.NoLoops) (hpos : G.PosCond)
    (w : E → ℝ) (hw0 : ∀ e, 0 ≤ w e) (f : V → ℝ) (hf : ∀ v, 0 < f v) :
    (w ⬝ᵥ (fun e => |(G.wInc *ᵥ f) e|)) ^ 2 ≤
      (halfEndpointMass G w ⬝ᵥ f) * dissipation G.lap f := by
  let A : E → ℝ := fun e => w e * Real.sqrt ((f (G.src e) + f (G.dst e)) / 2)
  let B : E → ℝ := fun e =>
    Real.sqrt (G.cond e * ((f (G.src e) - f (G.dst e)) *
      (Real.log (f (G.src e)) - Real.log (f (G.dst e)))))
  have hterm_le : ∀ e : E, w e * |(G.wInc *ᵥ f) e| ≤ A e * B e := by
    intro e
    have ha := hf (G.src e)
    have hb := hf (G.dst e)
    have hadd_nn : 0 ≤ (f (G.src e) + f (G.dst e)) / 2 := by linarith
    have hdiss_nn : 0 ≤ G.cond e * ((f (G.src e) - f (G.dst e)) *
        (Real.log (f (G.src e)) - Real.log (f (G.dst e)))) :=
      mul_nonneg (le_of_lt (hpos e)) (mul_log_diff_nonneg ha hb)
    have hAB_nn : 0 ≤ A e * B e :=
      mul_nonneg (mul_nonneg (hw0 e) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    have hLHS_eq : w e * |(G.wInc *ᵥ f) e| =
        w e * Real.sqrt (G.cond e) * |f (G.src e) - f (G.dst e)| := by
      rw [wInc_mulVec, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_assoc]
    rw [hLHS_eq]
    have hsq_ineq : (w e * Real.sqrt (G.cond e) * |f (G.src e) - f (G.dst e)|) ^ 2 ≤
        (A e * B e) ^ 2 := by
      have hl : (w e * Real.sqrt (G.cond e) * |f (G.src e) - f (G.dst e)|) ^ 2 =
          (w e ^ 2 * G.cond e) * (f (G.src e) - f (G.dst e)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (le_of_lt (hpos e)), sq_abs]
      have hr : (A e * B e) ^ 2 =
          (w e ^ 2 * G.cond e) * (((f (G.src e) + f (G.dst e)) / 2) *
            ((f (G.src e) - f (G.dst e)) *
              (Real.log (f (G.src e)) - Real.log (f (G.dst e))))) := by
        dsimp only [A, B]
        rw [mul_pow, mul_pow, Real.sq_sqrt hadd_nn, Real.sq_sqrt hdiss_nn]
        ring
      rw [hl, hr]
      have hlm := log_mean_sq_le ha hb
      have hlm' : (f (G.src e) - f (G.dst e)) ^ 2 ≤
          ((f (G.src e) + f (G.dst e)) / 2) *
            ((f (G.src e) - f (G.dst e)) *
              (Real.log (f (G.src e)) - Real.log (f (G.dst e)))) := by linarith
      exact mul_le_mul_of_nonneg_left hlm' (mul_nonneg (sq_nonneg _) (le_of_lt (hpos e)))
    rw [← Real.sqrt_sq (mul_nonneg (mul_nonneg (hw0 e) (Real.sqrt_nonneg _)) (abs_nonneg _)),
      ← Real.sqrt_sq hAB_nn]
    exact Real.sqrt_le_sqrt hsq_ineq
  have hsum_nn : 0 ≤ w ⬝ᵥ (fun e => |(G.wInc *ᵥ f) e|) :=
    Finset.sum_nonneg fun e _ => mul_nonneg (hw0 e) (abs_nonneg _)
  have hsum_le : w ⬝ᵥ (fun e => |(G.wInc *ᵥ f) e|) ≤ ∑ e : E, A e * B e :=
    Finset.sum_le_sum fun e _ => hterm_le e
  have hsq_step : (w ⬝ᵥ (fun e => |(G.wInc *ᵥ f) e|)) ^ 2 ≤ (∑ e : E, A e * B e) ^ 2 :=
    pow_le_pow_left₀ hsum_nn hsum_le 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset E) A B
  have hAsq : ∑ e : E, A e ^ 2 = halfEndpointMass G w ⬝ᵥ f := by
    rw [halfEndpointMass_dot G hloop w f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hadd_nn : 0 ≤ (f (G.src e) + f (G.dst e)) / 2 := by
      linarith [hf (G.src e), hf (G.dst e)]
    dsimp only [A]
    rw [mul_pow, Real.sq_sqrt hadd_nn]
    ring
  have hBsq : ∑ e : E, B e ^ 2 = dissipation G.lap f := by
    rw [dissipation_lap_eq]
    refine Finset.sum_congr rfl fun e _ => ?_
    have hdiss_nn : 0 ≤ G.cond e * ((f (G.src e) - f (G.dst e)) *
        (Real.log (f (G.src e)) - Real.log (f (G.dst e)))) :=
      mul_nonneg (le_of_lt (hpos e)) (mul_log_diff_nonneg (hf (G.src e)) (hf (G.dst e)))
    dsimp only [B]
    exact Real.sq_sqrt hdiss_nn
  rw [hAsq, hBsq] at hcs
  exact hsq_step.trans hcs

lemma blockUU_isUnit_det (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) : IsUnit (blockUU G.lap S).det := by
  let U := {v : V // v ∉ S}
  let A : Matrix U U ℝ := blockUU G.lap S
  have hinj : Function.Injective A.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    change A *ᵥ x = 0 at hx
    let x_ext : V → ℝ := fun v => if hv : v ∉ S then x ⟨v, hv⟩ else 0
    have hquad0 : x_ext ⬝ᵥ (G.lap *ᵥ x_ext) = 0 := by
      simp only [dotProduct]
      refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : v ∉ S
      · have hrow : (G.lap *ᵥ x_ext) v = 0 := by
          simp only [Matrix.mulVec, dotProduct]
          rw [sum_split_finset S]
          have h1 : (∑ s' : S, G.lap v s'.val * x_ext s'.val) = 0 := by
            refine Finset.sum_eq_zero fun s' _ => ?_
            simp [x_ext, s'.prop]
          have h2 : (∑ u' : {w : V // w ∉ S}, G.lap v u'.val * x_ext u'.val) =
              (A *ᵥ x) ⟨v, hv⟩ := by
            refine Finset.sum_congr rfl fun u' _ => ?_
            simp [x_ext, u'.prop, A, blockUU]
          rw [h1, h2, hx, Pi.zero_apply, add_zero]
        rw [hrow, mul_zero]
      · have hvS : v ∈ S := not_not.mp hv
        simp [x_ext, hvS]
    rcases hS with ⟨s₀, hs₀⟩
    have hs₀_zero : x_ext s₀ = 0 := by simp [x_ext, hs₀]
    ext u
    calc
      x u = x_ext u.val := by simp [x_ext, u.prop]
      _ = x_ext s₀ := const_of_quad_lap_zero G hpos hconn hquad0 u.val s₀
      _ = 0 := hs₀_zero
  have hsurj : Function.Surjective A.mulVecLin :=
    LinearMap.injective_iff_surjective.mp hinj
  choose Bcol hBcol using fun i : U => hsurj (Pi.single i 1)
  let B : Matrix U U ℝ := Matrix.of fun u i => Bcol i u
  have hAB : A * B = 1 := by
    ext u i
    have hi := congr_fun (hBcol i) u
    simpa [Matrix.mul_apply, B, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
      eq_comm] using hi
  have hdet : A.det * B.det = 1 := by
    rw [← Matrix.det_mul, hAB, Matrix.det_one]
  exact isUnit_iff_exists_inv.mpr ⟨B.det, hdet⟩

lemma blockUU_mul_inv (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    blockUU G.lap S * (blockUU G.lap S)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (blockUU_isUnit_det G hpos hconn S hS)

lemma blockUU_inv_transpose (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    ((blockUU G.lap S)⁻¹)ᵀ = (blockUU G.lap S)⁻¹ := by
  have hsym : (blockUU G.lap S)ᵀ = blockUU G.lap S := by
    ext u₁ u₂
    have hL := congr_fun (congr_fun (lap_transpose G) u₁.val) u₂.val
    simpa [blockUU, Matrix.transpose_apply] using hL
  have h1 : ((blockUU G.lap S)⁻¹)ᵀ * blockUU G.lap S = 1 := by
    calc
      ((blockUU G.lap S)⁻¹)ᵀ * blockUU G.lap S
          = ((blockUU G.lap S)⁻¹)ᵀ * (blockUU G.lap S)ᵀ := by rw [hsym]
      _ = (blockUU G.lap S * (blockUU G.lap S)⁻¹)ᵀ := (Matrix.transpose_mul _ _).symm
      _ = 1 := by rw [blockUU_mul_inv G hpos hconn S hS, Matrix.transpose_one]
  calc
    ((blockUU G.lap S)⁻¹)ᵀ
        = ((blockUU G.lap S)⁻¹)ᵀ * (blockUU G.lap S * (blockUU G.lap S)⁻¹) := by
            rw [blockUU_mul_inv G hpos hconn S hS, Matrix.mul_one]
    _ = (((blockUU G.lap S)⁻¹)ᵀ * blockUU G.lap S) * (blockUU G.lap S)⁻¹ := by
            rw [Matrix.mul_assoc]
    _ = (blockUU G.lap S)⁻¹ := by rw [h1, Matrix.one_mul]

lemma lap_mul_schurProj_transpose (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    G.lap * (schurProj G S)ᵀ = padOf S * schurLap G S := by
  have hSU_tr : (blockSU G.lap S)ᵀ = blockUS G.lap S := by
    ext u s
    have hL := congr_fun (congr_fun (lap_transpose G) u.val) s.val
    simpa [blockSU, blockUS, Matrix.transpose_apply] using hL
  have hP_U : ∀ (u : {w : V // w ∉ S}) (s : S),
      ((schurProj G S)ᵀ) u.val s = - ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
    intro u s
    have h1 : ((schurProj G S)ᵀ) u.val s = - (blockSU G.lap S * (blockUU G.lap S)⁻¹) s u := by
      simp [schurProj, schurProjOf, u.prop, Matrix.transpose_apply]
    have h2 : (blockSU G.lap S * (blockUU G.lap S)⁻¹) s u =
        ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
      calc
        (blockSU G.lap S * (blockUU G.lap S)⁻¹) s u
            = ((blockSU G.lap S * (blockUU G.lap S)⁻¹)ᵀ) u s := rfl
        _ = (((blockUU G.lap S)⁻¹)ᵀ * (blockSU G.lap S)ᵀ) u s := by rw [Matrix.transpose_mul]
        _ = ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
              rw [blockUU_inv_transpose G hpos hconn S hS, hSU_tr]
    rw [h1, h2]
  ext v s
  rw [Matrix.mul_apply, sum_split_finset S]
  have hsumS : (∑ s' : S, G.lap v s'.val * ((schurProj G S)ᵀ) s'.val s) =
      G.lap v s.val := by
    have hrew : ∀ s' : S,
        G.lap v s'.val * ((schurProj G S)ᵀ) s'.val s =
          if s' = s then G.lap v s.val else 0 := by
      intro s'
      by_cases hss' : s' = s
      · subst hss'; simp [schurProj, schurProjOf, s'.prop]
      · have hne : s.val ≠ s'.val := fun h => hss' (Subtype.ext h.symm)
        simp [schurProj, schurProjOf, s'.prop, hss', hne]
    simp_rw [hrew]
    simp
  have hsumU : (∑ u : {w : V // w ∉ S}, G.lap v u.val * ((schurProj G S)ᵀ) u.val s) =
      - ∑ u : {w : V // w ∉ S}, G.lap v u.val * ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hP_U u s, mul_neg]
  rw [hsumS, hsumU, ← sub_eq_add_neg]
  by_cases hv : v ∈ S
  · let s₀ : S := ⟨v, hv⟩
    have hrhs : (padOf S * schurLap G S) v s = schurLap G S s₀ s := by
      rw [Matrix.mul_apply]
      have hrew : ∀ s' : S, padOf S v s' * schurLap G S s' s =
          if s' = s₀ then schurLap G S s₀ s else 0 := by
        intro s'
        by_cases hs' : s' = s₀
        · subst hs'; simp [padOf, s₀]
        · have hne : v ≠ s'.val := fun h => hs' (Subtype.ext h.symm)
          simp [padOf, hs', hne]
      simp_rw [hrew]
      simp
    rw [hrhs]
    simp [schurLap, schurOf, blockSS, blockSU, s₀, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.mul_assoc]
  · let u₀ : {w : V // w ∉ S} := ⟨v, hv⟩
    have hrhs : (padOf S * schurLap G S) v s = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun s' _ => ?_
      have hne : v ≠ s'.val := fun h => hv (h ▸ s'.prop)
      simp [padOf, hne]
    rw [hrhs]
    have hlhs : G.lap v s.val -
        (∑ u : {w : V // w ∉ S}, G.lap v u.val * ((blockUU G.lap S)⁻¹ * blockUS G.lap S) u s) =
        blockUS G.lap S u₀ s -
          (blockUU G.lap S * ((blockUU G.lap S)⁻¹ * blockUS G.lap S)) u₀ s := by
      simp [blockUS, blockUU, u₀, Matrix.mul_apply]
    rw [hlhs, ← Matrix.mul_assoc, blockUU_mul_inv G hpos hconn S hS, Matrix.one_mul, sub_self]

lemma padOf_transpose_mul_schurProj_transpose {L : Matrix V V ℝ} (S : Finset V) :
    (padOf S)ᵀ * (schurProjOf L S)ᵀ = 1 := by
  have h : schurProjOf L S * padOf S = 1 := by
    ext s₁ s₂
    rw [Matrix.mul_apply]
    have hsum : (∑ v : V, schurProjOf L S s₁ v * padOf S v s₂) =
        schurProjOf L S s₁ s₂.val := by
      simp [padOf]
    rw [hsum]
    by_cases h12 : s₁ = s₂
    · subst h12; simp [schurProjOf, s₁.prop]
    · have hv : s₁.val ≠ s₂.val := fun hv => h12 (Subtype.ext hv)
      simp [schurProjOf, s₂.prop, h12, hv]
  rw [← Matrix.transpose_mul, h, Matrix.transpose_one]

lemma harmonic_ext_on_S {L : Matrix V V ℝ} (S : Finset V) (h : S → ℝ) (s : S) :
    ((schurProjOf L S)ᵀ *ᵥ h) s.val = h s := by
  have h1 := congr_fun (Matrix.one_mulVec h) s
  rw [← padOf_transpose_mul_schurProj_transpose (L := L) S, ← Matrix.mulVec_mulVec] at h1
  have hpad : ((padOf S)ᵀ *ᵥ ((schurProjOf L S)ᵀ *ᵥ h)) s =
      ((schurProjOf L S)ᵀ *ᵥ h) s.val := by
    simp [padOf, Matrix.mulVec, dotProduct]
  rw [hpad] at h1
  exact h1

lemma lap_mulVec_one (G : CGraph V E) : G.lap *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  ext v
  have hinc : G.incidence *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    ext e
    rw [incidence_mulVec, sub_self, Pi.zero_apply]
  calc
    (G.lap *ᵥ (fun _ => (1 : ℝ))) v
        = (G.incidenceᵀ *ᵥ (G.condMat *ᵥ (G.incidence *ᵥ (fun _ => (1 : ℝ))))) v := by
            simp only [CGraph.lap, Matrix.mul_assoc, Matrix.mulVec_mulVec]
    _ = 0 := by rw [hinc, Matrix.mulVec_zero, Matrix.mulVec_zero, Pi.zero_apply]

lemma schurProj_transpose_one (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    (schurProj G S)ᵀ *ᵥ (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) := by
  let w : V → ℝ := (schurProj G S)ᵀ *ᵥ (fun _ => (1 : ℝ)) - (fun _ => (1 : ℝ))
  have hwS : ∀ s : S, w s.val = 0 := by
    intro s
    simp [w, schurProj, harmonic_ext_on_S]
  have hwU : ∀ v : V, v ∉ S → (G.lap *ᵥ w) v = 0 := by
    intro v hv
    simp only [w, Matrix.mulVec_sub, lap_mulVec_one, sub_zero]
    rw [Matrix.mulVec_mulVec, lap_mul_schurProj_transpose G hpos hconn S hS,
      ← Matrix.mulVec_mulVec]
    simp only [padOf, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hne : v ≠ s.val := fun h => hv (h ▸ s.prop)
    simp [hne]
  have hquad0 : w ⬝ᵥ (G.lap *ᵥ w) = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v ∈ S
    · rw [hwS ⟨v, hv⟩, zero_mul]
    · rw [hwU v hv, mul_zero]
  rcases hS with ⟨s₀, hs₀⟩
  ext v
  have hconst := const_of_quad_lap_zero G hpos hconn hquad0 v s₀
  have hws₀ : w s₀ = 0 := hwS ⟨s₀, hs₀⟩
  have hwv : w v = 0 := hconst.trans hws₀
  dsimp only [w, Pi.sub_apply] at hwv
  linarith

lemma schurLap_mulVec_one (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    schurLap G S *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have h1 : padOf S *ᵥ (schurLap G S *ᵥ (fun _ => (1 : ℝ))) = 0 := by
    rw [Matrix.mulVec_mulVec, ← lap_mul_schurProj_transpose G hpos hconn S hS,
      ← Matrix.mulVec_mulVec, schurProj_transpose_one G hpos hconn S hS, lap_mulVec_one]
  have h2 : (padOf S)ᵀ *ᵥ (padOf S *ᵥ (schurLap G S *ᵥ (fun _ => (1 : ℝ)))) =
      (padOf S)ᵀ *ᵥ 0 := congr_arg ((padOf S)ᵀ *ᵥ ·) h1
  have hpad2 : (padOf S)ᵀ * padOf S = (1 : Matrix S S ℝ) := by
    ext s₁ s₂
    rw [Matrix.mul_apply]
    have hsum : (∑ v : V, (padOf S)ᵀ s₁ v * padOf S v s₂) = padOf S s₁.val s₂ := by
      simp [padOf, eq_comm]
    rw [hsum]
    by_cases h12 : s₁ = s₂
    · subst h12; simp [padOf]
    · have hv : s₁.val ≠ s₂.val := fun hv => h12 (Subtype.ext hv)
      simp [padOf, h12, hv]
  rw [Matrix.mulVec_mulVec, hpad2, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
  exact h2

lemma harmonic_ext_nonneg (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) {h : S → ℝ} (hh : ∀ s, 0 ≤ h s) :
    ∀ v : V, 0 ≤ ((schurProj G S)ᵀ *ᵥ h) v := by
  let φ : V → ℝ := (schurProj G S)ᵀ *ᵥ h
  let φn : V → ℝ := fun v => min (φ v) 0
  have hφnS : ∀ s : S, φn s.val = 0 := by
    intro s
    have hval : φ s.val = h s := harmonic_ext_on_S S h s
    simp [φn, hval, min_eq_right (hh s)]
  have hLφU : ∀ v : V, v ∉ S → (G.lap *ᵥ φ) v = 0 := by
    intro v hv
    dsimp only [φ]
    rw [Matrix.mulVec_mulVec, lap_mul_schurProj_transpose G hpos hconn S hS,
      ← Matrix.mulVec_mulVec]
    simp only [padOf, Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hne : v ≠ s.val := fun heq => hv (heq ▸ s.prop)
    simp [hne]
  have hdot0 : φn ⬝ᵥ (G.lap *ᵥ φ) = 0 := by
    simp only [dotProduct]
    refine Finset.sum_eq_zero fun v _ => ?_
    by_cases hv : v ∈ S
    · rw [hφnS ⟨v, hv⟩, zero_mul]
    · rw [hLφU v hv, mul_zero]
  have hquad_le : φn ⬝ᵥ (G.lap *ᵥ φn) ≤ φn ⬝ᵥ (G.lap *ᵥ φ) := by
    rw [quad_lap_eq, dotProduct_lap_mulVec]
    refine Finset.sum_le_sum fun e _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (min_zero_diff_sq_le (φ (G.src e)) (φ (G.dst e)))
      (le_of_lt (hpos e))
  have hquad_nn : 0 ≤ φn ⬝ᵥ (G.lap *ᵥ φn) := by
    rw [quad_lap_eq]
    exact Finset.sum_nonneg fun e _ => mul_nonneg (le_of_lt (hpos e)) (sq_nonneg _)
  have hquad0 : φn ⬝ᵥ (G.lap *ᵥ φn) = 0 := le_antisymm (hquad_le.trans_eq hdot0) hquad_nn
  rcases hS with ⟨s₀, hs₀⟩
  intro v
  have hconst := const_of_quad_lap_zero G hpos hconn hquad0 v s₀
  have hs0 : φn s₀ = 0 := hφnS ⟨s₀, hs₀⟩
  have hmin0 : min (φ v) 0 = 0 := hconst.trans hs0
  exact min_eq_right_iff.mp hmin0

lemma schurProj_entry_nonneg (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) (s : S) (v : V) :
    0 ≤ schurProj G S s v := by
  let ind : S → ℝ := fun s' => if s' = s then 1 else 0
  have h1 : ∀ s' : S, 0 ≤ ind s' := fun s' => by
    dsimp only [ind]; split_ifs <;> norm_num
  have hnn := harmonic_ext_nonneg G hpos hconn S hS h1 v
  simpa [ind, Matrix.mulVec, dotProduct, Matrix.transpose_apply] using hnn

lemma schurLap_offdiag_nonpos (G : CGraph V E) (hloop : G.NoLoops) (hpos : G.PosCond)
    (hconn : G.Connected) (S : Finset V) (hS : S.Nonempty) {s₁ s₂ : S} (hne : s₁ ≠ s₂) :
    schurLap G S s₁ s₂ ≤ 0 := by
  let h : S → ℝ := fun s => if s = s₂ then 1 else 0
  have hh : ∀ s, 0 ≤ h s := fun s => by dsimp only [h]; split_ifs <;> norm_num
  let φ : V → ℝ := (schurProj G S)ᵀ *ᵥ h
  have hφ_nn : ∀ v, 0 ≤ φ v := harmonic_ext_nonneg G hpos hconn S hS hh
  have hφ_s₁ : φ s₁.val = 0 := by
    change ((schurProjOf G.lap S)ᵀ *ᵥ h) s₁.val = 0
    rw [harmonic_ext_on_S S h s₁]
    simp [h, hne]
  let u₁ : V → ℝ := fun v => if v = s₁.val then 1 else 0
  have hentry : schurLap G S s₁ s₂ = u₁ ⬝ᵥ (G.lap *ᵥ φ) := by
    have h1 : (G.lap *ᵥ φ) s₁.val = (padOf S *ᵥ (schurLap G S *ᵥ h)) s₁.val := by
      dsimp only [φ]
      rw [Matrix.mulVec_mulVec, lap_mul_schurProj_transpose G hpos hconn S hS,
        ← Matrix.mulVec_mulVec]
    have h2 : (padOf S *ᵥ (schurLap G S *ᵥ h)) s₁.val = schurLap G S s₁ s₂ := by
      let wS : S → ℝ := schurLap G S *ᵥ h
      have hp : (padOf S *ᵥ wS) s₁.val = wS s₁ := by
        rw [Matrix.mulVec, dotProduct]
        have hrew : ∀ s' : S, padOf S s₁.val s' * wS s' =
            if s' = s₁ then wS s₁ else 0 := by
          intro s'
          by_cases hs' : s' = s₁
          · subst hs'; simp [padOf]
          · have hv : s₁.val ≠ s'.val := fun hv => hs' (Subtype.ext hv.symm)
            simp [padOf, hs', hv]
        simp_rw [hrew]
        simp
      change (padOf S *ᵥ wS) s₁.val = schurLap G S s₁ s₂
      rw [hp]
      dsimp only [wS, h]
      rw [Matrix.mulVec, dotProduct]
      simp
    rw [← h2, ← h1]
    simp [u₁, dotProduct]
  rw [hentry, dotProduct_lap_mulVec]
  refine Finset.sum_nonpos fun e _ => ?_
  have hcond_nn : 0 ≤ G.cond e := le_of_lt (hpos e)
  have hsrc_ne_dst : G.src e ≠ G.dst e := hloop e
  by_cases hsrc : G.src e = s₁.val
  · have hdst : G.dst e ≠ s₁.val := fun hd => hsrc_ne_dst (hsrc.trans hd.symm)
    have hp1 : u₁ (G.src e) = 1 := by simp [u₁, hsrc]
    have hp2 : u₁ (G.dst e) = 0 := by simp [u₁, hdst]
    rw [hp1, hp2, hsrc, hφ_s₁]
    nlinarith [hφ_nn (G.dst e)]
  · by_cases hdst : G.dst e = s₁.val
    · have hp1 : u₁ (G.src e) = 0 := by simp [u₁, hsrc]
      have hp2 : u₁ (G.dst e) = 1 := by simp [u₁, hdst]
      rw [hp1, hp2, hdst, hφ_s₁]
      nlinarith [hφ_nn (G.src e)]
    · have hp1 : u₁ (G.src e) = 0 := by simp [u₁, hsrc]
      have hp2 : u₁ (G.dst e) = 0 := by simp [u₁, hdst]
      rw [hp1, hp2]
      simp

lemma schurLap_transpose (G : CGraph V E) (hpos : G.PosCond) (hconn : G.Connected)
    (S : Finset V) (hS : S.Nonempty) :
    (schurLap G S)ᵀ = schurLap G S := by
  have h1 : schurProj G S * (G.lap * (schurProj G S)ᵀ) = schurLap G S := by
    rw [lap_mul_schurProj_transpose G hpos hconn S hS, ← Matrix.mul_assoc]
    have hPpad : schurProj G S * padOf S = 1 := by
      have ht := congr_arg Matrix.transpose
        (padOf_transpose_mul_schurProj_transpose (L := G.lap) S)
      simpa [schurProj, Matrix.transpose_mul] using ht
    rw [hPpad, Matrix.one_mul]
  rw [← h1]
  simp [Matrix.transpose_mul, lap_transpose G, Matrix.mul_assoc]

lemma sym_zero_row_quad_pair {W : Type} [Fintype W] {L : Matrix W W ℝ}
    (hsym : Lᵀ = L) (h1 : L *ᵥ (fun _ => (1 : ℝ)) = 0) (f g : W → ℝ) :
    f ⬝ᵥ (L *ᵥ g) =
      (1 / 2) * ∑ u : W, ∑ w : W, (- L u w) * ((f u - f w) * (g u - g w)) := by
  have hrow0 : ∀ u : W, ∑ w : W, L u w = 0 := by
    intro u
    have hu := congr_fun h1 u
    simpa [Matrix.mulVec, dotProduct] using hu
  have hcol0 : ∀ w : W, ∑ u : W, L u w = 0 := by
    intro w
    calc
      ∑ u : W, L u w = ∑ u : W, Lᵀ w u := rfl
      _ = ∑ u : W, L w u := Finset.sum_congr rfl fun u _ => by rw [hsym]
      _ = 0 := hrow0 w
  have hexp : ∑ u : W, ∑ w : W, (- L u w) * ((f u - f w) * (g u - g w)) =
      (∑ u : W, ∑ w : W, (- L u w) * (f u * g u)) +
      (∑ u : W, ∑ w : W, L u w * (f u * g w)) +
      (∑ u : W, ∑ w : W, L u w * (f w * g u)) +
      (∑ u : W, ∑ w : W, (- L u w) * (f w * g w)) := by
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun w _ => by ring
  have ht1 : ∑ u : W, ∑ w : W, (- L u w) * (f u * g u) = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    have : ∑ w : W, (- L u w) * (f u * g u) = - (f u * g u) * ∑ w : W, L u w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => by ring
    rw [this, hrow0 u, mul_zero]
  have ht4 : ∑ u : W, ∑ w : W, (- L u w) * (f w * g w) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun w _ => ?_
    have : ∑ u : W, (- L u w) * (f w * g w) = - (f w * g w) * ∑ u : W, L u w := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => by ring
    rw [this, hcol0 w, mul_zero]
  have ht2 : ∑ u : W, ∑ w : W, L u w * (f u * g w) = f ⬝ᵥ (L *ᵥ g) := by
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  have ht3 : ∑ u : W, ∑ w : W, L u w * (f w * g u) = f ⬝ᵥ (L *ᵥ g) := by
    rw [Finset.sum_comm]
    simp only [dotProduct, Matrix.mulVec]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hluw : L u w = L w u := by
      calc L u w = Lᵀ w u := rfl
      _ = L w u := by rw [hsym]
    rw [hluw]
    ring
  rw [hexp, ht1, ht2, ht3, ht4]
  ring

end GraphAndSchur

end Aux944

open FlowSparsSchur.Main
open Matrix

theorem solution {n m r : ℕ} (G : CGraph (Fin n) (Fin m)) (S : Finset (Fin n))
    (Ht : CGraph S (Fin r)) (ξ : ℝ) (hG : G.IsCondGraph) (hS : 2 ≤ S.card) (hξ : 1 ≤ ξ)
    (hHt : Ht.NoLoops ∧ Ht.PosCond) (happrox : SpecApprox ξ Ht.lap (schurLap G S))
    (x : Fin r → ℝ) (y : Fin m → ℝ) (hx0 : ∀ f, 0 ≤ x f) (hy0 : ∀ e, 0 ≤ y e)
    (hx1 : norm2 x = 1) (hy1 : norm2 y = 1) :
    (∀ v, 0 ≤ (schurProj G S *ᵥ halfEndpointMass G y) v) ∧
    ∑ v, halfEndpointMass Ht x v = 1 ∧ ∑ v, halfEndpointMass G y v = 1 ∧
    ∑ v, (schurProj G S *ᵥ halfEndpointMass G y) v = 1 ∧
    ∀ h : S → ℝ, (∀ v, 0 < h v) →
      (x ⬝ᵥ (fun f => |(Ht.wInc *ᵥ h) f|)) ^ 2 ≤
          (halfEndpointMass Ht x ⬝ᵥ h) * dissipation Ht.lap h ∧
      (y ⬝ᵥ (fun e => |(G.wInc *ᵥ ((schurProj G S)ᵀ *ᵥ h)) e|)) ^ 2 ≤
          ((schurProj G S *ᵥ halfEndpointMass G y) ⬝ᵥ (fun v => 1 + h v)) *
            dissipation (schurLap G S) (fun v => 1 + h v) ∧
      (x ⬝ᵥ (fun f => |(Ht.wInc *ᵥ h) f|)) ^ 2 ≤
          4 * ξ * (halfEndpointMass Ht x ⬝ᵥ h) * dissipation (schurLap G S) h := by
  have hS_ne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hν_nn : ∀ w : Fin n, 0 ≤ halfEndpointMass G y w := fun w =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun e _ => by
      split_ifs
      · exact sq_nonneg _
      · rfl)
  have hβ_nn : ∀ s : S, 0 ≤ (schurProj G S *ᵥ halfEndpointMass G y) s := by
    intro s
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun w _ =>
      mul_nonneg (Aux944.schurProj_entry_nonneg G hG.2.1 hG.2.2 S hS_ne s w) (hν_nn w)
  have hα_sum : ∑ v : S, halfEndpointMass Ht x v = 1 :=
    Aux944.halfEndpointMass_sum_eq_one Ht hHt.1 hx1
  have hν_sum : ∑ v : Fin n, halfEndpointMass G y v = 1 :=
    Aux944.halfEndpointMass_sum_eq_one G hG.1 hy1
  have hβ_sum : ∑ v : S, (schurProj G S *ᵥ halfEndpointMass G y) v = 1 := by
    calc
      ∑ v : S, (schurProj G S *ᵥ halfEndpointMass G y) v
          = (fun _ : S => (1 : ℝ)) ⬝ᵥ (schurProj G S *ᵥ halfEndpointMass G y) := by
              simp [dotProduct]
      _ = ((schurProj G S)ᵀ *ᵥ (fun _ : S => (1 : ℝ))) ⬝ᵥ halfEndpointMass G y := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      _ = (fun _ : Fin n => (1 : ℝ)) ⬝ᵥ halfEndpointMass G y := by
            rw [Aux944.schurProj_transpose_one G hG.2.1 hG.2.2 S hS_ne]
      _ = ∑ v : Fin n, halfEndpointMass G y v := by simp [dotProduct]
      _ = 1 := hν_sum
  refine ⟨hβ_nn, hα_sum, hν_sum, hβ_sum, fun h hh => ?_⟩
  refine ⟨Aux944.flow_sq_le_endpoint_dissip Ht hHt.1 hHt.2 x hx0 h hh, ?_, ?_⟩
  · -- Item 2
    let g : S → ℝ := fun v => 1 + h v
    have hg_pos : ∀ v : S, 0 < g v := fun v => by linarith [hh v]
    have hg_nn : ∀ v : S, 0 ≤ g v := fun v => le_of_lt (hg_pos v)
    let f : Fin n → ℝ := (schurProj G S)ᵀ *ᵥ g
    have hf_eq : f = (fun _ => (1 : ℝ)) + (schurProj G S)ᵀ *ᵥ h := by
      have hg_split : g = (fun _ => (1 : ℝ)) + h := rfl
      dsimp only [f]
      rw [hg_split, Matrix.mulVec_add, Aux944.schurProj_transpose_one G hG.2.1 hG.2.2 S hS_ne]
    have hf_pos : ∀ w : Fin n, 0 < f w := by
      intro w
      have hPh_nn : 0 ≤ ((schurProj G S)ᵀ *ᵥ h) w :=
        Aux944.harmonic_ext_nonneg G hG.2.1 hG.2.2 S hS_ne (fun v => le_of_lt (hh v)) w
      rw [hf_eq]
      simp only [Pi.add_apply]
      linarith
    have hwInc_eq : (fun e => |(G.wInc *ᵥ ((schurProj G S)ᵀ *ᵥ h)) e|) =
        (fun e => |(G.wInc *ᵥ f) e|) := by
      ext e
      rw [hf_eq, Matrix.mulVec_add]
      have hw1 : (G.wInc *ᵥ (fun _ : Fin n => (1 : ℝ))) e = 0 := by
        rw [Aux944.wInc_mulVec, sub_self, mul_zero]
      simp [hw1]
    have hdot_β : halfEndpointMass G y ⬝ᵥ f =
        (schurProj G S *ᵥ halfEndpointMass G y) ⬝ᵥ g := by
      dsimp only [f]
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    have hdiss_eq : dissipation G.lap f = dissipation (schurLap G S) g := by
      unfold dissipation
      have hLf : G.lap *ᵥ f = padOf S *ᵥ (schurLap G S *ᵥ g) := by
        dsimp only [f]
        rw [Matrix.mulVec_mulVec, Aux944.lap_mul_schurProj_transpose G hG.2.1 hG.2.2 S hS_ne,
          ← Matrix.mulVec_mulVec]
      rw [hLf, dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
      have hpad_log : (padOf S)ᵀ *ᵥ (fun w : Fin n => Real.log (f w)) =
          fun s : S => Real.log (g s) := by
        ext s
        have hfs : f s.val = g s := Aux944.harmonic_ext_on_S S g s
        simp [padOf, Matrix.mulVec, dotProduct, hfs]
      rw [hpad_log, dotProduct_comm]
    rw [hwInc_eq, ← hdot_β, ← hdiss_eq]
    exact Aux944.flow_sq_le_endpoint_dissip G hG.1 hG.2.1 y hy0 f hf_pos
  · -- Item 3
    let sh : S → ℝ := fun v => Real.sqrt (h v)
    let A : Fin r → ℝ := fun f => x f * (sh (Ht.src f) + sh (Ht.dst f))
    let B : Fin r → ℝ := fun f =>
      Real.sqrt (Ht.cond f) * |sh (Ht.src f) - sh (Ht.dst f)|
    have hLHS_eq : x ⬝ᵥ (fun f => |(Ht.wInc *ᵥ h) f|) = ∑ f : Fin r, A f * B f := by
      simp only [dotProduct]
      refine Finset.sum_congr rfl fun f _ => ?_
      have ha := hh (Ht.src f)
      have hb := hh (Ht.dst f)
      have hdiff : h (Ht.src f) - h (Ht.dst f) =
          (sh (Ht.src f) + sh (Ht.dst f)) * (sh (Ht.src f) - sh (Ht.dst f)) := by
        calc
          h (Ht.src f) - h (Ht.dst f)
              = (sh (Ht.src f)) ^ 2 - (sh (Ht.dst f)) ^ 2 := by
                  dsimp only [sh]
                  rw [Real.sq_sqrt (le_of_lt ha), Real.sq_sqrt (le_of_lt hb)]
          _ = (sh (Ht.src f) + sh (Ht.dst f)) * (sh (Ht.src f) - sh (Ht.dst f)) := by ring
      have hpos_sum : 0 ≤ sh (Ht.src f) + sh (Ht.dst f) :=
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [Aux944.wInc_mulVec, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), hdiff, abs_mul,
        abs_of_nonneg hpos_sum]
      dsimp only [A, B]
      ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin r)) A B
    have hAsq_le : ∑ f : Fin r, A f ^ 2 ≤ 4 * (halfEndpointMass Ht x ⬝ᵥ h) := by
      rw [Aux944.halfEndpointMass_dot Ht hHt.1 x h]
      have hrw : (4 : ℝ) * ((1 / 2) * ∑ f : Fin r, x f ^ 2 * (h (Ht.src f) + h (Ht.dst f))) =
          ∑ f : Fin r, x f ^ 2 * (2 * (h (Ht.src f) + h (Ht.dst f))) := by
        rw [← mul_assoc, show (4 : ℝ) * (1 / 2) = 2 by norm_num, Finset.mul_sum]
        refine Finset.sum_congr rfl fun f _ => by ring
      rw [hrw]
      refine Finset.sum_le_sum fun f _ => ?_
      dsimp only [A]
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      have hsq_u : (sh (Ht.src f)) ^ 2 = h (Ht.src f) :=
        Real.sq_sqrt (le_of_lt (hh (Ht.src f)))
      have hsq_v : (sh (Ht.dst f)) ^ 2 = h (Ht.dst f) :=
        Real.sq_sqrt (le_of_lt (hh (Ht.dst f)))
      have hdiff_nn : 0 ≤ (sh (Ht.src f) - sh (Ht.dst f)) ^ 2 := sq_nonneg _
      nlinarith
    have hBsq_eq : ∑ f : Fin r, B f ^ 2 = sh ⬝ᵥ (Ht.lap *ᵥ sh) := by
      rw [Aux944.quad_lap_eq Ht]
      refine Finset.sum_congr rfl fun f _ => ?_
      dsimp only [B]
      rw [mul_pow, Real.sq_sqrt (le_of_lt (hHt.2 f)), sq_abs]
    have hspec_le : sh ⬝ᵥ (Ht.lap *ᵥ sh) ≤ ξ * (sh ⬝ᵥ (schurLap G S *ᵥ sh)) := by
      have h1 := happrox.2 sh
      rwa [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
    have hschur_sym := Aux944.schurLap_transpose G hG.2.1 hG.2.2 S hS_ne
    have hschur_one := Aux944.schurLap_mulVec_one G hG.2.1 hG.2.2 S hS_ne
    have henergy_le_diss : sh ⬝ᵥ (schurLap G S *ᵥ sh) ≤ dissipation (schurLap G S) h := by
      have hE := Aux944.sym_zero_row_quad_pair hschur_sym hschur_one sh sh
      have hI : dissipation (schurLap G S) h =
          (1 / 2) * ∑ u : S, ∑ w : S, (- schurLap G S u w) *
            ((h u - h w) * (Real.log (h u) - Real.log (h w))) := by
        have hsym_I : (schurLap G S *ᵥ h) ⬝ᵥ (fun v => Real.log (h v)) =
            h ⬝ᵥ (schurLap G S *ᵥ (fun v => Real.log (h v))) := by
          calc
            (schurLap G S *ᵥ h) ⬝ᵥ (fun v => Real.log (h v))
                = (h ᵥ* (schurLap G S)ᵀ) ⬝ᵥ (fun v => Real.log (h v)) := by
                    rw [Matrix.vecMul_transpose]
            _ = h ⬝ᵥ (schurLap G S *ᵥ (fun v => Real.log (h v))) := by
                  rw [hschur_sym, ← Matrix.dotProduct_mulVec]
        unfold dissipation
        rw [hsym_I, Aux944.sym_zero_row_quad_pair hschur_sym hschur_one h (fun v => Real.log (h v))]
      rw [hE, hI]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun w _ => ?_
      by_cases huw : u = w
      · subst huw; simp
      · have hneg_nn : 0 ≤ - schurLap G S u w :=
          neg_nonneg.mpr (Aux944.schurLap_offdiag_nonpos G hG.1 hG.2.1 hG.2.2 S hS_ne huw)
        rw [← sq]
        exact mul_le_mul_of_nonneg_left
          (Aux944.sqrt_diff_sq_le_mul_log_diff (hh u) (hh w)) hneg_nn
    have hαh_nn : 0 ≤ halfEndpointMass Ht x ⬝ᵥ h := by
      rw [Aux944.halfEndpointMass_dot Ht hHt.1 x h]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun f _ =>
        mul_nonneg (sq_nonneg _) (by linarith [hh (Ht.src f), hh (Ht.dst f)]))
    have hBsq_nn : 0 ≤ ∑ f : Fin r, B f ^ 2 :=
      Finset.sum_nonneg fun f _ => sq_nonneg _
    have hξ_nn : 0 ≤ ξ := by linarith
    rw [hLHS_eq]
    calc
      (∑ f : Fin r, A f * B f) ^ 2
          ≤ (∑ f : Fin r, A f ^ 2) * (∑ f : Fin r, B f ^ 2) := hcs
      _ ≤ (4 * (halfEndpointMass Ht x ⬝ᵥ h)) * (∑ f : Fin r, B f ^ 2) :=
            mul_le_mul_of_nonneg_right hAsq_le hBsq_nn
      _ = (4 * (halfEndpointMass Ht x ⬝ᵥ h)) * (sh ⬝ᵥ (Ht.lap *ᵥ sh)) := by rw [hBsq_eq]
      _ ≤ (4 * (halfEndpointMass Ht x ⬝ᵥ h)) * (ξ * (sh ⬝ᵥ (schurLap G S *ᵥ sh))) :=
            mul_le_mul_of_nonneg_left hspec_le (by linarith)
      _ ≤ (4 * (halfEndpointMass Ht x ⬝ᵥ h)) * (ξ * dissipation (schurLap G S) h) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left henergy_le_diss hξ_nn) (by linarith)
      _ = 4 * ξ * (halfEndpointMass Ht x ⬝ᵥ h) * dissipation (schurLap G S) h := by ring
