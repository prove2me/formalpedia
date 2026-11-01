-- Prove2me | solution 1 for FBMStrongSim.RecordBreak.theorem_3_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T20:44:03.063801+00:00
-- url     : https://prove2.me/submissions/96d7b8d3-220c-4ac2-965d-a0eeca7200c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model
import Theorems.Thm_FBMStrongSim_RecordBreak_borell_tis_finite
import Theorems.Thm_FBMStrongSim_RecordBreak_lemma_3_3

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace FBM31Aux
open FBMStrongSim.RecordBreak

/-- Covariance of `U - (V + W)/2` against `Y`. -/
theorem cov_comb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V W Y : Ω → ℝ} (hU : MemLp U 2 P) (hV : MemLp V 2 P) (hW : MemLp W 2 P)
    (hY : MemLp Y 2 P) :
    cov[fun ω => U ω - (V ω + W ω) / 2, Y; P]
      = cov[U, Y; P] - (cov[V, Y; P] + cov[W, Y; P]) / 2 := by
  have hVW : MemLp (fun ω => (V ω + W ω) / 2) 2 P := by
    have h1 : MemLp (V + W) 2 P := hV.add hW
    have h2 : MemLp (fun ω => (1 / 2 : ℝ) * (V + W) ω) 2 P := h1.const_mul _
    have e : (fun ω => (V ω + W ω) / 2) = fun ω => (1 / 2 : ℝ) * (V + W) ω := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [e]; exact h2
  rw [covariance_fun_sub_left hU hVW hY, covariance_fun_div_left]
  have : cov[fun ω => V ω + W ω, Y; P] = cov[V + W, Y; P] := rfl
  rw [this, covariance_add_left hV hW hY]

theorem var_comb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V W : Ω → ℝ} (hU : MemLp U 2 P) (hV : MemLp V 2 P) (hW : MemLp W 2 P) :
    Var[fun ω => U ω - (V ω + W ω) / 2; P]
      = cov[U, U; P] - cov[U, V; P] - cov[U, W; P]
        + (cov[V, V; P] + 2 * cov[V, W; P] + cov[W, W; P]) / 4 := by
  have hVW : MemLp (fun ω => (V ω + W ω) / 2) 2 P := by
    have h1 : MemLp (V + W) 2 P := hV.add hW
    have h2 : MemLp (fun ω => (1 / 2 : ℝ) * (V + W) ω) 2 P := h1.const_mul _
    have e : (fun ω => (V ω + W ω) / 2) = fun ω => (1 / 2 : ℝ) * (V + W) ω := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [e]; exact h2
  have hZ : MemLp (fun ω => U ω - (V ω + W ω) / 2) 2 P := MemLp.sub hU hVW
  rw [← covariance_self hZ.aemeasurable, cov_comb hU hV hW hZ, covariance_comm U,
    covariance_comm V, covariance_comm W, cov_comb hU hV hW hU, cov_comb hU hV hW hV,
    cov_comb hU hV hW hW, covariance_comm V U, covariance_comm W U, covariance_comm W V]
  ring

/-- The fBM covariance algebra for a midpoint displacement with spacing `h`. -/
theorem fbm_disp_var (H l h : ℝ) (hH : 0 < H) (hh : 0 < h) :
    fbmCov H (l + h) (l + h) - fbmCov H (l + h) l - fbmCov H (l + h) (l + 2 * h)
      + (fbmCov H l l + 2 * fbmCov H l (l + 2 * h) + fbmCov H (l + 2 * h) (l + 2 * h)) / 4
      ≤ h ^ (2 * H) := by
  unfold fbmCov
  have h0 : |(0 : ℝ)| ^ (2 * H) = 0 := by rw [abs_zero, Real.zero_rpow (by positivity)]
  have e1 : l + h - (l + h) = 0 := by ring
  have e2 : |l + h - l| = h := by rw [show l + h - l = h by ring, abs_of_pos hh]
  have e3 : |l + h - (l + 2 * h)| = h := by
    rw [show l + h - (l + 2 * h) = -h by ring, abs_neg, abs_of_pos hh]
  have e4 : l - l = 0 := by ring
  have e5 : |l - (l + 2 * h)| = 2 * h := by
    rw [show l - (l + 2 * h) = -(2 * h) by ring, abs_neg, abs_of_pos (by linarith)]
  have e6 : l + 2 * h - (l + 2 * h) = 0 := by ring
  rw [e1, e2, e3, e4, e5, e6, h0]
  have hpos : 0 ≤ (2 * h) ^ (2 * H) := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- Growth: for `n` large, `4 √n ≤ ν 2^{δ n}`. -/
theorem knu_bdd (ν δ : ℝ) (hν : 0 < ν) (hδ : 0 < δ) :
    BddAbove {n : ℕ | 1 ≤ n ∧ ν * (2 : ℝ) ^ (δ * n) < 4 * Real.sqrt n} := by
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  set q : ℝ := δ * Real.log 2 with hq
  have hq0 : 0 < q := by positivity
  refine ⟨⌈8 / (ν * q ^ 2)⌉₊, fun n hn => ?_⟩
  obtain ⟨hn1, hlt⟩ := hn
  by_contra hcon
  push Not at hcon
  have hnr : (8 / (ν * q ^ 2) : ℝ) < n := by
    have := Nat.lt_of_ceil_lt hcon
    exact this
  have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hsq : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have hexp : (2 : ℝ) ^ (δ * n) = Real.exp (q * n) := by
    rw [Real.rpow_def_of_pos (by norm_num), hq]; ring_nf
  have hq2 := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ q * n)
  have h8 : 8 < ν * q ^ 2 * n := by
    rw [div_lt_iff₀ (by positivity)] at hnr; linarith
  have : 4 * (n : ℝ) ≤ ν * (2 : ℝ) ^ (δ * n) := by
    rw [hexp]
    have : ν * ((q * n) ^ 2 / 2) ≤ ν * Real.exp (q * n) := by
      apply mul_le_mul_of_nonneg_left _ hν.le; nlinarith
    nlinarith
  linarith

end FBM31Aux

open FBMStrongSim.RecordBreak FBM31Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hdelta0 : 0 < delta) (hdeltaH : delta < H)
    {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    {nu nuStar : ℝ} (hnu : 0 < nu) (hnuStar : 0 < nuStar) {k : ℕ} (hk : Knu nu delta < k) :
    P {ω | 2 * (nu + nuStar) * ell H delta k ≤ maxDisp (fun s => B s ω) k}
      ≤ ENNReal.ofReal (2 * Real.exp (-nuStar ^ 2 * (2 : ℝ) ^ (2 * (k : ℝ) * delta - 2))) := by
  classical
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  set n : ℕ := 2 ^ k' with hndef
  have hn : 0 < n := by rw [hndef]; positivity
  have h2k : (0 : ℝ) < 2 ^ k' := by positivity
  -- the three points of each displacement
  set pm : Fin n → ℝ := fun i => dyadic (k' + 1) (2 * (i : ℕ) + 1) with hpmdef
  set pl : Fin n → ℝ := fun i => dyadic k' (i : ℕ) with hpldef
  set pr : Fin n → ℝ := fun i => dyadic k' ((i : ℕ) + 1) with hprdef
  have hi_lt : ∀ i : Fin n, ((i : ℕ) : ℝ) + 1 ≤ 2 ^ k' := by
    intro i
    have : (i : ℕ) + 1 ≤ 2 ^ k' := i.2
    exact_mod_cast this
  have hpl : ∀ i, pl i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i; simp only [hpldef, dyadic]
    have := hi_lt i
    constructor
    · positivity
    · rw [div_le_one h2k]; linarith
  have hpr : ∀ i, pr i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i; simp only [hprdef, dyadic]
    have := hi_lt i
    constructor
    · positivity
    · rw [div_le_one h2k]; push_cast; linarith
  have hpm : ∀ i, pm i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i; simp only [hpmdef, dyadic]
    have := hi_lt i
    constructor
    · positivity
    · rw [div_le_one (by positivity), pow_succ]; push_cast; linarith
  -- the displacement vector
  set X : Fin n → Ω → ℝ := fun i ω => disp (fun s => B s ω) (k' + 1) (i : ℕ) with hXdef
  have hXeq : ∀ i ω, X i ω = B (pm i) ω - (B (pl i) ω + B (pr i) ω) / 2 := by
    intro i ω; simp [hXdef, disp, hpmdef, hpldef, hprdef]
  have hlaw : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), HasGaussianLaw (B t) P := fun t ht =>
    hB.gaussian.hasGaussianLaw_eval (⟨t, ht⟩ : Set.Icc (0 : ℝ) 1)
  have hmlp : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), MemLp (B t) 2 P := fun t ht => (hlaw t ht).memLp_two
  have hint : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) 1), Integrable (B t) P :=
    fun t ht => (hlaw t ht).integrable
  -- Gaussianity of the vector
  have hX : HasGaussianLaw (fun ω i => X i ω) P := by
    let gm : Fin n → Set.Icc (0 : ℝ) 1 := fun i => ⟨pm i, hpm i⟩
    let gl : Fin n → Set.Icc (0 : ℝ) 1 := fun i => ⟨pl i, hpl i⟩
    let gr : Fin n → Set.Icc (0 : ℝ) 1 := fun i => ⟨pr i, hpr i⟩
    let I : Finset (Set.Icc (0 : ℝ) 1) :=
      Finset.univ.image gm ∪ Finset.univ.image gl ∪ Finset.univ.image gr
    have hmI : ∀ i, gm i ∈ I := fun i => by simp [I]
    have hlI : ∀ i, gl i ∈ I := fun i => by simp [I]
    have hrI : ∀ i, gr i ∈ I := fun i => by simp [I]
    let L : (I → ℝ) →L[ℝ] (Fin n → ℝ) :=
      { toFun v i := v ⟨gm i, hmI i⟩ - (v ⟨gl i, hlI i⟩ + v ⟨gr i, hrI i⟩) / 2
        map_add' x y := by ext; simp; ring
        map_smul' c x := by ext; simp; ring }
    have hG := (hB.gaussian.hasGaussianLaw I).map L
    have heq : (fun ω i => X i ω) = L ∘ (fun ω => I.restrict (fun t : Set.Icc (0 : ℝ) 1 => B t ω)) := by
      funext ω i
      rw [hXeq]
      rfl
    rw [heq]
    exact hG
  have hcent : ∀ i, P[X i] = 0 := by
    intro i
    have e : X i = fun ω => B (pm i) ω - (B (pl i) ω + B (pr i) ω) / 2 := funext (hXeq i)
    rw [e]
    show ∫ ω, B (pm i) ω - (B (pl i) ω + B (pr i) ω) / 2 ∂P = 0
    have i1 : Integrable (fun ω => (B (pl i) ω + B (pr i) ω) / 2) P :=
      ((hint _ (hpl i)).add (hint _ (hpr i))).div_const 2
    have i2 : Integrable (fun ω => B (pl i) ω + B (pr i) ω) P := (hint _ (hpl i)).add (hint _ (hpr i))
    rw [integral_sub (hint _ (hpm i)) i1, integral_div, integral_add (hint _ (hpl i)) (hint _ (hpr i)),
      hB.centered _ (hpm i), hB.centered _ (hpl i), hB.centered _ (hpr i)]
    ring
  -- variance bound
  set K : ℝ := ((k' + 1 : ℕ) : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; push_cast; linarith [(k'.cast_nonneg : (0 : ℝ) ≤ k')]
  set h : ℝ := (2 : ℝ) ^ (-K) with hhdef
  have hh0 : 0 < h := Real.rpow_pos_of_pos (by norm_num) _
  set σ : ℝ := (2 : ℝ) ^ (-K * H) with hσdef
  have hσ0 : 0 < σ := Real.rpow_pos_of_pos (by norm_num) _
  have hσsq : σ ^ 2 = h ^ (2 * H) := by
    rw [hσdef, hhdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num)]
    congr 1; push_cast; ring
  have hh_eq : h = 1 / 2 ^ (k' + 1) := by
    rw [hhdef, hK, Real.rpow_neg (by norm_num), Real.rpow_natCast, one_div]
  have hpm_eq : ∀ i, pm i = pl i + h := by
    intro i; simp only [hpmdef, hpldef, dyadic]; rw [hh_eq, pow_succ]; push_cast
    field_simp
  have hpr_eq : ∀ i, pr i = pl i + 2 * h := by
    intro i; simp only [hprdef, hpldef, dyadic]; rw [hh_eq, pow_succ]; push_cast
    field_simp
  have hvar : ∀ i, Var[X i; P] ≤ σ ^ 2 := by
    intro i
    have e : X i = fun ω => B (pm i) ω - (B (pl i) ω + B (pr i) ω) / 2 := funext (hXeq i)
    rw [e, var_comb (hmlp _ (hpm i)) (hmlp _ (hpl i)) (hmlp _ (hpr i)),
      hB.covariance _ (hpm i) _ (hpm i), hB.covariance _ (hpm i) _ (hpl i),
      hB.covariance _ (hpm i) _ (hpr i), hB.covariance _ (hpl i) _ (hpl i),
      hB.covariance _ (hpl i) _ (hpr i), hB.covariance _ (hpr i) _ (hpr i),
      hpm_eq, hpr_eq, hσsq]
    exact fbm_disp_var H (pl i) h hH0 hh0
  -- the maximum and its expectation
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  set M : Ω → ℝ := fun ω => Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    fun i => |X i ω| with hMdef
  have h33 := FBMStrongSim.RecordBreak.lemma_3_3 hn X (fun i => hX.eval i) hcent hσ0.le hvar
  set ℓ : ℝ := ell H delta (k' + 1) with hℓdef
  have hℓσ : ℓ = (2 : ℝ) ^ (delta * K) * σ := by
    rw [hℓdef, ell, hσdef, ← Real.rpow_add (by norm_num)]
    congr 1; rw [hK]; ring
  have hE2 : (2 : ℝ) ^ (delta * K) > 0 := Real.rpow_pos_of_pos (by norm_num) _
  -- Knu bound
  have hKnu : 4 * Real.sqrt K ≤ nu * (2 : ℝ) ^ (delta * K) := by
    have hbdd := knu_bdd nu delta hnu hdelta0
    by_contra hcon
    push Not at hcon
    have hmem : k' + 1 ∈ {n : ℕ | 1 ≤ n ∧ nu * (2 : ℝ) ^ (delta * n) < 4 * Real.sqrt n} :=
      ⟨by omega, by rw [hK] at hcon; exact hcon⟩
    have := le_csSup hbdd hmem
    unfold Knu at hk
    omega
  have hlogn : Real.log (2 * (n : ℝ)) = K * Real.log 2 := by
    rw [hndef, hK]; push_cast
    rw [← pow_succ', Real.log_pow]; push_cast; ring
  have hsqrt : 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ))) ≤ 4 * Real.sqrt K := by
    rw [hlogn]
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; linarith
    have hl0 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have : Real.sqrt (2 * (K * Real.log 2)) ≤ Real.sqrt (4 * K) :=
      Real.sqrt_le_sqrt (by nlinarith)
    have h4 : Real.sqrt (4 * K) = 2 * Real.sqrt K := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) K, show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    linarith
  have hEM : P[M] ≤ nu * ℓ := by
    refine le_trans h33 ?_
    rw [hℓσ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_trans hsqrt hKnu) hσ0.le
  -- Borell–TIS
  set u : ℝ := 2 * nuStar * ℓ with hudef
  have hℓ0 : 0 < ℓ := by rw [hℓσ]; positivity
  have hu : 0 < u := by rw [hudef]; positivity
  have hbt := FBMStrongSim.RecordBreak.borell_tis_finite hn X hX hcent hσ0 hvar hu
  have hsub : {ω | 2 * (nu + nuStar) * ell H delta (k' + 1) ≤ maxDisp (fun s => B s ω) (k' + 1)}
      ⊆ {ω | M ω - P[M] > u} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hmax : maxDisp (fun s => B s ω) (k' + 1) ≤ M ω := by
      unfold maxDisp
      apply Finset.sup'_le
      intro j hj
      have hj' : j < n := by simpa [hndef] using hj
      exact Finset.le_sup' (fun i : Fin n => |X i ω|) (Finset.mem_univ (⟨j, hj'⟩ : Fin n))
    have : nu * ℓ > 0 := by positivity
    rw [← hℓdef] at hω
    linarith
  refine le_trans (measure_mono hsub) (le_trans hbt (ENNReal.ofReal_le_ofReal ?_))
  -- exponent comparison
  have hE2sq : ((2 : ℝ) ^ (delta * K)) ^ 2 = 4 * (2 : ℝ) ^ (2 * K * delta - 2) := by
    rw [Real.rpow_sub (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
    ring_nf
  have hexpo : -u ^ 2 / (2 * σ ^ 2) = -(8 * nuStar ^ 2 * (2 : ℝ) ^ (2 * K * delta - 2)) := by
    have hu2 : u ^ 2 = 4 * nuStar ^ 2 * ((2 : ℝ) ^ (delta * K)) ^ 2 * σ ^ 2 := by
      rw [hudef, hℓσ]; ring
    rw [hu2, hE2sq, neg_div]
    congr 1
    rw [div_eq_iff (by positivity)]
    ring
  rw [hexpo]
  have hQ : 0 < (2 : ℝ) ^ (2 * K * delta - 2) := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : Real.exp (-(8 * nuStar ^ 2 * (2 : ℝ) ^ (2 * K * delta - 2)))
      ≤ Real.exp (-nuStar ^ 2 * (2 : ℝ) ^ (2 * K * delta - 2)) := by
    apply Real.exp_le_exp.2
    have : 0 < nuStar ^ 2 * (2 : ℝ) ^ (2 * K * delta - 2) := by positivity
    nlinarith
  have h2 := Real.exp_pos (-nuStar ^ 2 * (2 : ℝ) ^ (2 * K * delta - 2))
  rw [hK] at h1 h2 ⊢
  linarith
