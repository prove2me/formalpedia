-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.retimed_weighted_process_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T07:07:38.203797+00:00
-- url     : https://prove2.me/submissions/396641d1-1b40-48c7-ae3a-7eaa2a503b6f

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_approximate_process_limits
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths

open MeasureTheory ProbabilityTheory Filter Topology Set
open BellWilliams2001.ThresholdPolicy
open scoped ENNReal NNReal

private theorem component_bound {k : ℕ} (v : Fin k → ℝ) (i : Fin k) :
    |v i| ≤ ‖v‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i

private theorem sum_weighted_difference {k : ℕ} (a x y : Fin k → ℝ) (ε : ℝ)
    (h : ∀ i, |x i-y i| ≤ ε) :
    |(∑ i,a i*x i)-(∑ i,a i*y i)| ≤ (∑ i, |a i|)*ε := by
  rw [←Finset.sum_sub_distrib,Finset.sum_mul]
  simp only [←mul_sub]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _))

set_option maxHeartbeats 3200000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k : ℕ} (X : ℕ → Ω → ℝ → Fin k → ℝ) (Z : Ω' → ℝ → Fin k → ℝ)
    (hF : ∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => X n ω (τ j)) atTop
        (fun ω j => Z ω (τ j)) (fun _ => P) P')
    (hM : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η)
    (a : ℕ → Fin k → ℝ) (b : ℕ → ℝ) (α : Fin k → ℝ) (β : ℝ)
    (ha : Tendsto a atTop (𝓝 α)) (hb : Tendsto b atTop (𝓝 β))
    (G : ℕ → Ω → ℝ → Fin k → ℝ) (g : ℝ → Fin k → ℝ)
    (hG : UocInProb P G g)
    (hg : ∀ t : ℝ, 0 ≤ t → ∀ i, g t i ∈ Icc 0 t)
    (hgLip : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ i, |g s i-g t i| ≤ |s-t|)
    (hGt : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t → ∀ i, G n ω t i ∈ Icc 0 t)
    (Y : ℕ → Ω → ℝ → Fin 1 → ℝ)
    (hY : ∀ n t, 0 ≤ t → AEMeasurable (fun ω => Y n ω t) P)
    (hYeq : ∀ᶠ n in atTop, ∀ ω t, 0 ≤ t →
      Y n ω t = ![(∑ i, a n i * X n ω (G n ω t i) i) + b n*t]) :
    let W (ω : Ω') (t : ℝ) := ![(∑ i, α i * Z ω (g t i) i) + β*t]
    (∀ (q : ℕ) (τ : Fin q → ℝ), (∀ j, 0 ≤ τ j) →
      TendstoInDistribution (fun n ω j => Y n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => P) P') ∧
    (∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Y n ω s-Y n ω t‖} ≤ ENNReal.ofReal η) := by
  intro W
  let D (n : ℕ) (ω : Ω) (t : ℝ) := ![(∑ i, a n i * X n ω (g t i) i) + b n*t]
  let C := (∑ i, |α i|) + |β| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hWeights : ∀ᶠ n in atTop, (∑ i, |a n i|) + |b n| ≤ C := by
    have h (i : Fin k) := ((tendsto_pi_nhds.1 ha) i).abs
    apply ((tendsto_order.1 ((tendsto_finsetSum _ fun i _ => h i).add hb.abs)).2 C ?_).mono
      (fun _ hh => hh.le)
    dsimp [C]
    linarith
  have hDF (q : ℕ) (τ : Fin q → ℝ) (hτ : ∀ j, 0 ≤ τ j) :
      TendstoInDistribution (fun n ω j => D n ω (τ j)) atTop
        (fun ω j => W ω (τ j)) (fun _ => P) P' := by
    let e : Fin q × Fin k ≃ Fin (q*k) := finProdFinEquiv
    let t (i : Fin (q*k)) := g (τ (e.symm i).1) (e.symm i).2
    have ht (i : Fin (q*k)) : 0 ≤ t i := (hg _ (hτ _) _).1
    let f (p : (Fin (q*k) → Fin k → ℝ) × ((Fin k → ℝ) × ℝ)) (j : Fin q) : Fin 1 → ℝ :=
      ![(∑ i, p.2.1 i * p.1 (e (j,i)) i) + p.2.2*τ j]
    have hf : Continuous f := by
      apply continuous_pi
      intro j
      apply continuous_pi
      intro l
      have hl : l = 0 := Fin.eq_zero l
      subst l
      exact (continuous_finsetSum _ fun i _ =>
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd)).mul
          ((continuous_apply i).comp ((continuous_apply (e (j,i))).comp continuous_fst))).add
        ((continuous_snd.comp continuous_snd).mul_const (τ j))
    have hCoe : TendstoInMeasure P (fun n (_ : Ω) => (a n,b n)) atTop (fun _ => (α,β)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
        (ae_of_all _ fun _ => ha.prodMk_nhds hb)
    have h := (hF (q*k) t ht).continuous_comp_prodMk_of_tendstoInMeasure_const hf hCoe
      (fun _ => aemeasurable_const)
    simpa only [f,t,D,W,Function.comp_def,Equiv.symm_apply_apply] using h
  have hDM (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          ε ≤ ‖D n ω s-D n ω t‖} ≤ ENNReal.ofReal η := by
    let η₀ := ε/(2*C)
    have hp : 0 < η₀ := by dsimp [η₀]; positivity
    obtain ⟨δ,hδ,hBad⟩ := hM T η₀ η hp hη
    refine ⟨min δ η₀,lt_min hδ hp,?_⟩
    filter_upwards [hBad,hWeights] with n hn hw
    apply le_trans (measure_mono ?_) hn
    rintro ω ⟨s,hs,t,ht,hst,hb⟩
    by_contra hNo
    have hi (i : Fin k) : |X n ω (g s i) i-X n ω (g t i) i| ≤ η₀ := by
      have h₁ := (hg s hs.1 i)
      have h₂ := (hg t ht.1 i)
      have hClose := (hgLip s t hs.1 ht.1 i).trans (hst.trans (min_le_left _ _))
      have h := lt_of_not_ge (fun h => hNo ⟨g s i,⟨h₁.1,h₁.2.trans hs.2⟩,g t i,
        ⟨h₂.1,h₂.2.trans ht.2⟩,hClose,h⟩)
      exact ((component_bound (X n ω (g s i)-X n ω (g t i)) i).trans h.le)
    have hSD := sum_weighted_difference (a n) (fun i => X n ω (g s i) i)
      (fun i => X n ω (g t i) i) η₀ hi
    have hLin : |b n*(s-t)| ≤ |b n| *η₀ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hst.trans (min_le_right _ _)) (abs_nonneg _)
    have hN : ‖D n ω s-D n ω t‖ ≤ ((∑ i, |a n i|)+|b n|)*η₀ := by
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro i
      have hi0 : i = 0 := Fin.eq_zero i
      subst i
      simp only [Real.norm_eq_abs,Pi.sub_apply,D,Matrix.cons_val_zero]
      rw [show (∑ i, a n i * X n ω (g s i) i) + b n*s -
          ((∑ i, a n i * X n ω (g t i) i)+b n*t) =
          ((∑ i, a n i * X n ω (g s i) i)-(∑ i, a n i * X n ω (g t i) i))+b n*(s-t) by ring]
      exact (abs_add_le _ _).trans (by linarith only [hSD,hLin])
    have hEq : C*η₀ = ε/2 := by dsimp only [η₀]; field_simp
    have hc := (mul_le_mul_of_nonneg_right hw hp.le).trans_eq hEq
    linarith
  have hA (T : ℕ) (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε ≤ ‖Y n ω t-D n ω t‖}) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.2
    intro η hη
    obtain ⟨η',_,hp,hη'⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
    have hηn := ENNReal.ofReal_pos.1 hp
    let e := ε/(2*C)
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨δ,hδ,hBad⟩ := hM T e (η'/2) he (by positivity)
    let S (n : ℕ) := {ω | ENNReal.ofReal δ ≤ supDist (G n ω) g T}
    let F (n : ℕ) := {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ δ ∧ e ≤ ‖X n ω s-X n ω t‖}
    have hS : ∀ᶠ n in atTop, P (S n) ≤ ENNReal.ofReal (η'/2) :=
      ((hG T (Nat.cast_nonneg _) δ hδ).eventually_lt_const (ENNReal.ofReal_pos.2 (by positivity))).mono
        (fun _ hn => hn.le)
    filter_upwards [hS,hBad,hGt,hYeq,hWeights] with n hn hs ht hEq hw
    have hm : P {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), ε ≤ ‖Y n ω t-D n ω t‖} ≤ P (S n ∪ F n) := by
      apply measure_mono
      rintro ω ⟨t,htm,hb⟩
      by_contra hNo
      have hNear (i : Fin k) : |G n ω t i-g t i| ≤ δ := by
        have hsum : |G n ω t i-g t i| ≤ ∑ j, |G n ω t j-g t j| :=
          Finset.single_le_sum (f := fun j => |G n ω t j-g t j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
        have hSup : ENNReal.ofReal (∑ j, |G n ω t j-g t j|) ≤ supDist (G n ω) g T :=
          le_iSup_of_le t (le_iSup_of_le htm le_rfl)
        exact ((ENNReal.ofReal_lt_ofReal_iff hδ).1 ((ENNReal.ofReal_le_ofReal hsum).trans_lt
          (hSup.trans_lt (lt_of_not_ge (fun h => hNo (Or.inl h)))))).le
      have hi (i : Fin k) : |X n ω (G n ω t i) i-X n ω (g t i) i| ≤ e := by
        have hv := ht ω t htm.1 i
        have hz := hg t htm.1 i
        have hNorm : ‖X n ω (G n ω t i)-X n ω (g t i)‖ ≤ e := (lt_of_not_ge
          (fun h => hNo (Or.inr ⟨G n ω t i,⟨hv.1,hv.2.trans htm.2⟩,g t i,
            ⟨hz.1,hz.2.trans htm.2⟩,hNear i,h⟩))).le
        exact (component_bound (X n ω (G n ω t i)-X n ω (g t i)) i).trans hNorm
      have heq : C*e = ε/2 := by dsimp only [e]; field_simp
      have hW : (∑ i, |a n i|)*e ≤ ε/2 :=
        (mul_le_mul_of_nonneg_right ((le_add_of_nonneg_right (abs_nonneg (b n))).trans hw) he.le).trans_eq heq
      have hDist : ‖Y n ω t-D n ω t‖ ≤ ε/2 := by
        rw [hEq ω t htm.1, pi_norm_le_iff_of_nonneg (by positivity)]
        intro i
        have hi0 : i = 0 := Fin.eq_zero i
        subst i
        simp only [Real.norm_eq_abs,Pi.sub_apply,D,Matrix.cons_val_zero,add_sub_add_right_eq_sub]
        exact (sum_weighted_difference (a n) (fun i => X n ω (G n ω t i) i)
          (fun i => X n ω (g t i) i) e hi).trans hW
      linarith
    calc
      _ ≤ P (S n ∪ F n) := hm
      _ ≤ P (S n) + P (F n) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (η'/2) + ENNReal.ofReal (η'/2) := add_le_add hn hs
      _ = ENNReal.ofReal η' := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
      _ ≤ η := hη'.le
  exact approximate_process_limits P P' D Y W hY hDF hDM hA
