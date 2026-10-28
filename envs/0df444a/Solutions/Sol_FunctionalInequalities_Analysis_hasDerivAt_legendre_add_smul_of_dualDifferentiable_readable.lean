-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasDerivAt_legendre_add_smul_of_dualDifferentiable_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:20.119473+00:00
-- url     : https://prove2.me/submissions/5e55c206-8278-4063-ac73-ecfbad237837

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_LegendreVariation_Derivative
import Theorems.Thm_FunctionalInequalities_Analysis_exists_delta_nearMaximizer_norm_sub_gradient_lt_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_legendre_maximizer_with_gradient_identity_readable
import Theorems.Thm_FunctionalInequalities_Analysis_legendre_bounded_perturbation_finite_curve_readable

section
noncomputable section
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- One finite value excludes `-∞` for the entire Legendre transform. -/
theorem FunctionalInequalities.Analysis.legendre_ne_bot (φ : E → EReal) (hφ : ProperPotential φ) (y : E) :
    legendre φ y ≠ ⊥ := by
  obtain ⟨x, hx⟩ := hφ.2
  have hb := hφ.1 x
  lift φ x to ℝ using ⟨hx, hb⟩ with r hr
  have hle : ((inner ℝ x y - r : ℝ) : EReal) ≤ legendre φ y := by
    change ((inner ℝ x y - r : ℝ) : EReal) ≤
      ⨆ z : E, (inner ℝ z y : EReal) - φ z
    simpa only [← hr, EReal.coe_sub] using
      (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ z) x)
  exact ne_of_gt ((EReal.bot_lt_coe _).trans_le hle)
end
end
end

noncomputable section
section Variation
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set
/-- Direct first variation of the Legendre transform under a bounded continuous
perturbation. The primal potential may take `⊤`; no primal differentiability,
global finiteness, nonnegativity, or positive-dimensional assumption is made. -/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (φ : E → EReal) (hφ : FunctionalInequalities.Analysis.ProperPotential φ)
    (hlsc : LowerSemicontinuous φ) (y : E)
    (hy : y ∈ interior {q : E | FunctionalInequalities.Analysis.legendre φ q ≠ ⊤})
    (hd : DifferentiableAt ℝ (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y)
    (b : E → ℝ) (hb : Continuous b)
    (hbounded : BddAbove (Set.range fun z : E => |b z|)) :
    HasDerivAt
      (fun t : ℝ =>
        (FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y).toReal)
      (-b (gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y)) 0 := by
    classical
    obtain ⟨M, hMb'⟩ := bddAbove_def.mp hbounded
    have hMb (z : E) : |b z| ≤ M := hMb' _ ⟨z, rfl⟩
    have hM : 0 ≤ M := (abs_nonneg (b 0)).trans (hMb 0)
    have hy_top : FunctionalInequalities.Analysis.legendre φ y ≠ ⊤ := interior_subset hy
    have hy_bot : FunctionalInequalities.Analysis.legendre φ y ≠ ⊥ := FunctionalInequalities.Analysis.legendre_ne_bot φ hφ y

    let p := gradient (fun q => (FunctionalInequalities.Analysis.legendre φ q).toReal) y
    let A : ℝ := (FunctionalInequalities.Analysis.legendre φ y).toReal
    let Ψ : ℝ → EReal :=
      fun t => FunctionalInequalities.Analysis.legendre (fun z : E => φ z + ((t * b z : ℝ) : EReal)) y
    let F : ℝ → ℝ := fun t => (Ψ t).toReal
    let a : E → ℝ := fun z => inner ℝ z y - (φ z).toReal

    have hcurve (t : ℝ) :
        Ψ t ≠ ⊤ ∧ Ψ t ≠ ⊥ ∧ |F t - A| ≤ |t| * M :=
      FunctionalInequalities.Analysis.legendre_bounded_perturbation_finite_curve_readable
        φ hφ y hy_top b M hM hMb t
    have hF (t : ℝ) : (F t : EReal) = Ψ t :=
      EReal.coe_toReal (hcurve t).1 (hcurve t).2.1
    have hF0 : F 0 = A := by
      simp [F, Ψ, A]

    have hterm (z : E) (hz : φ z ≠ ⊤) (t : ℝ) :
        ((a z - t * b z : ℝ) : EReal) =
          (inner ℝ z y : EReal) - (φ z + ((t * b z : ℝ) : EReal)) := by
      have hzcoe : ((φ z).toReal : EReal) = φ z :=
        EReal.coe_toReal hz (hφ.1 z)
      calc
        ((a z - t * b z : ℝ) : EReal) =
            ((inner ℝ z y - ((φ z).toReal + t * b z) : ℝ) : EReal) := by
              congr 1
              dsimp [a]
              ring
        _ = _ := by
          rw [EReal.coe_sub, EReal.coe_add, hzcoe]
    have hterm0 (z : E) (hz : φ z ≠ ⊤) :
        (a z : EReal) = (inner ℝ z y : EReal) - φ z := by
      simpa using hterm z hz 0

    obtain ⟨w, hw, hwgrad⟩ :=
      FunctionalInequalities.Analysis.exists_legendre_maximizer_with_gradient_identity_readable φ hφ hlsc y hy
    have hp : (inner ℝ p y : EReal) - φ p = FunctionalInequalities.Analysis.legendre φ y := by
      simpa only [hwgrad hd] using hw
    have hpfin : φ p ≠ ⊤ := by
      intro ht
      have hh := hp
      rw [ht, EReal.sub_top] at hh
      exact hy_bot hh.symm
    have hpa : a p = A := by
      have hh := congrArg EReal.toReal ((hterm0 p hpfin).trans hp)
      simpa only [EReal.toReal_coe] using hh

    have hupper (z : E) (hz : φ z ≠ ⊤) (t : ℝ) :
        a z - t * b z ≤ F t := by
      apply EReal.coe_le_coe_iff.mp
      rw [hterm z hz t, hF t]
      exact le_iSup
        (fun w : E =>
          (inner ℝ w y : EReal) - (φ w + ((t * b w : ℝ) : EReal))) z

    have hselect (t : ℝ) :
        ∃ z : E, φ z ≠ ⊤ ∧ F t - t ^ 2 ≤ a z - t * b z := by
      by_cases ht : t = 0
      · subst t
        refine ⟨p, hpfin, ?_⟩
        simp [hF0, hpa]
      · have hlt : ((F t - t ^ 2 : ℝ) : EReal) < Ψ t := by
          calc
            ((F t - t ^ 2 : ℝ) : EReal) < (F t : EReal) :=
              EReal.coe_lt_coe_iff.mpr (by
                have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
                linarith)
            _ = Ψ t := hF t
        change ((F t - t ^ 2 : ℝ) : EReal) <
          ⨆ z : E,
            (inner ℝ z y : EReal) - (φ z + ((t * b z : ℝ) : EReal)) at hlt
        obtain ⟨z, hz⟩ := lt_iSup_iff.mp hlt
        have hzfin : φ z ≠ ⊤ := by
          intro htop
          have hh := hz
          rw [htop, EReal.top_add_coe, EReal.sub_top] at hh
          exact (not_lt_of_ge bot_le) hh
        rw [← hterm z hzfin t] at hz
        exact ⟨z, hzfin, (EReal.coe_lt_coe_iff.mp hz).le⟩

    choose z hzfin hz using hselect
    have htb (t : ℝ) : |t * b (z t)| ≤ |t| * M := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hMb (z t)) (abs_nonneg t)
    have hnearReal (t : ℝ) :
        A - (2 * M * |t| + t ^ 2) ≤ a (z t) := by
      have h₁ : -(|t| * M) ≤ F t - A :=
        (abs_le.mp (hcurve t).2.2).1
      have h₂ : -(|t| * M) ≤ t * b (z t) :=
        (abs_le.mp (htb t)).1
      have h₃ := hz t
      linarith
    have hnear (t : ℝ) :
        ((A - (2 * M * |t| + t ^ 2) : ℝ) : EReal) ≤
          (inner ℝ (z t) y : EReal) - φ (z t) := by
      calc
        ((A - (2 * M * |t| + t ^ 2) : ℝ) : EReal) ≤
            (a (z t) : EReal) :=
          EReal.coe_le_coe_iff.mpr (hnearReal t)
        _ = _ := hterm0 (z t) (hzfin t)

    have hsmall :
        Filter.Tendsto (fun t : ℝ => 2 * M * |t| + t ^ 2)
          (nhds 0) (nhds 0) := by
      have hc : Continuous (fun t : ℝ => 2 * M * |t| + t ^ 2) := by
        fun_prop
      simpa using hc.tendsto 0
    have hzlim : Filter.Tendsto z (nhds 0) (nhds p) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨δ, hδ, hδmax⟩ :=
        FunctionalInequalities.Analysis.exists_delta_nearMaximizer_norm_sub_gradient_lt_readable
          φ hφ y hy hd ε hε
      filter_upwards [hsmall.eventually (Iio_mem_nhds hδ)] with t ht
      rw [dist_eq_norm]
      apply hδmax (z t)
      calc
        ((A - δ : ℝ) : EReal) ≤
            ((A - (2 * M * |t| + t ^ 2) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr (by linarith)
        _ ≤ _ := hnear t

    have hbz : Filter.Tendsto (fun t => b (z t))
        (nhds 0) (nhds (b p)) :=
      (hb.tendsto p).comp hzlim
    have hbconst : Filter.Tendsto (fun _ : ℝ => b p)
        (nhds 0) (nhds (b p)) :=
      continuous_const.tendsto 0
    have hbdiff : Filter.Tendsto (fun t => b (z t) - b p)
        (nhds 0) (nhds 0) := by
      simpa only [sub_self] using hbz.sub hbconst
    have hid : Filter.Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0) :=
      continuous_id.tendsto 0
    have hcontrol :
        Filter.Tendsto (fun t : ℝ => |t| + |b (z t) - b p|)
          (nhds 0) (nhds 0) := by
      simpa only [abs_zero, add_zero] using hid.abs.add hbdiff.abs

    have he_nonneg (t : ℝ) : 0 ≤ F t - A + t * b p := by
      have hh := hupper p hpfin t
      rw [hpa] at hh
      linarith
    have he_upper (t : ℝ) :
        F t - A + t * b p ≤ t ^ 2 + |t| * |b (z t) - b p| := by
      have haz : a (z t) ≤ A := by
        have hh := hupper (z t) (hzfin t) 0
        simpa only [hF0, zero_mul, sub_zero] using hh
      have hprod :
          t * (b p - b (z t)) ≤ |t| * |b (z t) - b p| := by
        calc
          t * (b p - b (z t)) ≤ |t * (b p - b (z t))| :=
            le_abs_self _
          _ = |t| * |b (z t) - b p| := by
            rw [abs_mul, abs_sub_comm (b p) (b (z t))]
      have hh := hz t
      linarith

    change HasDerivAt F (-b p) 0
    apply hasDerivAt_iff_isLittleO.mpr
    apply Asymptotics.isLittleO_iff.mpr
    intro c hc
    filter_upwards [hcontrol.eventually (Iio_mem_nhds hc)] with t ht
    simp only [sub_zero, smul_eq_mul, mul_neg, sub_neg_eq_add,
      Real.norm_eq_abs, hF0]
    rw [abs_of_nonneg (he_nonneg t)]
    calc
      F t - A + t * b p ≤ t ^ 2 + |t| * |b (z t) - b p| :=
        he_upper t
      _ = (|t| + |b (z t) - b p|) * |t| := by
        rw [← sq_abs t]
        ring
      _ ≤ c * |t| :=
        mul_le_mul_of_nonneg_right ht.le (abs_nonneg t)
