-- Prove2me | solution 1 for CarlssonPartition.Approx.Supplement.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:17:38.602987+00:00
-- url     : https://prove2.me/submissions/b985f2a1-6868-444b-acc2-1e131691f8cb

import Mathlib
import Definitions.Def_CarlssonPartition_Approx_Supplement_Heterogeneous

open Filter Topology MeasureTheory

open CarlssonPartition
open CarlssonPartition.Approx
open CarlssonPartition.Approx.Supplement

open CarlssonPartition.Equitable (Plane)

/-- Theorem 9 (p. 14): with heterogeneous, location-dependent service of mean `s̄(x)`, a
partition equitable in `∬ √f` and in `∬ (s̄(x) v q + 2 ‖x - x0‖) f` gives an asymptotically
optimal region partitioning policy when every vehicle follows the optimal single-vehicle
policy in its subregion. As the proof (p. ec12, "similar to that of Theorem 6") uses it, the
benchmark `Tstar` is the policy of Theorem 8, characterized by Theorem 8's leading term with
the heterogeneous workload `ρ + 2λ∬‖x - x0‖f/(mvq)`, `ρ = λ∬ s̄(x) f / m`; each district's
delivery time `T i a`, at its own rate `a`, obeys the same leading term with one vehicle and
the conditional density `f_i`. The fleet sum evaluates it at `λ_i = λ ∬_{R_i} f`.
`hmean` (finite spatial mean of `s̄`) is the source's requirement that the workload factor
take values in `(0,1)`; `2 ≤ q` excludes the capacity at which the leading term vanishes. -/
theorem solution (I : CarlssonPartition.Approx.Instance)
    (S : ServiceMarks Plane) (hS : serviceStanding I S) (hq : 2 ≤ I.q)
    (hmean : finiteMeanDomain I S I.R I.f)
    (Rs : Fin I.m → Set Plane) (hP : I.IsPartition Rs)
    (h1 : ∀ i, (∫ x in Rs i, Real.sqrt (I.f x)) =
      (1 / (I.m : ℝ)) * ∫ x in I.R, Real.sqrt (I.f x))
    (h2 : ∀ i, (∫ x in Rs i, (S.mean x * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x) =
      (1 / (I.m : ℝ)) * ∫ x in I.R, (S.mean x * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x)
    (Tstar : ℝ → ℝ)
    (hstar : Tendsto (fun lam => Tstar lam / finiteLeading I S I.m lam I.R I.f)
      (finiteHeavy I S I.m I.R I.f) (𝓝 1))
    (T : Fin I.m → ℝ → ℝ)
    (hT : ∀ i, Tendsto
      (fun a => T i a / finiteLeading I S 1 a (Rs i) (I.fSub (Rs i)))
      (finiteHeavy I S 1 (Rs i) (I.fSub (Rs i))) (𝓝 1)) :
    Tendsto (fun lam => (∑ i, I.pr (Rs i) * T i (I.lamSub lam (Rs i))) / Tstar lam)
      (finiteHeavy I S I.m I.R I.f) (𝓝 1) := by
        obtain ⟨hI, _hSfin⟩ := hS
        obtain ⟨hRc, _hRconv, _hx0, hf0, ⟨K, hK⟩, hf1, hm1, hv, hq1, _hsbar, _hbeta⟩ := hI
        obtain ⟨hnull, hdisj, hunion⟩ := hP
        have hsub : ∀ i, Rs i ⊆ I.R := fun i => hunion ▸ Set.subset_iUnion Rs i
        have hfint : IntegrableOn I.f I.R := by
          by_contra h
          rw [integral_undef h] at hf1
          exact zero_ne_one hf1
        have hfcont : ContinuousOn I.f I.R := hK.continuousOn
        have hBint : IntegrableOn (fun x => ‖x - I.x0‖ * I.f x) I.R :=
          ContinuousOn.integrableOn_compact hRc
            ((continuous_id.sub continuous_const).norm.continuousOn.mul hfcont)
        have hAint : IntegrableOn (fun x => S.mean x * I.f x) I.R := hmean
        have hpsum : ∑ i, I.pr (Rs i) = 1 := by
          have := integral_iUnion_ae (μ := volume) (f := I.f) hnull (fun i j hij => hdisj i j hij)
            (by rw [hunion]; exact hfint)
          rw [hunion, hf1, tsum_fintype] at this
          exact this.symm
        have hp0 : ∀ i, 0 ≤ I.pr (Rs i) := fun i =>
          integral_nonneg_of_ae ((ae_restrict_mem₀ (hnull i)).mono fun x hx => hf0 x (hsub i hx))
        have split : ∀ D, IntegrableOn (fun x => S.mean x * I.f x) D →
            IntegrableOn (fun x => ‖x - I.x0‖ * I.f x) D →
            ∫ x in D, (S.mean x * I.v * (I.q : ℝ) + 2 * ‖x - I.x0‖) * I.f x
              = I.v * I.q * (∫ x in D, S.mean x * I.f x) + 2 * ∫ x in D, ‖x - I.x0‖ * I.f x := by
          intro D ha hb
          rw [← integral_const_mul, ← integral_const_mul, ← integral_add (ha.const_mul _) (hb.const_mul _)]
          congr 1; ext x; ring
        have hev : ∀ᶠ lam in finiteHeavy I S I.m I.R I.f,
            finiteLeading I S I.m lam I.R I.f ≠ 0 ∧ Tstar lam ≠ 0 := by
          have := hstar.eventually (isOpen_Ioi.mem_nhds (show (1:ℝ) ∈ Set.Ioi (1/2) by norm_num))
          filter_upwards [this] with lam hlam
          constructor
          · intro h; rw [h, div_zero] at hlam; norm_num at hlam
          · intro h; rw [h, zero_div] at hlam; norm_num at hlam
        have hinv : Tendsto (fun lam => finiteLeading I S I.m lam I.R I.f / Tstar lam)
            (finiteHeavy I S I.m I.R I.f) (𝓝 1) := by
          have := hstar.inv₀ one_ne_zero
          simp only [inv_div, inv_one] at this
          exact this
        have hterm : ∀ i, Tendsto (fun lam => I.pr (Rs i) * T i (I.lamSub lam (Rs i)) / Tstar lam)
            (finiteHeavy I S I.m I.R I.f) (𝓝 (I.pr (Rs i))) := by
          intro i
          rcases (hp0 i).eq_or_lt with h | h
          · rw [← h]; simp only [zero_mul, zero_div]; exact tendsto_const_nhds
          have hpne : I.pr (Rs i) ≠ 0 := h.ne'
          have e1 : ∫ x in Rs i, S.mean x * I.fSub (Rs i) x
              = (∫ x in Rs i, S.mean x * I.f x) / I.pr (Rs i) := by
            simp only [Instance.fSub, ← mul_div_assoc]; exact integral_div _ _
          have e2 : ∫ x in Rs i, ‖x - I.x0‖ * I.fSub (Rs i) x
              = (∫ x in Rs i, ‖x - I.x0‖ * I.f x) / I.pr (Rs i) := by
            simp only [Instance.fSub, ← mul_div_assoc]; exact integral_div _ _
          have e3 : ∫ x in Rs i, Real.sqrt (I.fSub (Rs i) x)
              = (∫ x in Rs i, Real.sqrt (I.f x)) / Real.sqrt (I.pr (Rs i)) := by
            simp only [Instance.fSub, Real.sqrt_div' _ (hp0 i)]; exact integral_div _ _
          have h2' := h2 i
          rw [split _ (hAint.mono_set (hsub i)) (hBint.mono_set (hsub i)), split _ hAint hBint] at h2'
          have hm0 : (I.m : ℝ) ≠ 0 := by
            have : (1:ℝ) ≤ I.m := by exact_mod_cast hm1
            linarith
          have hq0 : (I.q : ℝ) ≠ 0 := by
            have : (2:ℝ) ≤ I.q := by exact_mod_cast hq
            linarith
          have hv0 : I.v ≠ 0 := hv.ne'
          have hW : ∀ lam, finiteWorkload I S 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
              = finiteWorkload I S I.m lam I.R I.f := by
            intro lam
            unfold finiteWorkload Instance.lamSub
            rw [e1, e2]
            push_cast
            have : lam * I.pr (Rs i) * ((∫ x in Rs i, S.mean x * I.f x) / I.pr (Rs i)) / 1 +
                2 * (lam * I.pr (Rs i)) * ((∫ x in Rs i, ‖x - I.x0‖ * I.f x) / I.pr (Rs i)) /
                  (1 * I.v * I.q)
                = lam * (I.v * I.q * (∫ x in Rs i, S.mean x * I.f x)
                    + 2 * ∫ x in Rs i, ‖x - I.x0‖ * I.f x) / (I.v * I.q) := by
              field_simp
            rw [this, h2']
            field_simp
          have hL : ∀ lam, finiteLeading I S 1 (I.lamSub lam (Rs i)) (Rs i) (I.fSub (Rs i))
              = finiteLeading I S I.m lam I.R I.f := by
            intro lam
            unfold finiteLeading
            rw [hW lam, e3, h1 i]
            unfold Instance.lamSub
            generalize (1 - finiteWorkload I S I.m lam I.R I.f) ^ 2 = D
            rw [div_pow, Real.sq_sqrt (hp0 i)]
            rcases eq_or_ne D 0 with rfl | hD
            · simp
            push_cast
            field_simp
          have hcomp : Tendsto (fun lam => I.lamSub lam (Rs i)) (finiteHeavy I S I.m I.R I.f)
              (finiteHeavy I S 1 (Rs i) (I.fSub (Rs i))) := by
            unfold finiteHeavy
            rw [tendsto_comap_iff]
            have : ((fun a => finiteWorkload I S 1 a (Rs i) (I.fSub (Rs i))) ∘
                fun lam => I.lamSub lam (Rs i)) = fun lam => finiteWorkload I S I.m lam I.R I.f :=
              funext hW
            rw [this]; exact tendsto_comap
          have h3 := (((hT i).comp hcomp).mul hinv).const_mul (I.pr (Rs i))
          rw [mul_one, mul_one] at h3
          refine h3.congr' ?_
          filter_upwards [hev] with lam ⟨hL0, hT0⟩
          simp only [Function.comp, hL]
          field_simp
        have := tendsto_finsetSum Finset.univ (fun i _ => hterm i)
        rw [hpsum] at this
        refine this.congr' (Eventually.of_forall fun lam => ?_)
        simp [Finset.sum_div]
