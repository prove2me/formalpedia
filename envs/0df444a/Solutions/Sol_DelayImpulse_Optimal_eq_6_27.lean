-- Prove2me | solution 1 for DelayImpulse.Optimal.eq_6_27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:24:53.219312+00:00
-- url     : https://prove2.me/submissions/a967d6f7-f405-449f-95de-95ef9f9f3f47
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DelayImpulse_Optimal_Scheme
import Theorems.Thm_DelayImpulse_Optimal_proposition_4_2_i

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open DelayImpulse.Optimal

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {d l : ℕ}
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : Peng1990.SMP.IsStdBrownian P B) (D : Data Ω l)
    (hD : IsStanding (ReflectedBSDE.Existence.augmentedFiltration P hB) P D)
    (Yn On : ℕ → Fam Ω l) (hS : IsScheme (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty Yn On)
    (O : Fam Ω l) (hO : IsLimitObstacle (ReflectedBSDE.Existence.augmentedFiltration P hB) P D hD.U_nonempty (Ylim Yn) O)
    (ν : Ω → WithTop ℝ≥0) (ξ : Ω → Fin l → ℝ) (hξ : IsIndex (ReflectedBSDE.Existence.augmentedFiltration P hB) ν ξ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, |O ν ξ t ω| ≤
      D.γ / D.r * (Real.exp (-D.r * t) - Real.exp (-D.r * ((t : ℝ) + D.Δ)))
      + psiNorm D hD.U_nonempty * Real.exp (-D.r * ((t : ℝ) + D.Δ))
      + D.γ / D.r * Real.exp (-D.r * ((t : ℝ) + D.Δ)) := by
  let m0 : MeasurableSpace Ω := ‹_›
  set 𝓕 := ReflectedBSDE.Existence.augmentedFiltration P hB with h𝓕
  have hr : 0 < D.r := hD.r_pos
  set N := psiNorm D hD.U_nonempty with hN
  -- γ ≥ 0
  have hγ : 0 ≤ D.γ := by
    obtain ⟨ω, hω⟩ := hD.h_bound.exists
    exact (hω 0 0).1.trans (hω 0 0).2
  have hψ : ∀ β ∈ D.U, |D.ψ β| ≤ N := fun β hβ =>
    Finset.le_sup' (f := fun β => |D.ψ β|) hβ
  have hN0 : 0 ≤ N := by
    obtain ⟨β, hβ⟩ := hD.U_nonempty
    exact (abs_nonneg _).trans (hψ β hβ)
  -- conditional expectations preserve bounds `a ≤ f ≤ b` with `a ≤ 0 ≤ b`
  have hce : ∀ (m : MeasurableSpace Ω), m ≤ m0 → ∀ (f : Ω → ℝ) (a b : ℝ),
      a ≤ 0 → 0 ≤ b → (∀ᵐ ω ∂P, a ≤ f ω ∧ f ω ≤ b) →
      ∀ᵐ ω ∂P, a ≤ P[f|m] ω ∧ P[f|m] ω ≤ b := by
    intro m hm f a b ha hb hf
    by_cases hint : Integrable f P
    · have h1 : P[fun _ => a|m] ≤ᵐ[P] P[f|m] :=
        condExp_mono (integrable_const a) hint (hf.mono fun ω h => h.1)
      have h2 : P[f|m] ≤ᵐ[P] P[fun _ => b|m] :=
        condExp_mono hint (integrable_const b) (hf.mono fun ω h => h.2)
      rw [condExp_const hm] at h1 h2
      filter_upwards [h1, h2] with ω h1 h2
      exact ⟨h1, h2⟩
    · rw [condExp_of_not_integrable hint]
      exact Eventually.of_forall fun ω => ⟨ha, hb⟩
  -- the integral of the discounted bound
  have hint_exp : ∀ a b : ℝ, a ≤ b →
      ∫ s in Ico a b, D.γ * Real.exp (-D.r * s) =
        D.γ / D.r * (Real.exp (-D.r * a) - Real.exp (-D.r * b)) := by
    intro a b hab
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hab]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s => -(D.γ / D.r) * Real.exp (-D.r * s))]
    · ring
    · intro x _
      have h := ((hasDerivAt_id x).const_mul (-D.r)).exp.const_mul (-(D.γ / D.r))
      have heq : -(D.γ / D.r) * (Real.exp (-D.r * id x) * (-D.r * 1)) =
          D.γ * Real.exp (-D.r * x) := by
        simp only [id]; field_simp
      rw [heq] at h
      exact h
    · exact (by fun_prop : Continuous fun s : ℝ => D.γ * Real.exp (-D.r * s)).intervalIntegrable _ _
  -- the bound at every fixed time
  have hfix : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, |O ν ξ t ω| ≤
      D.γ / D.r * (Real.exp (-D.r * t) - Real.exp (-D.r * ((t : ℝ) + D.Δ)))
      + N * Real.exp (-D.r * ((t : ℝ) + D.Δ))
      + D.γ / D.r * Real.exp (-D.r * ((t : ℝ) + D.Δ)) := by
    intro t
    set e2 := Real.exp (-D.r * ((t : ℝ) + D.Δ)) with he2
    set c1 := D.γ / D.r * (Real.exp (-D.r * t) - e2) with hc1
    have he2pos : 0 < e2 := Real.exp_pos _
    have hc1 : 0 ≤ c1 := by
      refine mul_nonneg (div_nonneg hγ hr.le) (sub_nonneg.mpr (Real.exp_le_exp.mpr ?_))
      have : (0 : ℝ) ≤ D.Δ := D.Δ.2
      nlinarith
    -- running-reward term
    have hA : ∀ᵐ ω ∂P, 0 ≤ P[fun ω' => segInt (fun s => run D ν ξ s ω') (t : WithTop ℝ≥0)
        ((t : WithTop ℝ≥0) + (D.Δ : WithTop ℝ≥0)) | 𝓕 t] ω ∧
        P[fun ω' => segInt (fun s => run D ν ξ s ω') (t : WithTop ℝ≥0)
        ((t : WithTop ℝ≥0) + (D.Δ : WithTop ℝ≥0)) | 𝓕 t] ω ≤ c1 := by
      refine hce _ (𝓕.le t) _ 0 c1 le_rfl hc1 ?_
      filter_upwards [hD.h_bound] with ω hω
      have hrun0 : ∀ s : ℝ, 0 ≤ run D ν ξ s ω := by
        intro s; unfold run; split_ifs
        · exact mul_nonneg (Real.exp_pos _).le (hω _ _).1
        · exact le_rfl
      have hrun1 : ∀ s : ℝ, run D ν ξ s ω ≤ D.γ * Real.exp (-D.r * s) := by
        intro s; unfold run; split_ifs
        · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hω _ _).2 (Real.exp_pos _).le
        · exact mul_nonneg hγ (Real.exp_pos _).le
      have hseg : segInt (fun s => run D ν ξ s ω) (t : WithTop ℝ≥0)
          ((t : WithTop ℝ≥0) + (D.Δ : WithTop ℝ≥0)) =
          ∫ s in Ico (t : ℝ) ((t : ℝ) + D.Δ), run D ν ξ s ω := by
        rw [← WithTop.coe_add]
        simp [segInt]
      rw [hseg]
      refine ⟨setIntegral_nonneg_ae measurableSet_Ico (Eventually.of_forall fun s _ => hrun0 s), ?_⟩
      have hle := integral_mono_of_nonneg (μ := volume.restrict (Ico (t : ℝ) ((t : ℝ) + D.Δ)))
        (f := fun s => run D ν ξ s ω) (g := fun s => D.γ * Real.exp (-D.r * s))
        (Eventually.of_forall fun s => hrun0 s)
        ((by fun_prop : Continuous fun s : ℝ => D.γ * Real.exp (-D.r * s)).integrableOn_Icc.mono_set
          Ico_subset_Icc_self)
        (Eventually.of_forall fun s => hrun1 s)
      refine hle.trans (le_of_eq ?_)
      rw [hint_exp _ _ (by have : (0 : ℝ) ≤ D.Δ := D.Δ.2; linarith)]
    -- intervention terms
    have hM : ∀ β ∈ D.U, ∀ᵐ ω ∂P,
        -(N * e2) ≤ P[fun ω' => -Real.exp (-D.r * ((t : ℝ) + D.Δ)) * D.ψ β
            + Ylim Yn ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω ∧
        P[fun ω' => -Real.exp (-D.r * ((t : ℝ) + D.Δ)) * D.ψ β
            + Ylim Yn ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω
          ≤ N * e2 + D.γ / D.r * e2 := by
      intro β hβ
      have hidx : IsIndex 𝓕 ν (fun ω'' => ξ ω'' + β) :=
        { stop := hξ.stop
          meas := hξ.meas.add_const β
          finite := (hξ.finite.image (· + β)).subset
            (by rintro _ ⟨ω, rfl⟩; exact ⟨ξ ω, ⟨ω, rfl⟩, rfl⟩) }
      obtain ⟨-, -, hYb, -, -⟩ := proposition_4_2_i P B hB D hD Yn On hS ν _ hidx
      refine hce _ (𝓕.le t) _ _ _ (by nlinarith) (by positivity) ?_
      filter_upwards [hYb] with ω hω
      obtain ⟨h0, h1⟩ := hω (t + D.Δ)
      have hab := abs_le.mp (hψ β hβ)
      have hcast : ((t + D.Δ : ℝ≥0) : ℝ) = (t : ℝ) + D.Δ := by push_cast; ring
      rw [hcast] at h1
      constructor
      · nlinarith
      · nlinarith
    have hM' : ∀ᵐ ω ∂P, ∀ β ∈ D.U,
        -(N * e2) ≤ P[fun ω' => -Real.exp (-D.r * ((t : ℝ) + D.Δ)) * D.ψ β
            + Ylim Yn ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω ∧
        P[fun ω' => -Real.exp (-D.r * ((t : ℝ) + D.Δ)) * D.ψ β
            + Ylim Yn ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω
          ≤ N * e2 + D.γ / D.r * e2 :=
      (Filter.eventually_all_finset _).mpr hM
    filter_upwards [hO.eq ν ξ hξ t, hA, hM'] with ω hOω hAω hMω
    rw [hOω]
    unfold obstacleRHS
    obtain ⟨β0, hβ0⟩ := hD.U_nonempty
    have hsup_lo := (hMω β0 hβ0).1.trans (Finset.le_sup' (fun β =>
        P[fun ω' => -Real.exp (-D.r * ((t : ℝ) + D.Δ)) * D.ψ β
            + Ylim Yn ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω) hβ0)
    have hsup_hi : D.U.sup' hD.U_nonempty (fun β =>
        P[fun ω' => -Real.exp (-D.r * ((t : ℝ) + D.Δ)) * D.ψ β
            + Ylim Yn ν (fun ω'' => ξ ω'' + β) (t + D.Δ) ω' | 𝓕 t] ω) ≤ N * e2 + D.γ / D.r * e2 :=
      Finset.sup'_le _ _ fun β hβ => (hMω β hβ).2
    have hpos : 0 ≤ D.γ / D.r * e2 := mul_nonneg (div_nonneg hγ hr.le) he2pos.le
    rw [abs_le]
    constructor <;> linarith [hAω.1, hAω.2]
  -- from rational times to all times, by right-continuity of `O`
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, |O ν ξ (q : ℝ).toNNReal ω| ≤
      D.γ / D.r * (Real.exp (-D.r * ((q : ℝ).toNNReal : ℝ)) -
        Real.exp (-D.r * (((q : ℝ).toNNReal : ℝ) + D.Δ)))
      + N * Real.exp (-D.r * (((q : ℝ).toNNReal : ℝ) + D.Δ))
      + D.γ / D.r * Real.exp (-D.r * (((q : ℝ).toNNReal : ℝ) + D.Δ)) :=
    ae_all_iff.mpr fun q => hfix _
  filter_upwards [hall] with ω hω t
  set g : ℝ≥0 → ℝ := fun t => D.γ / D.r * (Real.exp (-D.r * t) - Real.exp (-D.r * ((t : ℝ) + D.Δ)))
      + N * Real.exp (-D.r * ((t : ℝ) + D.Δ))
      + D.γ / D.r * Real.exp (-D.r * ((t : ℝ) + D.Δ)) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  -- rational approximations from the right
  have hq : ∀ n : ℕ, ∃ q : ℚ, (t : ℝ) < q ∧ (q : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose q hq1 hq2 using hq
  set u : ℕ → ℝ≥0 := fun n => ((q n : ℝ)).toNNReal with hu
  have hucoe : ∀ n, ((u n : ℝ≥0) : ℝ) = q n := fun n =>
    Real.coe_toNNReal _ ((t.2).trans (hq1 n).le)
  have hut : Tendsto u atTop (𝓝[Ici t] t) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
    · rw [← NNReal.tendsto_coe]
      simp_rw [hucoe]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun n => (hq1 n).le) (fun n => (hq2 n).le)
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (t : ℝ)
    · show t ≤ u n
      rw [← NNReal.coe_le_coe, hucoe]; exact (hq1 n).le
  have h1 : Tendsto (fun n => |O ν ξ (u n) ω|) atTop (𝓝 |O ν ξ t ω|) :=
    ((hO.rcont ν ξ hξ ω t).tendsto.comp hut).abs
  have h2 : Tendsto (fun n => g (u n)) atTop (𝓝 (g t)) :=
    (hgc.tendsto t).comp (tendsto_nhdsWithin_iff.mp hut).1
  exact le_of_tendsto_of_tendsto' h1 h2 fun n => hω (q n)
